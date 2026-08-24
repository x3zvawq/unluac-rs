//! 这个子模块负责从连续 stmt 区域里扫描表构造器候选步骤。
//!
//! 它依赖 HIR 已经稳定的赋值/构造器形状，只回答“哪些 stmt 可视为构造器 seed、record、
//! setlist 或 producer”，不会在这里直接改写语句。
//! 例如：`local t = {}; t.x = 1; t.y = 2` 会在这里被扫描成一串 constructor steps。

use crate::ast::DecompileDialect;
use crate::hir::common::{HirExpr, HirLValue, HirStmt, HirTableConstructor, HirValuePack};

use super::bindings::{
    BindingIndex, BindingOccurrenceIndex, binding_from_expr, binding_from_lvalue, expr_uses_binding,
};
use super::builder::ConstructorBuilder;
use super::rebuild::producer_value_can_be_dropped;
use super::rebuild::{RegionRebuildContext, try_extend_constructor_from_steps};
use super::{BindingId, RebuildScratch, RegionStep, TableBinding};

/// 按稳定 stmt id 记录每个 binding 最后可能扩展构造器的位置。
///
/// 空表 seed 只有在后面存在同 binding 的 record 或 SETLIST 时才需要扫描中间 producer；
/// 以最后位置作为 horizon，既允许跨过其他 seed，又能在线性预处理后排除独立 seed 的后缀扫描。
pub(super) struct ConstructorWriteIndex {
    last_write: Vec<Option<usize>>,
}

impl ConstructorWriteIndex {
    pub(super) fn new(stmts: &[HirStmt], binding_index: &BindingIndex) -> Self {
        let mut index = Self {
            last_write: vec![None; binding_index.len()],
        };
        for (stmt_id, stmt) in stmts.iter().enumerate() {
            if let Some(binding) = keyed_write_binding(stmt) {
                let binding_id = binding_index
                    .id_of(binding)
                    .expect("table record binding should be indexed");
                index.last_write[binding_id] = Some(stmt_id);
            } else if let Some(binding) = table_set_list_binding(stmt) {
                let binding_id = binding_index
                    .id_of(binding)
                    .expect("table set-list binding should be indexed");
                index.last_write[binding_id] = Some(stmt_id);
            }
        }
        index
    }

    pub(super) fn has_write_after(&self, binding_id: BindingId, stmt_id: usize) -> bool {
        self.last_write[binding_id].is_some_and(|last| last > stmt_id)
    }
}

pub(super) fn constructor_seed(stmt: &HirStmt) -> Option<(TableBinding, &HirTableConstructor)> {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            let [binding] = local_decl.bindings.as_slice() else {
                return None;
            };
            if local_decl.values.tail.is_some() {
                return None;
            }
            let [HirExpr::TableConstructor(table)] = local_decl.values.fixed.as_slice() else {
                return None;
            };
            Some((TableBinding::Local(*binding), table.as_ref()))
        }
        HirStmt::Assign(assign) => {
            let [target] = assign.targets.as_slice() else {
                return None;
            };
            let binding = binding_from_lvalue(target)?;
            if assign.values.tail.is_some() {
                return None;
            }
            let [HirExpr::TableConstructor(table)] = assign.values.fixed.as_slice() else {
                return None;
            };
            Some((binding, table.as_ref()))
        }
        _ => None,
    }
}

pub(super) fn install_constructor_seed(stmt: &mut HirStmt, constructor: HirTableConstructor) {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            local_decl.values = vec![HirExpr::TableConstructor(Box::new(constructor))].into();
        }
        HirStmt::Assign(assign) => {
            assign.values = vec![HirExpr::TableConstructor(Box::new(constructor))].into();
        }
        _ => unreachable!("constructor region must start from a constructor seed"),
    }
}

pub(super) fn constructor_uses_binding(
    constructor: &HirTableConstructor,
    binding: TableBinding,
) -> bool {
    constructor.fields.iter().any(|field| match field {
        crate::hir::common::HirTableField::Array(value) => expr_uses_binding(value, binding),
        crate::hir::common::HirTableField::Record(record) => {
            matches!(&record.key, crate::hir::common::HirTableKey::Expr(key) if expr_uses_binding(key, binding))
                || expr_uses_binding(&record.value, binding)
        }
    }) || constructor
        .trailing_multivalue
        .as_ref()
        .is_some_and(|tail| expr_uses_binding(tail.as_expr(), binding))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn try_rebuild_constructor_region(
    block: &crate::hir::common::HirBlock,
    seed_index: usize,
    binding: TableBinding,
    constructor: HirTableConstructor,
    binding_index: &BindingIndex,
    binding_occurrences: &BindingOccurrenceIndex,
    materialized_binding_counts: &[u32],
    stmt_ids: &[usize],
    dialect: DecompileDialect,
    scratch: &mut RebuildScratch,
) -> Option<(HirTableConstructor, usize)> {
    let mut steps = Vec::new();
    let mut use_horizon: Option<usize> = None;
    let mut best_end = None;
    let mut committed_builder = ConstructorBuilder::from_constructor(constructor);
    let scan_stmts = &block.stmts[(seed_index + 1)..];
    for (offset, stmt) in scan_stmts.iter().enumerate() {
        let index = seed_index + 1 + offset;
        let remaining_uses = binding_occurrences.remaining_uses_after(stmt_ids[index]);
        let boundary_step = if keyed_write_step(stmt, binding) {
            RegionStep::Record { stmt_index: index }
        } else if let Some(producer_bindings) = producer_steps(stmt, index, binding, &mut steps) {
            for producer_binding in producer_bindings {
                let binding_id = binding_index
                    .id_of(producer_binding)
                    .expect("producer binding should be indexed");
                if let Some(last_use) = binding_occurrences.last_use(binding_id) {
                    use_horizon =
                        Some(use_horizon.map_or(last_use, |horizon| horizon.max(last_use)));
                }
            }
            continue;
        } else if table_set_list_step(stmt, binding) {
            RegionStep::SetList { stmt_index: index }
        } else {
            break;
        };
        steps.push(boundary_step);
        // Producer 的最后一次 use 尚在 region 外时，本次事务必然因 remaining_uses
        // 回滚；候选仍完整保留到 horizon，不能因其他失败原因提前丢弃。
        if use_horizon.is_some_and(|horizon| stmt_ids[index] < horizon) {
            continue;
        }
        let mut rebuild_context = RegionRebuildContext::new(
            block,
            binding_index,
            remaining_uses,
            materialized_binding_counts,
            dialect,
            scratch,
        );
        if try_extend_constructor_from_steps(&mut committed_builder, &steps, &mut rebuild_context) {
            best_end = Some(index);
            steps.clear();
            use_horizon = None;
        } else {
            // horizon 已覆盖未来对现有 producer 的引用；后缀无法改写已失败的 segment。
            break;
        }
    }

    // 不要求“扫描到的最长前缀”整体可折叠。
    // 某些稳定构造区域后面会紧跟无关的 local producer；如果继续把它们吞进候选区，
    // 末尾那批未消费 producer 会让整段 region 失败，反而错过前面已经足够安全的
    // `{ ... }` 前缀。因此这里持续记住“最后一个成功前缀”，在真正遇到无关语句时
    // 回退到最近一次可证明安全的构造器边界。
    best_end.map(|end_index| (committed_builder.into_constructor(), end_index))
}

fn keyed_write_step(stmt: &HirStmt, binding: TableBinding) -> bool {
    keyed_write_binding(stmt) == Some(binding)
}

fn keyed_write_binding(stmt: &HirStmt) -> Option<TableBinding> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    let binding = binding_from_expr(&access.base)?;
    if expr_uses_binding(&access.key, binding) || expr_uses_binding(value, binding) {
        return None;
    }
    Some(binding)
}

fn producer_steps(
    stmt: &HirStmt,
    stmt_index: usize,
    constructor_binding: TableBinding,
    steps: &mut Vec<RegionStep>,
) -> Option<Vec<TableBinding>> {
    match stmt {
        HirStmt::LocalDecl(local_decl) if local_decl.values.tail.is_none() => {
            producer_steps_from_bindings(
                local_decl
                    .bindings
                    .iter()
                    .copied()
                    .map(TableBinding::Local)
                    .collect::<Vec<_>>(),
                &local_decl.values,
                constructor_binding,
                stmt_index,
                steps,
            )
        }
        // Existing assignments keep the physical overwrite point of their target.  They may
        // own a source-visible value even when the result is consumed only once.
        HirStmt::Assign(_) => None,
        _ => None,
    }
}

fn producer_steps_from_bindings(
    bindings: Vec<TableBinding>,
    values: &HirValuePack,
    constructor_binding: TableBinding,
    stmt_index: usize,
    steps: &mut Vec<RegionStep>,
) -> Option<Vec<TableBinding>> {
    if bindings.is_empty()
        || bindings.contains(&constructor_binding)
        || values.is_empty()
        || values
            .iter()
            .any(|value| expr_uses_binding(value, constructor_binding))
    {
        return None;
    }

    if values.tail.is_none() && bindings.len() == values.fixed.len() {
        steps.extend((0..bindings.len()).map(|slot_index| RegionStep::Producer {
            stmt_index,
            slot_index,
        }));
        return Some(bindings);
    }

    if bindings.len() > 1 && values.fixed.is_empty() && values.tail.is_some() {
        steps.push(RegionStep::ProducerGroup { stmt_index });
        return Some(bindings);
    }

    None
}

pub(super) fn seed_overwrite_delay_is_unobservable(
    block: &crate::hir::common::HirBlock,
    seed_index: usize,
    end_index: usize,
    binding: TableBinding,
) -> bool {
    block.stmts[(seed_index + 1)..=end_index]
        .iter()
        .all(|stmt| match stmt {
            HirStmt::LocalDecl(decl) => {
                decl.values.tail.is_none()
                    && decl.values.fixed.len() == decl.bindings.len()
                    && decl.values.fixed.iter().all(producer_value_can_be_dropped)
                    && decl
                        .values
                        .fixed
                        .iter()
                        .all(|value| !expr_uses_binding(value, binding))
            }
            HirStmt::Assign(assign) => {
                let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
                    return false;
                };
                assign.values.tail.is_none()
                    && binding_from_expr(&access.base) == Some(binding)
                    && seed_delay_expr_is_unobservable(&access.key)
                    && assign
                        .values
                        .fixed
                        .iter()
                        .all(seed_delay_expr_is_unobservable)
            }
            HirStmt::TableSetList(set_list) => {
                binding_from_expr(&set_list.base) == Some(binding)
                    && set_list.values.tail.is_none()
                    && set_list
                        .values
                        .fixed
                        .iter()
                        .all(seed_delay_expr_is_unobservable)
            }
            _ => false,
        })
}

pub(super) fn seed_delay_expr_is_unobservable(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Vector(_)
            | HirExpr::Complex { .. }
            | HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::TempRef(_)
    )
}

fn table_set_list_step(stmt: &HirStmt, binding: TableBinding) -> bool {
    table_set_list_binding(stmt) == Some(binding)
}

fn table_set_list_binding(stmt: &HirStmt) -> Option<TableBinding> {
    let HirStmt::TableSetList(set_list) = stmt else {
        return None;
    };
    let binding = binding_from_expr(&set_list.base)?;
    if set_list
        .values
        .fixed
        .iter()
        .any(|expr| expr_uses_binding(expr, binding))
        || set_list
            .values
            .tail
            .as_ref()
            .is_some_and(|tail| expr_uses_binding(tail.as_expr(), binding))
    {
        return None;
    }
    Some(binding)
}
