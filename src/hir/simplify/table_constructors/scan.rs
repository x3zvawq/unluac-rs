//! 这个子模块负责从连续 stmt 区域里扫描表构造器候选步骤。
//!
//! 它依赖 HIR 已经稳定的赋值/构造器形状，只回答“哪些 stmt 可视为构造器 seed、record、
//! setlist、producer 或 trailing handoff”，不会在这里直接改写语句。
//! 例如：`local t = {}; t.x = 1; t.y = 2` 会在这里被扫描成一串 constructor steps。

use crate::ast::DecompileDialect;
use crate::hir::common::{HirExpr, HirLValue, HirStmt, HirTableConstructor, HirValuePack};

use super::bindings::{
    BindingIndex, BindingOccurrenceIndex, binding_from_expr, binding_from_lvalue,
    expr_uses_binding, lvalue_uses_binding,
};
use super::builder::ConstructorBuilder;
use super::rebuild::{RegionRebuildContext, try_extend_constructor_from_steps};
use super::{RebuildScratch, RegionStep, TableBinding};

pub(super) fn constructor_seed(stmt: &HirStmt) -> Option<(TableBinding, HirTableConstructor)> {
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
            Some((TableBinding::Local(*binding), (**table).clone()))
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
            Some((binding, (**table).clone()))
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
    let mut best_end = None;
    let mut committed_builder = ConstructorBuilder::from_constructor(constructor);
    let scan_stmts = &block.stmts[(seed_index + 1)..];
    for (offset, stmt) in scan_stmts.iter().enumerate() {
        let index = seed_index + 1 + offset;
        let remaining_uses = binding_occurrences.remaining_uses_after(stmt_ids[index]);
        if keyed_write_step(stmt, binding) {
            steps.push(RegionStep::Record { stmt_index: index });
            let mut rebuild_context = RegionRebuildContext::new(
                block,
                binding_index,
                remaining_uses,
                materialized_binding_counts,
                dialect,
                scratch,
            );
            if try_extend_constructor_from_steps(
                &mut committed_builder,
                &steps,
                &mut rebuild_context,
            ) {
                best_end = Some(index);
                steps.clear();
            }
            continue;
        }
        if producer_steps(stmt, index, binding, &mut steps) {
            continue;
        }
        if table_set_list_step(stmt, binding) {
            steps.push(RegionStep::SetList { stmt_index: index });
            let mut rebuild_context = RegionRebuildContext::new(
                block,
                binding_index,
                remaining_uses,
                materialized_binding_counts,
                dialect,
                scratch,
            );
            if try_extend_constructor_from_steps(
                &mut committed_builder,
                &steps,
                &mut rebuild_context,
            ) {
                best_end = Some(index);
                steps.clear();
            }
            continue;
        }
        break;
    }

    // 不要求“扫描到的最长前缀”整体可折叠。
    // 某些稳定构造区域后面会紧跟无关的 local producer；如果继续把它们吞进候选区，
    // 末尾那批未消费 producer 会让整段 region 失败，反而错过前面已经足够安全的
    // `{ ... }` 前缀。因此这里持续记住“最后一个成功前缀”，在真正遇到无关语句时
    // 回退到最近一次可证明安全的构造器边界。
    best_end.map(|end_index| (committed_builder.into_constructor(), end_index))
}

/// open SETLIST 前的 producer 若不能安全内联，允许把空表 owner 延后到 SETLIST 原位。
/// producer 本身全部保留，因此这里只需证明 seed 在夹层中从未被读取或改写。
pub(super) fn try_defer_open_set_list_owner(
    block: &crate::hir::common::HirBlock,
    seed_index: usize,
    binding: TableBinding,
    seed: &HirTableConstructor,
) -> Option<(HirTableConstructor, usize)> {
    if !seed.fields.is_empty() || seed.trailing_multivalue.is_some() {
        return None;
    }

    let mut ignored_steps = Vec::new();
    for (offset, stmt) in block.stmts[(seed_index + 1)..].iter().enumerate() {
        let stmt_index = seed_index + 1 + offset;
        ignored_steps.clear();
        if producer_steps(stmt, stmt_index, binding, &mut ignored_steps) {
            continue;
        }

        let HirStmt::TableSetList(set_list) = stmt else {
            return None;
        };
        let tail = set_list.values.tail.as_ref()?;
        if tail.exact_width().is_some()
            || !table_set_list_step(stmt, binding)
            || set_list.start_index != 1
        {
            return None;
        }

        let mut constructor = seed.clone();
        constructor.fields.extend(
            set_list
                .values
                .fixed
                .iter()
                .cloned()
                .map(crate::hir::common::HirTableField::Array),
        );
        constructor.trailing_multivalue = Some(tail.clone());
        return Some((constructor, stmt_index));
    }
    None
}

pub(super) fn trailing_constructor_handoff(
    stmts: &[HirStmt],
    binding: TableBinding,
    binding_mentioned_after: bool,
) -> Option<HirLValue> {
    let HirStmt::Assign(assign) = stmts.first()? else {
        return None;
    };
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    if binding_from_expr(value) != Some(binding) {
        return None;
    }
    // 这里只认“构造器 seed 的唯一尾部 handoff”：
    // - target 自己不能再回看 seed binding，否则不是所有权转移而是继续同表写入；
    // - handoff 之后也不能再出现这个 binding，否则后层还需要它的稳定身份。
    if binding_from_lvalue(target) == Some(binding)
        || lvalue_uses_binding(target, binding)
        || binding_mentioned_after
    {
        return None;
    }
    Some(target.clone())
}

fn keyed_write_step(stmt: &HirStmt, binding: TableBinding) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
        return false;
    };
    if assign.values.tail.is_some() {
        return false;
    }
    let [value] = assign.values.fixed.as_slice() else {
        return false;
    };
    if binding_from_expr(&access.base) != Some(binding) {
        return false;
    }
    if expr_uses_binding(&access.key, binding) || expr_uses_binding(value, binding) {
        return false;
    }
    true
}

fn producer_steps(
    stmt: &HirStmt,
    stmt_index: usize,
    constructor_binding: TableBinding,
    steps: &mut Vec<RegionStep>,
) -> bool {
    match stmt {
        HirStmt::LocalDecl(local_decl) => producer_steps_from_bindings(
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
        ),
        HirStmt::Assign(assign) => {
            let bindings = assign
                .targets
                .iter()
                .map(binding_from_lvalue)
                .collect::<Option<Vec<_>>>();
            let Some(bindings) = bindings else {
                return false;
            };
            producer_steps_from_bindings(
                bindings,
                &assign.values,
                constructor_binding,
                stmt_index,
                steps,
            )
        }
        _ => false,
    }
}

fn producer_steps_from_bindings(
    bindings: Vec<TableBinding>,
    values: &HirValuePack,
    constructor_binding: TableBinding,
    stmt_index: usize,
    steps: &mut Vec<RegionStep>,
) -> bool {
    if bindings.is_empty()
        || bindings.contains(&constructor_binding)
        || values.is_empty()
        || values
            .iter()
            .any(|value| expr_uses_binding(value, constructor_binding))
    {
        return false;
    }

    if values.tail.is_none() && bindings.len() == values.fixed.len() {
        steps.extend((0..bindings.len()).map(|slot_index| RegionStep::Producer {
            stmt_index,
            slot_index,
        }));
        return true;
    }

    if bindings.len() > 1 && values.fixed.is_empty() && values.tail.is_some() {
        steps.push(RegionStep::ProducerGroup { stmt_index });
        return true;
    }

    false
}

fn table_set_list_step(stmt: &HirStmt, binding: TableBinding) -> bool {
    let HirStmt::TableSetList(set_list) = stmt else {
        return false;
    };
    if binding_from_expr(&set_list.base) != Some(binding) {
        return false;
    }
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
        return false;
    }
    true
}
