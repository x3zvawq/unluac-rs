//! 这个子模块负责从连续 stmt 区域里扫描表构造器候选步骤。
//!
//! 它依赖 HIR 已经稳定的赋值/构造器形状，只回答“哪些 stmt 可视为构造器 seed、record、
//! setlist、producer”，不会在这里直接改写语句。
//! 例如：`local t = {}; t.x = 1; t.y = 2` 会在这里被扫描成一串 constructor steps。

use std::collections::BTreeMap;

use crate::hir::common::{HirExpr, HirLValue, HirStmt, HirTableConstructor, HirTableSetList};

use super::bindings::{
    binding_from_expr, binding_from_lvalue, expr_uses_binding, table_key_from_expr,
};
use super::rebuild::rebuild_constructor_from_steps;
use super::{ProducerGroup, ProducerGroupSlot, RegionStep, TableBinding};

pub(super) fn constructor_seed(stmt: &HirStmt) -> Option<(TableBinding, HirTableConstructor)> {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            let [binding] = local_decl.bindings.as_slice() else {
                return None;
            };
            let [HirExpr::TableConstructor(table)] = local_decl.values.as_slice() else {
                return None;
            };
            Some((TableBinding::Local(*binding), (**table).clone()))
        }
        HirStmt::Assign(assign) => {
            let [target] = assign.targets.as_slice() else {
                return None;
            };
            let binding = binding_from_lvalue(target)?;
            let [HirExpr::TableConstructor(table)] = assign.values.as_slice() else {
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
            local_decl.values = vec![HirExpr::TableConstructor(Box::new(constructor))];
        }
        HirStmt::Assign(assign) => {
            assign.values = vec![HirExpr::TableConstructor(Box::new(constructor))];
        }
        _ => unreachable!("constructor region must start from a constructor seed"),
    }
}

pub(super) fn try_rebuild_constructor_region(
    block: &crate::hir::common::HirBlock,
    seed_index: usize,
    binding: TableBinding,
    constructor: HirTableConstructor,
    materialized_bindings: &BTreeMap<TableBinding, usize>,
) -> Option<(HirTableConstructor, usize)> {
    let mut steps = Vec::new();
    let mut index = seed_index + 1;
    let mut best = None;

    while let Some(stmt) = block.stmts.get(index) {
        if let Some(record) = keyed_write_step(stmt, binding) {
            steps.push(RegionStep::Record(record));
            if let Some(rebuilt) = rebuild_constructor_from_steps(
                constructor.clone(),
                &steps,
                &block.stmts[index + 1..],
                materialized_bindings,
            ) {
                best = Some((rebuilt, index));
            }
            index += 1;
            continue;
        }
        if let Some(mut producers) = producer_steps(stmt, binding) {
            steps.append(&mut producers);
            index += 1;
            continue;
        }
        if let Some(set_list) = table_set_list_step(stmt, binding) {
            steps.push(RegionStep::SetList(set_list));
            if let Some(rebuilt) = rebuild_constructor_from_steps(
                constructor.clone(),
                &steps,
                &block.stmts[index + 1..],
                materialized_bindings,
            ) {
                best = Some((rebuilt, index));
            }
            index += 1;
            continue;
        }
        break;
    }

    // 不要求“扫描到的最长前缀”整体可折叠。
    // 某些稳定构造区域后面会紧跟无关的 local producer；如果继续把它们吞进候选区，
    // 末尾那批未消费 producer 会让整段 region 失败，反而错过前面已经足够安全的
    // `{ ... }` 前缀。因此这里持续记住“最后一个成功前缀”，在真正遇到无关语句时
    // 回退到最近一次可证明安全的构造器边界。
    best
}

fn keyed_write_step(
    stmt: &HirStmt,
    binding: TableBinding,
) -> Option<crate::hir::common::HirRecordField> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.as_slice() else {
        return None;
    };
    if binding_from_expr(&access.base) != Some(binding) {
        return None;
    }
    if expr_uses_binding(&access.key, binding) || expr_uses_binding(value, binding) {
        return None;
    }
    Some(crate::hir::common::HirRecordField {
        key: table_key_from_expr(&access.key),
        value: value.clone(),
    })
}

fn producer_steps(stmt: &HirStmt, constructor_binding: TableBinding) -> Option<Vec<RegionStep>> {
    match stmt {
        HirStmt::LocalDecl(local_decl) => producer_steps_from_bindings(
            local_decl
                .bindings
                .iter()
                .copied()
                .map(TableBinding::Local)
                .collect(),
            &local_decl.values,
            constructor_binding,
        ),
        HirStmt::Assign(assign) => {
            let bindings = assign
                .targets
                .iter()
                .map(binding_from_lvalue)
                .collect::<Option<Vec<_>>>()?;
            producer_steps_from_bindings(bindings, &assign.values, constructor_binding)
        }
        _ => None,
    }
}

fn producer_steps_from_bindings(
    bindings: Vec<TableBinding>,
    values: &[HirExpr],
    constructor_binding: TableBinding,
) -> Option<Vec<RegionStep>> {
    if bindings.is_empty()
        || values.is_empty()
        || values
            .iter()
            .any(|value| expr_uses_binding(value, constructor_binding))
    {
        return None;
    }

    if bindings.len() == values.len() {
        return Some(
            bindings
                .into_iter()
                .zip(values.iter().cloned())
                .map(|(binding, value)| RegionStep::Producer(binding, value))
                .collect(),
        );
    }

    let [source] = values else {
        return None;
    };
    if bindings.len() > 1 && is_open_pack_source(source) {
        return Some(vec![RegionStep::ProducerGroup(ProducerGroup {
            slots: bindings
                .into_iter()
                .enumerate()
                .map(|(index, binding)| ProducerGroupSlot {
                    binding,
                    value: (index == 0).then_some(source.clone()),
                })
                .collect(),
            drop_without_consumption_is_safe: can_drop_open_pack_source_if_unused(source),
        })]);
    }

    None
}

fn is_open_pack_source(expr: &HirExpr) -> bool {
    matches!(expr, HirExpr::VarArg) || matches!(expr, HirExpr::Call(call) if call.multiret)
}

fn can_drop_open_pack_source_if_unused(expr: &HirExpr) -> bool {
    matches!(expr, HirExpr::VarArg)
}

fn table_set_list_step(stmt: &HirStmt, binding: TableBinding) -> Option<HirTableSetList> {
    let HirStmt::TableSetList(set_list) = stmt else {
        return None;
    };
    if binding_from_expr(&set_list.base) != Some(binding) {
        return None;
    }
    if set_list
        .values
        .iter()
        .any(|expr| expr_uses_binding(expr, binding))
        || set_list
            .trailing_multivalue
            .as_ref()
            .is_some_and(|expr| expr_uses_binding(expr, binding))
    {
        return None;
    }
    Some((**set_list).clone())
}
