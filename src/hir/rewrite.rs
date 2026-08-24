//! HIR 构建与 simplify 共用的定点表达式替换。

use std::collections::{BTreeMap, BTreeSet};

use super::{
    HirCallExpr, HirDecisionTarget, HirExpr, HirPackTail, HirTableField, HirTableKey, HirValuePack,
    TempId,
};

pub(crate) fn replace_temp_in_call(
    call: &mut HirCallExpr,
    temp: TempId,
    replacement: &HirExpr,
) -> usize {
    replace_temp_in_expr(&mut call.callee, temp, replacement)
        + replace_temp_in_value_pack(&mut call.args, temp, replacement)
}

/// Replace a set of forwarding temps in one expression traversal.
///
/// The map is a substitution DAG: each replacement may refer to another key, but
/// callers must reject cycles before invoking this helper.  Resolving the map while
/// walking the output keeps a long alias chain linear in the emitted expression size;
/// repeatedly rescanning a growing sink would make the same chain quadratic.
pub(crate) fn replace_temps_in_call(
    call: &mut HirCallExpr,
    replacements: &BTreeMap<TempId, HirExpr>,
) -> usize {
    let mut active = BTreeSet::new();
    replace_call_with_map(call, replacements, &mut active)
}

pub(crate) fn replace_temp_in_value_pack(
    pack: &mut HirValuePack,
    temp: TempId,
    replacement: &HirExpr,
) -> usize {
    let fixed = pack
        .fixed
        .iter_mut()
        .map(|value| replace_temp_in_expr(value, temp, replacement))
        .sum::<usize>();
    fixed
        + pack
            .tail
            .as_mut()
            .and_then(HirPackTail::call_mut)
            .map_or(0, |call| replace_temp_in_call(call, temp, replacement))
}

pub(crate) fn replace_temps_in_value_pack(
    pack: &mut HirValuePack,
    replacements: &BTreeMap<TempId, HirExpr>,
) -> usize {
    let mut active = BTreeSet::new();
    replace_value_pack_with_map(pack, replacements, &mut active)
}

pub(crate) fn replace_temp_in_expr(
    expr: &mut HirExpr,
    temp: TempId,
    replacement: &HirExpr,
) -> usize {
    match expr {
        HirExpr::TempRef(other) if *other == temp => {
            *expr = replacement.clone();
            1
        }
        HirExpr::TableAccess(access) => {
            replace_temp_in_expr(&mut access.base, temp, replacement)
                + replace_temp_in_expr(&mut access.key, temp, replacement)
        }
        HirExpr::Unary(unary) => replace_temp_in_expr(&mut unary.expr, temp, replacement),
        HirExpr::Binary(binary) => {
            replace_temp_in_expr(&mut binary.lhs, temp, replacement)
                + replace_temp_in_expr(&mut binary.rhs, temp, replacement)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            replace_temp_in_expr(&mut logical.lhs, temp, replacement)
                + replace_temp_in_expr(&mut logical.rhs, temp, replacement)
        }
        HirExpr::Decision(decision) => decision
            .nodes
            .iter_mut()
            .map(|node| {
                replace_temp_in_expr(&mut node.test, temp, replacement)
                    + replace_temp_in_target(&mut node.truthy, temp, replacement)
                    + replace_temp_in_target(&mut node.falsy, temp, replacement)
            })
            .sum(),
        HirExpr::Call(call) => replace_temp_in_call(call, temp, replacement),
        HirExpr::TableConstructor(table) => {
            let fields = table
                .fields
                .iter_mut()
                .map(|field| match field {
                    HirTableField::Array(value) => replace_temp_in_expr(value, temp, replacement),
                    HirTableField::Record(field) => {
                        let key = match &mut field.key {
                            HirTableKey::Expr(key) => replace_temp_in_expr(key, temp, replacement),
                            HirTableKey::Name(_) => 0,
                        };
                        key + replace_temp_in_expr(&mut field.value, temp, replacement)
                    }
                })
                .sum::<usize>();
            fields
                + table
                    .trailing_multivalue
                    .as_mut()
                    .and_then(HirPackTail::call_mut)
                    .map_or(0, |call| replace_temp_in_call(call, temp, replacement))
        }
        HirExpr::Closure(closure) => closure
            .captures
            .iter_mut()
            .map(|capture| replace_temp_in_expr(&mut capture.value, temp, replacement))
            .sum(),
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
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => 0,
    }
}

pub(crate) fn replace_temps_in_expr(
    expr: &mut HirExpr,
    replacements: &BTreeMap<TempId, HirExpr>,
) -> usize {
    let mut active = BTreeSet::new();
    replace_expr_with_map(expr, replacements, &mut active)
}

fn replace_call_with_map(
    call: &mut HirCallExpr,
    replacements: &BTreeMap<TempId, HirExpr>,
    active: &mut BTreeSet<TempId>,
) -> usize {
    replace_expr_with_map(&mut call.callee, replacements, active)
        + replace_value_pack_with_map(&mut call.args, replacements, active)
}

fn replace_value_pack_with_map(
    pack: &mut HirValuePack,
    replacements: &BTreeMap<TempId, HirExpr>,
    active: &mut BTreeSet<TempId>,
) -> usize {
    pack.fixed
        .iter_mut()
        .map(|value| replace_expr_with_map(value, replacements, active))
        .sum::<usize>()
        + pack
            .tail
            .as_mut()
            .and_then(HirPackTail::call_mut)
            .map_or(0, |call| replace_call_with_map(call, replacements, active))
}

fn replace_expr_with_map(
    expr: &mut HirExpr,
    replacements: &BTreeMap<TempId, HirExpr>,
    active: &mut BTreeSet<TempId>,
) -> usize {
    match expr {
        HirExpr::TempRef(temp) => {
            let Some(replacement) = replacements.get(temp) else {
                return 0;
            };
            // A cycle is invalid for a materialization run.  Leave the reference
            // intact if a caller violates that contract instead of recursing forever.
            if !active.insert(*temp) {
                return 0;
            }
            let mut expanded = replacement.clone();
            let nested = replace_expr_with_map(&mut expanded, replacements, active);
            active.remove(temp);
            *expr = expanded;
            1 + nested
        }
        HirExpr::TableAccess(access) => {
            replace_expr_with_map(&mut access.base, replacements, active)
                + replace_expr_with_map(&mut access.key, replacements, active)
        }
        HirExpr::Unary(unary) => replace_expr_with_map(&mut unary.expr, replacements, active),
        HirExpr::Binary(binary) => {
            replace_expr_with_map(&mut binary.lhs, replacements, active)
                + replace_expr_with_map(&mut binary.rhs, replacements, active)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            replace_expr_with_map(&mut logical.lhs, replacements, active)
                + replace_expr_with_map(&mut logical.rhs, replacements, active)
        }
        HirExpr::Decision(decision) => decision
            .nodes
            .iter_mut()
            .map(|node| {
                replace_expr_with_map(&mut node.test, replacements, active)
                    + replace_target_with_map(&mut node.truthy, replacements, active)
                    + replace_target_with_map(&mut node.falsy, replacements, active)
            })
            .sum(),
        HirExpr::Call(call) => replace_call_with_map(call, replacements, active),
        HirExpr::TableConstructor(table) => {
            table
                .fields
                .iter_mut()
                .map(|field| match field {
                    HirTableField::Array(value) => {
                        replace_expr_with_map(value, replacements, active)
                    }
                    HirTableField::Record(field) => {
                        let key = match &mut field.key {
                            HirTableKey::Expr(key) => {
                                replace_expr_with_map(key, replacements, active)
                            }
                            HirTableKey::Name(_) => 0,
                        };
                        key + replace_expr_with_map(&mut field.value, replacements, active)
                    }
                })
                .sum::<usize>()
                + table
                    .trailing_multivalue
                    .as_mut()
                    .and_then(HirPackTail::call_mut)
                    .map_or(0, |call| replace_call_with_map(call, replacements, active))
        }
        HirExpr::Closure(closure) => closure
            .captures
            .iter_mut()
            .map(|capture| replace_expr_with_map(&mut capture.value, replacements, active))
            .sum(),
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
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => 0,
    }
}

fn replace_target_with_map(
    target: &mut HirDecisionTarget,
    replacements: &BTreeMap<TempId, HirExpr>,
    active: &mut BTreeSet<TempId>,
) -> usize {
    if let HirDecisionTarget::Expr(expr) = target {
        replace_expr_with_map(expr, replacements, active)
    } else {
        0
    }
}

fn replace_temp_in_target(
    target: &mut HirDecisionTarget,
    temp: TempId,
    replacement: &HirExpr,
) -> usize {
    if let HirDecisionTarget::Expr(expr) = target {
        replace_temp_in_expr(expr, temp, replacement)
    } else {
        0
    }
}
