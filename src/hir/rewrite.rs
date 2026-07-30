//! HIR 构建与 simplify 共用的定点表达式替换。

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
