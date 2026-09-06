//! simplify 对共享 HIR 值域的查询入口。
//!
//! 结果种类与短路合流由 value_facts 统一解释；此处仅注入目标 VM 比较事实及已证明
//! 稳定的路径假设。例如 guard 成立时 guard or fallback 恒真，但不授权跨过修改 guard
//! 的调用，也不把正常返回的值事实当成求值可删除证明。

use crate::hir::common::HirExpr;
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::value_facts::{value_facts, value_facts_with};
use crate::value_semantics::results::LuaValueFacts;

pub(in crate::hir) fn expr_truthiness(expr: &HirExpr, safety: HirExprSafety) -> Option<bool> {
    value_facts_with(expr, &|value| comparison_facts(value, safety)).truthiness()
}

pub(super) fn expr_truthiness_assuming(
    expr: &HirExpr,
    subject: &HirExpr,
    subject_truthy: bool,
    safety: HirExprSafety,
) -> Option<bool> {
    value_facts_with(expr, &|value| {
        if value == subject {
            Some(LuaValueFacts::assuming_truthiness(subject_truthy))
        } else {
            comparison_facts(value, safety)
        }
    })
    .truthiness()
}

fn comparison_facts(expr: &HirExpr, safety: HirExprSafety) -> Option<LuaValueFacts> {
    let HirExpr::Binary(binary) = expr else {
        return None;
    };
    safety
        .primitive_literal_comparison_value(binary.op, &binary.lhs, &binary.rhs)
        .map(LuaValueFacts::boolean)
}

pub(super) fn expr_is_boolean_valued(expr: &HirExpr) -> bool {
    value_facts(expr).is_boolean()
}
