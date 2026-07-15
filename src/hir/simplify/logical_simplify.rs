//! 这个文件承载 HIR 的保守逻辑表达式整理。
//!
//! Lua 的 `and/or` 返回的是原始操作数，不是布尔值，所以很多看似显然的布尔代数
//! 恒等式其实并不安全。这里故意只实现一小撮在 Lua 值语义下也严格成立的规则，
//! 用来压掉短路 DAG 恢复后最机械的重复，而不越权重写控制流结构。
//!
//! 它依赖前面的 short-circuit / decision 恢复已经把候选逻辑表达式保守落成 HIR，
//! 这里仅做“值语义严格不变”的局部整理，不重新分析 CFG，也不替前层兜底修坏掉的
//! 短路结构。
//!
//! 例子：
//! - `x and x` 只会在 `x` 可稳定重复求值时折成 `x`
//! - `(a and b) or (a and c)` 只会在整段表达式均可稳定重复求值时整理
//! - `not a and x or y` 在 `x/y` 恒真时整理成 `a and y or x`
//! - `x or x` 会折成 `x`
//! - 它不会把一般 `if/branch` 结构强行改写成逻辑表达式，那仍然属于更前面的结构恢复职责

use super::expr_facts::expr_truthiness;
use super::walk::{ExprRewritePass, rewrite_proto_exprs};
use crate::hir::common::{HirExpr, HirLogicalExpr, HirProto, HirUnaryOpKind};
use crate::hir::expr_safety::{expr_is_discard_safe, expr_is_repeatable};

/// 对单个 proto 递归执行安全的逻辑表达式整理。
pub(super) fn simplify_logical_exprs_in_proto(proto: &mut HirProto) -> bool {
    rewrite_proto_exprs(proto, &mut LogicalExprPass)
}

struct LogicalExprPass;

impl ExprRewritePass for LogicalExprPass {
    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        let mut changed = false;

        if let Some(replacement) = simplify_logical_shape(expr) {
            *expr = replacement;
            changed = true;
        }
        if let Some(replacement) = super::decision::naturalize_pure_logical_expr(expr) {
            *expr = replacement;
            changed = true;
        }

        changed
    }

    fn rewrite_condition_expr(&mut self, expr: &mut HirExpr) -> bool {
        let mut changed = false;
        if let Some(replacement) = simplify_logical_shape(expr) {
            *expr = replacement;
            changed = true;
        }
        if let Some(replacement) = simplify_condition_truthiness_shape(expr) {
            *expr = replacement;
            changed = true;
        }
        changed
    }
}

pub(super) fn simplify_logical_shape(expr: &HirExpr) -> Option<HirExpr> {
    match expr {
        HirExpr::LogicalAnd(logical) => simplify_logical_and(&logical.lhs, &logical.rhs),
        HirExpr::LogicalOr(logical) => simplify_logical_or(&logical.lhs, &logical.rhs),
        _ => None,
    }
}

fn simplify_logical_and(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    if lhs == rhs && expr_is_repeatable(lhs) {
        return Some(lhs.clone());
    }

    if let Some(replacement) = fold_associative_duplicate_and(lhs, rhs) {
        return Some(replacement);
    }

    if let Some(replacement) = fold_constant_short_circuit_and(lhs, rhs) {
        return Some(replacement);
    }

    if !expr_is_repeatable(lhs) || !expr_is_repeatable(rhs) {
        return None;
    }

    match (lhs, rhs) {
        (lhs, HirExpr::LogicalOr(inner)) if lhs == &inner.lhs => Some(lhs.clone()),
        (HirExpr::LogicalOr(inner), rhs) if rhs == &inner.rhs => Some(rhs.clone()),
        _ => None,
    }
}

fn simplify_logical_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    if lhs == rhs && expr_is_repeatable(lhs) {
        return Some(lhs.clone());
    }

    if let Some(replacement) = fold_associative_duplicate_or(lhs, rhs) {
        return Some(replacement);
    }

    if let Some(replacement) = fold_constant_short_circuit_or(lhs, rhs) {
        return Some(replacement);
    }
    if let Some(replacement) = naturalize_truthy_ternary(lhs, rhs) {
        return Some(replacement);
    }
    if let Some(replacement) = factor_shared_and_guards(lhs, rhs) {
        return Some(replacement);
    }
    if let Some(replacement) = pull_shared_or_tail(lhs, rhs) {
        return Some(replacement);
    }
    if let Some(replacement) = fold_shared_fallback_or(lhs, rhs) {
        return Some(replacement);
    }

    if !expr_is_repeatable(lhs) || !expr_is_repeatable(rhs) {
        return None;
    }

    match (lhs, rhs) {
        (lhs, HirExpr::LogicalAnd(inner)) if lhs == &inner.lhs => Some(lhs.clone()),
        (HirExpr::LogicalAnd(inner), rhs) if rhs == &inner.rhs => Some(rhs.clone()),
        _ => None,
    }
}

/// `not a and x or y` 在 `x/y` 恒真时等价于 `a and y or x`。
///
/// 两种形状都会先且仅求值一次 `a`，随后在 `a` 为真时求值 `y`，否则求值 `x`；
/// 恒真约束保证选中分支不会继续落到另一个分支。
fn naturalize_truthy_ternary(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    let HirExpr::LogicalAnd(and_expr) = lhs else {
        return None;
    };
    let HirExpr::Unary(guard) = &and_expr.lhs else {
        return None;
    };
    if guard.op != HirUnaryOpKind::Not
        || expr_truthiness(&and_expr.rhs) != Some(true)
        || expr_truthiness(rhs) != Some(true)
    {
        return None;
    }

    Some(HirExpr::LogicalOr(Box::new(HirLogicalExpr {
        lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            lhs: guard.expr.clone(),
            rhs: rhs.clone(),
        })),
        rhs: and_expr.rhs.clone(),
    })))
}

fn fold_associative_duplicate_and(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    match (lhs, rhs) {
        (HirExpr::LogicalAnd(inner), rhs) if rhs == &inner.rhs && expr_is_repeatable(rhs) => {
            Some(lhs.clone())
        }
        (lhs, HirExpr::LogicalAnd(inner)) if lhs == &inner.lhs && expr_is_repeatable(lhs) => {
            Some(rhs.clone())
        }
        _ => None,
    }
}

fn fold_associative_duplicate_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    match (lhs, rhs) {
        (HirExpr::LogicalOr(inner), rhs) if rhs == &inner.rhs && expr_is_repeatable(rhs) => {
            Some(lhs.clone())
        }
        (lhs, HirExpr::LogicalOr(inner)) if lhs == &inner.lhs && expr_is_repeatable(lhs) => {
            Some(rhs.clone())
        }
        _ => None,
    }
}

fn factor_shared_and_guards(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    factor_shared_and_guards_one_side(lhs, rhs)
}

fn factor_shared_and_guards_one_side(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    if !expr_is_repeatable(lhs) || !expr_is_repeatable(rhs) {
        return None;
    }
    let HirExpr::LogicalAnd(lhs_and) = lhs else {
        return None;
    };
    let HirExpr::LogicalAnd(rhs_and) = rhs else {
        return None;
    };

    if lhs_and.lhs == rhs_and.lhs {
        return Some(HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            lhs: lhs_and.lhs.clone(),
            rhs: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                lhs: lhs_and.rhs.clone(),
                rhs: rhs_and.rhs.clone(),
            })),
        })));
    }

    None
}

fn pull_shared_or_tail(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    pull_shared_or_tail_one_side(lhs, rhs)
}

fn pull_shared_or_tail_one_side(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    if !expr_is_repeatable(lhs) || !expr_is_repeatable(rhs) {
        return None;
    }
    let HirExpr::LogicalAnd(lhs_and) = lhs else {
        return None;
    };
    let HirExpr::LogicalOr(inner_or) = &lhs_and.rhs else {
        return None;
    };
    if rhs != &inner_or.rhs {
        return None;
    }

    Some(HirExpr::LogicalOr(Box::new(HirLogicalExpr {
        lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            lhs: lhs_and.lhs.clone(),
            rhs: inner_or.lhs.clone(),
        })),
        rhs: rhs.clone(),
    })))
}

/// 这里只折叠“左值 truthiness 已知”的短路表达式。
fn fold_constant_short_circuit_and(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    match expr_truthiness(lhs) {
        Some(true) if expr_is_discard_safe(lhs) => Some(rhs.clone()),
        Some(false) => Some(lhs.clone()),
        Some(true) => None,
        None => None,
    }
}

fn fold_constant_short_circuit_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    match expr_truthiness(lhs) {
        Some(true) => Some(lhs.clone()),
        Some(false) if expr_is_discard_safe(lhs) => Some(rhs.clone()),
        Some(false) => None,
        None => None,
    }
}

/// 这里处理一类共享 fallback 的机械展开：
///
/// `((not x) and y) or (x or y)` 在 Lua 里和 `x or y` 等价，只是前者会在恢复
/// 决策 DAG 时留下重复的 fallback 片段。只要 `y` 无副作用，这里就可以安全地
/// 把它重新收回更自然的短路表达式。
fn fold_shared_fallback_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    shared_fallback_or_one_side(lhs, rhs).or_else(|| shared_fallback_or_one_side(rhs, lhs))
}

fn shared_fallback_or_one_side(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    if !expr_is_repeatable(lhs) || !expr_is_repeatable(rhs) {
        return None;
    }
    let HirExpr::LogicalAnd(lhs_and) = lhs else {
        return None;
    };
    let HirExpr::LogicalOr(rhs_or) = rhs else {
        return None;
    };
    let guard = strip_negation(&lhs_and.lhs)?;
    if guard != rhs_or.lhs || lhs_and.rhs != rhs_or.rhs {
        return None;
    }
    Some(rhs.clone())
}

fn strip_negation(expr: &HirExpr) -> Option<HirExpr> {
    match expr {
        HirExpr::Unary(unary) if matches!(unary.op, crate::hir::common::HirUnaryOpKind::Not) => {
            Some(unary.expr.clone())
        }
        _ => None,
    }
}

pub(super) fn simplify_condition_truthiness_shape(expr: &HirExpr) -> Option<HirExpr> {
    match expr {
        HirExpr::LogicalAnd(logical) => simplify_condition_logical_and(&logical.lhs, &logical.rhs),
        HirExpr::LogicalOr(logical) => simplify_condition_logical_or(&logical.lhs, &logical.rhs),
        _ => None,
    }
}

fn simplify_condition_logical_and(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    if matches!(rhs, HirExpr::Boolean(true)) {
        return Some(lhs.clone());
    }
    if matches!(rhs, HirExpr::Boolean(false)) && expr_is_discard_safe(lhs) {
        return Some(HirExpr::Boolean(false));
    }
    if matches!(lhs, HirExpr::Boolean(true)) {
        return Some(rhs.clone());
    }
    if matches!(lhs, HirExpr::Boolean(false)) {
        return Some(HirExpr::Boolean(false));
    }
    None
}

fn simplify_condition_logical_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    if matches!(rhs, HirExpr::Boolean(false)) {
        return Some(lhs.clone());
    }
    if matches!(rhs, HirExpr::Boolean(true)) && expr_is_discard_safe(lhs) {
        return Some(HirExpr::Boolean(true));
    }
    if matches!(lhs, HirExpr::Boolean(false)) {
        return Some(rhs.clone());
    }
    if matches!(lhs, HirExpr::Boolean(true)) {
        return Some(HirExpr::Boolean(true));
    }
    None
}
