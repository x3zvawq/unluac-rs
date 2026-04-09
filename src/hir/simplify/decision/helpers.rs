//! 这个文件承载 decision simplify 共享的表达式辅助逻辑。
//!
//! `decision.rs`、`eliminate.rs` 和 `synthesize.rs` 都会用到"逻辑短路形状整理"以及
//! "基础逻辑表达式构造"这些共通能力。把它们集中到这里的目的是避免三处各写一套
//! 近似实现，后续如果我们继续打磨 `Decision -> Expr` 选择策略，也只需要在这一处
//! 收紧语义边界。
//!
//! 纯表达式谓词（truthiness、side-effect-free、boolean-valued）和基础的关联重复
//! 折叠已迁移到 `super::super::expr_facts`，这里只保留 decision 专属的逻辑构造
//! 和条件上下文整理。

use super::super::expr_facts::{fold_associative_duplicate_and, fold_associative_duplicate_or};
use crate::hir::common::{HirExpr, HirLogicalExpr};

pub(super) fn logical_and(lhs: HirExpr, rhs: HirExpr) -> HirExpr {
    if lhs == rhs {
        lhs
    } else {
        HirExpr::LogicalAnd(Box::new(HirLogicalExpr { lhs, rhs }))
    }
}

pub(super) fn logical_or(lhs: HirExpr, rhs: HirExpr) -> HirExpr {
    if lhs == rhs {
        lhs
    } else {
        HirExpr::LogicalOr(Box::new(HirLogicalExpr { lhs, rhs }))
    }
}

pub(super) fn simplify_lua_logical_shape(expr: &HirExpr) -> Option<HirExpr> {
    match expr {
        HirExpr::LogicalAnd(logical) => simplify_logical_and(&logical.lhs, &logical.rhs),
        HirExpr::LogicalOr(logical) => simplify_logical_or(&logical.lhs, &logical.rhs),
        _ => None,
    }
}

/// 这里专门承载“只保留 truthiness、但不保留原始值”的条件上下文整理。
///
/// 和 `simplify_lua_logical_shape` 不同，这里的规则只应该用于 `if/while/repeat`
/// 条件，因为它们只关心真假，不关心原始值本身。这样我们就可以安全地把
/// `(x and true) or false` 这类布尔壳重新收回自然条件，而不会误伤值上下文。
pub(super) fn simplify_condition_truthiness_shape(expr: &HirExpr) -> Option<HirExpr> {
    match expr {
        HirExpr::LogicalAnd(logical) => simplify_condition_logical_and(&logical.lhs, &logical.rhs),
        HirExpr::LogicalOr(logical) => simplify_condition_logical_or(&logical.lhs, &logical.rhs),
        _ => None,
    }
}

fn simplify_logical_and(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    if lhs == rhs {
        return Some(lhs.clone());
    }

    if let Some(replacement) = fold_associative_duplicate_and(lhs, rhs) {
        return Some(replacement);
    }

    match rhs {
        HirExpr::LogicalOr(inner) if lhs == &inner.lhs => Some(lhs.clone()),
        _ => match lhs {
            HirExpr::LogicalOr(inner) if rhs == &inner.lhs || rhs == &inner.rhs => {
                Some(rhs.clone())
            }
            _ => None,
        },
    }
}

fn simplify_logical_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    if lhs == rhs {
        return Some(lhs.clone());
    }

    if let Some(replacement) = fold_associative_duplicate_or(lhs, rhs) {
        return Some(replacement);
    }
    if let Some(replacement) = factor_shared_and_guards(lhs, rhs) {
        return Some(replacement);
    }
    if let Some(replacement) = pull_shared_or_tail(lhs, rhs) {
        return Some(replacement);
    }

    match rhs {
        HirExpr::LogicalAnd(inner) if lhs == &inner.lhs => Some(lhs.clone()),
        _ => match lhs {
            HirExpr::LogicalAnd(inner) if rhs == &inner.lhs || rhs == &inner.rhs => {
                Some(rhs.clone())
            }
            _ => None,
        },
    }
}

fn factor_shared_and_guards(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    factor_shared_and_guards_one_side(lhs, rhs)
        .or_else(|| factor_shared_and_guards_one_side(rhs, lhs))
}

fn factor_shared_and_guards_one_side(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    let HirExpr::LogicalAnd(lhs_and) = lhs else {
        return None;
    };
    let HirExpr::LogicalAnd(rhs_and) = rhs else {
        return None;
    };

    if lhs_and.lhs == rhs_and.lhs {
        return Some(logical_and(
            lhs_and.lhs.clone(),
            logical_or(lhs_and.rhs.clone(), rhs_and.rhs.clone()),
        ));
    }

    if lhs_and.rhs == rhs_and.rhs {
        return Some(logical_and(
            logical_or(lhs_and.lhs.clone(), rhs_and.lhs.clone()),
            lhs_and.rhs.clone(),
        ));
    }

    None
}

fn pull_shared_or_tail(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    pull_shared_or_tail_one_side(lhs, rhs).or_else(|| pull_shared_or_tail_one_side(rhs, lhs))
}

fn pull_shared_or_tail_one_side(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    let HirExpr::LogicalAnd(lhs_and) = lhs else {
        return None;
    };
    let HirExpr::LogicalOr(inner_or) = &lhs_and.rhs else {
        return None;
    };
    if rhs != &inner_or.rhs {
        return None;
    }

    Some(logical_or(
        logical_and(lhs_and.lhs.clone(), inner_or.lhs.clone()),
        rhs.clone(),
    ))
}

fn simplify_condition_logical_and(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    if matches!(rhs, HirExpr::Boolean(true)) {
        return Some(lhs.clone());
    }
    if matches!(rhs, HirExpr::Boolean(false)) {
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
    if matches!(rhs, HirExpr::Boolean(true)) {
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
