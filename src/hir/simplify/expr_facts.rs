//! HIR simplify 共享的表达式事实查询。
//!
//! 多个 simplify pass（decision、boolean_shells、logical_simplify）需要判断表达式的
//! 副作用、truthiness、布尔值等属性，以及执行最基础的关联重复折叠。把这些谓词和
//! 恒等式集中在这里，避免同一组 match arm 在三处各写一份、任何一边增删变体时
//! 另外几处漏掉。

use crate::hir::common::{
    HirBinaryOpKind, HirDecisionTarget, HirExpr, HirUnaryOpKind,
};

/// 判断表达式是否保证没有运行时副作用。
///
/// 这里只看节点种类，不追踪别名；用于保守判断"能否安全折叠/删除"。
pub(super) fn expr_is_side_effect_free(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_) => true,
        HirExpr::Unary(unary) => expr_is_side_effect_free(&unary.expr),
        HirExpr::Binary(binary) => {
            expr_is_side_effect_free(&binary.lhs) && expr_is_side_effect_free(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_is_side_effect_free(&logical.lhs) && expr_is_side_effect_free(&logical.rhs)
        }
        HirExpr::Decision(decision) => decision.nodes.iter().all(|node| {
            expr_is_side_effect_free(&node.test)
                && decision_target_is_side_effect_free(&node.truthy)
                && decision_target_is_side_effect_free(&node.falsy)
        }),
        HirExpr::TableAccess(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => false,
    }
}

fn decision_target_is_side_effect_free(target: &HirDecisionTarget) -> bool {
    match target {
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => true,
        HirDecisionTarget::Expr(expr) => expr_is_side_effect_free(expr),
    }
}

/// 判断字面值的静态 truthiness。
///
/// 返回 `Some(true/false)` 当表达式 truthiness 可在编译期确定，运行时可能为真或假时返回 `None`。
pub(super) fn expr_truthiness(expr: &HirExpr) -> Option<bool> {
    match expr {
        HirExpr::Nil => Some(false),
        HirExpr::Boolean(value) => Some(*value),
        HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::Closure(_)
        | HirExpr::TableConstructor(_) => Some(true),
        HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::LogicalAnd(_)
        | HirExpr::LogicalOr(_)
        | HirExpr::Decision(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => None,
    }
}

/// 判断表达式是否保证产出布尔值。
pub(super) fn expr_is_boolean_valued(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Boolean(_) => true,
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => true,
        HirExpr::Binary(binary) => matches!(
            binary.op,
            HirBinaryOpKind::Eq | HirBinaryOpKind::Lt | HirBinaryOpKind::Le
        ),
        HirExpr::Decision(decision) => decision.nodes.iter().all(|node| {
            decision_target_is_boolean(&node.truthy) && decision_target_is_boolean(&node.falsy)
        }),
        _ => false,
    }
}

fn decision_target_is_boolean(target: &HirDecisionTarget) -> bool {
    match target {
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => false,
        HirDecisionTarget::Expr(expr) => expr_is_boolean_valued(expr),
    }
}

/// 折叠关联重复 `and`：`(a and b) and a` → `a and b`。
pub(super) fn fold_associative_duplicate_and(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    match lhs {
        HirExpr::LogicalAnd(inner) if rhs == &inner.lhs || rhs == &inner.rhs => Some(lhs.clone()),
        _ => match rhs {
            HirExpr::LogicalAnd(inner) if lhs == &inner.lhs || lhs == &inner.rhs => {
                Some(rhs.clone())
            }
            _ => None,
        },
    }
}

/// 折叠关联重复 `or`：`(a or b) or a` → `a or b`。
pub(super) fn fold_associative_duplicate_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    match lhs {
        HirExpr::LogicalOr(inner) if rhs == &inner.lhs || rhs == &inner.rhs => Some(lhs.clone()),
        _ => match rhs {
            HirExpr::LogicalOr(inner) if lhs == &inner.lhs || lhs == &inner.rhs => {
                Some(rhs.clone())
            }
            _ => None,
        },
    }
}
