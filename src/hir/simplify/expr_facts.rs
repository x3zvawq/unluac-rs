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
        // `a or b`: a 为真则返回 a（真），a 为假则返回 b。
        // 因此只要 a 或 b 其中一个恒真，整个表达式就恒真；
        // a 恒假时结果完全取决于 b。
        HirExpr::LogicalOr(logical) => {
            let a = expr_truthiness(&logical.lhs);
            let b = expr_truthiness(&logical.rhs);
            match (a, b) {
                (Some(true), _) | (_, Some(true)) => Some(true),
                (Some(false), b_val) => b_val,
                _ => None,
            }
        }
        // `a and b`: a 为假则返回 a（假），a 为真则返回 b。
        // 因此只要 a 或 b 其中一个恒假，整个表达式就恒假；
        // a 恒真时结果完全取决于 b。
        HirExpr::LogicalAnd(logical) => {
            let a = expr_truthiness(&logical.lhs);
            let b = expr_truthiness(&logical.rhs);
            match (a, b) {
                (Some(false), _) | (_, Some(false)) => Some(false),
                (Some(true), b_val) => b_val,
                _ => None,
            }
        }
        HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
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

/// 折叠关联重复 `and`。
///
/// 仅允许"不改变短路求值顺序"的两种形态：
/// - `(a and b) and b` → `a and b`：b 从内层已经被求值，外层重复冗余
/// - `a and (a and b)` → `a and b`：内层首项和外层相同，先 guard 再 guard 等价
///
/// 不能折叠 `(a and b) and a` 和 `a and (b and a)`：
/// 前者改变了结果值（truthy 时返回 a 而非 b），后者丢掉了 a 对 b 的短路保护
/// （若 a 为 nil/false 而 b 含比较，b 会运行时报错）。
pub(super) fn fold_associative_duplicate_and(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    match lhs {
        // (a and b) and b → a and b
        HirExpr::LogicalAnd(inner) if *rhs == inner.rhs => Some(lhs.clone()),
        _ => match rhs {
            // a and (a and b) → a and b
            HirExpr::LogicalAnd(inner) if *lhs == inner.lhs => {
                Some(rhs.clone())
            }
            _ => None,
        },
    }
}

/// 折叠关联重复 `or`。
///
/// 仅允许"不改变短路求值顺序"的两种形态：
/// - `(a or b) or b` → `a or b`
/// - `a or (a or b)` → `a or b`
///
/// 不能折叠 `(a or b) or a` 和 `a or (b or a)`：
/// 前者 falsy 路径返回值不同（a vs b），后者丢掉了 a 对 b 的优先拦截。
pub(super) fn fold_associative_duplicate_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    match lhs {
        // (a or b) or b → a or b
        HirExpr::LogicalOr(inner) if *rhs == inner.rhs => Some(lhs.clone()),
        _ => match rhs {
            // a or (a or b) → a or b
            HirExpr::LogicalOr(inner) if *lhs == inner.lhs => {
                Some(rhs.clone())
            }
            _ => None,
        },
    }
}
