//! HIR simplify 共享的表达式事实查询。
//!
//! 多个 simplify pass（decision、boolean_shells、logical_simplify）需要判断表达式的
//! truthiness 与布尔值属性。求值安全性由 `hir::expr_safety` 统一负责；这里不再维护
//! 第二套“纯表达式”分类。

use crate::hir::common::{HirBinaryOpKind, HirDecisionTarget, HirExpr, HirUnaryOpKind};

/// 判断字面值的静态 truthiness。
///
/// 返回 `Some(true/false)` 当表达式 truthiness 可在编译期确定，运行时可能为真或假时返回 `None`。
pub(in crate::hir) fn expr_truthiness(expr: &HirExpr) -> Option<bool> {
    match expr {
        HirExpr::Nil => Some(false),
        HirExpr::Boolean(value) => Some(*value),
        HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
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
