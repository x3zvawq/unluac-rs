//! 这个子模块负责 decision synthesis 的语法安全门槛。
//!
//! 它依赖 HIR 表达式当前的节点种类，只回答“这个 decision/expr 能不能安全参与综合”，
//! 不会在这里做成本比较或可读性排序。
//! 例如：含副作用调用的表达式会在这里被拒绝参与综合。

use crate::hir::common::{
    HirBinaryOpKind, HirDecisionExpr, HirDecisionTarget, HirExpr, HirUnaryOpKind,
};

pub(crate) fn decision_is_synth_safe(decision: &HirDecisionExpr) -> bool {
    decision.nodes.iter().all(|node| {
        expr_is_synth_safe(&node.test)
            && target_is_synth_safe(&node.truthy)
            && target_is_synth_safe(&node.falsy)
    })
}

pub(super) fn expr_is_synth_safe(expr: &HirExpr) -> bool {
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
        | HirExpr::TempRef(_) => true,
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => expr_is_synth_safe(&unary.expr),
        // 所有纯比较运算符（Eq/Lt/Le）本身无副作用，可安全内嵌到 and/or 表达式中。
        // 算术运算符（Add/Sub/...）因可能触发 __add 等元方法而被排除。
        HirExpr::Binary(binary)
            if matches!(
                binary.op,
                HirBinaryOpKind::Eq | HirBinaryOpKind::Lt | HirBinaryOpKind::Le
            ) =>
        {
            expr_is_synth_safe(&binary.lhs) && expr_is_synth_safe(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_is_synth_safe(&logical.lhs) && expr_is_synth_safe(&logical.rhs)
        }
        HirExpr::Decision(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => false,
    }
}

fn target_is_synth_safe(target: &HirDecisionTarget) -> bool {
    match target {
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => true,
        HirDecisionTarget::Expr(expr) => expr_is_synth_safe(expr),
    }
}
