//! 这个子模块负责 decision synthesis 的语法安全门槛。
//!
//! 它依赖 HIR 表达式当前的节点种类，只回答“这个 decision/expr 能不能安全参与综合”，
//! 不会在这里做成本比较或可读性排序。
//! 例如：含副作用调用的表达式会在这里被拒绝参与综合。

use crate::hir::common::{HirDecisionExpr, HirDecisionTarget, HirExpr};
use crate::hir::expr_safety::expr_is_repeatable;

pub(crate) fn decision_is_synth_safe(decision: &HirDecisionExpr) -> bool {
    decision.nodes.iter().all(|node| {
        expr_is_synth_safe(&node.test)
            && target_is_synth_safe(&node.truthy)
            && target_is_synth_safe(&node.falsy)
    })
}

pub(super) fn expr_is_synth_safe(expr: &HirExpr) -> bool {
    expr_is_repeatable(expr)
}

fn target_is_synth_safe(target: &HirDecisionTarget) -> bool {
    match target {
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => true,
        HirDecisionTarget::Expr(expr) => expr_is_synth_safe(expr),
    }
}
