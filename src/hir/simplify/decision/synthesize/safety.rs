//! 这个子模块负责 decision synthesis 的语法安全门槛。
//!
//! 它依赖 HIR 表达式当前的节点种类，只回答“这个 decision/expr 能不能安全参与综合”，
//! 不会在这里做成本比较或可读性排序。
//! 例如：含副作用调用的表达式会在这里被拒绝参与综合。

use crate::hir::common::{HirDecisionExpr, HirDecisionTarget, HirExpr};
use crate::hir::expr_safety::HirExprSafety;

pub(crate) fn decision_is_synth_safe(decision: &HirDecisionExpr, safety: HirExprSafety) -> bool {
    // 候选拒绝[ProofIncomplete]：当前 synthesis 只会证明全树 repeatable；需补候选级 eval-trace 对照，才能接纳未被复制/删除的单次 `f()`/lookup。
    decision.nodes.iter().all(|node| {
        expr_is_synth_safe(&node.test, safety)
            && target_is_synth_safe(&node.truthy, safety)
            && target_is_synth_safe(&node.falsy, safety)
    })
}

pub(super) fn expr_is_synth_safe(expr: &HirExpr, safety: HirExprSafety) -> bool {
    // 候选拒绝[ProofIncomplete]：当前 naturalize 只会证明全树 repeatable；需按候选对照 occurrence，区分被删除的 `f()` 与仍原位单次求值的 `f()`。
    safety.is_repeatable(expr)
}

fn target_is_synth_safe(target: &HirDecisionTarget, safety: HirExprSafety) -> bool {
    match target {
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => true,
        HirDecisionTarget::Expr(expr) => expr_is_synth_safe(expr, safety),
    }
}
