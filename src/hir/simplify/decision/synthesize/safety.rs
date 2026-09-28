//! 判断当前 HIR 是否满足 Decision synthesis 的语法安全要求。
//!
//! 为综合器发布参与许可，成本比较与源码形式选择由其它子模块负责。

use crate::hir::common::{HirDecisionExpr, HirDecisionTarget, HirExpr};
use crate::hir::expr_safety::HirExprSafety;

pub(crate) fn decision_is_synth_safe(decision: &HirDecisionExpr, safety: HirExprSafety) -> bool {
    // 候选拒绝[SemanticBarrier:EvalCount]：一般 structured candidate 会把 `f()` subject
    // 或共享的 `g()` continuation 复制进互斥逻辑臂；返回 falsy 时会多调用一次，代数 MDD
    // 只证明值映射，不能放行。effectful 图只由 value 的 exact-trace grammar 消费。
    decision.nodes.iter().all(|node| {
        expr_is_synth_safe(&node.test, safety)
            && target_is_synth_safe(&node.truthy, safety)
            && target_is_synth_safe(&node.falsy, safety)
    })
}

pub(super) fn expr_is_synth_safe(expr: &HirExpr, safety: HirExprSafety) -> bool {
    // 单值 Decision/logical operand 中的 vararg 是函数入口已冻结的首值，可以和普通
    // ref 一样进入 MDD；调用、lookup、动态环境与元方法仍由上面的 trace owner 拒绝。
    safety.is_repeatable_in_single_value_context(expr)
        && !HirExprSafety::contains_original_operation(expr)
}

fn target_is_synth_safe(target: &HirDecisionTarget, safety: HirExprSafety) -> bool {
    match target {
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => true,
        HirDecisionTarget::Expr(expr) => expr_is_synth_safe(expr, safety),
    }
}
