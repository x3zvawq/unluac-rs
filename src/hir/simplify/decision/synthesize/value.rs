//! 这个子模块负责把 decision expression 直接综合回值表达式。
//!
//! 它依赖 `domain` 的等价性环境和 `safety` 的约束，只在整棵 decision 真能等价表达成
//! 一个值时才返回结果，不会在这里兜底伪造分支。
//! 例如：`cond ? x : y` 这类纯值 decision 会在这里尝试还原成逻辑值表达式。

use std::collections::BTreeMap;

use crate::hir::common::{HirDecisionExpr, HirDecisionNodeRef, HirDecisionTarget, HirExpr};
use crate::hir::expr_safety::HirExprSafety;

use super::domain::{SynthesisContext, collect_refs_from_decision};
use super::safety::{decision_is_synth_safe, expr_is_synth_safe};
use super::{expr_cost, normalize_candidate_expr};

pub(crate) fn synthesize_value_decision_expr(
    decision: &HirDecisionExpr,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    if !decision_is_synth_safe(decision, safety) {
        return None;
    }

    let refs = collect_refs_from_decision(decision);
    // 候选拒绝[ResourceLimit]：穷举域目前只接纳 4 个独立引用；后续应改用符号等价或按依赖分区验证。
    if refs.len() > super::MAX_SYNTH_REFS {
        return None;
    }

    // 候选拒绝[ResourceLimit]：抽象环境笛卡尔积超过 4096 时停止综合；后续应避免完整枚举。
    let context = SynthesisContext::new(decision, refs, safety)?;
    let mut memo = BTreeMap::new();
    synthesize_value_node_expr(&context, decision.entry, &mut memo, safety)
}

#[derive(Clone, PartialEq)]
pub(super) enum SynthTarget {
    CurrentValue,
    Expr(HirExpr),
}

fn synthesize_value_node_expr(
    context: &SynthesisContext<'_>,
    node_ref: HirDecisionNodeRef,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    if let Some(cached) = memo.get(&node_ref) {
        return Some(cached.clone());
    }

    let node = &context.decision.nodes[node_ref.index()];
    let truthy = synthesize_value_target(context, &node.truthy, memo, safety)?;
    let falsy = synthesize_value_target(context, &node.falsy, memo, safety)?;
    let expr =
        choose_best_structured_candidate(context, node_ref, &node.test, &truthy, &falsy, safety)?;
    memo.insert(node_ref, expr.clone());
    Some(expr)
}

fn synthesize_value_target(
    context: &SynthesisContext<'_>,
    target: &HirDecisionTarget,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
    safety: HirExprSafety,
) -> Option<SynthTarget> {
    match target {
        HirDecisionTarget::Node(next_ref) => Some(SynthTarget::Expr(synthesize_value_node_expr(
            context, *next_ref, memo, safety,
        )?)),
        HirDecisionTarget::CurrentValue => Some(SynthTarget::CurrentValue),
        HirDecisionTarget::Expr(expr) if expr_is_synth_safe(expr, safety) => {
            Some(SynthTarget::Expr(expr.clone()))
        }
        HirDecisionTarget::Expr(_) => None,
    }
}

fn choose_best_structured_candidate(
    context: &SynthesisContext<'_>,
    node_ref: HirDecisionNodeRef,
    subject: &HirExpr,
    truthy: &SynthTarget,
    falsy: &SynthTarget,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    structured_candidates(subject, truthy, falsy, safety)
        .into_iter()
        .map(|candidate| normalize_candidate_expr(candidate, safety))
        // 候选拒绝[ProofIncomplete]：有限抽象域当前只能提供筛选反例；错误路径与跨数值表示尚未精确建模，不能据此宣称完整等价证明。
        .filter(|candidate| validate_candidate_for_node(context, node_ref, candidate))
        .min_by_key(expr_cost)
}

pub(super) fn structured_candidates(
    subject: &HirExpr,
    truthy: &SynthTarget,
    falsy: &SynthTarget,
    safety: HirExprSafety,
) -> Vec<HirExpr> {
    let mut candidates = Vec::new();

    if let Some(expr) = super::super::combine_value_expr(
        subject.clone(),
        target_as_collapsed(truthy),
        target_as_collapsed(falsy),
        safety,
    ) {
        candidates.push(expr);
    }

    let truthy_expr = target_as_expr(subject, truthy);
    let falsy_expr = target_as_expr(subject, falsy);
    let not_subject = subject.clone().negate();

    candidates.push(super::super::logical_or(
        super::super::logical_and(subject.clone(), truthy_expr.clone()),
        falsy_expr.clone(),
    ));
    candidates.push(super::super::logical_or(
        super::super::logical_and(subject.clone(), truthy_expr.clone()),
        super::super::logical_and(subject.clone().negate(), falsy_expr.clone()),
    ));
    candidates.push(super::super::logical_or(
        super::super::logical_and(not_subject.clone(), falsy_expr.clone()),
        truthy_expr.clone(),
    ));
    candidates.push(super::super::logical_or(
        super::super::logical_and(not_subject.clone(), falsy_expr.clone()),
        super::super::logical_and(subject.clone(), truthy_expr.clone()),
    ));
    candidates.push(super::super::logical_and(
        super::super::logical_or(subject.clone(), falsy_expr.clone()),
        truthy_expr.clone(),
    ));
    candidates.push(super::super::logical_and(
        super::super::logical_or(not_subject, truthy_expr),
        falsy_expr,
    ));
    candidates
}

fn target_as_collapsed(target: &SynthTarget) -> super::super::CollapsedValueTarget {
    match target {
        SynthTarget::CurrentValue => super::super::CollapsedValueTarget::CurrentValue,
        SynthTarget::Expr(expr) => super::super::CollapsedValueTarget::Expr(expr.clone()),
    }
}

fn target_as_expr(subject: &HirExpr, target: &SynthTarget) -> HirExpr {
    match target {
        SynthTarget::CurrentValue => subject.clone(),
        SynthTarget::Expr(expr) => expr.clone(),
    }
}

pub(super) fn validate_candidate_for_node(
    context: &SynthesisContext<'_>,
    node_ref: HirDecisionNodeRef,
    candidate: &HirExpr,
) -> bool {
    context.environments.iter().all(|env| {
        let decision_value = context.eval_node(node_ref, env);
        // 候选拒绝[ProofIncomplete]：抽象解释未知时没有候选等价证明，不能把未建模路径当作验证通过。
        let Some(decision_value) = decision_value else {
            return false;
        };
        let candidate_value = context.eval_expr(candidate, env);
        candidate_value.as_ref() == Some(&decision_value)
    })
}
