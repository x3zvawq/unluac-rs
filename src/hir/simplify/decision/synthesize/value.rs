//! 这个子模块负责把 decision expression 直接综合回值表达式。
//!
//! 它依赖 `domain` 的等价性环境和 `safety` 的约束，只在整棵 decision 真能等价表达成
//! 一个值时才返回结果，不会在这里兜底伪造分支。
//! 例如：`cond ? x : y` 这类纯值 decision 会在这里尝试还原成逻辑值表达式。

use std::collections::BTreeMap;

use crate::hir::common::{HirDecisionExpr, HirDecisionNodeRef, HirDecisionTarget, HirExpr};
use crate::hir::common::{HirLogicalExpr, HirUnaryExpr, HirUnaryOpKind};
use crate::hir::expr_safety::HirExprSafety;

use super::domain::{SynthesisContext, collect_refs_from_decision};
use super::safety::{decision_is_synth_safe, expr_is_synth_safe};
use super::{expr_cost, normalize_candidate_expr};

pub(crate) fn synthesize_value_decision_expr(
    decision: &HirDecisionExpr,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    if !decision_is_synth_safe(decision, safety) {
        return exact_trace_candidate(decision, safety);
    }

    let refs = collect_refs_from_decision(decision);
    let mut context = SynthesisContext::new(decision, refs, safety);
    let mut memo = BTreeMap::new();
    synthesize_value_node_expr(&mut context, decision.entry, &mut memo, safety)
}

/// Effectful synthesis is intentionally a proof-carrying grammar rather than algebraic search.
///
/// A node whose two edges are the same target has one unconditional trace: evaluate its test,
/// then evaluate that target. `not test or true` evaluates `test` exactly once, immediately
/// booleanizes its result (so no test root is retained across the continuation), and is always
/// truthy; the surrounding `and` therefore evaluates the continuation exactly once and returns it.
#[derive(Clone)]
enum ExactEvalTrace {
    Value(HirExpr),
    Then {
        discarded: HirExpr,
        continuation: Box<ExactEvalTrace>,
    },
}

impl ExactEvalTrace {
    fn into_expr(self) -> HirExpr {
        match self {
            Self::Value(expr) => expr,
            Self::Then {
                discarded,
                continuation,
            } => trace_sequence_expr(discarded, continuation.into_expr()),
        }
    }

    fn matches_expr(&self, candidate: &HirExpr) -> bool {
        match (self, candidate) {
            (Self::Value(expected), candidate) => expected == candidate,
            (
                Self::Then {
                    discarded,
                    continuation,
                },
                HirExpr::LogicalAnd(sequence),
            ) => {
                let HirExpr::LogicalOr(prefix) = &sequence.lhs else {
                    return false;
                };
                matches!(
                    &prefix.lhs,
                    HirExpr::Unary(negated)
                        if negated.op == HirUnaryOpKind::Not && negated.expr == *discarded
                ) && matches!(prefix.rhs, HirExpr::Boolean(true))
                    && continuation.matches_expr(&sequence.rhs)
            }
            _ => false,
        }
    }
}

fn exact_trace_candidate(decision: &HirDecisionExpr, safety: HirExprSafety) -> Option<HirExpr> {
    let trace = exact_eval_trace(decision, decision.entry, safety)?;
    let candidate = trace.clone().into_expr();
    // Keep the trace certificate at the commit boundary. Candidate normalization must not be
    // inserted between construction and this check: it may delete or duplicate observable nodes.
    trace.matches_expr(&candidate).then_some(candidate)
}

fn exact_eval_trace(
    decision: &HirDecisionExpr,
    node_ref: HirDecisionNodeRef,
    safety: HirExprSafety,
) -> Option<ExactEvalTrace> {
    let node = decision.nodes.get(node_ref.index())?;
    if node.truthy != node.falsy {
        // 候选拒绝[SemanticBarrier:EvalOrder]：effectful 分叉没有无条件 continuation；
        // `f() and g() or h()` 还会在 g 返回 falsy 时错误执行未选中的 h。
        return None;
    }
    match &node.truthy {
        HirDecisionTarget::CurrentValue => Some(ExactEvalTrace::Value(node.test.clone())),
        HirDecisionTarget::Expr(expr) => {
            if !safety.result_is_gc_inert(&node.test) {
                // 候选拒绝[SemanticBarrier:Lifetime]：`f()` 的 collectable 返回值可能仍由
                // 原 guard slot 持有；先 booleanize 再执行 `g()` 会提前断根，使 g 内的
                // weak-table/GC observation 与原程序不同。Decision 没有 test home/root 终止事实。
                return None;
            }
            Some(ExactEvalTrace::Then {
                discarded: node.test.clone(),
                continuation: Box::new(ExactEvalTrace::Value(expr.clone())),
            })
        }
        HirDecisionTarget::Node(next_ref) => {
            if !safety.result_is_gc_inert(&node.test) {
                // 候选拒绝[SemanticBarrier:Lifetime]：进入 child 前丢弃 collectable test
                // 会改变 child effect 可观察的 root 生命周期；当前 Decision 不携带 home 事实。
                return None;
            }
            Some(ExactEvalTrace::Then {
                discarded: node.test.clone(),
                continuation: Box::new(exact_eval_trace(decision, *next_ref, safety)?),
            })
        }
    }
}

fn trace_sequence_expr(discarded: HirExpr, continuation: HirExpr) -> HirExpr {
    let booleanized = HirExpr::Unary(Box::new(HirUnaryExpr {
        source_site: None,
        op: HirUnaryOpKind::Not,
        expr: discarded,
    }));
    HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
        preserves_boolean_prewrite: false,
        lhs: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
            preserves_boolean_prewrite: false,
            lhs: booleanized,
            rhs: HirExpr::Boolean(true),
        })),
        rhs: continuation,
    }))
}

#[derive(Clone, PartialEq)]
pub(super) enum SynthTarget {
    CurrentValue,
    Expr(HirExpr),
}

fn synthesize_value_node_expr(
    context: &mut SynthesisContext<'_>,
    node_ref: HirDecisionNodeRef,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    if let Some(cached) = memo.get(&node_ref) {
        return Some(cached.clone());
    }

    let node = context.decision.nodes[node_ref.index()].clone();
    let truthy = synthesize_value_target(context, &node.truthy, memo, safety)?;
    let falsy = synthesize_value_target(context, &node.falsy, memo, safety)?;
    let expr =
        choose_best_structured_candidate(context, node_ref, &node.test, &truthy, &falsy, safety)?;
    memo.insert(node_ref, expr.clone());
    Some(expr)
}

fn synthesize_value_target(
    context: &mut SynthesisContext<'_>,
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
    context: &mut SynthesisContext<'_>,
    node_ref: HirDecisionNodeRef,
    subject: &HirExpr,
    truthy: &SynthTarget,
    falsy: &SynthTarget,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    structured_candidates(subject, truthy, falsy, safety)
        .into_iter()
        .map(|candidate| normalize_candidate_expr(candidate, safety))
        // 候选验证：canonical MDD 共享同一 RefKey 的所有出现；任一未建模路径都会
        // 让符号求值返回 None 并拒绝候选。
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
    context: &mut SynthesisContext<'_>,
    node_ref: HirDecisionNodeRef,
    candidate: &HirExpr,
) -> bool {
    context.candidate_matches_node(node_ref, candidate)
}
