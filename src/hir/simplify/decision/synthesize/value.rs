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
    let mut context = SynthesisContext::new(decision, refs, safety);
    let mut memo = BTreeMap::new();
    synthesize_value_node_expr(&mut context, decision.entry, &mut memo, safety)
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

#[cfg(test)]
mod tests {
    use crate::decompile::DecompileDialect;
    use crate::hir::common::{
        HirBinaryExpr, HirBinaryOpKind, HirCallExpr, HirDecisionExpr, HirDecisionNode,
        HirDecisionNodeRef, HirDecisionTarget, HirExpr, HirGlobalRef, HirLogicalExpr, HirValuePack,
        LocalId,
    };
    use crate::hir::expr_safety::HirExprSafety;

    use super::synthesize_value_decision_expr;

    #[test]
    fn mixed_numeric_value_identity_uses_equality_closed_domain() {
        let value = HirExpr::LocalRef(LocalId(0));
        let integer_one = HirExpr::Integer(1);
        let decision = HirDecisionExpr {
            entry: HirDecisionNodeRef(0),
            nodes: vec![HirDecisionNode {
                id: HirDecisionNodeRef(0),
                test: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                    lhs: value.clone(),
                    rhs: integer_one.clone(),
                })),
                truthy: HirDecisionTarget::Expr(HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                    lhs: HirExpr::Binary(Box::new(HirBinaryExpr {
                        op: HirBinaryOpKind::Eq,
                        lhs: value.clone(),
                        rhs: integer_one.clone(),
                    })),
                    rhs: integer_one,
                }))),
                falsy: HirDecisionTarget::Expr(value),
            }],
        };

        assert!(
            synthesize_value_decision_expr(
                &decision,
                HirExprSafety::for_dialect(DecompileDialect::Lua54),
            )
            .is_some()
        );
    }

    #[test]
    fn single_value_vararg_can_participate_in_synthesis() {
        let decision = HirDecisionExpr {
            entry: HirDecisionNodeRef(0),
            nodes: vec![HirDecisionNode {
                id: HirDecisionNodeRef(0),
                test: HirExpr::VarArg,
                truthy: HirDecisionTarget::CurrentValue,
                falsy: HirDecisionTarget::Expr(HirExpr::Boolean(false)),
            }],
        };

        assert!(
            synthesize_value_decision_expr(
                &decision,
                HirExprSafety::for_dialect(DecompileDialect::Lua54),
            )
            .is_some()
        );
    }

    #[test]
    fn effectful_call_stays_outside_value_only_synthesis() {
        let call = HirExpr::Call(Box::new(HirCallExpr {
            callee: HirExpr::GlobalRef(HirGlobalRef {
                name: "effect".to_owned(),
            }),
            args: HirValuePack::default(),
            method: false,
            fastcall: None,
            method_name: None,
        }));
        let decision = HirDecisionExpr {
            entry: HirDecisionNodeRef(0),
            nodes: vec![HirDecisionNode {
                id: HirDecisionNodeRef(0),
                test: call,
                truthy: HirDecisionTarget::CurrentValue,
                falsy: HirDecisionTarget::Expr(HirExpr::Boolean(false)),
            }],
        };

        assert!(
            synthesize_value_decision_expr(
                &decision,
                HirExprSafety::for_dialect(DecompileDialect::Lua54),
            )
            .is_none()
        );
    }
}
