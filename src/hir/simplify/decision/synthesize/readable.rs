//! 这个子模块负责给 decision synthesis 提供“更像源码”的候选改写。
//!
//! 它依赖 `domain/safety/value` 已经确认的等价性和安全性，只在等价前提下挑选更自然的
//! 布尔表达式，不会越权放松语义约束。
//! 例如：`not (a == nil)` 可能在这里被整理成更顺的逻辑表达式。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirExpr,
};

use super::super::{logical_and, logical_or};
use super::cost;
use super::domain::{
    AbstractValue, RefKey, SynthesisContext, collect_literals_from_expr, collect_refs_from_expr,
    enumerate_environments, validate_pure_expr_equivalence,
};
use super::safety::expr_is_synth_safe;
use super::value::{SynthTarget, structured_candidates, validate_candidate_for_node};
use super::{MAX_SYNTH_REFS, normalize_candidate_expr};

pub(super) fn naturalize_pure_logical_expr(expr: &HirExpr) -> Option<HirExpr> {
    if !matches!(expr, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)) {
        return None;
    }
    if !expr_is_synth_safe(expr) {
        return None;
    }

    let current = normalize_candidate_expr(expr.clone());
    let candidates = direct_pure_logical_rewrite_candidates(&current);
    if candidates.is_empty() {
        return None;
    }

    let mut refs = BTreeSet::new();
    collect_refs_from_expr(&current, &mut refs);
    let refs = refs.into_iter().collect::<Vec<_>>();
    if refs.len() > MAX_SYNTH_REFS {
        return None;
    }

    let ref_positions = refs
        .iter()
        .enumerate()
        .map(|(index, key)| (*key, index))
        .collect::<BTreeMap<_, _>>();
    let mut literals = BTreeSet::new();
    collect_literals_from_expr(&current, &mut literals);
    let mut domain = vec![
        AbstractValue::Nil,
        AbstractValue::False,
        AbstractValue::True,
    ];
    domain.extend(literals);
    domain.extend(
        (0..super::EXTRA_TRUTHY_SYMBOLS).map(|index| AbstractValue::TruthySymbol(index as u8)),
    );
    let environments = enumerate_environments(refs.len(), &domain)?;
    let current_cost = super::expr_cost(&current);

    candidates
        .into_iter()
        .map(normalize_candidate_expr)
        .filter(|candidate| {
            validate_pure_expr_equivalence(expr, candidate, &environments, &ref_positions)
        })
        .filter(|candidate| super::expr_cost(candidate) < current_cost)
        .min_by_key(super::expr_cost)
}

pub(super) fn synthesize_readable_pure_logical_expr(expr: &HirExpr) -> Option<HirExpr> {
    if !matches!(expr, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)) {
        return None;
    }
    if !expr_is_synth_safe(expr) {
        return None;
    }

    let current = normalize_candidate_expr(expr.clone());
    let mut refs = BTreeSet::new();
    collect_refs_from_expr(&current, &mut refs);
    let refs = refs.into_iter().collect::<Vec<_>>();
    if refs.len() > MAX_SYNTH_REFS {
        return None;
    }

    let ref_positions = refs
        .iter()
        .enumerate()
        .map(|(index, key)| (*key, index))
        .collect::<BTreeMap<_, _>>();
    let mut literals = BTreeSet::new();
    collect_literals_from_expr(&current, &mut literals);
    let mut domain = vec![
        AbstractValue::Nil,
        AbstractValue::False,
        AbstractValue::True,
    ];
    domain.extend(literals);
    domain.extend(
        (0..super::EXTRA_TRUTHY_SYMBOLS).map(|index| AbstractValue::TruthySymbol(index as u8)),
    );
    let environments = enumerate_environments(refs.len(), &domain)?;
    let mut best = current.clone();
    let mut visited = vec![current.clone()];
    let mut queue = vec![current.clone()];
    if let Some(structured) = readable_structured_candidate(&current, &environments, &ref_positions)
    {
        let structured = normalize_candidate_expr(structured);
        if validate_pure_expr_equivalence(expr, &structured, &environments, &ref_positions) {
            if cost::readable_expr_cost(&structured) < cost::readable_expr_cost(&best) {
                best = structured.clone();
            }
            if !visited.iter().any(|seen| seen == &structured) {
                visited.push(structured.clone());
                queue.push(structured);
            }
        }
    }
    let mut cursor = 0usize;

    while cursor < queue.len() && visited.len() < 64 {
        let candidate = queue[cursor].clone();
        cursor += 1;

        let next_candidates = readable_local_rewrite_candidates(&candidate);

        for next in next_candidates.into_iter().map(normalize_candidate_expr) {
            if visited.iter().any(|seen| seen == &next) {
                continue;
            }
            if !validate_pure_expr_equivalence(expr, &next, &environments, &ref_positions) {
                continue;
            }
            if cost::readable_expr_cost(&next) < cost::readable_expr_cost(&best) {
                best = next.clone();
            }
            visited.push(next.clone());
            queue.push(next);
            if visited.len() >= 64 {
                break;
            }
        }
    }

    (cost::readable_expr_cost(&best) < cost::readable_expr_cost(&current)).then_some(best)
}

fn build_readable_decision(expr: &HirExpr) -> Option<HirDecisionExpr> {
    let mut nodes = Vec::new();
    let entry = lower_pure_expr_to_target(
        expr,
        HirDecisionTarget::CurrentValue,
        HirDecisionTarget::CurrentValue,
        &mut nodes,
    )?;
    let HirDecisionTarget::Node(entry) = entry else {
        return None;
    };
    Some(HirDecisionExpr { entry, nodes })
}

fn readable_structured_candidate(
    expr: &HirExpr,
    environments: &[Vec<AbstractValue>],
    ref_positions: &BTreeMap<RefKey, usize>,
) -> Option<HirExpr> {
    let decision = build_readable_decision(expr)?;
    let context = SynthesisContext {
        decision: &decision,
        ref_positions: ref_positions.clone(),
        environments: environments.to_vec(),
    };
    let mut memo = BTreeMap::new();
    synthesize_readable_value_node_expr(&context, decision.entry, &mut memo)
}

fn readable_local_rewrite_candidates(expr: &HirExpr) -> Vec<HirExpr> {
    let mut candidates = Vec::new();
    candidates.extend(fold_or_guard_with_shared_fallback(expr));
    candidates.extend(factor_falsy_fallback_guard(expr));
    candidates.extend(strip_falsy_fallback_inside_guard(expr));
    candidates
}

fn fold_or_guard_with_shared_fallback(expr: &HirExpr) -> Vec<HirExpr> {
    let outer_terms = flatten_or_chain(expr);
    if outer_terms.len() < 3 {
        return Vec::new();
    }

    let mut candidates = Vec::new();
    for (fallback_index, fallback) in outer_terms.iter().enumerate() {
        for (guard_index, guard_term) in outer_terms.iter().enumerate() {
            if guard_index == fallback_index {
                continue;
            }
            let HirExpr::LogicalAnd(guard) = guard_term else {
                continue;
            };
            let inner_terms = flatten_or_chain(&guard.rhs);
            if !inner_terms.contains(fallback) {
                continue;
            }

            let x_terms = outer_terms
                .iter()
                .enumerate()
                .filter_map(|(index, term)| {
                    (index != fallback_index && index != guard_index).then_some((*term).clone())
                })
                .collect::<Vec<_>>();
            if x_terms.is_empty() {
                continue;
            }

            let guarded = logical_and(
                logical_or(rebuild_or_chain(x_terms), guard.lhs.clone()),
                rebuild_or_chain(inner_terms.into_iter().cloned().collect()),
            );
            candidates.push(logical_or(guarded, (*fallback).clone()));
        }
    }
    candidates
}

fn factor_falsy_fallback_guard(expr: &HirExpr) -> Vec<HirExpr> {
    let outer_terms = flatten_or_chain(expr);
    if outer_terms.len() < 3 {
        return Vec::new();
    }

    let mut candidates = Vec::new();
    for (fallback_index, fallback) in outer_terms.iter().enumerate() {
        if super::super::expr_truthiness(fallback) != Some(false) {
            continue;
        }

        for (guard_index, guard_term) in outer_terms.iter().enumerate() {
            if guard_index == fallback_index {
                continue;
            }
            let HirExpr::LogicalAnd(guard) = guard_term else {
                continue;
            };
            let inner_terms = flatten_or_chain(&guard.rhs);
            let Some(inner_fallback_index) = inner_terms.iter().position(|term| *term == *fallback)
            else {
                continue;
            };
            if inner_terms.len() < 2 {
                continue;
            }

            let z_terms = inner_terms
                .iter()
                .enumerate()
                .filter_map(|(index, term)| (index != inner_fallback_index).then_some(*term))
                .collect::<Vec<_>>();
            if z_terms.is_empty() {
                continue;
            }
            let x_terms = outer_terms
                .iter()
                .enumerate()
                .filter_map(|(index, term)| {
                    (index != fallback_index && index != guard_index).then_some((*term).clone())
                })
                .collect::<Vec<_>>();

            let z = rebuild_or_chain(z_terms.into_iter().cloned().collect());
            let guarded = if x_terms.is_empty() {
                logical_and(guard.lhs.clone(), z)
            } else {
                logical_and(logical_or(rebuild_or_chain(x_terms), guard.lhs.clone()), z)
            };
            candidates.push(logical_or(guarded, (*fallback).clone()));
        }
    }
    candidates
}

fn strip_falsy_fallback_inside_guard(expr: &HirExpr) -> Vec<HirExpr> {
    let outer_terms = flatten_or_chain(expr);
    if outer_terms.len() < 2 {
        return Vec::new();
    }

    let mut candidates = Vec::new();
    for (fallback_index, fallback) in outer_terms.iter().enumerate() {
        if super::super::expr_truthiness(fallback) != Some(false) {
            continue;
        }

        for (guard_index, guard_term) in outer_terms.iter().enumerate() {
            if guard_index == fallback_index {
                continue;
            }
            let HirExpr::LogicalAnd(guard) = guard_term else {
                continue;
            };
            let inner_terms = flatten_or_chain(&guard.rhs);
            let Some(inner_fallback_index) = inner_terms.iter().position(|term| *term == *fallback)
            else {
                continue;
            };
            let z_terms = inner_terms
                .iter()
                .enumerate()
                .filter_map(|(index, term)| (index != inner_fallback_index).then_some(*term))
                .collect::<Vec<_>>();
            if z_terms.is_empty() {
                continue;
            }
            let replacement = logical_and(
                guard.lhs.clone(),
                rebuild_or_chain(z_terms.into_iter().cloned().collect()),
            );
            let rebuilt = outer_terms
                .iter()
                .enumerate()
                .map(|(index, term)| {
                    if index == guard_index {
                        replacement.clone()
                    } else {
                        (*term).clone()
                    }
                })
                .collect::<Vec<_>>();
            candidates.push(rebuild_or_chain(rebuilt));
        }
    }
    candidates
}

fn lower_pure_expr_to_target(
    expr: &HirExpr,
    truthy: HirDecisionTarget,
    falsy: HirDecisionTarget,
    nodes: &mut Vec<HirDecisionNode>,
) -> Option<HirDecisionTarget> {
    match expr {
        HirExpr::LogicalAnd(logical) => {
            let rhs = lower_pure_expr_to_target(&logical.rhs, truthy, falsy.clone(), nodes)?;
            lower_pure_expr_to_target(&logical.lhs, rhs, falsy, nodes)
        }
        HirExpr::LogicalOr(logical) => {
            let rhs = lower_pure_expr_to_target(&logical.rhs, truthy.clone(), falsy, nodes)?;
            lower_pure_expr_to_target(&logical.lhs, truthy, rhs, nodes)
        }
        _ if expr_is_synth_safe(expr) => {
            if let Some(existing) = nodes
                .iter()
                .find(|node| node.test == *expr && node.truthy == truthy && node.falsy == falsy)
            {
                return Some(HirDecisionTarget::Node(existing.id));
            }
            let id = HirDecisionNodeRef(nodes.len());
            nodes.push(HirDecisionNode {
                id,
                test: expr.clone(),
                truthy,
                falsy,
            });
            Some(HirDecisionTarget::Node(id))
        }
        _ => None,
    }
}

fn synthesize_readable_value_node_expr(
    context: &SynthesisContext<'_>,
    node_ref: HirDecisionNodeRef,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
) -> Option<HirExpr> {
    if let Some(cached) = memo.get(&node_ref) {
        return Some(cached.clone());
    }

    let node = &context.decision.nodes[node_ref.index()];
    let truthy = synthesize_readable_value_target(context, &node.truthy, memo)?;
    let falsy = synthesize_readable_value_target(context, &node.falsy, memo)?;
    let expr = structured_candidates(&node.test, &truthy, &falsy)
        .into_iter()
        .map(normalize_candidate_expr)
        .filter(|candidate| validate_candidate_for_node(context, node_ref, candidate))
        .min_by_key(cost::readable_expr_cost)?;
    memo.insert(node_ref, expr.clone());
    Some(expr)
}

fn synthesize_readable_value_target(
    context: &SynthesisContext<'_>,
    target: &HirDecisionTarget,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
) -> Option<SynthTarget> {
    match target {
        HirDecisionTarget::Node(next_ref) => Some(SynthTarget::Expr(
            synthesize_readable_value_node_expr(context, *next_ref, memo)?,
        )),
        HirDecisionTarget::CurrentValue => Some(SynthTarget::CurrentValue),
        HirDecisionTarget::Expr(expr) if expr_is_synth_safe(expr) => {
            Some(SynthTarget::Expr(expr.clone()))
        }
        HirDecisionTarget::Expr(_) => None,
    }
}

fn direct_pure_logical_rewrite_candidates(expr: &HirExpr) -> Vec<HirExpr> {
    let mut candidates = Vec::new();
    match expr {
        HirExpr::LogicalAnd(logical) => {
            if let HirExpr::LogicalOr(lhs_or) = &logical.lhs {
                candidates.push(logical_or(
                    logical_and(lhs_or.lhs.clone(), logical.rhs.clone()),
                    logical_and(lhs_or.rhs.clone(), logical.rhs.clone()),
                ));
            }
            if let HirExpr::LogicalOr(rhs_or) = &logical.rhs {
                candidates.push(logical_or(
                    logical_and(logical.lhs.clone(), rhs_or.lhs.clone()),
                    logical_and(logical.lhs.clone(), rhs_or.rhs.clone()),
                ));
            }
        }
        HirExpr::LogicalOr(logical) => {
            candidates.extend(factor_or_of_ands(&logical.lhs, &logical.rhs));
            candidates.extend(factor_or_chain_of_ands(expr));
        }
        _ => {}
    }
    candidates
}

fn factor_or_of_ands(lhs: &HirExpr, rhs: &HirExpr) -> Vec<HirExpr> {
    let mut candidates = Vec::new();
    let lhs_terms = flatten_and_chain(lhs);
    let rhs_terms = flatten_and_chain(rhs);
    if lhs_terms.len() < 2 || rhs_terms.len() < 2 {
        return candidates;
    }

    if let Some((lhs_prefix, rhs_prefix, common_prefix)) =
        split_common_prefix(&lhs_terms, &rhs_terms)
    {
        candidates.push(logical_and(
            rebuild_and_chain(common_prefix),
            logical_or(rebuild_and_chain(lhs_prefix), rebuild_and_chain(rhs_prefix)),
        ));
    }

    if let Some((lhs_suffix, rhs_suffix, common_suffix)) =
        split_common_suffix(&lhs_terms, &rhs_terms)
    {
        candidates.push(logical_and(
            logical_or(rebuild_and_chain(lhs_suffix), rebuild_and_chain(rhs_suffix)),
            rebuild_and_chain(common_suffix),
        ));
    }

    candidates
}

fn factor_or_chain_of_ands(expr: &HirExpr) -> Vec<HirExpr> {
    let terms = flatten_or_chain(expr);
    if terms.len() < 3 {
        return Vec::new();
    }

    let mut candidates = Vec::new();
    for left in 0..terms.len() {
        for right in left + 1..terms.len() {
            if let Some(factored) = factor_and_term_pair(terms[left], terms[right]) {
                let mut rebuilt = Vec::with_capacity(terms.len() - 1);
                for (index, term) in terms.iter().enumerate() {
                    if index == left {
                        rebuilt.push(factored.clone());
                    } else if index != right {
                        rebuilt.push((*term).clone());
                    }
                }
                candidates.push(rebuild_or_chain(rebuilt));
            }
        }
    }
    candidates
}

fn factor_and_term_pair(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    let lhs_terms = flatten_and_chain(lhs);
    let rhs_terms = flatten_and_chain(rhs);
    if lhs_terms.len() < 2 || rhs_terms.len() < 2 {
        return None;
    }

    if let Some((lhs_prefix, rhs_prefix, common_prefix)) =
        split_common_prefix(&lhs_terms, &rhs_terms)
    {
        return Some(logical_and(
            rebuild_and_chain(common_prefix),
            logical_or(rebuild_and_chain(lhs_prefix), rebuild_and_chain(rhs_prefix)),
        ));
    }

    if let Some((lhs_suffix, rhs_suffix, common_suffix)) =
        split_common_suffix(&lhs_terms, &rhs_terms)
    {
        return Some(logical_and(
            logical_or(rebuild_and_chain(lhs_suffix), rebuild_and_chain(rhs_suffix)),
            rebuild_and_chain(common_suffix),
        ));
    }

    None
}

fn flatten_and_chain(expr: &HirExpr) -> Vec<&HirExpr> {
    let mut terms = Vec::new();
    collect_and_chain(expr, &mut terms);
    terms
}

pub(super) fn flatten_or_chain(expr: &HirExpr) -> Vec<&HirExpr> {
    let mut terms = Vec::new();
    collect_or_chain(expr, &mut terms);
    terms
}

fn collect_and_chain<'a>(expr: &'a HirExpr, out: &mut Vec<&'a HirExpr>) {
    match expr {
        HirExpr::LogicalAnd(logical) => {
            collect_and_chain(&logical.lhs, out);
            collect_and_chain(&logical.rhs, out);
        }
        _ => out.push(expr),
    }
}

fn collect_or_chain<'a>(expr: &'a HirExpr, out: &mut Vec<&'a HirExpr>) {
    match expr {
        HirExpr::LogicalOr(logical) => {
            collect_or_chain(&logical.lhs, out);
            collect_or_chain(&logical.rhs, out);
        }
        _ => out.push(expr),
    }
}

fn rebuild_and_chain(terms: Vec<&HirExpr>) -> HirExpr {
    let mut iter = terms.into_iter();
    let first = iter
        .next()
        .expect("rebuilding logical chain requires at least one term")
        .clone();
    iter.fold(first, |acc, term| logical_and(acc, term.clone()))
}

fn rebuild_or_chain(terms: Vec<HirExpr>) -> HirExpr {
    let mut iter = terms.into_iter();
    let first = iter
        .next()
        .expect("rebuilding logical chain requires at least one term");
    iter.fold(first, logical_or)
}

fn split_common_prefix<'a>(
    lhs: &[&'a HirExpr],
    rhs: &[&'a HirExpr],
) -> Option<(Vec<&'a HirExpr>, Vec<&'a HirExpr>, Vec<&'a HirExpr>)> {
    let mut common_len = 0usize;
    while common_len < lhs.len() && common_len < rhs.len() && lhs[common_len] == rhs[common_len] {
        common_len += 1;
    }
    if common_len == 0 || common_len == lhs.len() || common_len == rhs.len() {
        return None;
    }
    Some((
        lhs[common_len..].to_vec(),
        rhs[common_len..].to_vec(),
        lhs[..common_len].to_vec(),
    ))
}

fn split_common_suffix<'a>(
    lhs: &[&'a HirExpr],
    rhs: &[&'a HirExpr],
) -> Option<(Vec<&'a HirExpr>, Vec<&'a HirExpr>, Vec<&'a HirExpr>)> {
    let mut common_len = 0usize;
    while common_len < lhs.len()
        && common_len < rhs.len()
        && lhs[lhs.len() - 1 - common_len] == rhs[rhs.len() - 1 - common_len]
    {
        common_len += 1;
    }
    if common_len == 0 || common_len == lhs.len() || common_len == rhs.len() {
        return None;
    }
    Some((
        lhs[..lhs.len() - common_len].to_vec(),
        rhs[..rhs.len() - common_len].to_vec(),
        lhs[lhs.len() - common_len..].to_vec(),
    ))
}
