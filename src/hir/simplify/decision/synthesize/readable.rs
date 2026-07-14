//! 这个子模块负责给 decision synthesis 提供“更像源码”的候选改写。
//!
//! 它依赖 `domain/safety/value` 已经确认的等价性和安全性，只在等价前提下挑选更自然的
//! 布尔表达式，不会越权放松语义约束。
//! 例如：`not (a == nil)` 可能在这里被整理成更顺的逻辑表达式。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::HirExpr;

use super::super::{logical_and, logical_or};
use super::domain::{
    AbstractValue, collect_literals_from_expr, collect_refs_from_expr, enumerate_environments,
    validate_pure_expr_equivalence,
};
use super::safety::expr_is_synth_safe;
use super::{MAX_SYNTH_REFS, normalize_candidate_expr};

pub(crate) fn naturalize_pure_logical_expr(expr: &HirExpr) -> Option<HirExpr> {
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
