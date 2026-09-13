//! 这个子模块负责给 decision synthesis 提供“更像源码”的候选改写。
//!
//! 它依赖 `domain/safety/value` 已经确认的等价性和安全性，只在等价前提下挑选更自然的
//! 布尔表达式，不会越权放松语义约束。
//! 例如：`not (a == nil)` 可能在这里被整理成更顺的逻辑表达式。

use std::collections::BTreeSet;
use std::hash::{DefaultHasher, Hash, Hasher};

use crate::hir::common::HirExpr;
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::visit::{HirVisitor, visit_expr};

use super::super::{logical_and, logical_or};
use super::domain::{
    AbstractValue, AtomKey, SymbolicVerifier, build_validation_domain, collect_literals_from_expr,
    collect_refs_from_expr,
};
use super::normalize_candidate_expr;
use super::safety::expr_is_synth_safe;

pub(crate) fn naturalize_pure_logical_expr(
    expr: &HirExpr,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    if !matches!(expr, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)) {
        return None;
    }
    if !expr_is_synth_safe(expr, safety) {
        return None;
    }

    // 只有已证明纯且稳定的逻辑综合可以重排/合并谓词。候选里的比较是值公式，
    // 不再代表某一次原跳转；否则相同 a==1 会因不同 PC 无法提取公因子。提交仍须
    // 成本下降与 MDD 等价证明，不能让合成比较借任一原谓词的 LOADBOOL 写回证书。
    struct SynthesizedPredicates;
    impl crate::hir::simplify::walk::HirRewritePass for SynthesizedPredicates {
        fn rewrite_expr_before_children(&mut self, expr: &mut HirExpr) -> bool {
            if let HirExpr::Binary(binary) = expr
                && matches!(
                    binary.op,
                    crate::hir::HirBinaryOpKind::Eq
                        | crate::hir::HirBinaryOpKind::Lt
                        | crate::hir::HirBinaryOpKind::Le
                )
            {
                return binary.source_site.take().is_some();
            }
            false
        }
    }
    let mut current = expr.clone();
    crate::hir::simplify::walk::rewrite_expr(&mut current, &mut SynthesizedPredicates);
    let mut current = normalize_candidate_expr(current, safety);
    let mut validation = None;
    let mut changed = false;
    // 每次提交都严格降低有限的 expr_cost；因此即使深层候选需要超过八轮，也会在有限步内
    // 收敛，不需要用任意轮数截断已证明安全的改写。
    loop {
        let current_cost = super::expr_cost(&current);
        let mut next = None;
        visit_pure_logical_rewrite_candidates(&current, &mut |candidate| {
            let candidate = normalize_candidate_expr(candidate, safety);
            let candidate_cost = super::expr_cost(&candidate);
            if candidate_cost >= current_cost {
                // 候选拒绝[PolicyBoundary]：不降低可读性成本的候选不会提交，
                // 无需为它求解整棵表达式的 MDD。
                return;
            }
            // 常见的已恢复短路链没有更短候选；仅在实际需要等价证明时建立共享验证域。
            let (verifier, expected) = validation.get_or_insert_with(|| {
                let mut refs = BTreeSet::new();
                collect_refs_from_expr(&current, &mut refs);
                let mut literals = BTreeSet::new();
                collect_literals_from_expr(&current, &mut literals);
                let domain = build_validation_domain(&literals, safety);
                let mut verifier =
                    SymbolicVerifier::new(refs.into_iter().collect(), domain, safety);
                let expected = verifier.eval_expr(expr);
                (verifier, expected)
            });
            if expected.is_none() || verifier.eval_expr(&candidate) != *expected {
                return;
            }
            if next
                .as_ref()
                .is_none_or(|(best_cost, _)| candidate_cost < *best_cost)
            {
                next = Some((candidate_cost, candidate));
            }
        });
        let Some((_, next)) = next else {
            break;
        };
        current = next;
        changed = true;
    }

    changed.then_some(current)
}

/// Visit one-step rewrites at the root and one logical child.
///
/// The fixed-point loop above revisits the rebuilt expression, so deeper opportunities are still
/// reached without enumerating all expression paths at once. Candidates are emitted immediately,
/// so the caller retains only the cheapest validated rewrite instead of an arbitrarily capped set.
fn visit_pure_logical_rewrite_candidates(expr: &HirExpr, emit: &mut impl FnMut(HirExpr)) {
    visit_direct_pure_logical_rewrite_candidates(expr, emit);
    let (lhs, rhs, is_and) = match expr {
        HirExpr::LogicalAnd(logical) => (&logical.lhs, &logical.rhs, true),
        HirExpr::LogicalOr(logical) => (&logical.lhs, &logical.rhs, false),
        _ => return,
    };

    for (left, child, sibling) in [(true, lhs, rhs), (false, rhs, lhs)] {
        visit_direct_pure_logical_rewrite_candidates(child, &mut |replacement| {
            emit(if is_and {
                if left {
                    logical_and(replacement, sibling.clone())
                } else {
                    logical_and(sibling.clone(), replacement)
                }
            } else if left {
                logical_or(replacement, sibling.clone())
            } else {
                logical_or(sibling.clone(), replacement)
            });
        });
    }
}

fn visit_direct_pure_logical_rewrite_candidates(expr: &HirExpr, emit: &mut impl FnMut(HirExpr)) {
    match expr {
        HirExpr::LogicalAnd(logical) => {
            for candidate in factor_or_shared_and_tail(&logical.lhs, &logical.rhs) {
                emit(candidate);
            }
            if let HirExpr::LogicalOr(lhs_or) = &logical.lhs {
                emit(logical_or(
                    logical_and(lhs_or.lhs.clone(), logical.rhs.clone()),
                    logical_and(lhs_or.rhs.clone(), logical.rhs.clone()),
                ));
            }
            if let HirExpr::LogicalOr(rhs_or) = &logical.rhs {
                emit(logical_or(
                    logical_and(logical.lhs.clone(), rhs_or.lhs.clone()),
                    logical_and(logical.lhs.clone(), rhs_or.rhs.clone()),
                ));
            }
        }
        HirExpr::LogicalOr(logical) => {
            for candidate in drop_shared_or_fallback(&logical.lhs, &logical.rhs) {
                emit(candidate);
            }
            for candidate in factor_or_of_ands(&logical.lhs, &logical.rhs) {
                emit(candidate);
            }
            visit_factor_or_chain_of_ands(expr, emit);
        }
        _ => {}
    }
}

/// Generate a candidate for `((a and (b or ... or c)) or c)` with the inner fallback removed.
///
/// The shape is common after a shared decision continuation is treeified.  Removing `c` is not
/// a general Lua value identity, so this helper only proposes the candidate; the caller's
/// exhaustive pure-expression validator decides whether the surrounding guards make it exact.
fn drop_shared_or_fallback(lhs: &HirExpr, rhs: &HirExpr) -> Vec<HirExpr> {
    let HirExpr::LogicalAnd(and_expr) = lhs else {
        return Vec::new();
    };
    let terms = flatten_or_chain(&and_expr.rhs);
    if terms.len() < 2 {
        return Vec::new();
    }

    let Some(index) = terms.iter().rposition(|term| *term == rhs) else {
        return Vec::new();
    };
    let shortened = terms
        .into_iter()
        .enumerate()
        .filter(|(term_index, _)| *term_index != index)
        .map(|(_, term)| term.clone())
        .collect::<Vec<_>>();
    let inner = rebuild_or_chain(shortened);
    vec![logical_or(
        logical_and(and_expr.lhs.clone(), inner),
        rhs.clone(),
    )]
}

/// `((a or (b and c)) and c)` can be shortened to `(a or b) and c`.
///
/// If `a` is truthy, both forms return `c`.  Otherwise both evaluate `b`; a falsy `b` is
/// returned directly and a truthy `b` proceeds to the same `c`.  The operands are restricted to
/// repeatable expressions by the caller, so removing the duplicate reads cannot expose a side
/// effect.  The symmetric inner `and` layout follows the same argument.
fn factor_or_shared_and_tail(lhs: &HirExpr, rhs: &HirExpr) -> Vec<HirExpr> {
    let HirExpr::LogicalOr(inner) = lhs else {
        return Vec::new();
    };
    let HirExpr::LogicalAnd(shared) = &inner.rhs else {
        return Vec::new();
    };

    let mut candidates = Vec::new();
    if shared.rhs == *rhs {
        candidates.push(logical_and(
            logical_or(inner.lhs.clone(), shared.lhs.clone()),
            rhs.clone(),
        ));
    }
    if shared.lhs == *rhs {
        candidates.push(logical_and(
            logical_or(inner.lhs.clone(), shared.rhs.clone()),
            rhs.clone(),
        ));
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

/// 只索引可能有共同首项或末项的分支。保留原 left/right 枚举次序和所有候选，
/// 不用排序键替代完整表达式比较或 Lua 值等价验证；配对流不分配平方大小的集合。
fn visit_factor_or_chain_of_ands(expr: &HirExpr, emit: &mut impl FnMut(HirExpr)) {
    let terms = flatten_or_chain(expr);
    if terms.len() < 3 {
        return;
    }
    let parts = terms
        .iter()
        .map(|term| flatten_and_chain(term))
        .collect::<Vec<_>>();
    let mut entries = Vec::with_capacity(terms.len() * 2);
    for (term, parts) in parts.iter().enumerate() {
        if parts.len() >= 2 {
            for (side, factor) in [parts[0], parts[parts.len() - 1]].into_iter().enumerate() {
                entries.push((side, factor_key(factor), term));
            }
        }
    }
    entries.sort_unstable();
    let mut memberships = vec![None; terms.len()];
    let mut start = 0;
    while start < entries.len() {
        let (side, key, _) = entries[start];
        let mut end = start + 1;
        while end < entries.len() && (entries[end].0, entries[end].1) == (side, key) {
            end += 1;
        }
        for &(_, _, term) in &entries[start..end] {
            memberships[term].get_or_insert([0..0, 0..0])[side] = start..end;
        }
        start = end;
    }

    for (left, membership) in memberships.into_iter().enumerate() {
        let Some([first, last]) = membership else {
            continue;
        };
        let first = &entries[first];
        let last = &entries[last];
        let mut first = first[first.partition_point(|entry| entry.2 <= left)..]
            .iter()
            .map(|entry| entry.2)
            .peekable();
        let mut last = last[last.partition_point(|entry| entry.2 <= left)..]
            .iter()
            .map(|entry| entry.2)
            .peekable();
        while let Some(right) = match (first.peek().copied(), last.peek().copied()) {
            (Some(a), Some(b)) => {
                if a <= b {
                    first.next();
                }
                if b <= a {
                    last.next();
                }
                Some(a.min(b))
            }
            (Some(_), None) => first.next(),
            (None, Some(_)) => last.next(),
            (None, None) => None,
        } {
            if let Some(factored) = factor_and_term_pair(&parts[left], &parts[right]) {
                let mut rebuilt = Vec::with_capacity(terms.len() - 1);
                let mut factored = Some(factored);
                for (position, term) in terms.iter().enumerate() {
                    if position == left {
                        rebuilt.push(factored.take().expect("left occurs once"));
                    } else if position != right {
                        rebuilt.push((*term).clone());
                    }
                }
                emit(rebuild_or_chain(rebuilt));
            }
        }
    }
}

/// 指纹只过滤不可能相等的项；碰撞仍经过完整 HIR 比较与 MDD 验证。
/// 共享 visitor 保留节点顺序，原子身份来自综合域，不另建表达式树或分配 token 序列。
fn factor_key(expr: &HirExpr) -> u64 {
    struct Fingerprint(DefaultHasher);
    impl HirVisitor<'_> for Fingerprint {
        fn visit_expr(&mut self, expr: &HirExpr) {
            std::mem::discriminant(expr).hash(&mut self.0);
            if let Some(mut atom) = AtomKey::from_expr(expr) {
                // HIR 结构比较把正负零视为相等；过滤键不能漏掉这些原有候选。
                let canonical_zero = |bits: &mut u64| {
                    if *bits == (-0.0f64).to_bits() {
                        *bits = 0;
                    }
                };
                match &mut atom {
                    AtomKey::Value(AbstractValue::Number(bits)) => canonical_zero(bits),
                    AtomKey::Value(AbstractValue::Complex {
                        real_bits,
                        imag_bits,
                    }) => {
                        canonical_zero(real_bits);
                        canonical_zero(imag_bits);
                    }
                    _ => {}
                }
                atom.hash(&mut self.0);
            } else {
                match expr {
                    HirExpr::Unary(unary) => unary.op.hash(&mut self.0),
                    HirExpr::Binary(binary) => binary.op.hash(&mut self.0),
                    _ => {}
                }
            }
        }
    }
    let mut fingerprint = Fingerprint(DefaultHasher::new());
    visit_expr(expr, &mut fingerprint);
    fingerprint.0.finish()
}

fn factor_and_term_pair(lhs_terms: &[&HirExpr], rhs_terms: &[&HirExpr]) -> Option<HirExpr> {
    if lhs_terms.len() < 2 || rhs_terms.len() < 2 {
        return None;
    }

    if let Some((lhs_prefix, rhs_prefix, common_prefix)) = split_common_prefix(lhs_terms, rhs_terms)
    {
        return Some(logical_and(
            rebuild_and_chain(common_prefix),
            logical_or(rebuild_and_chain(lhs_prefix), rebuild_and_chain(rhs_prefix)),
        ));
    }

    if let Some((lhs_suffix, rhs_suffix, common_suffix)) = split_common_suffix(lhs_terms, rhs_terms)
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
