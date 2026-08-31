//! 这个子模块负责给 decision synthesis 提供“更像源码”的候选改写。
//!
//! 它依赖 `domain/safety/value` 已经确认的等价性和安全性，只在等价前提下挑选更自然的
//! 布尔表达式，不会越权放松语义约束。
//! 例如：`not (a == nil)` 可能在这里被整理成更顺的逻辑表达式。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::HirExpr;
use crate::hir::expr_safety::HirExprSafety;

use super::super::{logical_and, logical_or};
use super::domain::{
    AbstractValue, collect_literals_from_expr, collect_refs_from_expr, enumerate_environments,
    validate_pure_expr_equivalence,
};
use super::safety::expr_is_synth_safe;
use super::{MAX_SYNTH_REFS, normalize_candidate_expr};

const MAX_NATURALIZE_OR_TERMS: usize = 16;
const MAX_NATURALIZE_NESTED_CANDIDATES: usize = 128;
const MAX_NATURALIZE_ROUNDS: usize = 8;

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

    let mut current = normalize_candidate_expr(expr.clone(), safety);
    let mut refs = BTreeSet::new();
    collect_refs_from_expr(&current, &mut refs);
    let refs = refs.into_iter().collect::<Vec<_>>();
    // 候选拒绝[ResourceLimit]：穷举域目前只接纳 4 个独立引用；后续应改用符号等价或依赖分区。
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
    // 候选拒绝[ResourceLimit]：抽象环境笛卡尔积超过 4096 时停止 naturalize；后续应避免完整枚举。
    let environments = enumerate_environments(refs.len(), &domain)?;
    let mut changed = false;
    // 候选搜索裁剪[ResourceLimit]：最多 8 轮单调降成本改写；更深机会交给更强的规范形算法。
    for _ in 0..MAX_NATURALIZE_ROUNDS {
        let current_cost = super::expr_cost(&current);
        let Some(next) = pure_logical_rewrite_candidates(&current)
            .into_iter()
            .map(|candidate| normalize_candidate_expr(candidate, safety))
            // 候选拒绝[ProofIncomplete]：有限抽象域当前只能筛掉已见反例；错误路径与跨数值表示尚未精确建模，不能据此宣称完整等价证明。
            .filter(|candidate| {
                validate_pure_expr_equivalence(
                    expr,
                    candidate,
                    &environments,
                    &ref_positions,
                    safety,
                )
            })
            // 候选拒绝[PolicyBoundary]：等价但不严格降低可读性成本的形状不提交。
            .filter(|candidate| super::expr_cost(candidate) < current_cost)
            .min_by_key(super::expr_cost)
        else {
            break;
        };
        current = next;
        changed = true;
    }

    changed.then_some(current)
}

/// Return one-step rewrites at the root and one logical child.
///
/// The fixed-point loop above revisits the rebuilt expression, so deeper opportunities are still
/// reached without enumerating all expression paths at once.  Rebuilding one child at a time is
/// bounded and, because the caller validates every result and requires a lower cost, cannot relax
/// the semantic or convergence contract.
fn pure_logical_rewrite_candidates(expr: &HirExpr) -> Vec<HirExpr> {
    let mut candidates = direct_pure_logical_rewrite_candidates(expr);
    let (lhs, rhs, is_and) = match expr {
        HirExpr::LogicalAnd(logical) => (&logical.lhs, &logical.rhs, true),
        HirExpr::LogicalOr(logical) => (&logical.lhs, &logical.rhs, false),
        _ => return candidates,
    };

    for (left, child, sibling) in [(true, lhs, rhs), (false, rhs, lhs)] {
        for replacement in direct_pure_logical_rewrite_candidates(child) {
            let rebuilt = if is_and {
                if left {
                    logical_and(replacement, sibling.clone())
                } else {
                    logical_and(sibling.clone(), replacement)
                }
            } else if left {
                logical_or(replacement, sibling.clone())
            } else {
                logical_or(sibling.clone(), replacement)
            };
            if !candidates.contains(&rebuilt) {
                candidates.push(rebuilt);
            }
            if candidates.len() >= MAX_NATURALIZE_NESTED_CANDIDATES {
                // 候选搜索裁剪[ResourceLimit]：单轮最多保留 128 个一层子树候选；后续应使用去重工作队列。
                return candidates;
            }
        }
    }

    // 候选搜索裁剪[ResourceLimit]：root 直接生成的候选同样最多保留 128 个；后续应使用增量最小成本队列。
    candidates.truncate(MAX_NATURALIZE_NESTED_CANDIDATES);
    candidates
}

fn direct_pure_logical_rewrite_candidates(expr: &HirExpr) -> Vec<HirExpr> {
    let mut candidates = Vec::new();
    match expr {
        HirExpr::LogicalAnd(logical) => {
            candidates.extend(factor_or_shared_and_tail(&logical.lhs, &logical.rhs));
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
            candidates.extend(drop_shared_or_fallback(&logical.lhs, &logical.rhs));
            candidates.extend(factor_or_of_ands(&logical.lhs, &logical.rhs));
            candidates.extend(factor_or_chain_of_ands(expr));
        }
        _ => {}
    }
    candidates
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

fn factor_or_chain_of_ands(expr: &HirExpr) -> Vec<HirExpr> {
    let terms = flatten_or_chain(expr);
    // 候选搜索裁剪[ResourceLimit]：超过 16 项的 or 链不做两两因式分解，避免二次候选爆炸。
    if !(3..=MAX_NATURALIZE_OR_TERMS).contains(&terms.len()) {
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
