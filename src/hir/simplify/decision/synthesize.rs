//! 这个文件负责为“纯、稳定”的 `Decision` 提供值表达式综合。
//!
//! 前面的 `collapse_value_decision_expr` 只覆盖一批很直接的局部形状；一旦共享 DAG
//! 需要稍微跨一层做组合，它就会保守失败，然后被末端物化成嵌套 `if`。这对正确性
//! 没问题，但会把本来能够自然保留成短路表达式的 case 也压平。这里补的是一条确定性的
//! 结构性路径：
//! 1. 只接受无副作用、表达式求值顺序稳定的 decision；
//! 2. 沿 DAG 自顶向下提取每个节点的单一最佳表达式候选；
//! 3. 只在少量固定模板里做选择，而不是枚举表达式空间；
//! 4. 用抽象值解释器验证候选是否与原 decision 等价。

use std::collections::{BTreeMap, BTreeSet};

mod cost;

use crate::hir::common::{
    HirBinaryOpKind, HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirExpr,
    HirLogicalExpr, HirUnaryExpr, HirUnaryOpKind, LocalId, ParamId, TempId, UpvalueId,
};

use super::{logical_and, logical_or};
use cost::is_truthy;

const MAX_SYNTH_REFS: usize = 4;
const EXTRA_TRUTHY_SYMBOLS: usize = 2;
pub(super) fn synthesize_value_decision_expr(decision: &HirDecisionExpr) -> Option<HirExpr> {
    if !decision_is_synth_safe(decision) {
        return None;
    }

    let refs = collect_refs_from_decision(decision);
    if refs.len() > MAX_SYNTH_REFS {
        return None;
    }

    let context = SynthesisContext::new(decision, refs)?;
    let mut memo = BTreeMap::new();
    synthesize_value_node_expr(&context, decision.entry, &mut memo)
}

pub(super) fn expr_cost(expr: &HirExpr) -> usize {
    cost::expr_cost(expr)
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum RefKey {
    Param(ParamId),
    Local(LocalId),
    Upvalue(UpvalueId),
    Temp(TempId),
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AbstractValue {
    Nil,
    False,
    True,
    Integer(i64),
    Number(u64),
    String(String),
    TruthySymbol(u8),
}

#[derive(Clone)]
struct SynthesisContext<'a> {
    decision: &'a HirDecisionExpr,
    ref_positions: BTreeMap<RefKey, usize>,
    environments: Vec<Vec<AbstractValue>>,
}

impl<'a> SynthesisContext<'a> {
    fn new(decision: &'a HirDecisionExpr, refs: Vec<RefKey>) -> Option<Self> {
        let ref_positions = refs
            .iter()
            .enumerate()
            .map(|(index, key)| (*key, index))
            .collect::<BTreeMap<_, _>>();
        let domain = build_domain(decision);
        let environments = enumerate_environments(refs.len(), &domain)?;
        Some(Self {
            decision,
            ref_positions,
            environments,
        })
    }

    fn eval_node(
        &self,
        node_ref: HirDecisionNodeRef,
        env: &[AbstractValue],
    ) -> Option<AbstractValue> {
        let node = self.decision.nodes.get(node_ref.index())?;
        let test = self.eval_expr(&node.test, env)?;
        let branch = if is_truthy(&test) {
            &node.truthy
        } else {
            &node.falsy
        };
        self.eval_target(branch, &test, env)
    }

    fn eval_target(
        &self,
        target: &HirDecisionTarget,
        current: &AbstractValue,
        env: &[AbstractValue],
    ) -> Option<AbstractValue> {
        match target {
            HirDecisionTarget::Node(next_ref) => self.eval_node(*next_ref, env),
            HirDecisionTarget::CurrentValue => Some(current.clone()),
            HirDecisionTarget::Expr(expr) => self.eval_expr(expr, env),
        }
    }

    fn eval_expr(&self, expr: &HirExpr, env: &[AbstractValue]) -> Option<AbstractValue> {
        eval_pure_expr(expr, env, &self.ref_positions)
    }
}

fn eval_pure_expr(
    expr: &HirExpr,
    env: &[AbstractValue],
    ref_positions: &BTreeMap<RefKey, usize>,
) -> Option<AbstractValue> {
    match expr {
        HirExpr::Nil => Some(AbstractValue::Nil),
        HirExpr::Boolean(false) => Some(AbstractValue::False),
        HirExpr::Boolean(true) => Some(AbstractValue::True),
        HirExpr::Integer(value) => Some(AbstractValue::Integer(*value)),
        HirExpr::Number(value) => Some(AbstractValue::Number(value.to_bits())),
        HirExpr::String(value) => Some(AbstractValue::String(value.clone())),
        HirExpr::ParamRef(param) => env
            .get(*ref_positions.get(&RefKey::Param(*param))?)
            .cloned(),
        HirExpr::LocalRef(local) => env
            .get(*ref_positions.get(&RefKey::Local(*local))?)
            .cloned(),
        HirExpr::UpvalueRef(upvalue) => env
            .get(*ref_positions.get(&RefKey::Upvalue(*upvalue))?)
            .cloned(),
        HirExpr::TempRef(temp) => env.get(*ref_positions.get(&RefKey::Temp(*temp))?).cloned(),
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            let value = eval_pure_expr(&unary.expr, env, ref_positions)?;
            Some(if is_truthy(&value) {
                AbstractValue::False
            } else {
                AbstractValue::True
            })
        }
        HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Eq => {
            let lhs = eval_pure_expr(&binary.lhs, env, ref_positions)?;
            let rhs = eval_pure_expr(&binary.rhs, env, ref_positions)?;
            Some(if lhs == rhs {
                AbstractValue::True
            } else {
                AbstractValue::False
            })
        }
        HirExpr::LogicalAnd(logical) => {
            let lhs = eval_pure_expr(&logical.lhs, env, ref_positions)?;
            if is_truthy(&lhs) {
                eval_pure_expr(&logical.rhs, env, ref_positions)
            } else {
                Some(lhs)
            }
        }
        HirExpr::LogicalOr(logical) => {
            let lhs = eval_pure_expr(&logical.lhs, env, ref_positions)?;
            if is_truthy(&lhs) {
                Some(lhs)
            } else {
                eval_pure_expr(&logical.rhs, env, ref_positions)
            }
        }
        HirExpr::Decision(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => None,
    }
}

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
    domain.extend((0..EXTRA_TRUTHY_SYMBOLS).map(|index| AbstractValue::TruthySymbol(index as u8)));
    let environments = enumerate_environments(refs.len(), &domain)?;
    let current_cost = expr_cost(&current);

    candidates
        .into_iter()
        .map(normalize_candidate_expr)
        .filter(|candidate| {
            validate_pure_expr_equivalence(expr, candidate, &environments, &ref_positions)
        })
        .filter(|candidate| expr_cost(candidate) < current_cost)
        .min_by_key(expr_cost)
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
    domain.extend((0..EXTRA_TRUTHY_SYMBOLS).map(|index| AbstractValue::TruthySymbol(index as u8)));
    let environments = enumerate_environments(refs.len(), &domain)?;
    let mut best = current.clone();
    let mut visited = vec![current.clone()];
    let mut queue = vec![current.clone()];
    if let Some(structured) = readable_structured_candidate(&current, &environments, &ref_positions) {
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
        if super::expr_truthiness(fallback) != Some(false) {
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
        if super::expr_truthiness(fallback) != Some(false) {
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
            if let Some(existing) = nodes.iter().find(|node| {
                node.test == *expr && node.truthy == truthy && node.falsy == falsy
            }) {
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

fn validate_pure_expr_equivalence(
    lhs: &HirExpr,
    rhs: &HirExpr,
    environments: &[Vec<AbstractValue>],
    ref_positions: &BTreeMap<RefKey, usize>,
) -> bool {
    environments.iter().all(|env| {
        eval_pure_expr(lhs, env, ref_positions) == eval_pure_expr(rhs, env, ref_positions)
    })
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

fn flatten_or_chain(expr: &HirExpr) -> Vec<&HirExpr> {
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

#[derive(Clone, PartialEq)]
enum SynthTarget {
    CurrentValue,
    Expr(HirExpr),
}

fn synthesize_value_node_expr(
    context: &SynthesisContext<'_>,
    node_ref: HirDecisionNodeRef,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
) -> Option<HirExpr> {
    if let Some(cached) = memo.get(&node_ref) {
        return Some(cached.clone());
    }

    let node = &context.decision.nodes[node_ref.index()];
    let truthy = synthesize_value_target(context, &node.truthy, memo)?;
    let falsy = synthesize_value_target(context, &node.falsy, memo)?;
    let expr = choose_best_structured_candidate(context, node_ref, &node.test, &truthy, &falsy)?;
    memo.insert(node_ref, expr.clone());
    Some(expr)
}

fn synthesize_value_target(
    context: &SynthesisContext<'_>,
    target: &HirDecisionTarget,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
) -> Option<SynthTarget> {
    match target {
        HirDecisionTarget::Node(next_ref) => Some(SynthTarget::Expr(synthesize_value_node_expr(
            context, *next_ref, memo,
        )?)),
        HirDecisionTarget::CurrentValue => Some(SynthTarget::CurrentValue),
        HirDecisionTarget::Expr(expr) if expr_is_synth_safe(expr) => {
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
) -> Option<HirExpr> {
    structured_candidates(subject, truthy, falsy)
        .into_iter()
        .map(normalize_candidate_expr)
        .filter(|candidate| validate_candidate_for_node(context, node_ref, candidate))
        .min_by_key(expr_cost)
}

fn structured_candidates(
    subject: &HirExpr,
    truthy: &SynthTarget,
    falsy: &SynthTarget,
) -> Vec<HirExpr> {
    let mut candidates = Vec::new();

    if let Some(expr) = super::combine_value_expr(
        subject.clone(),
        target_as_collapsed(truthy),
        target_as_collapsed(falsy),
    ) {
        candidates.push(expr);
    }

    let truthy_expr = target_as_expr(subject, truthy);
    let falsy_expr = target_as_expr(subject, falsy);
    let not_subject = super::negate_expr(subject.clone());

    candidates.push(super::logical_or(
        super::logical_and(subject.clone(), truthy_expr.clone()),
        falsy_expr.clone(),
    ));
    candidates.push(super::logical_or(
        super::logical_and(subject.clone(), truthy_expr.clone()),
        super::logical_and(super::negate_expr(subject.clone()), falsy_expr.clone()),
    ));
    candidates.push(super::logical_or(
        super::logical_and(not_subject.clone(), falsy_expr.clone()),
        truthy_expr.clone(),
    ));
    candidates.push(super::logical_or(
        super::logical_and(not_subject.clone(), falsy_expr.clone()),
        super::logical_and(subject.clone(), truthy_expr.clone()),
    ));
    candidates.push(super::logical_and(
        super::logical_or(subject.clone(), falsy_expr.clone()),
        truthy_expr.clone(),
    ));
    candidates.push(super::logical_and(
        super::logical_or(not_subject, truthy_expr),
        falsy_expr,
    ));
    candidates
}

fn target_as_collapsed(target: &SynthTarget) -> super::CollapsedValueTarget {
    match target {
        SynthTarget::CurrentValue => super::CollapsedValueTarget::CurrentValue,
        SynthTarget::Expr(expr) => super::CollapsedValueTarget::Expr(expr.clone()),
    }
}

fn target_as_expr(subject: &HirExpr, target: &SynthTarget) -> HirExpr {
    match target {
        SynthTarget::CurrentValue => subject.clone(),
        SynthTarget::Expr(expr) => expr.clone(),
    }
}

fn validate_candidate_for_node(
    context: &SynthesisContext<'_>,
    node_ref: HirDecisionNodeRef,
    candidate: &HirExpr,
) -> bool {
    context.environments.iter().all(|env| {
        let decision_value = context.eval_node(node_ref, env);
        let candidate_value = context.eval_expr(candidate, env);
        decision_value.is_some() && decision_value == candidate_value
    })
}

fn decision_is_synth_safe(decision: &HirDecisionExpr) -> bool {
    decision.nodes.iter().all(|node| {
        expr_is_synth_safe(&node.test)
            && target_is_synth_safe(&node.truthy)
            && target_is_synth_safe(&node.falsy)
    })
}

fn target_is_synth_safe(target: &HirDecisionTarget) -> bool {
    match target {
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => true,
        HirDecisionTarget::Expr(expr) => expr_is_synth_safe(expr),
    }
}

fn expr_is_synth_safe(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_) => true,
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => expr_is_synth_safe(&unary.expr),
        HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Eq => {
            expr_is_synth_safe(&binary.lhs) && expr_is_synth_safe(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_is_synth_safe(&logical.lhs) && expr_is_synth_safe(&logical.rhs)
        }
        HirExpr::Decision(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => false,
    }
}

fn collect_refs_from_decision(decision: &HirDecisionExpr) -> Vec<RefKey> {
    let mut refs = BTreeSet::new();
    for node in &decision.nodes {
        collect_refs_from_expr(&node.test, &mut refs);
        collect_refs_from_target(&node.truthy, &mut refs);
        collect_refs_from_target(&node.falsy, &mut refs);
    }
    refs.into_iter().collect()
}

fn collect_refs_from_target(target: &HirDecisionTarget, refs: &mut BTreeSet<RefKey>) {
    if let HirDecisionTarget::Expr(expr) = target {
        collect_refs_from_expr(expr, refs);
    }
}

fn collect_refs_from_expr(expr: &HirExpr, refs: &mut BTreeSet<RefKey>) {
    match expr {
        HirExpr::ParamRef(param) => {
            refs.insert(RefKey::Param(*param));
        }
        HirExpr::LocalRef(local) => {
            refs.insert(RefKey::Local(*local));
        }
        HirExpr::UpvalueRef(upvalue) => {
            refs.insert(RefKey::Upvalue(*upvalue));
        }
        HirExpr::TempRef(temp) => {
            refs.insert(RefKey::Temp(*temp));
        }
        HirExpr::Unary(unary) => collect_refs_from_expr(&unary.expr, refs),
        HirExpr::Binary(binary) => {
            collect_refs_from_expr(&binary.lhs, refs);
            collect_refs_from_expr(&binary.rhs, refs);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_refs_from_expr(&logical.lhs, refs);
            collect_refs_from_expr(&logical.rhs, refs);
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Decision(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => {}
    }
}

fn build_domain(decision: &HirDecisionExpr) -> Vec<AbstractValue> {
    let mut domain = vec![
        AbstractValue::Nil,
        AbstractValue::False,
        AbstractValue::True,
    ];
    let mut literals = BTreeSet::new();
    for node in &decision.nodes {
        collect_literals_from_expr(&node.test, &mut literals);
        collect_literals_from_target(&node.truthy, &mut literals);
        collect_literals_from_target(&node.falsy, &mut literals);
    }
    domain.extend(literals);
    domain.extend((0..EXTRA_TRUTHY_SYMBOLS).map(|index| AbstractValue::TruthySymbol(index as u8)));
    domain
}

fn collect_literals_from_target(
    target: &HirDecisionTarget,
    literals: &mut BTreeSet<AbstractValue>,
) {
    if let HirDecisionTarget::Expr(expr) = target {
        collect_literals_from_expr(expr, literals);
    }
}

fn collect_literals_from_expr(expr: &HirExpr, literals: &mut BTreeSet<AbstractValue>) {
    match expr {
        HirExpr::Integer(value) => {
            literals.insert(AbstractValue::Integer(*value));
        }
        HirExpr::Number(value) => {
            literals.insert(AbstractValue::Number(value.to_bits()));
        }
        HirExpr::String(value) => {
            literals.insert(AbstractValue::String(value.clone()));
        }
        HirExpr::Unary(unary) => collect_literals_from_expr(&unary.expr, literals),
        HirExpr::Binary(binary) => {
            collect_literals_from_expr(&binary.lhs, literals);
            collect_literals_from_expr(&binary.rhs, literals);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_literals_from_expr(&logical.lhs, literals);
            collect_literals_from_expr(&logical.rhs, literals);
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::Decision(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => {}
    }
}

fn enumerate_environments(
    ref_count: usize,
    domain: &[AbstractValue],
) -> Option<Vec<Vec<AbstractValue>>> {
    let total = domain.len().checked_pow(ref_count as u32)?;
    if total > 4096 {
        return None;
    }

    let mut envs = Vec::with_capacity(total);
    let mut current = Vec::with_capacity(ref_count);
    enumerate_envs_recursive(ref_count, domain, &mut current, &mut envs);
    Some(envs)
}

fn enumerate_envs_recursive(
    remaining: usize,
    domain: &[AbstractValue],
    current: &mut Vec<AbstractValue>,
    out: &mut Vec<Vec<AbstractValue>>,
) {
    if remaining == 0 {
        out.push(current.clone());
        return;
    }

    for value in domain {
        current.push(value.clone());
        enumerate_envs_recursive(remaining - 1, domain, current, out);
        current.pop();
    }
}

fn normalize_candidate_expr(expr: HirExpr) -> HirExpr {
    match expr {
        HirExpr::Unary(unary) => match unary.op {
            HirUnaryOpKind::Not => match normalize_candidate_expr(unary.expr) {
                HirExpr::Boolean(value) => HirExpr::Boolean(!value),
                inner => HirExpr::Unary(Box::new(HirUnaryExpr {
                    op: HirUnaryOpKind::Not,
                    expr: inner,
                })),
            },
            _ => HirExpr::Unary(Box::new(HirUnaryExpr {
                op: unary.op,
                expr: normalize_candidate_expr(unary.expr),
            })),
        },
        HirExpr::LogicalAnd(logical) => {
            let lhs = normalize_candidate_expr(logical.lhs);
            let rhs = normalize_candidate_expr(logical.rhs);
            if let Some(lhs_truthy) = super::expr_truthiness(&lhs) {
                if lhs_truthy { rhs } else { lhs }
            } else if super::expr_is_boolean_valued(&lhs) && matches!(rhs, HirExpr::Boolean(true)) {
                lhs
            } else if super::expr_is_boolean_valued(&lhs) && matches!(rhs, HirExpr::Boolean(false))
            {
                HirExpr::Boolean(false)
            } else {
                let expr = HirExpr::LogicalAnd(Box::new(HirLogicalExpr { lhs, rhs }));
                super::simplify_lua_logical_shape(&expr).unwrap_or(expr)
            }
        }
        HirExpr::LogicalOr(logical) => {
            let lhs = normalize_candidate_expr(logical.lhs);
            let rhs = normalize_candidate_expr(logical.rhs);
            if let Some(lhs_truthy) = super::expr_truthiness(&lhs) {
                if lhs_truthy { lhs } else { rhs }
            } else if super::expr_is_boolean_valued(&lhs) && matches!(rhs, HirExpr::Boolean(false))
            {
                lhs
            } else if super::expr_is_boolean_valued(&lhs) && matches!(rhs, HirExpr::Boolean(true)) {
                HirExpr::Boolean(true)
            } else {
                let expr = HirExpr::LogicalOr(Box::new(HirLogicalExpr { lhs, rhs }));
                super::simplify_lua_logical_shape(&expr).unwrap_or(expr)
            }
        }
        HirExpr::Binary(binary) => HirExpr::Binary(Box::new(crate::hir::common::HirBinaryExpr {
            op: binary.op,
            lhs: normalize_candidate_expr(binary.lhs),
            rhs: normalize_candidate_expr(binary.rhs),
        })),
        other => other,
    }
}
