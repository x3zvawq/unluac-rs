//! 这个文件承载 HIR `Decision` DAG 的通用归一化。
//!
//! 既然我们已经决定让共享短路子图先以 DAG 的形式保留在 HIR 里，那么后处理也应该
//! 围绕 DAG 自身做“图级别”的收敛，而不是继续往外堆局部特判。这里专门实现几类
//! 与具体 case 无关的通用规则：
//! 1. 常量 truthiness 驱动的分支裁剪；
//! 2. `then/else` 指向同一结果时的节点消除；
//! 3. 根节点和内部节点裁剪后留下的不可达节点清理。

use std::collections::{BTreeMap, BTreeSet, VecDeque};

mod eliminate;
mod eliminate_materialize;
mod eliminate_state;
mod helpers;
mod synthesize;

use super::expr_facts::{expr_is_boolean_valued, expr_truthiness};
use super::walk::{ExprRewritePass, rewrite_proto_exprs};
use crate::hir::common::{
    HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirExpr, HirProto,
};
use crate::hir::expr_safety::{expr_is_discard_safe, expr_is_repeatable};
use helpers::{logical_and, logical_or};

/// 对单个 proto 递归执行 decision DAG 归一化。
pub(super) fn simplify_decision_exprs_in_proto(proto: &mut HirProto) -> bool {
    rewrite_proto_exprs(proto, &mut DecisionExprPass)
}

/// 把前面保留在 HIR 内部的 `Decision` 彻底消掉。
///
/// `Decision` 只应该是 HIR 内部为了保住共享短路子图而暂存的过渡节点；一旦进入最终
/// HIR 输出，它就应该已经被重新线性化成普通 `if/local/assign` 或纯表达式，避免把
/// 共享图的语义恢复继续后移给 AST。
pub(crate) use eliminate::eliminate_remaining_decisions_in_proto;
pub(crate) use synthesize::naturalize_pure_logical_expr;

struct DecisionExprPass;

impl ExprRewritePass for DecisionExprPass {
    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        let mut decision_replacement = None;
        let mut changed = false;
        if let HirExpr::Decision(decision) = expr {
            let (decision_changed, replacement) = simplify_decision_expr(decision);
            decision_replacement = replacement;
            changed |= decision_changed;
        }

        if let Some(replacement) = decision_replacement {
            *expr = replacement;
            changed = true;
        }

        changed
    }

    fn rewrite_condition_expr(&mut self, expr: &mut HirExpr) -> bool {
        let mut changed = false;
        if let HirExpr::Decision(decision) = expr
            && !decision_has_cycles(decision)
            && let Some(replacement) = collapse_condition_decision_expr(decision)
        {
            *expr = replacement;
            changed = true;
        }
        changed
    }
}

fn simplify_decision_expr(decision: &mut HirDecisionExpr) -> (bool, Option<HirExpr>) {
    let Some(reduced) = reduce_decision_expr(decision) else {
        return (false, None);
    };

    match reduced {
        ReducedDecision::Expr(expr) => (true, Some(expr)),
        ReducedDecision::Decision(reduced_decision) => {
            *decision = reduced_decision;
            (true, None)
        }
    }
}

enum ReducedDecision {
    Expr(HirExpr),
    Decision(HirDecisionExpr),
}

#[derive(Clone, PartialEq)]
pub(super) enum ResolvedDecisionTarget {
    Node(HirDecisionNodeRef),
    Expr(HirExpr),
}

fn reduce_decision_expr(decision: &HirDecisionExpr) -> Option<ReducedDecision> {
    // 循环 DAG 目前只允许“原样保留为 Decision”，不能继续走 value-collapse /
    // known-test specialize 这条树化路径。否则会把同一条环上的节点反复递归展开，
    // 最后在 simplify 阶段自己把栈打穿。
    if decision_has_cycles(decision) {
        return None;
    }

    let mut nodes = decision.nodes.clone();
    let mut replacements = vec![None; nodes.len()];
    let mut changed = false;

    for index in (0..nodes.len()).rev() {
        let node_ref = HirDecisionNodeRef(index);
        let mut node = nodes[index].clone();
        let mut node_changed = false;

        if let HirDecisionTarget::Node(child_ref) = &node.truthy
            && nodes
                .get(child_ref.index())
                .is_some_and(|child| child.test == node.test)
            && expr_is_repeatable(&node.test)
        {
            node.truthy = resolve_child_branch(&nodes, &replacements, *child_ref, true);
            node_changed = true;
        } else {
            let (truthy, resolved) = resolve_target_for_parent(&replacements, &node.truthy);
            node.truthy = truthy;
            node_changed |= resolved;
        }

        if let HirDecisionTarget::Node(child_ref) = &node.falsy
            && nodes
                .get(child_ref.index())
                .is_some_and(|child| child.test == node.test)
            && expr_is_repeatable(&node.test)
        {
            node.falsy = resolve_child_branch(&nodes, &replacements, *child_ref, false);
            node_changed = true;
        } else {
            let (falsy, resolved) = resolve_target_for_parent(&replacements, &node.falsy);
            node.falsy = falsy;
            node_changed |= resolved;
        }

        if let Some(constant_truthy) = expr_truthiness(&node.test)
            && expr_is_discard_safe(&node.test)
        {
            replacements[node_ref.index()] = Some(resolve_target_in_node_context(
                &replacements,
                &node,
                if constant_truthy {
                    &node.truthy
                } else {
                    &node.falsy
                },
            ));
            changed = true;
            continue;
        }

        if node.truthy == node.falsy && expr_is_discard_safe(&node.test) {
            replacements[node_ref.index()] = Some(resolve_target_in_node_context(
                &replacements,
                &node,
                &node.truthy,
            ));
            changed = true;
            continue;
        }

        changed |= node_changed;
        nodes[index] = node;
    }

    let root = if let Some(Some(replacement)) = replacements.get(decision.entry.index()) {
        replacement.clone()
    } else {
        ResolvedDecisionTarget::Node(decision.entry)
    };

    match root {
        ResolvedDecisionTarget::Expr(expr) => Some(ReducedDecision::Expr(expr)),
        ResolvedDecisionTarget::Node(entry) => {
            let (rebuilt, topology_changed) = rebuild_decision(entry, &nodes);
            changed |= topology_changed;
            if let Some(expr) = collapse_value_decision_expr(&rebuilt) {
                return Some(ReducedDecision::Expr(expr));
            }
            if changed {
                Some(ReducedDecision::Decision(rebuilt))
            } else {
                None
            }
        }
    }
}

fn resolve_target_for_parent(
    replacements: &[Option<ResolvedDecisionTarget>],
    target: &HirDecisionTarget,
) -> (HirDecisionTarget, bool) {
    match target {
        HirDecisionTarget::Node(node_ref) => {
            if let Some(Some(replacement)) = replacements.get(node_ref.index()) {
                (replacement_as_target(replacement), true)
            } else {
                (HirDecisionTarget::Node(*node_ref), false)
            }
        }
        HirDecisionTarget::CurrentValue => (HirDecisionTarget::CurrentValue, false),
        HirDecisionTarget::Expr(expr) => (HirDecisionTarget::Expr(expr.clone()), false),
    }
}

fn resolve_target_in_node_context(
    replacements: &[Option<ResolvedDecisionTarget>],
    node: &HirDecisionNode,
    target: &HirDecisionTarget,
) -> ResolvedDecisionTarget {
    match target {
        HirDecisionTarget::Node(node_ref) => replacements
            .get(node_ref.index())
            .and_then(|r| r.clone())
            .unwrap_or(ResolvedDecisionTarget::Node(*node_ref)),
        HirDecisionTarget::CurrentValue => ResolvedDecisionTarget::Expr(node.test.clone()),
        HirDecisionTarget::Expr(expr) => ResolvedDecisionTarget::Expr(expr.clone()),
    }
}

fn resolve_child_branch(
    nodes: &[HirDecisionNode],
    replacements: &[Option<ResolvedDecisionTarget>],
    child_ref: HirDecisionNodeRef,
    truthy: bool,
) -> HirDecisionTarget {
    let Some(child) = nodes.get(child_ref.index()) else {
        return HirDecisionTarget::Node(child_ref);
    };
    let branch = if truthy { &child.truthy } else { &child.falsy };
    replacement_as_target(&resolve_target_in_node_context(replacements, child, branch))
}

pub(super) fn replacement_as_target(target: &ResolvedDecisionTarget) -> HirDecisionTarget {
    match target {
        ResolvedDecisionTarget::Node(node_ref) => HirDecisionTarget::Node(*node_ref),
        ResolvedDecisionTarget::Expr(expr) => HirDecisionTarget::Expr(expr.clone()),
    }
}

fn rebuild_decision(
    entry: HirDecisionNodeRef,
    nodes: &[HirDecisionNode],
) -> (HirDecisionExpr, bool) {
    let mut reachable = Vec::new();
    let mut visited = BTreeSet::new();
    let mut worklist = VecDeque::from([entry]);

    while let Some(node_ref) = worklist.pop_front() {
        if !visited.insert(node_ref) {
            continue;
        }
        let Some(node) = nodes.get(node_ref.index()) else {
            continue;
        };
        reachable.push(node_ref);
        for target in [&node.truthy, &node.falsy] {
            if let HirDecisionTarget::Node(next_ref) = target {
                worklist.push_back(*next_ref);
            }
        }
    }

    let topology_changed = reachable.len() != nodes.len()
        || reachable
            .iter()
            .enumerate()
            .any(|(index, old_ref)| old_ref.index() != index);
    let remap = reachable
        .iter()
        .enumerate()
        .map(|(index, node_ref)| (*node_ref, HirDecisionNodeRef(index)))
        .collect::<BTreeMap<_, _>>();

    let rebuilt_nodes = reachable
        .into_iter()
        .filter_map(|old_ref| {
            let old = nodes.get(old_ref.index())?;
            Some(HirDecisionNode {
                id: remap[&old_ref],
                test: old.test.clone(),
                truthy: remap_target(&old.truthy, &remap),
                falsy: remap_target(&old.falsy, &remap),
            })
        })
        .collect::<Vec<_>>();

    (
        HirDecisionExpr {
            entry: remap[&entry],
            nodes: rebuilt_nodes,
        },
        topology_changed,
    )
}

fn remap_target(
    target: &HirDecisionTarget,
    remap: &BTreeMap<HirDecisionNodeRef, HirDecisionNodeRef>,
) -> HirDecisionTarget {
    match target {
        HirDecisionTarget::Node(node_ref) => HirDecisionTarget::Node(remap[node_ref]),
        HirDecisionTarget::CurrentValue => HirDecisionTarget::CurrentValue,
        HirDecisionTarget::Expr(expr) => HirDecisionTarget::Expr(expr.clone()),
    }
}

pub(in crate::hir) fn collapse_value_decision_expr(decision: &HirDecisionExpr) -> Option<HirExpr> {
    if decision_has_cycles(decision) {
        return None;
    }

    if decision_has_shared_nodes(decision) {
        synthesize::synthesize_value_decision_expr(decision).or_else(|| {
            let mut memo = BTreeMap::new();
            collapse_value_node(decision, decision.entry, &mut memo)
        })
    } else {
        if let Some(expr) = collapse_linear_value_chain(decision) {
            return Some(expr);
        }
        let mut memo = BTreeMap::new();
        collapse_value_node(decision, decision.entry, &mut memo)
            .or_else(|| synthesize::synthesize_value_decision_expr(decision))
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum LinearValueOp {
    And,
    Or,
}

fn collapse_linear_value_chain(decision: &HirDecisionExpr) -> Option<HirExpr> {
    let mut steps = Vec::new();
    let mut current = decision.entry;
    let tail = loop {
        let node = decision.nodes.get(current.index())?;
        match (&node.truthy, &node.falsy) {
            (HirDecisionTarget::CurrentValue, HirDecisionTarget::Node(next)) => {
                steps.push((LinearValueOp::Or, node.test.clone()));
                current = *next;
            }
            (HirDecisionTarget::Node(next), HirDecisionTarget::CurrentValue) => {
                steps.push((LinearValueOp::And, node.test.clone()));
                current = *next;
            }
            (HirDecisionTarget::CurrentValue, HirDecisionTarget::Expr(expr)) => {
                steps.push((LinearValueOp::Or, node.test.clone()));
                break expr.clone();
            }
            (HirDecisionTarget::Expr(expr), HirDecisionTarget::CurrentValue) => {
                steps.push((LinearValueOp::And, node.test.clone()));
                break expr.clone();
            }
            (HirDecisionTarget::CurrentValue, HirDecisionTarget::CurrentValue) => {
                break node.test.clone();
            }
            _ => return None,
        }
    };

    let mut tail = tail;
    let mut end = steps.len();
    while end > 0 {
        let op = steps[end - 1].0;
        let start = steps[..end]
            .iter()
            .rposition(|(candidate, _)| *candidate != op)
            .map_or(0, |index| index + 1);
        let mut operands = steps[start..end]
            .iter_mut()
            .map(|(_, expr)| std::mem::replace(expr, HirExpr::Boolean(false)))
            .collect::<Vec<_>>();
        operands.push(tail);
        tail = balanced_logical_expr(op, operands)?;
        end = start;
    }
    Some(tail)
}

fn balanced_logical_expr(op: LinearValueOp, mut terms: Vec<HirExpr>) -> Option<HirExpr> {
    while terms.len() > 1 {
        let mut next = Vec::with_capacity(terms.len().div_ceil(2));
        let mut current = std::mem::take(&mut terms).into_iter();
        while let Some(lhs) = current.next() {
            next.push(match current.next() {
                Some(rhs) => match op {
                    LinearValueOp::And => logical_and(lhs, rhs),
                    LinearValueOp::Or => logical_or(lhs, rhs),
                },
                None => lhs,
            });
        }
        terms = next;
    }
    terms.pop()
}

fn collapse_value_node(
    decision: &HirDecisionExpr,
    node_ref: HirDecisionNodeRef,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
) -> Option<HirExpr> {
    if let Some(expr) = memo.get(&node_ref) {
        return Some(expr.clone());
    }

    if let Some(expr) = collapse_shared_falsy_chain(decision, node_ref, memo) {
        memo.insert(node_ref, expr.clone());
        return Some(expr);
    }

    let node = decision.nodes.get(node_ref.index())?;
    let truthy = collapse_value_target(decision, &node.truthy, memo)?;
    let falsy = collapse_value_target(decision, &node.falsy, memo)?;
    let expr = combine_value_expr(node.test.clone(), truthy, falsy)?;
    memo.insert(node_ref, expr.clone());
    Some(expr)
}

fn collapse_shared_falsy_chain(
    decision: &HirDecisionExpr,
    node_ref: HirDecisionNodeRef,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
) -> Option<HirExpr> {
    let mut next_ref = node_ref;
    let mut terms = Vec::new();
    let tail = loop {
        let Some((term, fallback)) = collapse_shared_falsy_term(decision, next_ref) else {
            if terms.is_empty() {
                return None;
            }
            break collapse_value_node(decision, next_ref, memo)?;
        };
        terms.push(term);
        match fallback {
            HirDecisionTarget::Node(fallback_ref) => next_ref = fallback_ref,
            HirDecisionTarget::Expr(expr) => break expr,
            HirDecisionTarget::CurrentValue => return None,
        }
    };

    terms.into_iter().rev().try_fold(tail, |fallback, term| {
        combine_value_expr(
            term,
            CollapsedValueTarget::CurrentValue,
            CollapsedValueTarget::Expr(fallback),
        )
    })
}

fn collapse_shared_falsy_term(
    decision: &HirDecisionExpr,
    node_ref: HirDecisionNodeRef,
) -> Option<(HirExpr, HirDecisionTarget)> {
    let node = decision.nodes.get(node_ref.index())?;
    let fallback = match &node.falsy {
        HirDecisionTarget::Node(_) | HirDecisionTarget::Expr(_) => node.falsy.clone(),
        HirDecisionTarget::CurrentValue => return None,
    };
    let HirDecisionTarget::Node(mut child_ref) = node.truthy else {
        return None;
    };
    let mut guard = node.test.clone();

    loop {
        let child = decision.nodes.get(child_ref.index())?;
        if child.falsy != fallback {
            return None;
        }
        guard = logical_and(guard, child.test.clone());
        match &child.truthy {
            HirDecisionTarget::CurrentValue => return Some((guard, fallback)),
            HirDecisionTarget::Expr(expr) if expr == &child.test => {
                return Some((guard, fallback));
            }
            HirDecisionTarget::Node(next_ref) => child_ref = *next_ref,
            HirDecisionTarget::Expr(_) => return None,
        }
    }
}

#[derive(Clone)]
enum CollapsedValueTarget {
    CurrentValue,
    Expr(HirExpr),
}

fn collapse_value_target(
    decision: &HirDecisionExpr,
    target: &HirDecisionTarget,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
) -> Option<CollapsedValueTarget> {
    match target {
        HirDecisionTarget::Node(next_ref) => Some(CollapsedValueTarget::Expr(collapse_value_node(
            decision, *next_ref, memo,
        )?)),
        HirDecisionTarget::CurrentValue => Some(CollapsedValueTarget::CurrentValue),
        HirDecisionTarget::Expr(expr) => Some(CollapsedValueTarget::Expr(expr.clone())),
    }
}

fn combine_value_expr(
    subject: HirExpr,
    truthy: CollapsedValueTarget,
    falsy: CollapsedValueTarget,
) -> Option<HirExpr> {
    let truthy = normalize_collapsed_target(&subject, truthy);
    let falsy = normalize_collapsed_target(&subject, falsy);

    if expr_is_boolean_valued(&subject) {
        match (&truthy, &falsy) {
            (CollapsedValueTarget::Expr(lhs), CollapsedValueTarget::Expr(rhs))
                if is_true(lhs) && is_false(rhs) =>
            {
                return Some(subject);
            }
            (CollapsedValueTarget::Expr(lhs), CollapsedValueTarget::Expr(rhs))
                if is_false(lhs) && is_true(rhs) =>
            {
                return Some(subject.negate());
            }
            (CollapsedValueTarget::CurrentValue, CollapsedValueTarget::Expr(rhs))
                if is_false(rhs) =>
            {
                return Some(subject);
            }
            (CollapsedValueTarget::Expr(lhs), CollapsedValueTarget::CurrentValue)
                if is_true(lhs) =>
            {
                return Some(subject);
            }
            (CollapsedValueTarget::Expr(lhs), CollapsedValueTarget::Expr(rhs))
                if expr_is_boolean_valued(lhs) && is_false(rhs) =>
            {
                return Some(logical_and(subject, lhs.clone()));
            }
            (CollapsedValueTarget::Expr(lhs), CollapsedValueTarget::Expr(rhs))
                if is_true(lhs) && expr_is_boolean_valued(rhs) =>
            {
                return Some(logical_or(subject, rhs.clone()));
            }
            (CollapsedValueTarget::Expr(lhs), CollapsedValueTarget::Expr(rhs))
                if is_false(lhs) && expr_is_boolean_valued(rhs) =>
            {
                return Some(logical_and(subject.negate(), rhs.clone()));
            }
            (CollapsedValueTarget::Expr(lhs), CollapsedValueTarget::Expr(rhs))
                if expr_is_boolean_valued(lhs) && is_true(rhs) =>
            {
                return Some(logical_or(subject.negate(), lhs.clone()));
            }
            _ => {}
        }
    }

    match (truthy, falsy) {
        (CollapsedValueTarget::CurrentValue, CollapsedValueTarget::CurrentValue) => Some(subject),
        (CollapsedValueTarget::CurrentValue, CollapsedValueTarget::Expr(rhs)) => {
            Some(logical_or(subject, rhs))
        }
        (CollapsedValueTarget::Expr(lhs), CollapsedValueTarget::CurrentValue) => {
            Some(logical_and(subject, lhs))
        }
        (CollapsedValueTarget::Expr(lhs), CollapsedValueTarget::Expr(rhs)) => {
            if expr_truthiness(&lhs) == Some(true) {
                Some(logical_or(logical_and(subject, lhs), rhs))
            } else if expr_truthiness(&rhs) == Some(true) {
                Some(logical_or(logical_and(subject.negate(), rhs), lhs))
            } else if expr_is_repeatable(&subject)
                && expr_is_repeatable(&lhs)
                && expr_truthiness_assuming(&lhs, &subject, true) == Some(true)
            {
                // 分支值可能只在当前 guard 成立时恒真。把这种路径约束留在
                // Decision 外就会误判成普通三元式并物化为 if；guard 与被跨越的
                // 分支都可重复时，原顺序的 `subject and lhs or rhs` 才不会因求值中
                // 改写 guard 而误入 fallback。
                Some(logical_or(logical_and(subject, lhs), rhs))
            } else if expr_is_repeatable(&subject)
                && expr_is_repeatable(&rhs)
                && expr_truthiness_assuming(&rhs, &subject, false) == Some(true)
            {
                Some(logical_or(logical_and(subject.negate(), rhs), lhs))
            } else {
                None
            }
        }
    }
}

fn expr_truthiness_assuming(
    expr: &HirExpr,
    subject: &HirExpr,
    subject_truthy: bool,
) -> Option<bool> {
    if expr == subject {
        return Some(subject_truthy);
    }
    match expr {
        HirExpr::Unary(unary) if unary.op == crate::hir::HirUnaryOpKind::Not => {
            expr_truthiness_assuming(&unary.expr, subject, subject_truthy).map(|value| !value)
        }
        HirExpr::LogicalOr(logical) => {
            let lhs = expr_truthiness_assuming(&logical.lhs, subject, subject_truthy);
            let rhs = expr_truthiness_assuming(&logical.rhs, subject, subject_truthy);
            match (lhs, rhs) {
                (Some(true), _) | (_, Some(true)) => Some(true),
                (Some(false), rhs) => rhs,
                _ => None,
            }
        }
        HirExpr::LogicalAnd(logical) => {
            let lhs = expr_truthiness_assuming(&logical.lhs, subject, subject_truthy);
            let rhs = expr_truthiness_assuming(&logical.rhs, subject, subject_truthy);
            match (lhs, rhs) {
                (Some(false), _) | (_, Some(false)) => Some(false),
                (Some(true), rhs) => rhs,
                _ => None,
            }
        }
        _ => expr_truthiness(expr),
    }
}

fn normalize_collapsed_target(
    subject: &HirExpr,
    target: CollapsedValueTarget,
) -> CollapsedValueTarget {
    match target {
        CollapsedValueTarget::Expr(expr) if &expr == subject && expr_is_repeatable(subject) => {
            CollapsedValueTarget::CurrentValue
        }
        other => other,
    }
}

pub(in crate::hir) fn collapse_condition_decision_expr(
    decision: &HirDecisionExpr,
) -> Option<HirExpr> {
    if decision_has_cycles(decision) {
        return None;
    }

    let mut memo = BTreeMap::new();
    collapse_condition_node(decision, decision.entry, &mut memo)
}

fn collapse_condition_node(
    decision: &HirDecisionExpr,
    node_ref: HirDecisionNodeRef,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
) -> Option<HirExpr> {
    if let Some(expr) = memo.get(&node_ref) {
        return Some(expr.clone());
    }

    if let Some(expr) = collapse_shared_condition_chain(decision, node_ref, memo) {
        memo.insert(node_ref, expr.clone());
        return Some(expr);
    }

    let node = decision.nodes.get(node_ref.index())?;
    let truthy = collapse_condition_target(decision, node, &node.truthy, memo)?;
    let falsy = collapse_condition_target(decision, node, &node.falsy, memo)?;
    let expr = combine_condition_expr(node.test.clone(), truthy, falsy)?;
    memo.insert(node_ref, expr.clone());
    Some(expr)
}

fn collapse_shared_condition_chain(
    decision: &HirDecisionExpr,
    node_ref: HirDecisionNodeRef,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
) -> Option<HirExpr> {
    let node = decision.nodes.get(node_ref.index())?;
    if matches!(node.truthy, HirDecisionTarget::Node(_))
        && let Some(expr) =
            collapse_condition_chain_with_fallback(decision, node_ref, true, &node.falsy, memo)
    {
        return Some(expr);
    }
    if matches!(node.falsy, HirDecisionTarget::Node(_)) {
        return collapse_condition_chain_with_fallback(
            decision,
            node_ref,
            false,
            &node.truthy,
            memo,
        );
    }
    None
}

fn collapse_condition_chain_with_fallback(
    decision: &HirDecisionExpr,
    node_ref: HirDecisionNodeRef,
    mut follow_truthy: bool,
    shared: &HirDecisionTarget,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
) -> Option<HirExpr> {
    if matches!(shared, HirDecisionTarget::CurrentValue) {
        return None;
    }

    let mut current = node_ref;
    let mut guard_terms = Vec::new();
    let mut node_count = 0;
    let terminal = loop {
        let node = decision.nodes.get(current.index())?;
        let (next, fallback) = if follow_truthy {
            (&node.truthy, &node.falsy)
        } else {
            (&node.falsy, &node.truthy)
        };
        if fallback != shared {
            return None;
        }

        let term = if follow_truthy {
            node.test.clone()
        } else {
            node.test.clone().negate()
        };
        guard_terms.push(term);
        node_count += 1;

        let HirDecisionTarget::Node(next_ref) = next else {
            break match next {
                HirDecisionTarget::CurrentValue => HirExpr::Boolean(follow_truthy),
                HirDecisionTarget::Expr(expr) => expr.clone(),
                HirDecisionTarget::Node(_) => unreachable!(),
            };
        };
        let child = decision.nodes.get(next_ref.index())?;
        follow_truthy = if child.falsy == *shared {
            true
        } else if child.truthy == *shared {
            false
        } else {
            return None;
        };
        current = *next_ref;
    };

    if node_count < 2 {
        return None;
    }
    let shared = match shared {
        HirDecisionTarget::Node(shared_ref) => {
            collapse_condition_node(decision, *shared_ref, memo)?
        }
        HirDecisionTarget::Expr(expr) => expr.clone(),
        HirDecisionTarget::CurrentValue => return None,
    };
    combine_condition_expr(balanced_logical_and(guard_terms)?, terminal, shared)
}

fn balanced_logical_and(mut terms: Vec<HirExpr>) -> Option<HirExpr> {
    while terms.len() > 1 {
        let mut next = Vec::with_capacity(terms.len().div_ceil(2));
        let mut current = std::mem::take(&mut terms).into_iter();
        while let Some(lhs) = current.next() {
            next.push(match current.next() {
                Some(rhs) => logical_and(lhs, rhs),
                None => lhs,
            });
        }
        terms = next;
    }
    terms.pop()
}

fn collapse_condition_target(
    decision: &HirDecisionExpr,
    node: &HirDecisionNode,
    target: &HirDecisionTarget,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
) -> Option<HirExpr> {
    match target {
        HirDecisionTarget::Node(next_ref) => collapse_condition_node(decision, *next_ref, memo),
        HirDecisionTarget::CurrentValue => Some(node.test.clone()),
        HirDecisionTarget::Expr(expr) => Some(expr.clone()),
    }
}

fn combine_condition_expr(subject: HirExpr, truthy: HirExpr, falsy: HirExpr) -> Option<HirExpr> {
    if is_true(&truthy) && is_false(&falsy) {
        return Some(subject);
    }
    if is_true(&truthy) {
        return Some(logical_or(subject, falsy));
    }
    if is_false(&falsy) {
        return Some(logical_and(subject, truthy));
    }
    if is_false(&truthy) && is_true(&falsy) {
        return Some(subject.negate());
    }
    if is_false(&truthy) {
        return Some(logical_and(subject.negate(), falsy));
    }
    if is_true(&falsy) {
        return Some(logical_or(subject.negate(), truthy));
    }
    // 条件位置只观察 truthiness。guard 与两臂都不会在求值间改写状态时，互斥 guard
    // 才能保证只求值原 decision 选中的 value arm；这覆盖 phi/value decision 随后
    // 立刻作为 branch 条件的通用形状，避免把内部 Decision 泄漏到 AST。
    if expr_is_repeatable(&subject) && expr_is_repeatable(&truthy) && expr_is_repeatable(&falsy) {
        let falsy_guard = subject.clone().negate();
        return Some(logical_or(
            logical_and(subject, truthy),
            logical_and(falsy_guard, falsy),
        ));
    }
    None
}

fn is_true(expr: &HirExpr) -> bool {
    matches!(expr, HirExpr::Boolean(true))
}

fn is_false(expr: &HirExpr) -> bool {
    matches!(expr, HirExpr::Boolean(false))
}

pub(in crate::hir) fn decision_has_shared_nodes(decision: &HirDecisionExpr) -> bool {
    if decision.nodes.is_empty() || decision.entry.index() >= decision.nodes.len() {
        return false;
    }

    let mut incoming = vec![0usize; decision.nodes.len()];
    incoming[decision.entry.index()] += 1;

    for node in &decision.nodes {
        for target in [&node.truthy, &node.falsy] {
            if let HirDecisionTarget::Node(node_ref) = target
                && let Some(count) = incoming.get_mut(node_ref.index())
            {
                *count += 1;
            }
        }
    }

    incoming.into_iter().any(|count| count > 1)
}

pub(in crate::hir) fn decision_has_cycles(decision: &HirDecisionExpr) -> bool {
    if decision.nodes.is_empty() || decision.entry.index() >= decision.nodes.len() {
        return false;
    }

    #[derive(Clone, Copy, Eq, PartialEq)]
    enum VisitState {
        Unvisited,
        Visiting,
        Done,
    }

    let mut states = vec![VisitState::Unvisited; decision.nodes.len()];
    let mut stack = vec![(decision.entry, false)];

    while let Some((node_ref, expanded)) = stack.pop() {
        let node_index = node_ref.index();
        let Some(node) = decision.nodes.get(node_index) else {
            continue;
        };

        if expanded {
            states[node_index] = VisitState::Done;
            continue;
        }

        match states[node_index] {
            VisitState::Done => continue,
            VisitState::Visiting => return true,
            VisitState::Unvisited => {
                states[node_index] = VisitState::Visiting;
                stack.push((node_ref, true));
            }
        }

        for target in [&node.truthy, &node.falsy] {
            let HirDecisionTarget::Node(next_ref) = target else {
                continue;
            };
            match states.get(next_ref.index()) {
                Some(VisitState::Done) | None => {}
                Some(VisitState::Visiting) => return true,
                Some(VisitState::Unvisited) => stack.push((*next_ref, false)),
            }
        }
    }

    false
}
