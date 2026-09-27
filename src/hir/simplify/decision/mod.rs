//! 这个文件承载 HIR `Decision` DAG 的通用归一化。
//!
//! 既然我们已经决定让共享短路子图先以 DAG 的形式保留在 HIR 里，那么后处理也应该
//! 围绕 DAG 自身做“图级别”的收敛，而不是继续往外堆局部特判。这里专门实现几类
//! 与具体 case 无关的通用规则：
//! 1. 常量 truthiness 驱动的分支裁剪；
//! 2. `then/else` 指向同一结果时的节点消除；
//! 3. 根节点和内部节点裁剪后留下的不可达节点清理。

use std::collections::BTreeMap;

mod eliminate;
mod eliminate_control;
mod eliminate_materialize;
mod eliminate_state;
mod helpers;
mod short_circuit;
mod synthesize;

use super::expr_facts::{expr_is_boolean_valued, expr_truthiness, expr_truthiness_assuming};
use super::walk::{HirRewritePass, rewrite_proto};
use crate::hir::common::{
    HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirExpr, HirProto,
};
use crate::hir::decision::{DecisionFacts, analyze_decision};
use crate::hir::expr_safety::HirExprSafety;
use helpers::{logical_and, logical_or};

/// 对单个 proto 递归执行 decision DAG 归一化。
pub(super) fn simplify_decision_exprs_in_proto(
    proto: &mut HirProto,
    safety: HirExprSafety,
) -> bool {
    rewrite_proto(proto, &mut DecisionExprPass { safety })
}

/// 消除未签发的 Decision；完整源码帧已证明的 Luau if 表达式留给 AST 机械降低。
/// 共享图的语义恢复必须在 HIR 完成，AST 不承担决策或帧证明。
pub(crate) use eliminate::eliminate_remaining_decisions_in_proto;
pub(crate) use synthesize::expr_cost;

struct DecisionExprPass {
    safety: HirExprSafety,
}

impl HirRewritePass for DecisionExprPass {
    fn rewrite_condition_expr_before_children(&mut self, expr: &mut HirExpr) -> bool {
        if let HirExpr::Decision(decision) = expr
            && !decision.emit_as_luau_if
            && let Some(replacement) =
                short_circuit::collapse_condition_graph(&analyze_decision(decision), self.safety)
        {
            *expr = replacement;
            return true;
        }
        false
    }

    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        let mut decision_replacement = None;
        let mut changed = false;
        if let HirExpr::Decision(decision) = expr {
            let (decision_changed, replacement) = simplify_decision_expr(decision, self.safety);
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
            && !decision.emit_as_luau_if
            && let Some(replacement) =
                collapse_condition_decision_expr(&analyze_decision(decision), self.safety)
        {
            *expr = replacement;
            changed = true;
        }
        changed
    }
}

fn simplify_decision_expr(
    decision: &mut HirDecisionExpr,
    safety: HirExprSafety,
) -> (bool, Option<HirExpr>) {
    if decision.emit_as_luau_if {
        return (false, None);
    }
    let Some(reduced) = reduce_decision_expr(decision, safety) else {
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

fn reduce_decision_expr(
    decision: &HirDecisionExpr,
    safety: HirExprSafety,
) -> Option<ReducedDecision> {
    let topology = analyze_decision(decision);

    let mut nodes = decision.nodes.clone();
    let mut replacements = vec![None; nodes.len()];
    let mut changed = false;
    let mut linear_nodes = vec![false; nodes.len()];
    let mut consumed = vec![false; nodes.len()];
    if !topology.has_shared_nodes() {
        for node in topology.topological_nodes().rev() {
            linear_nodes[node.id.index()] = match (&node.truthy, &node.falsy) {
                (HirDecisionTarget::CurrentValue, HirDecisionTarget::Expr(_))
                | (HirDecisionTarget::Expr(_), HirDecisionTarget::CurrentValue)
                | (HirDecisionTarget::CurrentValue, HirDecisionTarget::CurrentValue) => true,
                (HirDecisionTarget::CurrentValue, HirDecisionTarget::Node(next))
                | (HirDecisionTarget::Node(next), HirDecisionTarget::CurrentValue) => {
                    linear_nodes[next.index()]
                }
                _ => false,
            };
        }
        // 外层一般条件选择不能折成 and/or，其内部的短路值链仍可独立恢复。
        // CurrentValue 保留本次 test 的值和后继求值顺序，不重测父 guard；每条
        // 最大链只消费一次，避免从每个节点重复扫描或复制不断增长的后缀表达式。
        for node in topology.topological_nodes() {
            if !linear_nodes[node.id.index()] || consumed[node.id.index()] {
                continue;
            }
            let expr = collapse_linear_value_chain_with(node.id, |next| {
                consumed[next.index()] = true;
                Some(decision.nodes[next.index()].clone())
            })
            .expect("linear Decision chain must have a value exit");
            replacements[node.id.index()] = Some(ResolvedDecisionTarget::Expr(expr));
            changed = true;
        }
    }

    // arena 重编号只保留稠密身份，不保证拓扑顺序；共享 tail 必须先于所有父节点归约。
    for original in topology.topological_nodes().rev() {
        let node_ref = original.id;
        let index = node_ref.index();
        if consumed[index] {
            continue;
        }
        let node = &nodes[index];

        let truthy = reduce_target(&replacements, &node.truthy);
        let falsy = reduce_target(&replacements, &node.falsy);
        let resolved_truthy = truthy.as_ref().unwrap_or(&node.truthy);
        let resolved_falsy = falsy.as_ref().unwrap_or(&node.falsy);

        // 候选拒绝[SemanticBarrier:EvalCount]：即使 truthiness 已知，删除 `{ f() }` test 也会漏掉字段表达式中的一次 `f()`。
        if let Some(constant_truthy) = expr_truthiness(&node.test, safety)
            && safety.is_discard_safe(&node.test)
        {
            replacements[node_ref.index()] = Some(resolve_target_in_node_context(
                &replacements,
                &node.test,
                if constant_truthy {
                    resolved_truthy
                } else {
                    resolved_falsy
                },
            ));
            changed = true;
            continue;
        }

        // 候选拒绝[SemanticBarrier:EvalCount]：两臂相同也不能删除 `f()` test，否则原来必达的一次调用消失。
        if resolved_truthy == resolved_falsy && safety.is_discard_safe(&node.test) {
            replacements[node_ref.index()] = Some(resolve_target_in_node_context(
                &replacements,
                &node.test,
                resolved_truthy,
            ));
            changed = true;
            continue;
        }

        changed |= truthy.is_some() || falsy.is_some();
        if let Some(truthy) = truthy {
            nodes[index].truthy = truthy;
        }
        if let Some(falsy) = falsy {
            nodes[index].falsy = falsy;
        }
    }

    let root = if let Some(replacement) = &replacements[decision.entry.index()] {
        replacement.clone()
    } else {
        ResolvedDecisionTarget::Node(decision.entry)
    };

    match root {
        ResolvedDecisionTarget::Expr(expr) => Some(ReducedDecision::Expr(expr)),
        ResolvedDecisionTarget::Node(entry) => {
            let (rebuilt, topology_changed) = rebuild_decision(entry, &nodes);
            changed |= topology_changed;
            if let Some(expr) =
                collapse_value_decision_expr(&analyze_decision(&rebuilt), safety, |_| false)
            {
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

fn reduce_target(
    replacements: &[Option<ResolvedDecisionTarget>],
    target: &HirDecisionTarget,
) -> Option<HirDecisionTarget> {
    let HirDecisionTarget::Node(child_ref) = target else {
        return None;
    };
    // 候选拒绝[PolicyBoundary]：父子 test 即使相同且稳定，也代表两次显式检查；
    // 父边 truthiness 不能授权跳过子节点，只消费子节点自身已经完成的归约。
    replacements[child_ref.index()]
        .as_ref()
        .map(replacement_as_target)
}

fn resolve_target_in_node_context(
    replacements: &[Option<ResolvedDecisionTarget>],
    test: &HirExpr,
    target: &HirDecisionTarget,
) -> ResolvedDecisionTarget {
    match target {
        HirDecisionTarget::Node(node_ref) => replacements[node_ref.index()]
            .clone()
            .unwrap_or(ResolvedDecisionTarget::Node(*node_ref)),
        HirDecisionTarget::CurrentValue => ResolvedDecisionTarget::Expr(test.clone()),
        HirDecisionTarget::Expr(expr) => ResolvedDecisionTarget::Expr(expr.clone()),
    }
}

pub(super) fn replacement_as_target(target: &ResolvedDecisionTarget) -> HirDecisionTarget {
    match target {
        ResolvedDecisionTarget::Node(node_ref) => HirDecisionTarget::Node(*node_ref),
        ResolvedDecisionTarget::Expr(expr) => HirDecisionTarget::Expr(expr.clone()),
    }
}

/// 输入已验证稠密身份；归约只重定向到原图后继，投影不引入域外节点。
/// 首次入队时签发新身份，同时去重并保留 BFS 顺序，不重新按旧 id 搜索或跳过非法边。
fn rebuild_decision(
    entry: HirDecisionNodeRef,
    nodes: &[HirDecisionNode],
) -> (HirDecisionExpr, bool) {
    let mut remap = vec![None; nodes.len()];
    let mut reachable = vec![entry];
    remap[entry.index()] = Some(HirDecisionNodeRef(0));
    let mut cursor = 0;
    while cursor < reachable.len() {
        let node = &nodes[reachable[cursor].index()];
        cursor += 1;
        for target in [&node.truthy, &node.falsy] {
            if let HirDecisionTarget::Node(next_ref) = target
                && remap[next_ref.index()].is_none()
            {
                remap[next_ref.index()] = Some(HirDecisionNodeRef(reachable.len()));
                reachable.push(*next_ref);
            }
        }
    }

    let topology_changed = reachable.len() != nodes.len()
        || reachable
            .iter()
            .enumerate()
            .any(|(index, old_ref)| old_ref.index() != index);
    let rebuilt_nodes = reachable
        .into_iter()
        .enumerate()
        .map(|(index, old_ref)| {
            let old = &nodes[old_ref.index()];
            HirDecisionNode {
                id: HirDecisionNodeRef(index),
                test: old.test.clone(),
                test_source: old.test_source,
                truthy: remap_target(&old.truthy, &remap),
                falsy: remap_target(&old.falsy, &remap),
            }
        })
        .collect::<Vec<_>>();

    (
        HirDecisionExpr {
            emit_as_luau_if: false,
            entry: HirDecisionNodeRef(0),
            nodes: rebuilt_nodes,
        },
        topology_changed,
    )
}

/// 把某条 Decision edge 投影为独立的值表达式。
///
/// `CurrentValue` 属于 edge 的父节点，调用方必须传入该已选路径上的精确值；Node edge
/// 则只保留其可达子图并重编号，避免构造带不可达 root 的非法 Decision。
pub(super) fn project_value_decision_target(
    topology: &DecisionFacts<'_>,
    target: &HirDecisionTarget,
    current_value: HirExpr,
    safety: HirExprSafety,
) -> HirExpr {
    let decision = topology.decision();
    match target {
        HirDecisionTarget::Expr(expr) => expr.clone(),
        HirDecisionTarget::CurrentValue => current_value,
        HirDecisionTarget::Node(entry) => {
            let (projected, _) = rebuild_decision(*entry, &decision.nodes);
            collapse_value_decision_expr(&analyze_decision(&projected), safety, |_| false)
                .unwrap_or_else(|| HirExpr::Decision(Box::new(projected)))
        }
    }
}

fn remap_target(
    target: &HirDecisionTarget,
    remap: &[Option<HirDecisionNodeRef>],
) -> HirDecisionTarget {
    match target {
        HirDecisionTarget::Node(node_ref) => HirDecisionTarget::Node(
            remap[node_ref.index()]
                .expect("reachable Decision edge must have a projected identity"),
        ),
        HirDecisionTarget::CurrentValue => HirDecisionTarget::CurrentValue,
        HirDecisionTarget::Expr(expr) => HirDecisionTarget::Expr(expr.clone()),
    }
}

pub(in crate::hir) fn collapse_value_decision_expr(
    topology: &DecisionFacts<'_>,
    safety: HirExprSafety,
    root_ends: impl Fn(&HirDecisionNode) -> bool,
) -> Option<HirExpr> {
    let preserves_boolean_test = topology.topological_nodes().any(|node| {
        node.test_source == crate::hir::HirDecisionTestSource::Value
            && matches!(node.test, HirExpr::Boolean(_))
    });
    let mut expr = collapse_value_decision_shape(topology, safety, root_ends)?;
    if preserves_boolean_test {
        // 原 Decision 仍 TEST 已物化的 Boolean；表达式化只改变控制的表示，
        // 不能让后续布尔转换把这次显式检查消掉。
        let mut pending = vec![&mut expr];
        while let Some(value) = pending.pop() {
            if let HirExpr::LogicalOr(or) = value
                && matches!(or.rhs, HirExpr::Boolean(false))
                && let HirExpr::LogicalAnd(and) = &mut or.lhs
                && matches!(and.rhs, HirExpr::Boolean(true))
            {
                or.preserves_boolean_prewrite = true;
                and.preserves_boolean_prewrite = true;
            }
            if let HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) = value {
                pending.push(&mut logical.lhs);
                pending.push(&mut logical.rhs);
            }
        }
    }
    Some(expr)
}

fn collapse_value_decision_shape(
    topology: &DecisionFacts<'_>,
    safety: HirExprSafety,
    root_ends: impl Fn(&HirDecisionNode) -> bool,
) -> Option<HirExpr> {
    let decision = topology.decision();

    // Boolean 结果的共享出口先按控制边归约；提前把 true/false 改成
    // CurrentValue 会打散共同出口，迫使后层制造丢失原槽身份的临时声明。
    // 所有测试与恢复结果都必须是 Boolean，不能把任意 truthy 值当作 true。
    if topology
        .topological_nodes()
        .all(|node| expr_is_boolean_valued(&node.test))
        && let Some(expr) = short_circuit::collapse_condition_graph(topology, safety)
        && expr_is_boolean_valued(&expr)
    {
        return Some(expr);
    }

    if !topology.has_shared_nodes()
        && let Some(expr) = collapse_linear_value_chain(decision)
    {
        return Some(expr);
    }
    // 共同 continuation 也可以是 Expr 终端，不仅是多入边 Node；原 Boolean test 的
    // 极性归约必须在这两种图上都先于值到谓词物化。
    if let Some(expr) = short_circuit::collapse_short_circuit_graph(topology, safety, root_ends) {
        return Some(expr);
    }
    if topology.has_shared_nodes() {
        synthesize::synthesize_value_decision_expr(decision, safety).or_else(|| {
            let mut memo = BTreeMap::new();
            collapse_value_node(decision, decision.entry, &mut memo, safety)
        })
    } else {
        let mut memo = BTreeMap::new();
        collapse_value_node(decision, decision.entry, &mut memo, safety)
            .or_else(|| synthesize::synthesize_value_decision_expr(decision, safety))
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum LinearValueOp {
    And,
    Or,
}

fn collapse_linear_value_chain(decision: &HirDecisionExpr) -> Option<HirExpr> {
    collapse_linear_value_chain_with(decision.entry, |node| {
        decision.nodes.get(node.index()).cloned()
    })
}

fn collapse_linear_value_chain_with(
    entry: HirDecisionNodeRef,
    mut take_node: impl FnMut(HirDecisionNodeRef) -> Option<HirDecisionNode>,
) -> Option<HirExpr> {
    let mut steps = Vec::new();
    let mut current = entry;
    let tail = loop {
        let node = take_node(current)?;
        match (node.truthy, node.falsy) {
            (HirDecisionTarget::CurrentValue, HirDecisionTarget::Node(next)) => {
                steps.push((LinearValueOp::Or, node.test));
                current = next;
            }
            (HirDecisionTarget::Node(next), HirDecisionTarget::CurrentValue) => {
                steps.push((LinearValueOp::And, node.test));
                current = next;
            }
            (HirDecisionTarget::Node(next), HirDecisionTarget::Expr(HirExpr::Boolean(false)))
                if expr_is_boolean_valued(&node.test) =>
            {
                // 原比较已产生 Boolean，false 出口可由 and 承载；不要求比较可重复，
                // 也不复制其求值。归一化后的外层极性不能因这个显式出口退回原 DAG。
                steps.push((LinearValueOp::And, node.test));
                current = next;
            }
            (HirDecisionTarget::Expr(HirExpr::Boolean(true)), HirDecisionTarget::Node(next))
                if expr_is_boolean_valued(&node.test) =>
            {
                steps.push((LinearValueOp::Or, node.test));
                current = next;
            }
            (HirDecisionTarget::CurrentValue, HirDecisionTarget::Expr(expr)) => {
                steps.push((LinearValueOp::Or, node.test));
                break expr;
            }
            (HirDecisionTarget::Expr(expr), HirDecisionTarget::CurrentValue) => {
                steps.push((LinearValueOp::And, node.test));
                break expr;
            }
            (HirDecisionTarget::CurrentValue, HirDecisionTarget::CurrentValue) => {
                break node.test;
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
    safety: HirExprSafety,
) -> Option<HirExpr> {
    if let Some(expr) = memo.get(&node_ref) {
        return Some(expr.clone());
    }

    if let Some(expr) = collapse_shared_falsy_chain(decision, node_ref, memo, safety) {
        memo.insert(node_ref, expr.clone());
        return Some(expr);
    }

    let node = decision.nodes.get(node_ref.index())?;
    let truthy = collapse_value_target(decision, &node.truthy, memo, safety)?;
    let falsy = collapse_value_target(decision, &node.falsy, memo, safety)?;
    let expr = combine_value_expr(node.test.clone(), truthy, falsy, safety)?;
    memo.insert(node_ref, expr.clone());
    Some(expr)
}

fn collapse_shared_falsy_chain(
    decision: &HirDecisionExpr,
    node_ref: HirDecisionNodeRef,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    let mut next_ref = node_ref;
    let mut terms = Vec::new();
    let tail = loop {
        let Some((term, fallback)) = collapse_shared_falsy_term(decision, next_ref) else {
            if terms.is_empty() {
                return None;
            }
            break collapse_value_node(decision, next_ref, memo, safety)?;
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
            safety,
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
    safety: HirExprSafety,
) -> Option<CollapsedValueTarget> {
    match target {
        HirDecisionTarget::Node(next_ref) => Some(CollapsedValueTarget::Expr(collapse_value_node(
            decision, *next_ref, memo, safety,
        )?)),
        HirDecisionTarget::CurrentValue => Some(CollapsedValueTarget::CurrentValue),
        HirDecisionTarget::Expr(expr) => Some(CollapsedValueTarget::Expr(expr.clone())),
    }
}

fn combine_value_expr(
    mut subject: HirExpr,
    mut truthy: CollapsedValueTarget,
    mut falsy: CollapsedValueTarget,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    // `not call() and value` 的 Boolean guard 已可直接承载任意假值；若翻成
    // call() ? false : value，Lua 无法在一般 value 上用 and/or 表达这组三元值。
    // 两侧均为一般值可交后续因式恢复，两个 Boolean 出口则有单次求值的物化形式。
    let is_boolean_target = |target: &CollapsedValueTarget| {
        matches!(
            target,
            CollapsedValueTarget::CurrentValue | CollapsedValueTarget::Expr(HirExpr::Boolean(_))
        )
    };
    let normalize_polarity = is_boolean_target(&truthy) == is_boolean_target(&falsy);
    // 控制极性的合成 NOT 不是原 VM 的值写入。先交换出口，避免把 TEST 的
    // Boolean 合流变成双 NOT，提前覆盖仍可能被下一次 GC 观察到的操作数根。
    while normalize_polarity
        && matches!(&subject, HirExpr::Unary(unary)
        if unary.op == crate::hir::HirUnaryOpKind::Not && unary.source_site.is_none())
    {
        // CurrentValue 指被测试的 NOT 结果；翻转极性后不能误指向原操作数。
        if matches!(truthy, CollapsedValueTarget::CurrentValue) {
            truthy = CollapsedValueTarget::Expr(HirExpr::Boolean(true));
        }
        if matches!(falsy, CollapsedValueTarget::CurrentValue) {
            falsy = CollapsedValueTarget::Expr(HirExpr::Boolean(false));
        }
        let HirExpr::Unary(unary) = subject else {
            unreachable!()
        };
        subject = unary.expr;
        std::mem::swap(&mut truthy, &mut falsy);
    }
    let truthy = normalize_collapsed_target(&subject, truthy, safety);
    let falsy = normalize_collapsed_target(&subject, falsy, safety);

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
            (CollapsedValueTarget::Expr(lhs), CollapsedValueTarget::Expr(rhs)) if is_false(rhs) => {
                // subject 已是 Boolean，false 分支可直接由 and 承载；选中的值臂
                // 可以返回 nil、对象或任意值。这里不重复 test，也不删除原 false 出口。
                return Some(logical_and(subject, lhs.clone()));
            }
            (CollapsedValueTarget::Expr(lhs), CollapsedValueTarget::Expr(rhs)) if is_true(lhs) => {
                return Some(logical_or(subject, rhs.clone()));
            }
            (CollapsedValueTarget::Expr(lhs), CollapsedValueTarget::Expr(rhs)) if is_false(lhs) => {
                return Some(logical_and(subject.negate(), rhs.clone()));
            }
            (CollapsedValueTarget::Expr(lhs), CollapsedValueTarget::Expr(rhs)) if is_true(rhs) => {
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
            if expr_truthiness(&lhs, safety) == Some(true) {
                Some(logical_or(logical_and(subject, lhs), rhs))
            } else if expr_truthiness(&rhs, safety) == Some(true) {
                Some(logical_or(logical_and(subject.negate(), rhs), lhs))
            } else if safety.is_repeatable(&subject)
                && safety.is_repeatable(&lhs)
                && expr_truthiness_assuming(&lhs, &subject, true, safety) == Some(true)
            {
                // 分支值可能只在当前 guard 成立时恒真。把这种路径约束留在
                // Decision 外就会误判成普通三元式并物化为 if；guard 与被跨越的
                // 分支都可重复时，原顺序的 `subject and lhs or rhs` 才不会因求值中
                // 改写 guard 而误入 fallback。
                Some(logical_or(logical_and(subject, lhs), rhs))
            } else if safety.is_repeatable(&subject)
                && safety.is_repeatable(&rhs)
                && expr_truthiness_assuming(&rhs, &subject, false, safety) == Some(true)
            {
                Some(logical_or(logical_and(subject.negate(), rhs), lhs))
            } else {
                // 候选拒绝[LayerBoundary]：一般 Lua 三元值不能总由单个 `and/or` 精确承载；保留 Decision 交给 eliminate-decisions 原位物化。
                None
            }
        }
    }
}

fn normalize_collapsed_target(
    subject: &HirExpr,
    target: CollapsedValueTarget,
    safety: HirExprSafety,
) -> CollapsedValueTarget {
    match target {
        CollapsedValueTarget::Expr(expr) if &expr == subject => {
            if safety.is_repeatable(subject) {
                CollapsedValueTarget::CurrentValue
            } else {
                // 候选拒绝[SemanticBarrier:EvalCount]：把两次同形 `f()` 归一成 CurrentValue 会把后一次调用错误复用为前一次结果。
                CollapsedValueTarget::Expr(expr)
            }
        }
        other => other,
    }
}

pub(in crate::hir) fn collapse_condition_decision_expr(
    topology: &DecisionFacts<'_>,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    // 先按原连边消费串并联子图，避免树化共享 continuation 后合成重复 guard。
    if let Some(expr) = short_circuit::collapse_condition_graph(topology, safety) {
        return Some(expr);
    }
    let decision = topology.decision();

    let mut memo = BTreeMap::new();
    collapse_condition_node(decision, decision.entry, &mut memo, safety)
}

fn collapse_condition_node(
    decision: &HirDecisionExpr,
    node_ref: HirDecisionNodeRef,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    if let Some(expr) = memo.get(&node_ref) {
        return Some(expr.clone());
    }

    if let Some(expr) = collapse_shared_condition_chain(decision, node_ref, memo, safety) {
        memo.insert(node_ref, expr.clone());
        return Some(expr);
    }

    let node = decision.nodes.get(node_ref.index())?;
    let truthy = collapse_condition_target(decision, node, &node.truthy, memo, safety)?;
    let falsy = collapse_condition_target(decision, node, &node.falsy, memo, safety)?;
    let expr = combine_condition_expr(node.test.clone(), truthy, falsy, safety)?;
    memo.insert(node_ref, expr.clone());
    Some(expr)
}

fn collapse_shared_condition_chain(
    decision: &HirDecisionExpr,
    node_ref: HirDecisionNodeRef,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    let node = decision.nodes.get(node_ref.index())?;
    if matches!(node.truthy, HirDecisionTarget::Node(_))
        && let Some(expr) = collapse_condition_chain_with_fallback(
            decision,
            node_ref,
            true,
            &node.falsy,
            memo,
            safety,
        )
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
            safety,
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
    safety: HirExprSafety,
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
            collapse_condition_node(decision, *shared_ref, memo, safety)?
        }
        HirDecisionTarget::Expr(expr) => expr.clone(),
        HirDecisionTarget::CurrentValue => return None,
    };
    combine_condition_expr(balanced_logical_and(guard_terms)?, terminal, shared, safety)
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
    safety: HirExprSafety,
) -> Option<HirExpr> {
    match target {
        HirDecisionTarget::Node(next_ref) => {
            collapse_condition_node(decision, *next_ref, memo, safety)
        }
        HirDecisionTarget::CurrentValue => Some(node.test.clone()),
        HirDecisionTarget::Expr(expr) => Some(expr.clone()),
    }
}

fn combine_condition_expr(
    subject: HirExpr,
    truthy: HirExpr,
    falsy: HirExpr,
    safety: HirExprSafety,
) -> Option<HirExpr> {
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
    if safety.is_repeatable(&subject)
        && safety.is_repeatable(&truthy)
        && safety.is_repeatable(&falsy)
    {
        let falsy_guard = subject.clone().negate();
        return Some(logical_or(
            logical_and(subject, truthy),
            logical_and(falsy_guard, falsy),
        ));
    }
    // 候选拒绝[LayerBoundary]：非稳定条件/分支需要 statement prefix 才能只求值选中臂
    // 一次；纯表达式 collapse 返回 None，由 eliminate-decisions 的语句 owner 物化。
    None
}

fn is_true(expr: &HirExpr) -> bool {
    matches!(expr, HirExpr::Boolean(true))
}

fn is_false(expr: &HirExpr) -> bool {
    matches!(expr, HirExpr::Boolean(false))
}
