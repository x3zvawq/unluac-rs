//! 这个文件承载 HIR `Decision` DAG 的通用归一化。
//!
//! 既然我们已经决定让共享短路子图先以 DAG 的形式保留在 HIR 里，那么后处理也应该
//! 围绕 DAG 自身做“图级别”的收敛，而不是继续往外堆局部特判。这里专门实现几类
//! 与具体 case 无关的通用规则：
//! 1. 常量 truthiness 驱动的分支裁剪；
//! 2. `then/else` 指向同一结果时的节点消除；
//! 3. 已知某条边上 test 结果后，对子节点同一 test 的重复判断消除；
//! 4. 根节点和内部节点裁剪后留下的不可达节点清理。

use std::collections::{BTreeMap, BTreeSet, VecDeque};

mod eliminate;
mod helpers;
mod synthesize;

use super::walk::{ExprRewritePass, rewrite_proto_exprs};
use helpers::{
    expr_is_boolean_valued, expr_truthiness, logical_and, logical_or,
    simplify_condition_truthiness_shape, simplify_lua_logical_shape,
};

use crate::hir::common::{
    HirBinaryOpKind, HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget,
    HirExpr, HirProto, HirUnaryOpKind,
};

#[cfg(test)]
use crate::hir::common::{HirBlock, HirStmt, HirTableField, HirTableKey};

/// 对单个 proto 递归执行 decision DAG 归一化。
pub(super) fn simplify_decision_exprs_in_proto(proto: &mut HirProto) -> bool {
    rewrite_proto_exprs(proto, &mut DecisionExprPass)
}

/// 把前面保留在 HIR 内部的 `Decision` 彻底消掉。
///
/// `Decision` 只应该是 HIR 内部为了保住共享短路子图而暂存的过渡节点；一旦进入最终
/// HIR 输出，它就应该已经被重新线性化成普通 `if/local/assign` 或纯表达式，避免把
/// 共享图的语义恢复继续后移给 AST。
pub(super) fn eliminate_remaining_decisions_in_proto(proto: &mut HirProto) -> bool {
    eliminate::eliminate_remaining_decisions_in_proto(proto)
}

pub(super) fn naturalize_pure_logical_expr(expr: &HirExpr) -> Option<HirExpr> {
    synthesize::naturalize_pure_logical_expr(expr)
}

pub(crate) fn synthesize_readable_pure_logical_expr(expr: &HirExpr) -> Option<HirExpr> {
    synthesize::synthesize_readable_pure_logical_expr(expr)
}

pub(crate) fn decision_is_synth_safe(decision: &HirDecisionExpr) -> bool {
    synthesize::decision_is_synth_safe(decision)
}

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

        if let Some(replacement) = simplify_lua_logical_shape(expr) {
            *expr = replacement;
            changed = true;
        }
        if let Some(replacement) = simplify_condition_truthiness_shape(expr) {
            *expr = replacement;
            changed = true;
        }

        changed
    }

    fn rewrite_condition_expr(&mut self, expr: &mut HirExpr) -> bool {
        if let HirExpr::Decision(decision) = expr
            && !decision_has_shared_nodes(decision)
            && !decision_has_cycles(decision)
            && let Some(replacement) = collapse_condition_decision_expr(decision)
        {
            *expr = replacement;
            return true;
        }
        false
    }
}

fn simplify_decision_expr(decision: &mut HirDecisionExpr) -> (bool, Option<HirExpr>) {
    let Some(reduced) = reduce_decision_expr(decision) else {
        return (false, None);
    };

    match reduced {
        ReducedDecision::Expr(expr) => (true, Some(expr)),
        ReducedDecision::Decision(reduced_decision) => {
            let changed = reduced_decision != *decision;
            *decision = reduced_decision;
            (changed, None)
        }
    }
}

enum ReducedDecision {
    Expr(HirExpr),
    Decision(HirDecisionExpr),
}

#[derive(Clone, PartialEq)]
enum ResolvedDecisionTarget {
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
        let original = nodes[index].clone();
        let mut node = original.clone();

        if let HirDecisionTarget::Node(child_ref) = &node.truthy
            && nodes[child_ref.index()].test == node.test
        {
            node.truthy = resolve_child_branch(&nodes, &replacements, *child_ref, true);
        } else {
            node.truthy = resolve_target_for_parent(&replacements, &node.truthy);
        }

        if let HirDecisionTarget::Node(child_ref) = &node.falsy
            && nodes[child_ref.index()].test == node.test
        {
            node.falsy = resolve_child_branch(&nodes, &replacements, *child_ref, false);
        } else {
            node.falsy = resolve_target_for_parent(&replacements, &node.falsy);
        }

        if let Some(constant_truthy) = expr_truthiness(&node.test) {
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

        if node.truthy == node.falsy {
            replacements[node_ref.index()] = Some(resolve_target_in_node_context(
                &replacements,
                &node,
                &node.truthy,
            ));
            changed = true;
            continue;
        }

        changed |= node != original;
        nodes[index] = node;
    }

    let root = if let Some(replacement) = &replacements[decision.entry.index()] {
        replacement.clone()
    } else {
        ResolvedDecisionTarget::Node(decision.entry)
    };

    match root {
        ResolvedDecisionTarget::Expr(expr) => Some(ReducedDecision::Expr(expr)),
        ResolvedDecisionTarget::Node(entry) => {
            let rebuilt = rebuild_decision(entry, &nodes);
            let rebuilt = if decision_has_cycles(&rebuilt) {
                rebuilt
            } else {
                specialize_decision_by_known_tests(&rebuilt).unwrap_or(rebuilt)
            };
            if let Some(expr) = collapse_value_decision_expr(&rebuilt) {
                return Some(ReducedDecision::Expr(expr));
            }
            if changed || rebuilt != *decision {
                Some(ReducedDecision::Decision(rebuilt))
            } else {
                None
            }
        }
    }
}

/// 这里做的是“沿路径传播已知稳定 test 结果”的图级专门化。
///
/// 和局部规则不同，这一步直接在共享 DAG 上工作：当某个 descendant 节点再次判断一个
/// 在当前路径上已经确定 truthiness 的稳定表达式时，就直接按已知结果裁掉该节点。
/// 这样既能减少重复片段，也不会把 case-specific 的结构判断重新塞回 simplify。
fn specialize_decision_by_known_tests(decision: &HirDecisionExpr) -> Option<HirDecisionExpr> {
    let mut specializer = DecisionSpecializer::new(decision);
    let facts = TruthFacts::default();
    let root = specializer.specialize_node(decision.entry, &facts);
    match root {
        ResolvedDecisionTarget::Expr(_) => None,
        ResolvedDecisionTarget::Node(entry) => {
            let specialized = HirDecisionExpr {
                entry,
                nodes: specializer.nodes,
            };
            (specialized != *decision).then_some(specialized)
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum TruthFactExprKey {
    Nil,
    Boolean(bool),
    Integer(i64),
    Number(u64),
    String(String),
    Int64(i64),
    UInt64(u64),
    Complex { real_bits: u64, imag_bits: u64 },
    Param(usize),
    Local(usize),
    Upvalue(usize),
    Temp(usize),
    Not(Box<TruthFactExprKey>),
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct TruthFact {
    expr: TruthFactExprKey,
    truthy: bool,
}

#[derive(Debug, Clone, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct TruthFacts(Vec<TruthFact>);

impl TruthFacts {
    fn extended_with(&self, expr: &HirExpr, truthy: bool) -> Self {
        let mut extended = self.clone();
        extended.insert_expr(expr, truthy);
        if let HirExpr::Unary(unary) = expr
            && unary.op == HirUnaryOpKind::Not
        {
            extended.insert_expr(&unary.expr, !truthy);
        }
        extended
    }

    fn known_truthiness(&self, expr: &HirExpr) -> Option<bool> {
        let key = truth_fact_expr_key(expr)?;
        self.truthiness_for_key(&key)
    }

    fn insert_expr(&mut self, expr: &HirExpr, truthy: bool) {
        let Some(expr) = truth_fact_expr_key(expr) else {
            return;
        };
        self.insert_key(expr, truthy);
    }

    fn insert_key(&mut self, expr: TruthFactExprKey, truthy: bool) {
        match self.0.binary_search_by(|fact| fact.expr.cmp(&expr)) {
            Ok(index) => {
                debug_assert_eq!(
                    self.0[index].truthy, truthy,
                    "truth fact set should not record contradictory facts for the same expression",
                );
            }
            Err(index) => self.0.insert(index, TruthFact { expr, truthy }),
        }
    }

    fn truthiness_for_key(&self, expr: &TruthFactExprKey) -> Option<bool> {
        self.0
            .binary_search_by(|fact| fact.expr.cmp(expr))
            .ok()
            .map(|index| self.0[index].truthy)
    }
}

#[derive(Clone, PartialEq)]
struct InternedDecisionNode {
    test: HirExpr,
    truthy: ResolvedDecisionTarget,
    falsy: ResolvedDecisionTarget,
    node_ref: HirDecisionNodeRef,
}

struct DecisionSpecializer<'a> {
    decision: &'a HirDecisionExpr,
    memo: BTreeMap<HirDecisionNodeRef, BTreeMap<TruthFacts, ResolvedDecisionTarget>>,
    interner: Vec<InternedDecisionNode>,
    nodes: Vec<HirDecisionNode>,
}

impl<'a> DecisionSpecializer<'a> {
    fn new(decision: &'a HirDecisionExpr) -> Self {
        Self {
            decision,
            memo: BTreeMap::new(),
            interner: Vec::new(),
            nodes: Vec::new(),
        }
    }

    fn specialize_node(
        &mut self,
        node_ref: HirDecisionNodeRef,
        facts: &TruthFacts,
    ) -> ResolvedDecisionTarget {
        if let Some(result) = self
            .memo
            .get(&node_ref)
            .and_then(|results| results.get(facts))
        {
            return result.clone();
        }

        let node = &self.decision.nodes[node_ref.index()];
        let result = if let Some(known_truthy) = known_truthiness_from_facts(&node.test, facts) {
            let chosen = if known_truthy {
                &node.truthy
            } else {
                &node.falsy
            };
            self.specialize_target(node, chosen, facts)
        } else {
            let truthy_facts = extend_truth_facts(facts, &node.test, true);
            let falsy_facts = extend_truth_facts(facts, &node.test, false);
            let truthy = self.specialize_target(node, &node.truthy, &truthy_facts);
            let falsy = self.specialize_target(node, &node.falsy, &falsy_facts);

            if truthy == falsy {
                truthy
            } else if let Some(existing) = self.interner.iter().find(|entry| {
                entry.test == node.test && entry.truthy == truthy && entry.falsy == falsy
            }) {
                ResolvedDecisionTarget::Node(existing.node_ref)
            } else {
                let mapped = HirDecisionNodeRef(self.nodes.len());
                self.nodes.push(HirDecisionNode {
                    id: mapped,
                    test: node.test.clone(),
                    truthy: replacement_as_target(&truthy),
                    falsy: replacement_as_target(&falsy),
                });
                self.interner.push(InternedDecisionNode {
                    test: node.test.clone(),
                    truthy,
                    falsy,
                    node_ref: mapped,
                });
                ResolvedDecisionTarget::Node(mapped)
            }
        };

        self.memo
            .entry(node_ref)
            .or_default()
            .insert(facts.clone(), result.clone());
        result
    }

    fn specialize_target(
        &mut self,
        node: &HirDecisionNode,
        target: &HirDecisionTarget,
        facts: &TruthFacts,
    ) -> ResolvedDecisionTarget {
        match target {
            HirDecisionTarget::Node(next_ref) => self.specialize_node(*next_ref, facts),
            HirDecisionTarget::CurrentValue => ResolvedDecisionTarget::Expr(node.test.clone()),
            HirDecisionTarget::Expr(expr) => ResolvedDecisionTarget::Expr(expr.clone()),
        }
    }
}

fn extend_truth_facts(facts: &TruthFacts, expr: &HirExpr, truthy: bool) -> TruthFacts {
    facts.extended_with(expr, truthy)
}

fn known_truthiness_from_facts(expr: &HirExpr, facts: &TruthFacts) -> Option<bool> {
    facts
        .known_truthiness(expr)
        .or_else(|| expr_truthiness(expr))
        .or_else(|| known_truthiness_from_shape(expr, facts))
}

fn known_truthiness_from_shape(expr: &HirExpr, facts: &TruthFacts) -> Option<bool> {
    match expr {
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            known_truthiness_from_facts(&unary.expr, facts).map(|truthy| !truthy)
        }
        HirExpr::LogicalAnd(logical) => match known_truthiness_from_facts(&logical.lhs, facts) {
            Some(false) => Some(false),
            Some(true) => known_truthiness_from_facts(&logical.rhs, facts),
            None => None,
        },
        HirExpr::LogicalOr(logical) => match known_truthiness_from_facts(&logical.lhs, facts) {
            Some(true) => Some(true),
            Some(false) => known_truthiness_from_facts(&logical.rhs, facts),
            None => None,
        },
        HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Eq => {
            known_eq_truthiness_from_facts(&binary.lhs, &binary.rhs, facts)
        }
        _ => None,
    }
}

fn known_eq_truthiness_from_facts(
    lhs: &HirExpr,
    rhs: &HirExpr,
    facts: &TruthFacts,
) -> Option<bool> {
    if lhs == rhs {
        return Some(true);
    }

    match (
        truth_sensitive_literal(lhs),
        truth_sensitive_literal(rhs),
        known_truthiness_from_facts(lhs, facts),
        known_truthiness_from_facts(rhs, facts),
    ) {
        (Some(left), Some(right), _, _) => Some(left == right),
        (Some(literal), None, _, Some(truthy)) | (None, Some(literal), Some(truthy), _) => {
            literal_eq_by_truthiness(literal, truthy)
        }
        _ => None,
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum TruthSensitiveLiteral {
    Nil,
    False,
    True,
}

fn truth_sensitive_literal(expr: &HirExpr) -> Option<TruthSensitiveLiteral> {
    match expr {
        HirExpr::Nil => Some(TruthSensitiveLiteral::Nil),
        HirExpr::Boolean(false) => Some(TruthSensitiveLiteral::False),
        HirExpr::Boolean(true) => Some(TruthSensitiveLiteral::True),
        _ => None,
    }
}

fn literal_eq_by_truthiness(literal: TruthSensitiveLiteral, truthy: bool) -> Option<bool> {
    match literal {
        TruthSensitiveLiteral::Nil | TruthSensitiveLiteral::False => truthy.then_some(false),
        TruthSensitiveLiteral::True => (!truthy).then_some(false),
    }
}

fn truth_fact_expr_key(expr: &HirExpr) -> Option<TruthFactExprKey> {
    match expr {
        HirExpr::Nil => Some(TruthFactExprKey::Nil),
        HirExpr::Boolean(value) => Some(TruthFactExprKey::Boolean(*value)),
        HirExpr::Integer(value) => Some(TruthFactExprKey::Integer(*value)),
        HirExpr::Number(value) => Some(TruthFactExprKey::Number(value.to_bits())),
        HirExpr::String(value) => Some(TruthFactExprKey::String(value.clone())),
        HirExpr::Int64(value) => Some(TruthFactExprKey::Int64(*value)),
        HirExpr::UInt64(value) => Some(TruthFactExprKey::UInt64(*value)),
        HirExpr::Complex { real, imag } => Some(TruthFactExprKey::Complex {
            real_bits: real.to_bits(),
            imag_bits: imag.to_bits(),
        }),
        HirExpr::ParamRef(param) => Some(TruthFactExprKey::Param(param.index())),
        HirExpr::LocalRef(local) => Some(TruthFactExprKey::Local(local.index())),
        HirExpr::UpvalueRef(upvalue) => Some(TruthFactExprKey::Upvalue(upvalue.index())),
        HirExpr::TempRef(temp) => Some(TruthFactExprKey::Temp(temp.index())),
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => Some(TruthFactExprKey::Not(
            Box::new(truth_fact_expr_key(&unary.expr)?),
        )),
        HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::LogicalAnd(_)
        | HirExpr::LogicalOr(_)
        | HirExpr::Decision(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => None,
    }
}

fn resolve_target_for_parent(
    replacements: &[Option<ResolvedDecisionTarget>],
    target: &HirDecisionTarget,
) -> HirDecisionTarget {
    match target {
        HirDecisionTarget::Node(node_ref) => {
            if let Some(replacement) = &replacements[node_ref.index()] {
                replacement_as_target(replacement)
            } else {
                HirDecisionTarget::Node(*node_ref)
            }
        }
        HirDecisionTarget::CurrentValue => HirDecisionTarget::CurrentValue,
        HirDecisionTarget::Expr(expr) => HirDecisionTarget::Expr(expr.clone()),
    }
}

fn resolve_target_in_node_context(
    replacements: &[Option<ResolvedDecisionTarget>],
    node: &HirDecisionNode,
    target: &HirDecisionTarget,
) -> ResolvedDecisionTarget {
    match target {
        HirDecisionTarget::Node(node_ref) => replacements[node_ref.index()]
            .clone()
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
    let child = &nodes[child_ref.index()];
    let branch = if truthy { &child.truthy } else { &child.falsy };
    replacement_as_target(&resolve_target_in_node_context(replacements, child, branch))
}

fn replacement_as_target(target: &ResolvedDecisionTarget) -> HirDecisionTarget {
    match target {
        ResolvedDecisionTarget::Node(node_ref) => HirDecisionTarget::Node(*node_ref),
        ResolvedDecisionTarget::Expr(expr) => HirDecisionTarget::Expr(expr.clone()),
    }
}

fn rebuild_decision(entry: HirDecisionNodeRef, nodes: &[HirDecisionNode]) -> HirDecisionExpr {
    let mut reachable = Vec::new();
    let mut visited = BTreeSet::new();
    let mut worklist = VecDeque::from([entry]);

    while let Some(node_ref) = worklist.pop_front() {
        if !visited.insert(node_ref) {
            continue;
        }
        reachable.push(node_ref);

        let node = &nodes[node_ref.index()];
        for target in [&node.truthy, &node.falsy] {
            if let HirDecisionTarget::Node(next_ref) = target {
                worklist.push_back(*next_ref);
            }
        }
    }

    let remap = reachable
        .iter()
        .enumerate()
        .map(|(index, node_ref)| (*node_ref, HirDecisionNodeRef(index)))
        .collect::<BTreeMap<_, _>>();

    let rebuilt_nodes = reachable
        .into_iter()
        .map(|old_ref| {
            let old = &nodes[old_ref.index()];
            HirDecisionNode {
                id: remap[&old_ref],
                test: old.test.clone(),
                truthy: remap_target(&old.truthy, &remap),
                falsy: remap_target(&old.falsy, &remap),
            }
        })
        .collect::<Vec<_>>();

    HirDecisionExpr {
        entry: remap[&entry],
        nodes: rebuilt_nodes,
    }
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
        let mut memo = BTreeMap::new();
        collapse_value_node(decision, decision.entry, &mut memo)
            .or_else(|| synthesize::synthesize_value_decision_expr(decision))
    }
}

fn collapse_value_node(
    decision: &HirDecisionExpr,
    node_ref: HirDecisionNodeRef,
    memo: &mut BTreeMap<HirDecisionNodeRef, HirExpr>,
) -> Option<HirExpr> {
    if let Some(expr) = memo.get(&node_ref) {
        return Some(expr.clone());
    }

    let node = decision.nodes.get(node_ref.index())?;
    let truthy = collapse_value_target(decision, &node.truthy, memo)?;
    let falsy = collapse_value_target(decision, &node.falsy, memo)?;
    let expr = combine_value_expr(node.test.clone(), truthy, falsy)?;
    memo.insert(node_ref, expr.clone());
    Some(expr)
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
            } else {
                None
            }
        }
    }
}

fn normalize_collapsed_target(
    subject: &HirExpr,
    target: CollapsedValueTarget,
) -> CollapsedValueTarget {
    match target {
        CollapsedValueTarget::Expr(expr) if &expr == subject => CollapsedValueTarget::CurrentValue,
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

    let node = decision.nodes.get(node_ref.index())?;
    let truthy = collapse_condition_target(decision, node, &node.truthy, memo)?;
    let falsy = collapse_condition_target(decision, node, &node.falsy, memo)?;
    let expr = combine_condition_expr(node.test.clone(), truthy, falsy);
    memo.insert(node_ref, expr.clone());
    Some(expr)
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

fn combine_condition_expr(subject: HirExpr, truthy: HirExpr, falsy: HirExpr) -> HirExpr {
    if is_true(&truthy) && is_false(&falsy) {
        return subject;
    }
    if is_true(&truthy) {
        return logical_or(subject, falsy);
    }
    if is_false(&falsy) {
        return logical_and(subject, truthy);
    }
    if is_false(&truthy) && is_true(&falsy) {
        return subject.negate();
    }
    if is_false(&truthy) {
        return logical_and(subject.negate(), falsy);
    }
    if is_true(&falsy) {
        return logical_or(subject.negate(), truthy);
    }

    logical_or(
        logical_and(subject.clone(), truthy),
        logical_and(subject.negate(), falsy),
    )
}

fn is_true(expr: &HirExpr) -> bool {
    matches!(expr, HirExpr::Boolean(true))
}

fn is_false(expr: &HirExpr) -> bool {
    matches!(expr, HirExpr::Boolean(false))
}

pub(in crate::hir) fn decision_has_shared_nodes(decision: &HirDecisionExpr) -> bool {
    let mut incoming = vec![0usize; decision.nodes.len()];
    incoming[decision.entry.index()] += 1;

    for node in &decision.nodes {
        for target in [&node.truthy, &node.falsy] {
            if let HirDecisionTarget::Node(node_ref) = target {
                incoming[node_ref.index()] += 1;
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
            match states[next_ref.index()] {
                VisitState::Done => {}
                VisitState::Visiting => return true,
                VisitState::Unvisited => stack.push((*next_ref, false)),
            }
        }
    }

    false
}

#[cfg(test)]
mod tests;
