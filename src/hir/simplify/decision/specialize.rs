//! Decision DAG 的已知 test 结果专门化。
//!
//! 这个模块只做“沿路径传播已知稳定 test 结果”的图级优化：当某个 descendant 节点再次
//! 判断当前路径上已经确定 truthiness 的表达式时，直接选择对应分支，并用 interner
//! 合并专门化后相同的节点。它依赖父模块的 `ResolvedDecisionTarget` 表示和 target
//! 回写工具，但不负责常量裁剪、value/condition collapse 或最终 Decision 消除。
//!
//! 例子：
//! - 输入：`if a then if a then X else Y end else Z end`
//! - 输出：`if a then X else Z end`

use std::collections::BTreeMap;

use crate::hir::common::{
    HirBinaryOpKind, HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget,
    HirExpr, HirUnaryOpKind,
};

use super::super::expr_facts::expr_truthiness;
use super::{ResolvedDecisionTarget, replacement_as_target};

pub(super) fn specialize_decision_by_known_tests(
    decision: &HirDecisionExpr,
) -> Option<HirDecisionExpr> {
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

        let Some(node) = self.decision.nodes.get(node_ref.index()) else {
            return ResolvedDecisionTarget::Node(node_ref);
        };
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
