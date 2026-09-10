//! 稳定词法绑定的路径 truthiness 专门化。
//!
//! Param/Local 必须在整个 proto 内没有写入、for binder 或 ByReference capture；绑定稳定性
//! 由本模块证明，控制流、条件边和不动点调度由共享 HIR CFG 持有。must-fact 合流只保留
//! 所有可达入边共同成立的真假事实；矛盾条件边不进入合流，循环后续入边可削弱既有事实。
//! 例如 `if flag then return end; if flag then body end` 的第二个条件可变为 false，
//! goto、break 和 continue 通过同一 topology 获得相同证明，不重建独立的 label 传播算法。
//!
//! 收敛后只替换条件骨架，不进入值语境，不把 truthy 原值替换成布尔结果。候选表达式地址
//! 仅关联同一次 HIR 快照的查询与原地改写，不解引用地址；子块完成改写后才截断不可达尾部，
//! 不移动后续仍待查询的语句。源码身份、控制入口和诊断仍由 DiscardBoundaryFacts 决定保留。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirBlock, HirExpr, HirLValue, HirLocalDecl, HirStmt, HirUnaryOpKind, LocalId, ParamId,
};
use crate::hir::expr_safety::HirExprSafety;

use super::super::expr_facts::expr_truthiness;
use super::super::lexical_cfg::{FlowRefinement, HirFlowGraph, HirFlowNodeKind};
use super::super::logical_simplify::{
    simplify_condition_truthiness_shape_with_safety, simplify_logical_shape_with_safety,
};
use super::super::mention::stmts_reference_captured_bindings;
use super::super::walk::{HirRewritePass, for_each_nested_block_mut, rewrite_block};
use super::DiscardBoundaryFacts;
use crate::hir::visit::{HirVisitor, visit_block};

#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
enum StableBinding {
    Param(ParamId),
    Local(LocalId),
}

fn stable_binding(expr: &HirExpr) -> Option<StableBinding> {
    match expr {
        HirExpr::ParamRef(param) => Some(StableBinding::Param(*param)),
        HirExpr::LocalRef(local) => Some(StableBinding::Local(*local)),
        _ => None,
    }
}

#[derive(Clone, Default, Eq, PartialEq)]
struct PathFacts(BTreeMap<StableBinding, bool>);

impl PathFacts {
    fn insert(&mut self, binding: StableBinding, truthy: bool) -> bool {
        match self.0.get(&binding) {
            Some(current) => *current == truthy,
            None => {
                self.0.insert(binding, truthy);
                true
            }
        }
    }

    fn get(&self, binding: StableBinding) -> Option<bool> {
        self.0.get(&binding).copied()
    }

    fn remove_local(&mut self, local: LocalId) {
        self.0.remove(&StableBinding::Local(local));
    }

    fn intersect(&mut self, incoming: &Self) -> bool {
        let previous_len = self.0.len();
        self.0
            .retain(|binding, truthy| incoming.get(*binding) == Some(*truthy));
        self.0.len() != previous_len
    }
}

struct StableBindingIndex {
    candidates: BTreeSet<StableBinding>,
    unstable: BTreeSet<StableBinding>,
    safety: HirExprSafety,
}

impl StableBindingIndex {
    fn new(body: &HirBlock, safety: HirExprSafety) -> Self {
        let mut index = Self {
            candidates: BTreeSet::new(),
            unstable: BTreeSet::new(),
            safety,
        };
        visit_block(body, &mut index);

        let captured = stmts_reference_captured_bindings(&body.stmts);
        index
            .unstable
            .extend(captured.params.into_iter().map(StableBinding::Param));
        index
            .unstable
            .extend(captured.locals.into_iter().map(StableBinding::Local));
        index
    }

    fn contains(&self, binding: StableBinding) -> bool {
        self.candidates.contains(&binding) && !self.unstable.contains(&binding)
    }

    fn track_condition(&mut self, expr: &HirExpr) {
        if let Some(binding) = stable_binding(expr) {
            self.candidates.insert(binding);
            return;
        }

        match expr {
            HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
                self.track_condition(&unary.expr);
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                self.track_condition(&logical.lhs);
                self.track_condition(&logical.rhs);
            }
            _ => {}
        }
    }
}

impl HirVisitor for StableBindingIndex {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::If(if_stmt) => self.track_condition(&if_stmt.cond),
            HirStmt::While(while_stmt) => self.track_condition(&while_stmt.cond),
            HirStmt::Repeat(repeat_stmt) => self.track_condition(&repeat_stmt.cond),
            HirStmt::NumericFor(numeric_for) => {
                self.unstable
                    .insert(StableBinding::Local(numeric_for.binding));
            }
            HirStmt::GenericFor(generic_for) => {
                self.unstable.extend(
                    generic_for
                        .bindings
                        .iter()
                        .copied()
                        .map(StableBinding::Local),
                );
            }
            _ => {}
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        let binding = match lvalue {
            HirLValue::Param(param) => Some(StableBinding::Param(*param)),
            HirLValue::Local(local) => Some(StableBinding::Local(*local)),
            HirLValue::Temp(_)
            | HirLValue::Upvalue(_)
            | HirLValue::Global(_)
            | HirLValue::TableAccess(_) => None,
        };
        self.unstable.extend(binding);
    }
}

pub(super) fn specialize_stable_path_conditions(
    body: &mut HirBlock,
    discard_facts: &DiscardBoundaryFacts,
    safety: HirExprSafety,
) -> bool {
    let stable = StableBindingIndex::new(body, safety);
    let Ok(graph) = HirFlowGraph::for_proto(body, safety) else {
        // 候选拒绝[ProofIncomplete]：歧义 label 不能建立唯一控制流，不在消费者重猜入口。
        return false;
    };
    let candidates = graph.solve_forward(
        PathFacts::default(),
        PathFacts::intersect,
        |id, kind, facts| {
            if let HirFlowNodeKind::Stmt(HirStmt::LocalDecl(decl)) = kind {
                record_local_declaration(decl, facts, &stable);
            }
            let condition = graph.nodes()[id.index()].condition()?;
            let mut replacement = condition.clone();
            specialize_condition(&mut replacement, facts, &stable)
                .then_some((std::ptr::from_ref(condition), replacement))
        },
        |condition, truthy, facts| match facts_for_condition(facts, condition, truthy, &stable) {
            None => FlowRefinement::Unreachable,
            Some(refined) if refined == *facts => FlowRefinement::Unchanged,
            Some(refined) => FlowRefinement::Refined(refined),
        },
    );
    let mut replacements = BTreeMap::new();
    let mut live_stmts = BTreeSet::new();
    for (node, candidate) in graph.nodes().iter().zip(candidates) {
        if candidate.is_some()
            && let Some(stmt) = node.owner_stmt()
        {
            live_stmts.insert(std::ptr::from_ref(stmt));
        }
        if let Some(Some((condition, replacement))) = candidate {
            replacements.insert(condition, replacement);
        }
    }
    rewrite_block(
        body,
        &mut PathConditionRewrite {
            replacements,
            live_stmts,
            discard_facts,
        },
    )
}

struct PathConditionRewrite<'a, 'b> {
    replacements: BTreeMap<*const HirExpr, HirExpr>,
    live_stmts: BTreeSet<*const HirStmt>,
    discard_facts: &'a DiscardBoundaryFacts<'b>,
}

impl HirRewritePass for PathConditionRewrite<'_, '_> {
    const PRESERVES_GENERIC_FOR_INITIALIZER_TRANSACTION: bool = true;

    fn rewrite_stmt(&mut self, stmt: &mut HirStmt) -> bool {
        // Block 没有独立求值事件；repeat 的条件也可能被 body 的 return 绕过。
        // 后序只合并子树已经求出的可达性，不重新解释控制结构或传播抽象状态。
        let mut live_child = false;
        for_each_nested_block_mut(stmt, &mut |block| {
            live_child |= block
                .stmts
                .iter()
                .any(|stmt| self.live_stmts.contains(&std::ptr::from_ref(stmt)));
        });
        if live_child {
            self.live_stmts.insert(std::ptr::from_ref(stmt));
        }
        false
    }

    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let retained_len = block
            .stmts
            .iter()
            .rposition(|stmt| self.live_stmts.contains(&std::ptr::from_ref(stmt)))
            .map_or(0, |index| index + 1);
        if retained_len == block.stmts.len() {
            return false;
        }
        let boundary = self
            .discard_facts
            .stmts_boundary(&block.stmts[retained_len..]);
        if boundary.has_control_entry() {
            // 候选拒绝[SemanticBarrier:ControlFlow]：词法引用仍指向尾部，不能留下失配的 goto。
            return false;
        }
        if boundary.has_identity() || boundary.has_diagnostic() {
            // 候选拒绝[PolicyBoundary]：保留不可达 debug/PhysicalRoot/TBC 身份及 permissive 诊断。
            return false;
        }
        block.stmts.truncate(retained_len);
        true
    }

    fn rewrite_condition_expr(&mut self, expr: &mut HirExpr) -> bool {
        let Some(replacement) = self.replacements.remove(&std::ptr::from_ref(expr)) else {
            return false;
        };
        *expr = replacement;
        true
    }
}

fn record_local_declaration(
    local_decl: &HirLocalDecl,
    facts: &mut PathFacts,
    stable: &StableBindingIndex,
) {
    for local in &local_decl.bindings {
        facts.remove_local(*local);
    }
    let ([local], [value], None) = (
        local_decl.bindings.as_slice(),
        local_decl.values.fixed.as_slice(),
        &local_decl.values.tail,
    ) else {
        return;
    };
    let binding = StableBinding::Local(*local);
    if stable.contains(binding)
        && let Some(truthy) = expr_truthiness(value, stable.safety)
    {
        let inserted = facts.insert(binding, truthy);
        assert!(
            inserted,
            "new local declaration cannot contradict prior facts"
        );
    }
}

fn specialize_condition(
    expr: &mut HirExpr,
    facts: &PathFacts,
    stable: &StableBindingIndex,
) -> bool {
    if let Some(truthy) = stable_binding(expr)
        .filter(|binding| stable.contains(*binding))
        .and_then(|binding| facts.get(binding))
    {
        *expr = HirExpr::Boolean(truthy);
        return true;
    }

    let mut changed = match expr {
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            specialize_condition(&mut unary.expr, facts, stable)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            specialize_condition(&mut logical.lhs, facts, stable)
                | specialize_condition(&mut logical.rhs, facts, stable)
        }
        _ => false,
    };
    loop {
        let replacement = simplify_logical_shape_with_safety(expr, stable.safety)
            .or_else(|| simplify_condition_truthiness_shape_with_safety(expr, stable.safety));
        let Some(replacement) = replacement.filter(|replacement| replacement != expr) else {
            break;
        };
        *expr = replacement;
        changed = true;
    }
    changed
}

fn facts_for_condition(
    facts: &PathFacts,
    expr: &HirExpr,
    truthy: bool,
    stable: &StableBindingIndex,
) -> Option<PathFacts> {
    let mut extended = facts.clone();
    extend_condition_facts(&mut extended, expr, truthy, stable).then_some(extended)
}

fn extend_condition_facts(
    facts: &mut PathFacts,
    expr: &HirExpr,
    truthy: bool,
    stable: &StableBindingIndex,
) -> bool {
    if let Some(known) = expr_truthiness(expr, stable.safety) {
        return known == truthy;
    }

    if let Some(binding) = stable_binding(expr).filter(|binding| stable.contains(*binding)) {
        return facts.insert(binding, truthy);
    }

    match expr {
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            extend_condition_facts(facts, &unary.expr, !truthy, stable)
        }
        HirExpr::LogicalAnd(logical) if truthy => {
            extend_condition_facts(facts, &logical.lhs, true, stable)
                && extend_condition_facts(facts, &logical.rhs, true, stable)
        }
        HirExpr::LogicalOr(logical) if !truthy => {
            extend_condition_facts(facts, &logical.lhs, false, stable)
                && extend_condition_facts(facts, &logical.rhs, false, stable)
        }
        _ => true,
    }
}
