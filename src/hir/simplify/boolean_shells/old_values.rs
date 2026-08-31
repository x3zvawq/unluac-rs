//! 证明 dead local boolean shell 入口的旧值不承载可观察的 GC 生命周期。
//!
//! 分析只消费当前 HIR 已有的结构化控制流与 trusted home。每个状态分别跟踪候选 local
//! 与 raw home 的 `GC-inert / 可承载资源 / 证明不完整`；分支合流保留任一路径上的资源
//! 可能，循环对回边求有限不动点。
//! 分析阶段只记录完整语句路径，验证结束后才一次性应用删除，避免边改边算让 reaching
//! value 漂移。label/goto 与 residual 仍由各自 owner 维护，本分析不在线性 HIR 上猜 CFG。
//! 值是否 GC-inert 由外层传入的目标方言安全上下文判定，避免 reaching class 与删除证明漂移。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirLValue, HirLocalDecl, HirProto, HirStmt, LocalId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::{
    BindingRelation, BooleanShellFacts, DeadShellOldValueFacts, OldValueClass, home_relation,
};
use crate::hir::simplify::expr_facts::expr_truthiness;
use crate::hir::simplify::visit::{self, HirVisitor};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum PathComponent {
    Stmt(usize),
    Then,
    Else,
    Body,
}

type StmtPath = Vec<PathComponent>;

#[derive(Default)]
pub(super) struct DeadShellPlan {
    removable: BTreeSet<StmtPath>,
    not_removable: BTreeSet<StmtPath>,
}

impl DeadShellPlan {
    pub(super) fn collect(
        proto: &HirProto,
        facts: &BooleanShellFacts,
        promotion_facts: &ProtoPromotionFacts,
        safety: HirExprSafety,
    ) -> Self {
        let mut boundary = AnalysisBoundary::default();
        visit::visit_proto(proto, &mut boundary);
        if boundary.unstructured_control {
            // 分析停用[LayerBoundary]：label/goto 的非局部 predecessor 由 Structure island/branch-control owner 维护；相邻空声明的局部证明仍由外层 fallback 消费。
            return Self::default();
        }
        if boundary.residual_expr {
            // 分析停用[LayerBoundary]：Decision/Unresolved 的路径和值域由 decision/dead-unresolved owner 收敛；本分析不把 residual 当成普通 reaching value。
            return Self::default();
        }

        let mut candidates = CandidateValues {
            locals: BTreeSet::new(),
            homes: BTreeSet::new(),
            promotion_facts,
        };
        visit::visit_proto(proto, &mut candidates);
        if candidates.locals.is_empty() && candidates.homes.is_empty() {
            return Self::default();
        }

        let parameter_homes = proto
            .params
            .iter()
            .map(|param| HomeSlotKey::new(param.index(), 0))
            .collect::<BTreeSet<_>>();
        let initial_state = OldValueState::initial(&candidates, &parameter_homes);
        let mut analyzer = OldValueAnalyzer {
            facts,
            promotion_facts,
            safety,
            candidate_locals: candidates.locals,
            candidate_homes: candidates.homes,
            plan: Self::default(),
        };
        let _ = analyzer.analyze_block(&proto.body, &[], Some(initial_state));
        analyzer.plan
    }

    pub(super) fn apply(self, block: &mut HirBlock) -> bool {
        if self.removable.is_empty() {
            return false;
        }
        apply_block_plan(block, &[], &self.removable);
        true
    }
}

#[derive(Default)]
struct AnalysisBoundary {
    unstructured_control: bool,
    residual_expr: bool,
}

impl HirVisitor for AnalysisBoundary {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.unstructured_control |= matches!(stmt, HirStmt::Goto(_) | HirStmt::Label(_));
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        self.residual_expr |= matches!(expr, HirExpr::Decision(_) | HirExpr::Unresolved(_));
    }
}

struct CandidateValues<'a> {
    locals: BTreeSet<LocalId>,
    homes: BTreeSet<HomeSlotKey>,
    promotion_facts: &'a ProtoPromotionFacts,
}

impl HirVisitor for CandidateValues<'_> {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        let HirStmt::If(if_stmt) = stmt else {
            return;
        };
        let Some(else_block) = &if_stmt.else_block else {
            return;
        };
        let Some((then_target, _)) = super::single_fixed_assign_pattern(&if_stmt.then_block) else {
            return;
        };
        let Some((else_target, _)) = super::single_fixed_assign_pattern(else_block) else {
            return;
        };
        if let HirLValue::Local(local) = then_target {
            self.locals.insert(*local);
        }
        if let HirLValue::Temp(temp) = then_target
            && let Some(home) = self.promotion_facts.home_slot(*temp)
        {
            self.homes.insert(home);
        }
        if let HirLValue::Local(local) = else_target {
            self.locals.insert(*local);
        }
        if let HirLValue::Temp(temp) = else_target
            && let Some(home) = self.promotion_facts.home_slot(*temp)
        {
            self.homes.insert(home);
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct OldValueState {
    local_classes: BTreeMap<LocalId, OldValueClass>,
    home_classes: BTreeMap<HomeSlotKey, OldValueClass>,
}

impl OldValueState {
    fn initial(candidates: &CandidateValues<'_>, parameter_homes: &BTreeSet<HomeSlotKey>) -> Self {
        Self {
            local_classes: candidates
                .locals
                .iter()
                .copied()
                .map(|local| {
                    let class = candidates
                        .promotion_facts
                        .local_home_slot(local)
                        .filter(|home| parameter_homes.contains(home))
                        .map_or(OldValueClass::ProofIncomplete, |_| {
                            OldValueClass::MayCarryResource
                        });
                    (local, class)
                })
                .collect(),
            home_classes: candidates
                .homes
                .iter()
                .copied()
                .map(|home| {
                    let class = if parameter_homes.contains(&home) {
                        OldValueClass::MayCarryResource
                    } else {
                        OldValueClass::ProofIncomplete
                    };
                    (home, class)
                })
                .collect(),
        }
    }

    fn as_facts(&self) -> DeadShellOldValueFacts {
        DeadShellOldValueFacts {
            locals: self.local_classes.clone(),
            homes: self.home_classes.clone(),
        }
    }

    fn merge_possible_local_write(&mut self, local: LocalId, written: OldValueClass) {
        let current = self
            .local_classes
            .entry(local)
            .or_insert(OldValueClass::ProofIncomplete);
        *current = join_value_classes(*current, written);
    }

    fn merge_possible_home_write(&mut self, home: HomeSlotKey, written: OldValueClass) {
        let current = self
            .home_classes
            .entry(home)
            .or_insert(OldValueClass::ProofIncomplete);
        *current = join_value_classes(*current, written);
    }

    fn obscure_physical_homes(mut self) -> Self {
        self.home_classes
            .values_mut()
            .for_each(|class| *class = OldValueClass::MayCarryResource);
        self
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct InertFlow {
    fallthrough: Option<OldValueState>,
    breaks: Option<OldValueState>,
    continues: Option<OldValueState>,
}

impl InertFlow {
    fn fallthrough(state: Option<OldValueState>) -> Self {
        Self {
            fallthrough: state,
            ..Self::default()
        }
    }
}

struct OldValueAnalyzer<'a> {
    facts: &'a BooleanShellFacts,
    promotion_facts: &'a ProtoPromotionFacts,
    safety: HirExprSafety,
    candidate_locals: BTreeSet<LocalId>,
    candidate_homes: BTreeSet<HomeSlotKey>,
    plan: DeadShellPlan,
}

impl OldValueAnalyzer<'_> {
    fn analyze_block(
        &mut self,
        block: &HirBlock,
        prefix: &[PathComponent],
        mut state: Option<OldValueState>,
    ) -> InertFlow {
        let mut breaks = None;
        let mut continues = None;
        for (index, stmt) in block.stmts.iter().enumerate() {
            if state.is_none() {
                break;
            }
            let mut path = prefix.to_vec();
            path.push(PathComponent::Stmt(index));
            let flow = self.analyze_stmt(stmt, &path, state.expect("reachable state checked"));
            state = flow.fallthrough;
            breaks = join_optional_states(breaks, flow.breaks);
            continues = join_optional_states(continues, flow.continues);
        }
        InertFlow {
            fallthrough: state,
            breaks,
            continues,
        }
    }

    fn analyze_stmt(&mut self, stmt: &HirStmt, path: &StmtPath, state: OldValueState) -> InertFlow {
        match stmt {
            HirStmt::LocalDecl(decl) => {
                InertFlow::fallthrough(Some(self.apply_local_decl(decl, state)))
            }
            HirStmt::Assign(assign) => {
                InertFlow::fallthrough(Some(self.apply_assignment(assign, state)))
            }
            HirStmt::If(if_stmt) => {
                let old_values = state.as_facts();
                let removable = super::removable_dead_materialization_shell(
                    stmt,
                    self.facts,
                    None,
                    &old_values,
                    self.safety,
                );
                if shell_has_old_value_target(stmt, self.promotion_facts) {
                    self.plan.observe(path, removable);
                }

                let mut then_prefix = path.clone();
                then_prefix.push(PathComponent::Then);
                let then_flow = if expr_truthiness(&if_stmt.cond, self.safety) == Some(false) {
                    InertFlow::default()
                } else {
                    self.analyze_block(&if_stmt.then_block, &then_prefix, Some(state.clone()))
                };
                let else_flow = if expr_truthiness(&if_stmt.cond, self.safety) == Some(true) {
                    InertFlow::default()
                } else if let Some(else_block) = &if_stmt.else_block {
                    let mut else_prefix = path.clone();
                    else_prefix.push(PathComponent::Else);
                    self.analyze_block(else_block, &else_prefix, Some(state))
                } else {
                    InertFlow::fallthrough(Some(state))
                };
                join_flows(then_flow, else_flow)
            }
            HirStmt::Block(block) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                self.analyze_block(block, &body_prefix, Some(state))
            }
            HirStmt::While(while_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                self.analyze_while(&while_stmt.body, &while_stmt.cond, &body_prefix, state)
            }
            HirStmt::Repeat(repeat_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                self.analyze_repeat(&repeat_stmt.body, &repeat_stmt.cond, &body_prefix, state)
            }
            HirStmt::NumericFor(for_stmt) => {
                let zero_exit = state.clone();
                let body_state =
                    self.write_local_binding(for_stmt.binding, OldValueClass::GcInert, state);
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                self.analyze_zero_or_more(
                    &for_stmt.body,
                    &body_prefix,
                    zero_exit,
                    body_state,
                    &[(for_stmt.binding, OldValueClass::GcInert)],
                )
            }
            HirStmt::GenericFor(for_stmt) => {
                let zero_exit = state.clone();
                let mut body_state = state;
                let binding_values = for_stmt
                    .bindings
                    .iter()
                    .copied()
                    .map(|binding| (binding, OldValueClass::MayCarryResource))
                    .collect::<Vec<_>>();
                for (binding, value_class) in &binding_values {
                    body_state = self.write_local_binding(*binding, *value_class, body_state);
                }
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                self.analyze_zero_or_more(
                    &for_stmt.body,
                    &body_prefix,
                    zero_exit,
                    body_state,
                    &binding_values,
                )
            }
            HirStmt::Return(_) | HirStmt::Goto(_) => InertFlow::default(),
            HirStmt::Break => InertFlow {
                breaks: Some(state),
                ..InertFlow::default()
            },
            HirStmt::Continue => InertFlow {
                continues: Some(state),
                ..InertFlow::default()
            },
            HirStmt::GlobalDecl(_) => {
                // The syntax node hides call-result/probe writes to raw VM slots, so home facts
                // cannot cross it. Lexical locals remain distinct bindings; reference-captured
                // locals are already rejected by the enclosing boolean-shell facts.
                InertFlow::fallthrough(Some(state.obscure_physical_homes()))
            }
            HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Label(_) => InertFlow::fallthrough(Some(state)),
        }
    }

    fn analyze_while(
        &mut self,
        body: &HirBlock,
        condition: &HirExpr,
        body_prefix: &[PathComponent],
        incoming: OldValueState,
    ) -> InertFlow {
        let truthiness = expr_truthiness(condition, self.safety);
        let mut entries = incoming.clone();
        let mut break_exits = None;
        loop {
            let body_flow = if truthiness == Some(false) {
                InertFlow::default()
            } else {
                self.analyze_block(body, body_prefix, Some(entries.clone()))
            };
            let back_edges = join_optional_states(body_flow.fallthrough, body_flow.continues);
            let next_entries = join_optional_states(Some(incoming.clone()), back_edges)
                .expect("loop entry always includes incoming state");
            let next_break_exits = join_optional_states(break_exits.clone(), body_flow.breaks);
            if next_entries == entries && next_break_exits == break_exits {
                let normal_exits = (truthiness != Some(true)).then_some(entries);
                return InertFlow::fallthrough(join_optional_states(normal_exits, break_exits));
            }
            entries = next_entries;
            break_exits = next_break_exits;
        }
    }

    fn analyze_repeat(
        &mut self,
        body: &HirBlock,
        condition: &HirExpr,
        body_prefix: &[PathComponent],
        incoming: OldValueState,
    ) -> InertFlow {
        let truthiness = expr_truthiness(condition, self.safety);
        let mut entries = incoming.clone();
        let mut break_exits = None;
        loop {
            let body_flow = self.analyze_block(body, body_prefix, Some(entries.clone()));
            let condition_states = join_optional_states(body_flow.fallthrough, body_flow.continues);
            let back_edges = if truthiness == Some(true) {
                None
            } else {
                condition_states.clone()
            };
            let next_entries = join_optional_states(Some(incoming.clone()), back_edges)
                .expect("repeat entry always includes incoming state");
            let next_break_exits = join_optional_states(break_exits.clone(), body_flow.breaks);
            if next_entries == entries && next_break_exits == break_exits {
                let normal_exits = if truthiness == Some(false) {
                    None
                } else {
                    condition_states
                };
                return InertFlow::fallthrough(join_optional_states(normal_exits, break_exits));
            }
            entries = next_entries;
            break_exits = next_break_exits;
        }
    }

    fn analyze_zero_or_more(
        &mut self,
        body: &HirBlock,
        body_prefix: &[PathComponent],
        zero_exit: OldValueState,
        initial_body_entry: OldValueState,
        bindings: &[(LocalId, OldValueClass)],
    ) -> InertFlow {
        let mut entries = initial_body_entry.clone();
        let mut break_exits = None;
        loop {
            let body_flow = self.analyze_block(body, body_prefix, Some(entries.clone()));
            let iteration_exits = join_optional_states(body_flow.fallthrough, body_flow.continues);
            let back_edges = iteration_exits.clone().map(|mut state| {
                for (binding, value_class) in bindings {
                    state = self.write_local_binding(*binding, *value_class, state);
                }
                state
            });
            let next_entries = join_optional_states(Some(initial_body_entry.clone()), back_edges)
                .expect("for body entry always includes first iteration");
            let next_break_exits = join_optional_states(break_exits.clone(), body_flow.breaks);
            if next_entries == entries && next_break_exits == break_exits {
                return InertFlow::fallthrough(join_optional_states(
                    join_optional_states(Some(zero_exit), iteration_exits),
                    break_exits,
                ));
            }
            entries = next_entries;
            break_exits = next_break_exits;
        }
    }

    fn apply_assignment(&self, assign: &HirAssign, mut state: OldValueState) -> OldValueState {
        for (index, target) in assign.targets.iter().enumerate() {
            state = self.write_target(
                target,
                assigned_value_class(assign, index, self.safety),
                state,
            );
        }
        state
    }

    fn apply_local_decl(&self, decl: &HirLocalDecl, mut state: OldValueState) -> OldValueState {
        for (index, binding) in decl.bindings.iter().enumerate() {
            state = self.write_local_binding(
                *binding,
                declared_value_class(decl, index, self.safety),
                state,
            );
        }
        state
    }

    fn write_local_binding(
        &self,
        binding: LocalId,
        value_class: OldValueClass,
        state: OldValueState,
    ) -> OldValueState {
        self.write_target(&HirLValue::Local(binding), value_class, state)
    }

    fn write_target(
        &self,
        target: &HirLValue,
        value_class: OldValueClass,
        mut state: OldValueState,
    ) -> OldValueState {
        for candidate in &self.candidate_locals {
            match self.local_binding_relation(target, *candidate) {
                BindingRelation::None => {}
                BindingRelation::Possible => {
                    // `Possible` 表示该写可能命中 candidate，也可能完全不命中；后态必须
                    // 合流“保留旧值”和“写入新值”，不能用 ProofIncomplete 覆盖两端事实。
                    state.merge_possible_local_write(*candidate, value_class);
                }
                BindingRelation::Definite => {
                    state.local_classes.insert(*candidate, value_class);
                }
            }
        }
        for candidate in &self.candidate_homes {
            match self.home_binding_relation(target, *candidate) {
                BindingRelation::None => {}
                BindingRelation::Possible => {
                    state.merge_possible_home_write(*candidate, value_class);
                }
                BindingRelation::Definite => {
                    state.home_classes.insert(*candidate, value_class);
                }
            }
        }
        state
    }

    fn local_binding_relation(&self, target: &HirLValue, candidate: LocalId) -> BindingRelation {
        let candidate_home = self.promotion_facts.trusted_local_home_slot(candidate);
        match target {
            HirLValue::Local(local) if *local == candidate => BindingRelation::Definite,
            HirLValue::Local(local) => home_relation(
                candidate_home,
                self.promotion_facts.trusted_local_home_slot(*local),
            ),
            HirLValue::Param(param) => home_relation(
                candidate_home,
                self.promotion_facts.trusted_param_home_slot(*param),
            ),
            HirLValue::Temp(temp) => home_relation(
                candidate_home,
                self.promotion_facts.trusted_temp_home_slot(*temp),
            ),
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => {
                BindingRelation::None
            }
        }
    }

    fn home_binding_relation(&self, target: &HirLValue, candidate: HomeSlotKey) -> BindingRelation {
        match target {
            HirLValue::Temp(temp) => match self.promotion_facts.home_slot(*temp) {
                Some(home) if home == candidate => BindingRelation::Definite,
                Some(_) => BindingRelation::None,
                None => BindingRelation::Possible,
            },
            HirLValue::Param(param) => home_relation(
                Some(candidate),
                self.promotion_facts.trusted_param_home_slot(*param),
            ),
            HirLValue::Local(local) => home_relation(
                Some(candidate),
                self.promotion_facts.trusted_local_home_slot(*local),
            ),
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => {
                BindingRelation::None
            }
        }
    }
}

impl DeadShellPlan {
    fn observe(&mut self, path: &StmtPath, removable: bool) {
        if removable && !self.not_removable.contains(path) {
            self.removable.insert(path.clone());
        } else if !removable {
            self.removable.remove(path);
            self.not_removable.insert(path.clone());
        }
    }
}

fn shell_has_old_value_target(stmt: &HirStmt, facts: &ProtoPromotionFacts) -> bool {
    let HirStmt::If(if_stmt) = stmt else {
        return false;
    };
    let Some(else_block) = &if_stmt.else_block else {
        return false;
    };
    let Some((then_target, _)) = super::single_fixed_assign_pattern(&if_stmt.then_block) else {
        return false;
    };
    let Some((else_target, _)) = super::single_fixed_assign_pattern(else_block) else {
        return false;
    };
    matches!(then_target, HirLValue::Local(_))
        || matches!(else_target, HirLValue::Local(_))
        || matches!(then_target, HirLValue::Temp(temp) if facts.home_slot(*temp).is_some())
        || matches!(else_target, HirLValue::Temp(temp) if facts.home_slot(*temp).is_some())
}

fn assigned_value_class(
    assign: &HirAssign,
    target_index: usize,
    safety: HirExprSafety,
) -> OldValueClass {
    value_at_class(
        &assign.values.fixed,
        assign.values.tail.is_some(),
        target_index,
        safety,
    )
}

fn declared_value_class(
    decl: &HirLocalDecl,
    binding_index: usize,
    safety: HirExprSafety,
) -> OldValueClass {
    value_at_class(
        &decl.values.fixed,
        decl.values.tail.is_some(),
        binding_index,
        safety,
    )
}

fn value_at_class(
    fixed: &[HirExpr],
    has_tail: bool,
    index: usize,
    safety: HirExprSafety,
) -> OldValueClass {
    let Some(value) = fixed.get(index) else {
        return if has_tail {
            OldValueClass::MayCarryResource
        } else {
            OldValueClass::GcInert
        };
    };
    if safety.result_is_gc_inert(value) {
        return OldValueClass::GcInert;
    }
    match value {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
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
        | HirExpr::Unresolved(_) => OldValueClass::MayCarryResource,
    }
}

fn join_states(mut left: OldValueState, right: OldValueState) -> OldValueState {
    join_class_maps(&mut left.local_classes, right.local_classes);
    join_class_maps(&mut left.home_classes, right.home_classes);
    left
}

fn join_class_maps<K: Ord>(
    left: &mut BTreeMap<K, OldValueClass>,
    right: BTreeMap<K, OldValueClass>,
) {
    for (binding, left_class) in left.iter_mut() {
        let right_class = right
            .get(binding)
            .copied()
            .unwrap_or(OldValueClass::ProofIncomplete);
        *left_class = join_value_classes(*left_class, right_class);
    }
    for (binding, right_class) in right {
        left.entry(binding)
            .or_insert_with(|| join_value_classes(OldValueClass::ProofIncomplete, right_class));
    }
}

fn join_value_classes(left: OldValueClass, right: OldValueClass) -> OldValueClass {
    match (left, right) {
        (OldValueClass::GcInert, OldValueClass::GcInert) => OldValueClass::GcInert,
        (OldValueClass::MayCarryResource, _) | (_, OldValueClass::MayCarryResource) => {
            OldValueClass::MayCarryResource
        }
        (OldValueClass::ProofIncomplete, _) | (_, OldValueClass::ProofIncomplete) => {
            OldValueClass::ProofIncomplete
        }
    }
}

fn join_optional_states(
    left: Option<OldValueState>,
    right: Option<OldValueState>,
) -> Option<OldValueState> {
    match (left, right) {
        (Some(left), Some(right)) => Some(join_states(left, right)),
        (Some(state), None) | (None, Some(state)) => Some(state),
        (None, None) => None,
    }
}

fn join_flows(left: InertFlow, right: InertFlow) -> InertFlow {
    InertFlow {
        fallthrough: join_optional_states(left.fallthrough, right.fallthrough),
        breaks: join_optional_states(left.breaks, right.breaks),
        continues: join_optional_states(left.continues, right.continues),
    }
}

fn apply_block_plan(block: &mut HirBlock, prefix: &[PathComponent], plan: &BTreeSet<StmtPath>) {
    let mut remove = Vec::new();
    for (index, stmt) in block.stmts.iter_mut().enumerate() {
        let mut path = prefix.to_vec();
        path.push(PathComponent::Stmt(index));
        match stmt {
            HirStmt::If(if_stmt) => {
                let mut then_prefix = path.clone();
                then_prefix.push(PathComponent::Then);
                apply_block_plan(&mut if_stmt.then_block, &then_prefix, plan);
                if let Some(else_block) = &mut if_stmt.else_block {
                    let mut else_prefix = path.clone();
                    else_prefix.push(PathComponent::Else);
                    apply_block_plan(else_block, &else_prefix, plan);
                }
            }
            HirStmt::While(while_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                apply_block_plan(&mut while_stmt.body, &body_prefix, plan);
            }
            HirStmt::Repeat(repeat_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                apply_block_plan(&mut repeat_stmt.body, &body_prefix, plan);
            }
            HirStmt::NumericFor(for_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                apply_block_plan(&mut for_stmt.body, &body_prefix, plan);
            }
            HirStmt::GenericFor(for_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                apply_block_plan(&mut for_stmt.body, &body_prefix, plan);
            }
            HirStmt::Block(nested) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                apply_block_plan(nested, &body_prefix, plan);
            }
            HirStmt::LocalDecl(_)
            | HirStmt::GlobalDecl(_)
            | HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Return(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => {}
        }
        if plan.contains(&path) {
            remove.push(index);
        }
    }
    for index in remove.into_iter().rev() {
        block.stmts.remove(index);
    }
}
