//! 证明 dead local boolean shell 入口的旧值不承载可观察的 GC 生命周期。
//!
//! 分析只消费当前 HIR 已有的结构化控制流与 trusted home。每个状态分别跟踪候选 local
//! 与 raw home 的 `GC-inert / 可承载资源 / 证明不完整`；分支合流保留任一路径上的资源
//! 可能，循环对回边求有限不动点。
//! 分析阶段只记录完整语句路径，验证结束后才一次性应用删除，避免边改边算让 reaching
//! value 漂移。同 block 单调 forward goto 可直接跳到唯一 label；含跨层或回边 goto 的
//! 区域按显式控制边界切成独立小岛，每个小岛从资源保守状态重新证明，避免一个非结构化
//! 区域停用整个 proto，也避免在线性 HIR 上猜 predecessor。
//! 值是否 GC-inert 由外层传入的目标方言安全上下文判定，避免 reaching class 与删除证明漂移。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirLValue, HirLocalDecl, HirProto, HirStmt, LocalId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::{
    BindingRelation, BooleanShellFacts, DeadShellOldValueFacts, OldValueClass,
    complete_possible_home_slots, possible_home_relation,
};
use crate::hir::simplify::expr_facts::expr_truthiness;
use crate::hir::simplify::temp_touch::stmt_contains_nested_nonlocal_control;
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
        let mut candidates = CandidateValues {
            locals: BTreeSet::new(),
            homes: BTreeSet::new(),
            entry_nil_homes: BTreeSet::new(),
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

fn forward_label_indices(block: &HirBlock) -> Option<BTreeMap<crate::hir::HirLabelId, usize>> {
    let mut labels = BTreeMap::new();
    for (index, stmt) in block.stmts.iter().enumerate() {
        let HirStmt::Label(label) = stmt else {
            continue;
        };
        if labels.insert(label.id, index).is_some() {
            return None;
        }
    }
    for (index, stmt) in block.stmts.iter().enumerate() {
        let HirStmt::Goto(goto) = stmt else {
            continue;
        };
        if labels
            .get(&goto.target)
            .is_none_or(|target| *target <= index)
        {
            return None;
        }
    }
    Some(labels)
}

fn forward_control_is_self_contained(block: &HirBlock) -> bool {
    forward_label_indices(block).is_some()
        && block.stmts.iter().all(|stmt| match stmt {
            HirStmt::If(if_stmt) => {
                forward_control_is_self_contained(&if_stmt.then_block)
                    && if_stmt
                        .else_block
                        .as_ref()
                        .is_none_or(forward_control_is_self_contained)
            }
            HirStmt::While(while_stmt) => forward_control_is_self_contained(&while_stmt.body),
            HirStmt::Repeat(repeat_stmt) => forward_control_is_self_contained(&repeat_stmt.body),
            HirStmt::NumericFor(for_stmt) => forward_control_is_self_contained(&for_stmt.body),
            HirStmt::GenericFor(for_stmt) => forward_control_is_self_contained(&for_stmt.body),
            HirStmt::Block(nested) => forward_control_is_self_contained(nested),
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
            | HirStmt::Label(_) => true,
        })
}

struct CandidateValues<'a> {
    locals: BTreeSet<LocalId>,
    homes: BTreeSet<HomeSlotKey>,
    entry_nil_homes: BTreeSet<HomeSlotKey>,
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
        if let HirLValue::Temp(temp) = then_target {
            let homes = complete_possible_home_slots(
                self.promotion_facts.possible_temp_home_slots(*temp),
                self.promotion_facts,
            );
            self.homes.extend(homes.iter().copied());
            if homes.len() == 1 && self.promotion_facts.overwrites_entry_nil(*temp) {
                self.entry_nil_homes.extend(homes);
            }
        }
        if let HirLValue::Local(local) = else_target {
            self.locals.insert(*local);
        }
        if let HirLValue::Temp(temp) = else_target {
            let homes = complete_possible_home_slots(
                self.promotion_facts.possible_temp_home_slots(*temp),
                self.promotion_facts,
            );
            self.homes.extend(homes.iter().copied());
            if homes.len() == 1 && self.promotion_facts.overwrites_entry_nil(*temp) {
                self.entry_nil_homes.extend(homes);
            }
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
                    let class = if candidates
                        .promotion_facts
                        .entry_nil_writes_were_pruned(local)
                    {
                        OldValueClass::GcInert
                    } else if candidates
                        .promotion_facts
                        .local_home_slot(local)
                        .is_some_and(|home| parameter_homes.contains(&home))
                    {
                        OldValueClass::MayCarryResource
                    } else {
                        OldValueClass::Unknown
                    };
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
                    } else if candidates.entry_nil_homes.contains(&home) {
                        OldValueClass::GcInert
                    } else {
                        OldValueClass::Unknown
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
            .or_insert(OldValueClass::Unknown);
        *current = join_value_classes(*current, written);
    }

    fn merge_possible_home_write(&mut self, home: HomeSlotKey, written: OldValueClass) {
        let current = self
            .home_classes
            .entry(home)
            .or_insert(OldValueClass::Unknown);
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
        if !forward_control_is_self_contained(block) {
            return self.analyze_unstructured_block(block, prefix);
        }
        let label_indices = forward_label_indices(block)
            .expect("self-contained forward control must retain local labels");
        let mut breaks = None;
        let mut continues = None;
        let mut index = 0;
        while let Some(stmt) = block.stmts.get(index) {
            if state.is_none() {
                break;
            }
            if let HirStmt::Goto(goto) = stmt {
                index = *label_indices
                    .get(&goto.target)
                    .expect("validated forward goto must retain its local label");
                continue;
            }
            let mut path = prefix.to_vec();
            path.push(PathComponent::Stmt(index));
            let flow = self.analyze_stmt(stmt, &path, state.expect("reachable state checked"));
            state = flow.fallthrough;
            breaks = join_optional_states(breaks, flow.breaks);
            continues = join_optional_states(continues, flow.continues);
            index += 1;
        }
        InertFlow {
            fallthrough: state,
            breaks,
            continues,
        }
    }

    fn analyze_unstructured_block(
        &mut self,
        block: &HirBlock,
        prefix: &[PathComponent],
    ) -> InertFlow {
        let conservative = OldValueState {
            local_classes: self
                .candidate_locals
                .iter()
                .copied()
                .map(|local| (local, OldValueClass::MayCarryResource))
                .collect(),
            home_classes: self
                .candidate_homes
                .iter()
                .copied()
                .map(|home| (home, OldValueClass::MayCarryResource))
                .collect(),
        };
        let mut state = Some(conservative.clone());
        for (index, stmt) in block.stmts.iter().enumerate() {
            let mut path = prefix.to_vec();
            path.push(PathComponent::Stmt(index));
            if stmt_contains_nested_nonlocal_control(stmt) {
                self.analyze_unstructured_children(stmt, &path);
                // 分析停用[SemanticBarrier:ControlFlow]：label/goto 可绕过此前写入，回边还
                // 会带入上一轮值；`::L:: shell(x); x = {}; goto L` 的第二轮旧值可承载资源。
                state = Some(conservative.clone());
                continue;
            }
            let Some(incoming) = state.take() else {
                continue;
            };
            state = self.analyze_stmt(stmt, &path, incoming).fallthrough;
        }
        InertFlow {
            fallthrough: Some(conservative.clone()),
            breaks: Some(conservative.clone()),
            continues: Some(conservative),
        }
    }

    fn analyze_unstructured_children(&mut self, stmt: &HirStmt, path: &StmtPath) {
        match stmt {
            HirStmt::If(if_stmt) => {
                let mut then_prefix = path.clone();
                then_prefix.push(PathComponent::Then);
                let _ = self.analyze_unstructured_block(&if_stmt.then_block, &then_prefix);
                if let Some(else_block) = &if_stmt.else_block {
                    let mut else_prefix = path.clone();
                    else_prefix.push(PathComponent::Else);
                    let _ = self.analyze_unstructured_block(else_block, &else_prefix);
                }
            }
            HirStmt::While(while_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                let _ = self.analyze_unstructured_block(&while_stmt.body, &body_prefix);
            }
            HirStmt::Repeat(repeat_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                let _ = self.analyze_unstructured_block(&repeat_stmt.body, &body_prefix);
            }
            HirStmt::NumericFor(for_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                let _ = self.analyze_unstructured_block(&for_stmt.body, &body_prefix);
            }
            HirStmt::GenericFor(for_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                let _ = self.analyze_unstructured_block(&for_stmt.body, &body_prefix);
            }
            HirStmt::Block(nested) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                let _ = self.analyze_unstructured_block(nested, &body_prefix);
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
            HirStmt::Return(_) => InertFlow::default(),
            HirStmt::Goto(_) => {
                unreachable!("block analyzer must consume validated forward gotos")
            }
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
                    // 合流“保留旧值”和“写入新值”，不能用 Unknown 覆盖两端事实。
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
        let candidate_homes = complete_possible_home_slots(
            self.promotion_facts.possible_local_home_slots(candidate),
            self.promotion_facts,
        );
        match target {
            HirLValue::Local(local) if *local == candidate => BindingRelation::Definite,
            HirLValue::Local(local) => possible_home_relation(
                candidate_home,
                Some(&candidate_homes),
                self.promotion_facts.trusted_local_home_slot(*local),
                Some(&complete_possible_home_slots(
                    self.promotion_facts.possible_local_home_slots(*local),
                    self.promotion_facts,
                )),
            ),
            HirLValue::Param(param) => possible_home_relation(
                candidate_home,
                Some(&candidate_homes),
                self.promotion_facts.trusted_param_home_slot(*param),
                Some(&complete_possible_home_slots(
                    self.promotion_facts.possible_param_home_slots(*param),
                    self.promotion_facts,
                )),
            ),
            HirLValue::Temp(temp) => possible_home_relation(
                candidate_home,
                Some(&candidate_homes),
                self.promotion_facts.trusted_temp_home_slot(*temp),
                Some(&complete_possible_home_slots(
                    self.promotion_facts.possible_temp_home_slots(*temp),
                    self.promotion_facts,
                )),
            ),
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => {
                BindingRelation::None
            }
        }
    }

    fn home_binding_relation(&self, target: &HirLValue, candidate: HomeSlotKey) -> BindingRelation {
        match target {
            HirLValue::Temp(temp) => possible_home_relation(
                Some(candidate),
                None,
                self.promotion_facts.trusted_temp_home_slot(*temp),
                Some(&complete_possible_home_slots(
                    self.promotion_facts.possible_temp_home_slots(*temp),
                    self.promotion_facts,
                )),
            ),
            HirLValue::Param(param) => possible_home_relation(
                Some(candidate),
                None,
                self.promotion_facts.trusted_param_home_slot(*param),
                Some(&complete_possible_home_slots(
                    self.promotion_facts.possible_param_home_slots(*param),
                    self.promotion_facts,
                )),
            ),
            HirLValue::Local(local) => possible_home_relation(
                Some(candidate),
                None,
                self.promotion_facts.trusted_local_home_slot(*local),
                Some(&complete_possible_home_slots(
                    self.promotion_facts.possible_local_home_slots(*local),
                    self.promotion_facts,
                )),
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
        || matches!(then_target, HirLValue::Temp(temp) if !complete_possible_home_slots(facts.possible_temp_home_slots(*temp), facts).is_empty())
        || matches!(else_target, HirLValue::Temp(temp) if !complete_possible_home_slots(facts.possible_temp_home_slots(*temp), facts).is_empty())
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
            .unwrap_or(OldValueClass::Unknown);
        *left_class = join_value_classes(*left_class, right_class);
    }
    for (binding, right_class) in right {
        left.entry(binding)
            .or_insert_with(|| join_value_classes(OldValueClass::Unknown, right_class));
    }
}

fn join_value_classes(left: OldValueClass, right: OldValueClass) -> OldValueClass {
    match (left, right) {
        (OldValueClass::GcInert, OldValueClass::GcInert) => OldValueClass::GcInert,
        (OldValueClass::MayCarryResource, _) | (_, OldValueClass::MayCarryResource) => {
            OldValueClass::MayCarryResource
        }
        (OldValueClass::Unknown, _) | (_, OldValueClass::Unknown) => OldValueClass::Unknown,
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

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::hir::common::LocalId;
    use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

    use super::{CandidateValues, OldValueClass, OldValueState};

    #[test]
    fn entry_nil_provenance_seeds_only_proven_candidates_as_gc_inert() {
        let pruned_local = LocalId(0);
        let unknown_local = LocalId(1);
        let entry_nil_home = HomeSlotKey::new(2, 0);
        let unknown_home = HomeSlotKey::new(3, 0);
        let parameter_home = HomeSlotKey::new(0, 0);
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.mark_entry_nil_writes_pruned(pruned_local);
        let candidates = CandidateValues {
            locals: BTreeSet::from([pruned_local, unknown_local]),
            homes: BTreeSet::from([entry_nil_home, unknown_home, parameter_home]),
            entry_nil_homes: BTreeSet::from([entry_nil_home]),
            promotion_facts: &promotion_facts,
        };

        let state = OldValueState::initial(&candidates, &BTreeSet::from([parameter_home]));

        assert_eq!(
            state.local_classes.get(&pruned_local),
            Some(&OldValueClass::GcInert)
        );
        assert_eq!(
            state.local_classes.get(&unknown_local),
            Some(&OldValueClass::Unknown)
        );
        assert_eq!(
            state.home_classes.get(&entry_nil_home),
            Some(&OldValueClass::GcInert)
        );
        assert_eq!(
            state.home_classes.get(&unknown_home),
            Some(&OldValueClass::Unknown)
        );
        assert_eq!(
            state.home_classes.get(&parameter_home),
            Some(&OldValueClass::MayCarryResource)
        );
    }
}
