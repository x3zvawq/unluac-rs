//! 裁剪 Structure 为同槽 `Entry(nil)` region-result phi 物化出的冗余 nil 边写入。
//!
//! 候选必须来自 promotion 保留的 direct canonical phi provenance。分析以可信的
//! `(slot, close epoch)` 为身份，分别传播普通落空、`break` 与 `continue` 状态；循环对
//! 回边求有限不动点。分析阶段只记录路径，验证成功后才在原 HIR 上一次性提交删除。
//! reference capture 本身不会让 `nil = nil` 变得可观察，但 capture 逃逸后的调用或
//! `__close` 可能回写该 cell，因此会把值状态降为 unknown。

use std::collections::BTreeSet;

use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirIf, HirLValue, HirLocalDecl, HirProto, HirStmt, LocalId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::super::expr_facts::expr_truthiness;
use super::super::mention::ReferenceCapturedBindings;
use super::super::visit::{self, HirVisitor};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NilPathState {
    known_nil: bool,
    reference_exposed: bool,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct NilStates(BTreeSet<NilPathState>);

impl NilStates {
    fn entry() -> Self {
        Self(BTreeSet::from([NilPathState {
            known_nil: true,
            reference_exposed: false,
        }]))
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn all_known_nil(&self) -> bool {
        !self.is_empty() && self.0.iter().all(|state| state.known_nil)
    }

    fn union(mut self, other: Self) -> Self {
        self.0.extend(other.0);
        self
    }

    fn set_known_nil(self, known_nil: bool) -> Self {
        Self(
            self.0
                .into_iter()
                .map(|mut state| {
                    state.known_nil = known_nil;
                    state
                })
                .collect(),
        )
    }

    fn expose_reference(self) -> Self {
        Self(
            self.0
                .into_iter()
                .map(|mut state| {
                    state.reference_exposed = true;
                    state
                })
                .collect(),
        )
    }

    fn opaque_callback(self) -> Self {
        Self(
            self.0
                .into_iter()
                .map(|mut state| {
                    if state.reference_exposed {
                        state.known_nil = false;
                    }
                    state
                })
                .collect(),
        )
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct NilFlow {
    fallthrough: NilStates,
    breaks: NilStates,
    continues: NilStates,
}

impl NilFlow {
    fn fallthrough(states: NilStates) -> Self {
        Self {
            fallthrough: states,
            ..Self::default()
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PruneError {
    ResidualExpr,
    UnstructuredControl,
    BindingInvariant,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum PathComponent {
    Stmt(usize),
    Then,
    Else,
    Body,
}

type StmtPath = Vec<PathComponent>;

#[derive(Default)]
struct PrunePlan {
    redundant: BTreeSet<StmtPath>,
    not_redundant: BTreeSet<StmtPath>,
}

impl PrunePlan {
    fn observe_nil_write(&mut self, path: &StmtPath, states: &NilStates) {
        if states.all_known_nil() && !self.not_redundant.contains(path) {
            self.redundant.insert(path.clone());
        } else {
            self.redundant.remove(path);
            self.not_redundant.insert(path.clone());
        }
    }
}

pub(super) fn prune_redundant_entry_nil_writes(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
    safety: HirExprSafety,
) -> bool {
    if proto.body.stmts.len() < 2 {
        return false;
    }

    let debug_identity = debug_identity_bindings(proto);
    let mut changed = false;
    for index in 0..proto.body.stmts.len() - 1 {
        let Some(local) = empty_local(&proto.body.stmts[index]) else {
            continue;
        };
        if !facts.is_entry_nil_phi_local(local) {
            // 候选拒绝[LayerBoundary]：普通空 local 没有 canonical Entry(nil) phi provenance，不属于本定向裁剪器。
            continue;
        }
        let candidate_home = facts
            .trusted_local_home_slot(local)
            .expect("entry-nil phi local must retain its trusted home");
        if bindings_share_home(&debug_identity, candidate_home, facts) {
            // 候选拒绝[PolicyBoundary]：候选自身或已证明同 home 的 binding 带 source debug identity 时保留显式 nil 边写，维护源码/调试形状。
            continue;
        }
        let HirStmt::If(if_stmt) = &proto.body.stmts[index + 1] else {
            continue;
        };

        let mut analyzer = EntryNilAnalyzer {
            local,
            candidate_home,
            facts,
            safety,
            plan: PrunePlan::default(),
        };
        if let Err(error) = analyzer.analyze_if(if_stmt, NilStates::entry()) {
            match error {
                PruneError::ResidualExpr => {
                    // 候选拒绝[LayerBoundary]：Decision/Unresolved 的执行路径由 decision/dead-unresolved owner 收敛，本 pass 不解释残留表达式。
                }
                PruneError::UnstructuredControl => {
                    // 候选拒绝[LayerBoundary]：label/goto 的 predecessor 与目标边由 Structure island/branch-control owner 维护，本 pass 不在线性 HIR 上重建 CFG。
                }
                PruneError::BindingInvariant => {
                    // 候选拒绝[ConvergenceGuard]：同一 LocalId 再次声明或充当 for binder 违反唯一 binding 身份，不能删除异常 HIR 中的写入。
                }
            }
            continue;
        }
        if analyzer.plan.redundant.is_empty() {
            continue;
        }

        let mut rewritten = (**if_stmt).clone();
        apply_if_plan(&mut rewritten, &analyzer.plan.redundant);
        proto.body.stmts[index + 1] = HirStmt::If(Box::new(rewritten));
        facts.mark_entry_nil_writes_pruned(local);
        changed = true;
    }
    changed
}

fn empty_local(stmt: &HirStmt) -> Option<LocalId> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [local] = local_decl.bindings.as_slice() else {
        return None;
    };
    local_decl.values.is_empty().then_some(*local)
}

struct EntryNilAnalyzer<'a> {
    local: LocalId,
    candidate_home: HomeSlotKey,
    facts: &'a ProtoPromotionFacts,
    safety: HirExprSafety,
    plan: PrunePlan,
}

impl EntryNilAnalyzer<'_> {
    fn analyze_if(&mut self, if_stmt: &HirIf, incoming: NilStates) -> Result<NilFlow, PruneError> {
        let states = self.evaluate_expr(&if_stmt.cond, incoming)?;
        let then_flow = if expr_truthiness(&if_stmt.cond, self.safety) == Some(false) {
            NilFlow::default()
        } else {
            self.analyze_block(&if_stmt.then_block, &[PathComponent::Then], states.clone())?
        };
        let else_flow = if expr_truthiness(&if_stmt.cond, self.safety) == Some(true) {
            NilFlow::default()
        } else if let Some(else_block) = &if_stmt.else_block {
            self.analyze_block(else_block, &[PathComponent::Else], states)?
        } else {
            NilFlow::fallthrough(states)
        };
        Ok(union_flows(then_flow, else_flow))
    }

    fn analyze_block(
        &mut self,
        block: &HirBlock,
        prefix: &[PathComponent],
        mut states: NilStates,
    ) -> Result<NilFlow, PruneError> {
        let mut breaks = NilStates::default();
        let mut continues = NilStates::default();
        for (index, stmt) in block.stmts.iter().enumerate() {
            if states.is_empty() {
                break;
            }
            let mut path = prefix.to_vec();
            path.push(PathComponent::Stmt(index));
            let flow = self.analyze_stmt(stmt, &path, states)?;
            states = flow.fallthrough;
            breaks = breaks.union(flow.breaks);
            continues = continues.union(flow.continues);
        }
        Ok(NilFlow {
            fallthrough: states,
            breaks,
            continues,
        })
    }

    fn analyze_stmt(
        &mut self,
        stmt: &HirStmt,
        path: &StmtPath,
        states: NilStates,
    ) -> Result<NilFlow, PruneError> {
        match stmt {
            HirStmt::Assign(assign) => {
                let states = self.evaluate_stmt_exprs(stmt, states)?;
                if is_direct_nil_write(assign, self.local) {
                    self.plan.observe_nil_write(path, &states);
                }
                Ok(NilFlow::fallthrough(self.apply_assignment(assign, states)))
            }
            HirStmt::LocalDecl(local_decl) => {
                if local_decl.bindings.contains(&self.local) {
                    return Err(PruneError::BindingInvariant);
                }
                let states = self.evaluate_stmt_exprs(stmt, states)?;
                Ok(NilFlow::fallthrough(
                    self.apply_local_decl(local_decl, states),
                ))
            }
            HirStmt::If(if_stmt) => {
                let states = self.evaluate_expr(&if_stmt.cond, states)?;
                let mut then_prefix = path.clone();
                then_prefix.push(PathComponent::Then);
                let then_flow = if expr_truthiness(&if_stmt.cond, self.safety) == Some(false) {
                    NilFlow::default()
                } else {
                    self.analyze_block(&if_stmt.then_block, &then_prefix, states.clone())?
                };
                let else_flow = if expr_truthiness(&if_stmt.cond, self.safety) == Some(true) {
                    NilFlow::default()
                } else if let Some(else_block) = &if_stmt.else_block {
                    let mut else_prefix = path.clone();
                    else_prefix.push(PathComponent::Else);
                    self.analyze_block(else_block, &else_prefix, states)?
                } else {
                    NilFlow::fallthrough(states)
                };
                Ok(union_flows(then_flow, else_flow))
            }
            HirStmt::Block(block) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                self.analyze_block(block, &body_prefix, states)
            }
            HirStmt::While(while_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                self.analyze_while(&while_stmt.body, &while_stmt.cond, &body_prefix, states)
            }
            HirStmt::Repeat(repeat_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                self.analyze_repeat(&repeat_stmt.body, &repeat_stmt.cond, &body_prefix, states)
            }
            HirStmt::NumericFor(numeric_for) => {
                if numeric_for.binding == self.local {
                    return Err(PruneError::BindingInvariant);
                }
                let states = self.evaluate_exprs(
                    [&numeric_for.start, &numeric_for.limit, &numeric_for.step],
                    states,
                )?;
                let body_states = self.write_local_binding(numeric_for.binding, states.clone());
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                self.analyze_zero_or_more(
                    &numeric_for.body,
                    &body_prefix,
                    states,
                    body_states,
                    &[numeric_for.binding],
                    false,
                )
            }
            HirStmt::GenericFor(generic_for) => {
                if generic_for.bindings.contains(&self.local) {
                    return Err(PruneError::BindingInvariant);
                }
                let states = self.evaluate_exprs(generic_for.iterator.iter(), states)?;
                // 即使循环执行零次，也会调用一次 iterator；reference capture 已逃逸时，
                // 该调用可能经由外部别名回写候选 cell。
                let zero_exit = states.opaque_callback();
                let mut body_states = zero_exit.clone();
                for binding in &generic_for.bindings {
                    body_states = self.write_local_binding(*binding, body_states);
                }
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                self.analyze_zero_or_more(
                    &generic_for.body,
                    &body_prefix,
                    zero_exit,
                    body_states,
                    &generic_for.bindings,
                    true,
                )
            }
            HirStmt::Return(_) => {
                self.evaluate_stmt_exprs(stmt, states)?;
                Ok(NilFlow::default())
            }
            HirStmt::Break => Ok(NilFlow {
                breaks: states,
                ..NilFlow::default()
            }),
            HirStmt::Continue => Ok(NilFlow {
                continues: states,
                ..NilFlow::default()
            }),
            HirStmt::Goto(_) | HirStmt::Label(_) => Err(PruneError::UnstructuredControl),
            HirStmt::Close(_) => Ok(NilFlow::fallthrough(states.opaque_callback())),
            HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::CallStmt(_) => Ok(NilFlow::fallthrough(
                self.evaluate_stmt_exprs(stmt, states)?,
            )),
        }
    }

    fn analyze_while(
        &mut self,
        body: &HirBlock,
        condition: &HirExpr,
        body_prefix: &[PathComponent],
        incoming: NilStates,
    ) -> Result<NilFlow, PruneError> {
        let truthiness = expr_truthiness(condition, self.safety);
        let mut entries = incoming.clone();
        let mut break_exits = NilStates::default();
        loop {
            let condition_states = self.evaluate_expr(condition, entries.clone())?;
            let body_flow = if truthiness == Some(false) {
                NilFlow::default()
            } else {
                self.analyze_block(body, body_prefix, condition_states.clone())?
            };
            let next_entries = incoming
                .clone()
                .union(body_flow.fallthrough)
                .union(body_flow.continues);
            let next_break_exits = break_exits.clone().union(body_flow.breaks);
            if next_entries == entries && next_break_exits == break_exits {
                let normal_exits = if truthiness == Some(true) {
                    NilStates::default()
                } else {
                    condition_states
                };
                return Ok(NilFlow::fallthrough(normal_exits.union(break_exits)));
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
        incoming: NilStates,
    ) -> Result<NilFlow, PruneError> {
        let truthiness = expr_truthiness(condition, self.safety);
        let mut entries = incoming.clone();
        let mut break_exits = NilStates::default();
        loop {
            let body_flow = self.analyze_block(body, body_prefix, entries.clone())?;
            let condition_states =
                self.evaluate_expr(condition, body_flow.fallthrough.union(body_flow.continues))?;
            let back_edges = if truthiness == Some(true) {
                NilStates::default()
            } else {
                condition_states.clone()
            };
            let next_entries = incoming.clone().union(back_edges);
            let next_break_exits = break_exits.clone().union(body_flow.breaks);
            if next_entries == entries && next_break_exits == break_exits {
                let normal_exits = if truthiness == Some(false) {
                    NilStates::default()
                } else {
                    condition_states
                };
                return Ok(NilFlow::fallthrough(normal_exits.union(break_exits)));
            }
            entries = next_entries;
            break_exits = next_break_exits;
        }
    }

    fn analyze_zero_or_more(
        &mut self,
        body: &HirBlock,
        body_prefix: &[PathComponent],
        zero_exit: NilStates,
        initial_body_entry: NilStates,
        bindings: &[LocalId],
        opaque_each_iteration: bool,
    ) -> Result<NilFlow, PruneError> {
        let mut entries = initial_body_entry.clone();
        let mut break_exits = NilStates::default();
        loop {
            let body_flow = self.analyze_block(body, body_prefix, entries.clone())?;
            let iteration_exits = body_flow.fallthrough.union(body_flow.continues);
            let callback_exits = if opaque_each_iteration {
                iteration_exits.clone().opaque_callback()
            } else {
                iteration_exits.clone()
            };
            let mut back_edges = callback_exits.clone();
            for binding in bindings {
                back_edges = self.write_local_binding(*binding, back_edges);
            }
            let next_entries = initial_body_entry.clone().union(back_edges);
            let next_break_exits = break_exits.clone().union(body_flow.breaks);
            if next_entries == entries && next_break_exits == break_exits {
                return Ok(NilFlow::fallthrough(
                    zero_exit.union(callback_exits).union(break_exits),
                ));
            }
            entries = next_entries;
            break_exits = next_break_exits;
        }
    }

    fn evaluate_expr(&self, expr: &HirExpr, states: NilStates) -> Result<NilStates, PruneError> {
        let mut effects = ExprEffects::new(self.candidate_home, self.facts);
        visit::visit_expr(expr, &mut effects);
        effects.apply(states)
    }

    fn evaluate_exprs<'a>(
        &self,
        exprs: impl IntoIterator<Item = &'a HirExpr>,
        mut states: NilStates,
    ) -> Result<NilStates, PruneError> {
        for expr in exprs {
            states = self.evaluate_expr(expr, states)?;
        }
        Ok(states)
    }

    fn evaluate_stmt_exprs(
        &self,
        stmt: &HirStmt,
        states: NilStates,
    ) -> Result<NilStates, PruneError> {
        let mut effects = ExprEffects::new(self.candidate_home, self.facts);
        visit::visit_stmts(std::slice::from_ref(stmt), &mut effects);
        effects.apply(states)
    }

    fn apply_assignment(&self, assign: &HirAssign, mut states: NilStates) -> NilStates {
        for (index, target) in assign.targets.iter().enumerate() {
            states = match self.binding_relation(target) {
                BindingRelation::None => states,
                BindingRelation::Possible => states.set_known_nil(false),
                BindingRelation::Definite => {
                    states.set_known_nil(assigned_value_is_nil(assign, index))
                }
            };
        }
        states
    }

    fn apply_local_decl(&self, decl: &HirLocalDecl, mut states: NilStates) -> NilStates {
        for (index, binding) in decl.bindings.iter().enumerate() {
            states = match self.local_binding_relation(*binding) {
                BindingRelation::None => states,
                BindingRelation::Possible => states.set_known_nil(false),
                BindingRelation::Definite => {
                    states.set_known_nil(declared_value_is_nil(decl, index))
                }
            };
        }
        states
    }

    fn write_local_binding(&self, binding: LocalId, states: NilStates) -> NilStates {
        match self.local_binding_relation(binding) {
            BindingRelation::None => states,
            BindingRelation::Possible | BindingRelation::Definite => states.set_known_nil(false),
        }
    }

    fn binding_relation(&self, target: &HirLValue) -> BindingRelation {
        match target {
            HirLValue::Local(local) => self.local_binding_relation(*local),
            HirLValue::Param(param) => relation_for_home(
                self.facts.trusted_param_home_slot(*param),
                self.candidate_home,
            ),
            HirLValue::Temp(temp) => relation_for_home(
                self.facts.trusted_temp_home_slot(*temp),
                self.candidate_home,
            ),
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => {
                BindingRelation::None
            }
        }
    }

    fn local_binding_relation(&self, local: LocalId) -> BindingRelation {
        if local == self.local {
            BindingRelation::Definite
        } else {
            relation_for_home(
                self.facts.trusted_local_home_slot(local),
                self.candidate_home,
            )
        }
    }
}

#[derive(Clone, Copy)]
enum BindingRelation {
    None,
    Possible,
    Definite,
}

fn relation_for_home(home: Option<HomeSlotKey>, candidate: HomeSlotKey) -> BindingRelation {
    match home {
        Some(home) if home == candidate => BindingRelation::Definite,
        Some(_) => BindingRelation::None,
        None => BindingRelation::Possible,
    }
}

fn is_direct_nil_write(assign: &HirAssign, local: LocalId) -> bool {
    matches!(assign.targets.as_slice(), [HirLValue::Local(target)] if *target == local)
        && matches!(assign.values.fixed.as_slice(), [HirExpr::Nil])
        && assign.values.tail.is_none()
}

fn assigned_value_is_nil(assign: &HirAssign, target_index: usize) -> bool {
    value_at_is_nil(
        &assign.values.fixed,
        assign.values.tail.is_some(),
        target_index,
    )
}

fn declared_value_is_nil(decl: &HirLocalDecl, binding_index: usize) -> bool {
    value_at_is_nil(
        &decl.values.fixed,
        decl.values.tail.is_some(),
        binding_index,
    )
}

fn value_at_is_nil(fixed: &[HirExpr], has_tail: bool, index: usize) -> bool {
    fixed
        .get(index)
        .is_some_and(|value| matches!(value, HirExpr::Nil))
        || (!has_tail && index >= fixed.len())
}

fn union_flows(left: NilFlow, right: NilFlow) -> NilFlow {
    NilFlow {
        fallthrough: left.fallthrough.union(right.fallthrough),
        breaks: left.breaks.union(right.breaks),
        continues: left.continues.union(right.continues),
    }
}

struct ExprEffects<'a> {
    candidate_home: HomeSlotKey,
    facts: &'a ProtoPromotionFacts,
    captures_reference: bool,
    has_call: bool,
    residual: bool,
}

impl<'a> ExprEffects<'a> {
    fn new(candidate_home: HomeSlotKey, facts: &'a ProtoPromotionFacts) -> Self {
        Self {
            candidate_home,
            facts,
            captures_reference: false,
            has_call: false,
            residual: false,
        }
    }

    fn apply(self, mut states: NilStates) -> Result<NilStates, PruneError> {
        if self.residual {
            return Err(PruneError::ResidualExpr);
        }
        if self.has_call {
            states = states.opaque_callback();
        }
        if self.captures_reference {
            states = states.expose_reference();
            if self.has_call {
                states = states.set_known_nil(false);
            }
        }
        Ok(states)
    }
}

impl HirVisitor for ExprEffects<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        match expr {
            HirExpr::GlobalRef(_)
            | HirExpr::TableAccess(_)
            | HirExpr::Unary(_)
            | HirExpr::Binary(_)
            | HirExpr::Call(_) => self.has_call = true,
            HirExpr::Decision(_) | HirExpr::Unresolved(_) => self.residual = true,
            HirExpr::Closure(closure) => {
                self.captures_reference |= closure.captures.iter().any(|capture| {
                    capture.mode == crate::hir::common::HirCaptureMode::ByReference
                        && expr_may_reference_home(&capture.value, self.candidate_home, self.facts)
                });
            }
            _ => {}
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.has_call |= matches!(lvalue, HirLValue::Global(_) | HirLValue::TableAccess(_));
    }

    fn visit_call(&mut self, _call: &crate::hir::common::HirCallExpr) {
        self.has_call = true;
    }
}

fn expr_may_reference_home(
    expr: &HirExpr,
    candidate_home: HomeSlotKey,
    facts: &ProtoPromotionFacts,
) -> bool {
    struct Collector<'a> {
        candidate_home: HomeSlotKey,
        facts: &'a ProtoPromotionFacts,
        may_reference: bool,
    }

    impl HirVisitor for Collector<'_> {
        fn visit_expr(&mut self, expr: &HirExpr) {
            let home = match expr {
                HirExpr::LocalRef(local) => self.facts.trusted_local_home_slot(*local),
                HirExpr::ParamRef(param) => self.facts.trusted_param_home_slot(*param),
                HirExpr::TempRef(temp) => self.facts.trusted_temp_home_slot(*temp),
                _ => return,
            };
            self.may_reference |= home.is_none_or(|home| home == self.candidate_home);
        }
    }

    let mut collector = Collector {
        candidate_home,
        facts,
        may_reference: false,
    };
    visit::visit_expr(expr, &mut collector);
    collector.may_reference
}

fn apply_if_plan(if_stmt: &mut HirIf, redundant: &BTreeSet<StmtPath>) {
    apply_block_plan(&mut if_stmt.then_block, &[PathComponent::Then], redundant);
    if let Some(else_block) = &mut if_stmt.else_block {
        apply_block_plan(else_block, &[PathComponent::Else], redundant);
    }
}

fn apply_block_plan(
    block: &mut HirBlock,
    prefix: &[PathComponent],
    redundant: &BTreeSet<StmtPath>,
) {
    let mut remove = Vec::new();
    for (index, stmt) in block.stmts.iter_mut().enumerate() {
        let mut path = prefix.to_vec();
        path.push(PathComponent::Stmt(index));
        match stmt {
            HirStmt::If(if_stmt) => {
                let mut then_prefix = path.clone();
                then_prefix.push(PathComponent::Then);
                apply_block_plan(&mut if_stmt.then_block, &then_prefix, redundant);
                if let Some(else_block) = &mut if_stmt.else_block {
                    let mut else_prefix = path.clone();
                    else_prefix.push(PathComponent::Else);
                    apply_block_plan(else_block, &else_prefix, redundant);
                }
            }
            HirStmt::While(while_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                apply_block_plan(&mut while_stmt.body, &body_prefix, redundant);
            }
            HirStmt::Repeat(repeat_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                apply_block_plan(&mut repeat_stmt.body, &body_prefix, redundant);
            }
            HirStmt::NumericFor(numeric_for) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                apply_block_plan(&mut numeric_for.body, &body_prefix, redundant);
            }
            HirStmt::GenericFor(generic_for) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                apply_block_plan(&mut generic_for.body, &body_prefix, redundant);
            }
            HirStmt::Block(nested) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                apply_block_plan(nested, &body_prefix, redundant);
            }
            HirStmt::LocalDecl(_)
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
        if redundant.contains(&path) {
            remove.push(index);
        }
    }
    for index in remove.into_iter().rev() {
        block.stmts.remove(index);
    }
}

fn debug_identity_bindings(proto: &HirProto) -> ReferenceCapturedBindings {
    let mut bindings = ReferenceCapturedBindings::default();
    bindings.locals.extend(
        proto
            .locals
            .iter()
            .copied()
            .zip(&proto.local_debug_hints)
            .filter_map(|(local, hint)| hint.is_some().then_some(local)),
    );
    bindings.params.extend(
        proto
            .params
            .iter()
            .copied()
            .zip(&proto.param_debug_hints)
            .filter_map(|(param, hint)| hint.is_some().then_some(param)),
    );
    bindings.temps.extend(
        proto
            .temps
            .iter()
            .copied()
            .zip(&proto.temp_debug_locals)
            .filter_map(|(temp, hint)| hint.is_some().then_some(temp)),
    );
    bindings
}

fn bindings_share_home(
    bindings: &ReferenceCapturedBindings,
    candidate: HomeSlotKey,
    facts: &ProtoPromotionFacts,
) -> bool {
    bindings
        .locals
        .iter()
        .any(|binding| facts.trusted_local_home_slot(*binding) == Some(candidate))
        || bindings
            .params
            .iter()
            .any(|binding| facts.trusted_param_home_slot(*binding) == Some(candidate))
        || bindings
            .temps
            .iter()
            .any(|binding| facts.trusted_temp_home_slot(*binding) == Some(candidate))
}
