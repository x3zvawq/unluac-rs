//! 路径敏感地消除机械 result -> carried state 交棒。
//!
//! Structure/HIR 已经提供结构化分支与循环、binding 的 `(slot, close epoch)`、capture 和
//! source debug 身份；这里在这些事实之上证明两个 HIR binding 只是同一物理状态的阶段性
//! 名称，不重新推断 CFG owner，也不移动或复制 RHS。证明只接受同一精确 home-slot，并沿
//! 共享 HIR 图的可达路径跟踪 `Unproduced/Pending/Synced`；Decision 的全部 test/target 读取按并集
//! 保守验证。入口验证与 topology 在同一区域的候选间共享，关系域消费 typed event 而不建边；外部入口、
//! 未同步的外跳与 Unresolved 保留原形。cleanup 只有在 possible-home 与改写端点相交时
//! 才由 proto 级身份门拒绝，不相交的 cleanup 原位保留。
//!
//! 例如 `local r; if c then r = s + 1 else r = s + 2 end; s = r` 会收成两臂直接更新
//! `s`；若任一路在同步前读取旧 `s`、跳出循环，或随后仍读取已经被消费的 `r`，则整项拒绝。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirAssign, HirBlock, HirExpr, HirLValue, HirStmt, HirValuePack, LocalId};
use crate::hir::promotion::ProtoPromotionFacts;

use super::super::super::lexical_cfg::{HirFlowGraph, HirFlowNodeKind, validate_region_entry};
use super::super::super::walk::rewrite_stmts;
use super::super::binding::{
    BindingClassRewritePass, BindingProtection, CarryBinding, binding_home_slot,
    carry_binding_from_expr, carry_binding_from_lvalue,
};
use super::super::prune::{RedundantSelfAssignPrunePass, prune_empty_assign_stmts};
use super::super::reads::{BindingReadCollector, collect_binding_mentions_by_stmt};
use super::super::{HandoffIdentityFacts, RegionControlFacts};
use super::binding_facts;
use crate::hir::visit::{HirVisitor, visit_expr, visit_stmts};

pub(in crate::hir::simplify::carried_locals) fn collapse_result_writeback_transactions(
    block: &mut HirBlock,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &mut ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
    control_facts: &RegionControlFacts,
    inherited_locals: &BTreeSet<LocalId>,
) -> bool {
    let mut changed = false;
    while let Some(candidate) = find_candidate(
        block,
        outer_bindings,
        promotion_facts,
        identity_facts,
        control_facts,
        inherited_locals,
    ) {
        apply_candidate(block, candidate, promotion_facts);
        changed = true;
    }
    changed
}

#[derive(Clone)]
struct Candidate {
    declaration: usize,
    last_mention: usize,
    result: LocalId,
    state: CarryBinding,
    initializer: Option<HirValuePack>,
}

fn find_candidate(
    block: &HirBlock,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
    control_facts: &RegionControlFacts,
    inherited_locals: &BTreeSet<LocalId>,
) -> Option<Candidate> {
    let mentions = collect_binding_mentions_by_stmt(&block.stmts);
    for (declaration, stmt) in block.stmts.iter().enumerate() {
        let Some((result, initializer)) = candidate_declaration(stmt) else {
            continue;
        };
        let result_binding = CarryBinding::Local(result);
        // 候选拒绝[PolicyBoundary]：debug result 是项目选择保留的源码身份。
        // 候选拒绝[SemanticBarrier:Scope]：for result 每轮重建且只在 loop body 可见；
        // 合并到跨轮 state 会改变迭代 refresh 和词法作用域。
        // 候选拒绝[SemanticBarrier:Scope]：outer result 可在 region 外被观察，不能删除其 binding identity。
        if identity_facts.contains(result)
            || outer_bindings.contains(&result_binding)
            || mentions[..declaration]
                .iter()
                .any(|bindings| bindings.contains(&result_binding))
        {
            continue;
        }
        let Some(last_mention) = mentions[declaration + 1..]
            .iter()
            .rposition(|bindings| bindings.contains(&result_binding))
            .map(|relative| declaration + 1 + relative)
        else {
            continue;
        };
        if region_has_hard_barrier(&block.stmts[declaration + 1..=last_mention], control_facts) {
            // 候选拒绝[PolicyBoundary]：Unresolved 是 permissive 输出保留的失败证据。
            // 候选拒绝[SemanticBarrier:ControlFlow]：owner-wide label refs 证明外部入口时，
            // producer 可被绕过或重执行；self-contained edge 交给 relation CFG。
            continue;
        }
        let target_states =
            writeback_targets(&block.stmts[declaration + 1..=last_mention], result_binding)
                .into_iter()
                .filter(|(state, _)| *state != result_binding)
                .collect::<Vec<_>>();
        if target_states.is_empty() {
            continue;
        }
        let available_states = target_states
            .into_iter()
            .filter(|(state, _)| {
                binding_available_before(
                    block,
                    declaration,
                    *state,
                    outer_bindings,
                    inherited_locals,
                )
            })
            .collect::<Vec<_>>();
        if available_states.is_empty() {
            // 候选拒绝[SemanticBarrier:Scope]：writeback target 在 result 声明前不可用时，
            // 把 producer 直接改写为 target 会制造声明前写入。
            continue;
        }
        let eligible_states = available_states
            .into_iter()
            .filter(|(state, phi_writeback)| {
                identity_facts.binding_merge_preserves_retained_target(
                    result_binding,
                    *state,
                    promotion_facts,
                    false,
                    *phi_writeback,
                ) && !state
                    .local()
                    .is_some_and(|local| identity_facts.for_bindings.contains(&local))
                    && same_exact_home_slot(result_binding, *state, promotion_facts)
            })
            .map(|(state, _)| state)
            .collect::<Vec<_>>();
        if eligible_states.is_empty() {
            // 候选拒绝[SemanticBarrier:Lifetime]：capture/for/异槽 state 与 result 具有
            // 可区分的 cell 或 root epoch。
            continue;
        }
        let completed_states = completed_writeback_states(
            result_binding,
            &eligible_states,
            initializer,
            &block.stmts[declaration + 1..=last_mention],
            control_facts,
        );
        if completed_states.is_empty() {
            // 候选拒绝[SemanticBarrier:Lifetime]：每个 eligible target 都在某条路径
            // 读取错误 epoch、丢失 result，或以 Pending 退出；改名会提前覆盖旧 state。
            continue;
        }
        // `completed_writeback_states` 对每个 target 独立跑完整三态 verifier；因此列表中
        // 每一个 target 都是全路径 owner，选择稳定排序的首个不会混合不同候选的局部证明。
        let state = completed_states[0];
        return Some(Candidate {
            declaration,
            last_mention,
            result,
            state,
            initializer: initializer.cloned(),
        });
    }
    None
}

fn candidate_declaration(stmt: &HirStmt) -> Option<(LocalId, Option<&HirValuePack>)> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [result] = local_decl.bindings.as_slice() else {
        return None;
    };
    Some((
        *result,
        (!local_decl.values.is_empty()).then_some(&local_decl.values),
    ))
}

fn writeback_targets(stmts: &[HirStmt], result: CarryBinding) -> BTreeMap<CarryBinding, bool> {
    let mut collector = WritebackTargetCollector {
        result,
        targets: BTreeMap::new(),
    };
    visit_stmts(stmts, &mut collector);
    collector.targets
}

fn completed_writeback_states(
    result: CarryBinding,
    eligible_states: &[CarryBinding],
    initializer: Option<&HirValuePack>,
    stmts: &[HirStmt],
    control_facts: &RegionControlFacts,
) -> Vec<CarryBinding> {
    if eligible_states.is_empty() {
        return Vec::new();
    }
    // 调用方已验证整区入口与 Unresolved；同一快照的候选只重算各自的关系域。
    let Ok(graph) = HirFlowGraph::for_stmts(stmts, control_facts.expr_safety) else {
        return Vec::new();
    };
    eligible_states
        .iter()
        .copied()
        .filter(|state| {
            let verifier = FlowVerifier {
                result,
                state: *state,
                validate_rewritten_reads: true,
            };
            let Some(states) = verifier.validate_initializer(initializer) else {
                return false;
            };
            verifier
                .validate_region(&graph, states)
                .is_some_and(|states| !states.contains(Relation::Pending))
        })
        .collect()
}

#[derive(Clone, Copy)]
pub(super) enum ExternalTransferScope {
    WholeRegion,
    LoopExitPlan,
}

pub(super) fn region_rewrites_preserve_external_transfers(
    stmts: &[HirStmt],
    rewrites: &BTreeMap<CarryBinding, CarryBinding>,
    control_facts: &RegionControlFacts,
    scope: ExternalTransferScope,
) -> bool {
    if rewrites.is_empty() {
        return true;
    }
    if region_has_hard_barrier(stmts, control_facts) {
        return false;
    }
    let Ok(graph) = HirFlowGraph::for_stmts(stmts, control_facts.expr_safety) else {
        return false;
    };
    rewrites.iter().all(|(result, state)| {
        let verifier = FlowVerifier {
            result: *result,
            state: *state,
            // Whole-region plans rename every read. Loop plans rename only tracked exit
            // producers and the live-out suffix, so unrelated body reads remain untouched.
            validate_rewritten_reads: matches!(scope, ExternalTransferScope::WholeRegion),
        };
        let Some(outcome) =
            verifier.validate_graph(&graph, RelationSet::only(Relation::Unproduced))
        else {
            return false;
        };
        let has_unsynced = |states: RelationSet| {
            states.contains(Relation::Unproduced) || states.contains(Relation::Pending)
        };
        let unsynced_goto = has_unsynced(outcome.outgoing);
        let unsynced_loop_transfer = matches!(scope, ExternalTransferScope::WholeRegion)
            && (has_unsynced(outcome.breaks) || has_unsynced(outcome.continues));
        if unsynced_goto || unsynced_loop_transfer {
            // 候选拒绝[SemanticBarrier:ControlFlow]：跨 owner transfer 只有在 result/state
            // 已同步时才等价。Unproduced 改名会把 nil 换成旧 state；Pending 改名会提前
            // 覆盖旧 state，目标 owner 都可能观察不同 epoch。
            return false;
        }
        true
    })
}

struct WritebackTargetCollector {
    result: CarryBinding,
    targets: BTreeMap<CarryBinding, bool>,
}

impl HirVisitor<'_> for WritebackTargetCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        let HirStmt::Assign(assign) = stmt else {
            return;
        };
        for (index, target) in assign.targets.iter().enumerate() {
            let value = assign
                .values
                .fixed
                .get(index)
                .or_else(|| assign.values.tail.as_ref().map(|tail| tail.as_expr()));
            if value.is_some_and(|value| binding_reads_in_expr(value).contains(&self.result))
                && let Some(target) = carry_binding_from_lvalue(target)
                && target != self.result
            {
                let phi_writeback = assign.is_phi_transfer
                    && assign.values.tail.is_none()
                    && value.and_then(carry_binding_from_expr) == Some(self.result);
                self.targets
                    .entry(target)
                    .and_modify(|all_phi| *all_phi &= phi_writeback)
                    .or_insert(phi_writeback);
            }
        }
    }
}

fn binding_available_before(
    block: &HirBlock,
    declaration: usize,
    binding: CarryBinding,
    outer_bindings: &dyn BindingProtection,
    inherited_locals: &BTreeSet<LocalId>,
) -> bool {
    match binding {
        CarryBinding::Param(_) => true,
        CarryBinding::Local(local) => {
            inherited_locals.contains(&local)
                || block.stmts[..declaration].iter().any(|stmt| {
                    matches!(stmt,
                        HirStmt::LocalDecl(local_decl)
                            if local_decl.bindings.contains(&local))
                })
        }
        CarryBinding::Temp(_) => {
            outer_bindings.contains(&binding)
                || binding_facts(&block.stmts[..declaration])
                    .writes
                    .contains_key(&binding)
        }
    }
}

fn same_exact_home_slot(
    result: CarryBinding,
    state: CarryBinding,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    !promotion_facts.compacts_home_slots()
        && binding_home_slot(result, promotion_facts)
            .zip(binding_home_slot(state, promotion_facts))
            .is_some_and(|(result, state)| result == state)
}

#[derive(Clone, Copy)]
struct FlowVerifier {
    result: CarryBinding,
    state: CarryBinding,
    validate_rewritten_reads: bool,
}

impl FlowVerifier {
    fn validate_initializer(&self, initializer: Option<&HirValuePack>) -> Option<RelationSet> {
        let Some(initializer) = initializer else {
            return Some(RelationSet::only(Relation::Unproduced));
        };
        let states = RelationSet::only(Relation::Unproduced);
        self.validate_pack(initializer, states)?;
        let value = initializer
            .first()
            .expect("non-empty result initializer must provide a first value");
        Some(if carry_binding_from_expr(value) == Some(self.state) {
            RelationSet::only(Relation::Synced)
        } else {
            RelationSet::only(Relation::Pending)
        })
    }

    fn validate_region(
        &self,
        graph: &HirFlowGraph<'_>,
        states: RelationSet,
    ) -> Option<RelationSet> {
        let outcome = self.validate_graph(graph, states)?;
        if outcome.breaks.contains(Relation::Pending)
            || outcome.continues.contains(Relation::Pending)
            || outcome.outgoing.contains(Relation::Pending)
        {
            // 候选拒绝[SemanticBarrier:ControlFlow]：离开候选 owner 的 Pending path 未执行
            // writeback；把 result producer 提前改成 state write 会改变目标 owner 的读取。
            return None;
        }
        Some(outcome.fallthrough)
    }

    fn validate_graph(&self, graph: &HirFlowGraph<'_>, states: RelationSet) -> Option<FlowOutcome> {
        // Err 是吸收态；terminal 节点没有后继，失败仍须单调记录，不能被 return/goto 吞掉。
        let mut rejected = false;
        let outputs = graph.solve_forward(
            Ok(states),
            |current, incoming| {
                let next = match (*current, *incoming) {
                    (Ok(current), Ok(incoming)) => Ok(current.union(incoming)),
                    _ => Err(()),
                };
                let changed = *current != next;
                *current = next;
                changed
            },
            |_, kind, states| {
                *states = states.and_then(|states| self.validate_event(kind, states).ok_or(()));
                rejected |= states.is_err();
                *states
            },
        );
        if rejected {
            return None;
        }
        let mut exits = FlowOutcome::default();
        for (node, output) in graph.nodes().iter().zip(outputs) {
            let Some(Ok(states)) = output else { continue };
            let exit = match node.kind() {
                HirFlowNodeKind::Exit => &mut exits.fallthrough,
                HirFlowNodeKind::Stmt(stmt) if node.successors().is_empty() => match stmt {
                    HirStmt::Break => &mut exits.breaks,
                    HirStmt::Continue => &mut exits.continues,
                    HirStmt::Goto(_) => &mut exits.outgoing,
                    // return pack 已验证读取，identity 门负责 capture/resource；函数终止后
                    // 不再要求旧 state 同步。内部 transfer 由共享图的最近 owner 消费。
                    _ => continue,
                },
                _ => continue,
            };
            *exit = exit.union(states);
        }
        Some(exits)
    }

    fn validate_event(
        &self,
        kind: HirFlowNodeKind<'_>,
        states: RelationSet,
    ) -> Option<RelationSet> {
        if states.is_empty() {
            return Some(states);
        }
        match kind {
            HirFlowNodeKind::Stmt(stmt) => match stmt {
                HirStmt::LocalRootRelease(local) => {
                    // nil 只更新逻辑端点，不同步具有相同 VM home 的另一个 binding。
                    return Some(if CarryBinding::Local(*local) == self.result {
                        RelationSet::only(Relation::Pending)
                    } else if CarryBinding::Local(*local) == self.state {
                        RelationSet::only(Relation::Unproduced)
                    } else {
                        states
                    });
                }
                HirStmt::Assign(assign) => return self.validate_assign(assign, states),
                HirStmt::If(branch) => self.validate_expr(&branch.cond, states)?,
                HirStmt::While(loop_stmt) => self.validate_expr(&loop_stmt.cond, states)?,
                HirStmt::NumericFor(loop_stmt) => {
                    self.validate_expr(&loop_stmt.start, states)?;
                    self.validate_expr(&loop_stmt.limit, states)?;
                    self.validate_expr(&loop_stmt.step, states)?;
                }
                HirStmt::Return(stmt) => self.validate_pack(&stmt.values, states)?,
                HirStmt::ToBeClosed(stmt) => self.validate_expr(&stmt.value, states)?,
                HirStmt::LocalDecl(stmt) => {
                    if stmt.bindings.iter().any(|&local| {
                        [self.result, self.state].contains(&CarryBinding::Local(local))
                    }) {
                        // 候选拒绝[SemanticBarrier:Scope]：端点重声明不能跨 lexical owner 改名。
                        return None;
                    }
                    self.validate_pack(&stmt.values, states)?;
                }
                HirStmt::GlobalDecl(stmt) => self.validate_pack(&stmt.values, states)?,
                HirStmt::TableSetList(_) | HirStmt::ErrNil(_) | HirStmt::CallStmt(_) => {
                    self.validate_leaf(stmt, states)?;
                }
                HirStmt::Break
                | HirStmt::Continue
                | HirStmt::Goto(_)
                | HirStmt::Label(_)
                | HirStmt::Close(_) => {}
                HirStmt::Block(_) | HirStmt::Repeat(_) | HirStmt::GenericFor(_) => {
                    unreachable!("structured owner must be lowered to HIR flow events")
                }
            },
            HirFlowNodeKind::RepeatCondition(stmt) => self.validate_expr(&stmt.cond, states)?,
            HirFlowNodeKind::GenericForInit(flow) => {
                self.validate_pack(&flow.for_stmt().iterator, states)?;
            }
            // identity 门排除了 for binding 与候选端点相交；这里不重证协议写入或资源身份。
            HirFlowNodeKind::NumericForDispatch
            | HirFlowNodeKind::GenericForDispatch(_)
            | HirFlowNodeKind::ForBinding(_)
            | HirFlowNodeKind::Exit => {}
            HirFlowNodeKind::FunctionExit | HirFlowNodeKind::UnknownControl => {
                unreachable!("writeback verification requires a region graph")
            }
        }
        Some(states)
    }

    fn validate_assign(&self, assign: &HirAssign, states: RelationSet) -> Option<RelationSet> {
        self.validate_pack(&assign.values, states)?;
        for target in &assign.targets {
            self.validate_lvalue_address(target, states)?;
        }

        let mut next = RelationSet::EMPTY;
        for relation in [Relation::Unproduced, Relation::Pending, Relation::Synced] {
            if states.contains(relation) {
                next = next.union(RelationSet::only(
                    self.assignment_relation(assign, relation)?,
                ));
            }
        }
        Some(next)
    }

    fn assignment_relation(&self, assign: &HirAssign, relation: Relation) -> Option<Relation> {
        let mut result_value = AssignmentValue::OldResult;
        let mut state_value = AssignmentValue::OldState;
        let mut merged_value = match relation {
            Relation::Unproduced => AssignmentValue::OldState,
            Relation::Pending | Relation::Synced => AssignmentValue::OldResult,
        };

        for (index, target) in assign.targets.iter().enumerate() {
            let Some(target) = carry_binding_from_lvalue(target) else {
                continue;
            };
            let value = self.assignment_value(assign, index);
            if target == self.result {
                result_value = value;
                merged_value = value;
            } else if target == self.state {
                state_value = value;
                merged_value = value;
            }
        }

        let preserves_result = assignment_values_equal(merged_value, result_value, relation);
        let preserves_state = assignment_values_equal(merged_value, state_value, relation);
        match (preserves_result, preserves_state) {
            (true, true) => Some(Relation::Synced),
            (true, false) => Some(Relation::Pending),
            (false, true) => Some(Relation::Unproduced),
            (false, false) => None,
        }
    }

    fn assignment_value(&self, assign: &HirAssign, target: usize) -> AssignmentValue {
        if let Some(value) = assign.values.fixed.get(target) {
            return match carry_binding_from_expr(value) {
                Some(binding) if binding == self.result => AssignmentValue::OldResult,
                Some(binding) if binding == self.state => AssignmentValue::OldState,
                _ => AssignmentValue::Fixed(target),
            };
        }
        if assign.values.tail.is_some() {
            AssignmentValue::Tail(target - assign.values.fixed.len())
        } else {
            AssignmentValue::Nil
        }
    }

    fn validate_leaf(&self, stmt: &HirStmt, states: RelationSet) -> Option<()> {
        if stmt_contains_unresolved_expr(stmt) {
            // 候选拒绝[PolicyBoundary]：Unresolved 的未知读取属于 permissive 失败证据。
            return None;
        }
        let mut reads = BindingReadCollector::default();
        reads.collect_stmts(std::slice::from_ref(stmt));
        self.validate_reads(&reads.reads, states)
    }

    fn validate_pack(&self, pack: &HirValuePack, states: RelationSet) -> Option<()> {
        for value in pack {
            self.validate_expr(value, states)?;
        }
        Some(())
    }

    fn validate_expr(&self, expr: &HirExpr, states: RelationSet) -> Option<()> {
        if expr_has_hard_barrier(expr) {
            // 候选拒绝[PolicyBoundary]：Unresolved 的未知读取属于 permissive 失败证据。
            return None;
        }
        // BindingReadCollector 递归覆盖 Decision 的每个 test 与 expression target。按读取并集
        // 验证会保守拒绝任一路径上的错误 epoch，同时允许与 result/state 无关的残留 Decision。
        self.validate_reads(&binding_reads_in_expr(expr), states)
    }

    fn validate_lvalue_address(&self, lvalue: &HirLValue, states: RelationSet) -> Option<()> {
        let HirLValue::TableAccess(access) = lvalue else {
            return Some(());
        };
        self.validate_expr(&access.base, states)?;
        self.validate_expr(&access.key, states)
    }

    fn validate_reads(&self, reads: &BTreeSet<CarryBinding>, states: RelationSet) -> Option<()> {
        if !self.validate_rewritten_reads {
            return Some(());
        }
        // 候选拒绝[SemanticBarrier:Lifetime]：读取未产出的 result 或 Pending 期间的旧 state 时，二者改名会把读取切到错误 epoch。
        (!reads.contains(&self.result) || !states.contains(Relation::Unproduced)).then_some(())?;
        (!reads.contains(&self.state) || !states.contains(Relation::Pending)).then_some(())
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Relation {
    Unproduced = 1,
    Pending = 2,
    Synced = 4,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum AssignmentValue {
    OldResult,
    OldState,
    Fixed(usize),
    Tail(usize),
    Nil,
}

fn assignment_values_equal(
    left: AssignmentValue,
    right: AssignmentValue,
    relation: Relation,
) -> bool {
    left == right
        || relation == Relation::Synced
            && matches!(
                (left, right),
                (AssignmentValue::OldResult, AssignmentValue::OldState)
                    | (AssignmentValue::OldState, AssignmentValue::OldResult)
            )
}

#[derive(Clone, Copy, Eq, PartialEq)]
struct RelationSet(u8);

impl RelationSet {
    const EMPTY: Self = Self(0);

    const fn only(relation: Relation) -> Self {
        Self(relation as u8)
    }

    const fn contains(self, relation: Relation) -> bool {
        self.0 & relation as u8 != 0
    }

    const fn is_empty(self) -> bool {
        self.0 == 0
    }

    const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
}

#[derive(Default)]
struct FlowOutcome {
    fallthrough: RelationSet,
    breaks: RelationSet,
    continues: RelationSet,
    outgoing: RelationSet,
}

impl Default for RelationSet {
    fn default() -> Self {
        Self::EMPTY
    }
}

fn binding_reads_in_expr(expr: &HirExpr) -> BTreeSet<CarryBinding> {
    let mut reads = BindingReadCollector::default();
    reads.collect_expr(expr);
    reads.reads
}

fn stmt_contains_unresolved_expr(stmt: &HirStmt) -> bool {
    let mut collector = UnresolvedExprCollector::default();
    visit_stmts(std::slice::from_ref(stmt), &mut collector);
    collector.found
}

#[derive(Default)]
struct UnresolvedExprCollector {
    found: bool,
}

pub(super) fn region_has_hard_barrier(
    stmts: &[HirStmt],
    control_facts: &RegionControlFacts,
) -> bool {
    let mut collector = UnresolvedExprCollector::default();
    visit_stmts(stmts, &mut collector);
    // 候选拒绝[SemanticBarrier:ControlFlow]：owner-wide label refs 证明候选区域有外部
    // 入口或重复 label；改写 result 声明/producer 会被该入口绕过或重执行。
    collector.found || validate_region_entry(stmts, &control_facts.label_refs).is_err()
}

pub(super) fn expr_has_hard_barrier(expr: &HirExpr) -> bool {
    let mut collector = UnresolvedExprCollector::default();
    visit_expr(expr, &mut collector);
    collector.found
}

impl HirVisitor<'_> for UnresolvedExprCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.found |= matches!(expr, HirExpr::Unresolved(_));
    }
}

fn apply_candidate(
    block: &mut HirBlock,
    candidate: Candidate,
    promotion_facts: &mut ProtoPromotionFacts,
) {
    let result = CarryBinding::Local(candidate.result);
    promotion_facts.record_consumed_local_binding(
        candidate.result,
        match candidate.state {
            CarryBinding::Local(local) => crate::hir::HirBinding::Local(local),
            CarryBinding::Param(param) => crate::hir::HirBinding::Param(param),
            CarryBinding::Temp(temp) => crate::hir::HirBinding::Temp(temp),
        },
    );
    if let Some(values) = candidate.initializer {
        block.stmts[candidate.declaration] = HirStmt::Assign(Box::new(HirAssign {
            luau_function_declaration: false,
            luau_compound_global: false,
            upvalue_write_source: None,
            is_phi_transfer: false,
            parallel_nil_frame: None,
            targets: vec![binding_lvalue(candidate.state)],
            values,
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            generic_for_dispatch_release: None,
            method_rewrite_transaction: None,
        }));
        rewrite_stmts(
            &mut block.stmts[candidate.declaration..=candidate.last_mention],
            &mut BindingClassRewritePass {
                rewrites: [(result, candidate.state)].into_iter().collect(),
                promotion_facts,
            },
        );
    } else {
        rewrite_stmts(
            &mut block.stmts[candidate.declaration + 1..=candidate.last_mention],
            &mut BindingClassRewritePass {
                rewrites: [(result, candidate.state)].into_iter().collect(),
                promotion_facts,
            },
        );
        block.stmts.remove(candidate.declaration);
    }
    rewrite_stmts(
        &mut block.stmts,
        &mut RedundantSelfAssignPrunePass::for_bindings([candidate.state]),
    );
    prune_empty_assign_stmts(block);
}

fn binding_lvalue(binding: CarryBinding) -> HirLValue {
    match binding {
        CarryBinding::Param(param) => HirLValue::Param(param),
        CarryBinding::Local(local) => HirLValue::Local(local),
        CarryBinding::Temp(temp) => HirLValue::Temp(temp),
    }
}
