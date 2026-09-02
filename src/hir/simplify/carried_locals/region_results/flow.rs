//! 路径敏感地消除机械 result -> carried state 交棒。
//!
//! Structure/HIR 已经提供结构化分支与循环、binding 的 `(slot, close epoch)`、capture 和
//! source debug 身份；这里在这些事实之上证明两个 HIR binding 只是同一物理状态的阶段性
//! 名称，不重新推断 CFG owner，也不移动或复制 RHS。证明只接受同一精确 home-slot，并沿
//! 每条结构化路径跟踪 `Unproduced/Pending/Synced`；Decision 的全部 test/target 读取按并集
//! 保守验证。owner-wide label refs 与 lexical CFG 会精确跟踪候选内 goto；外部入口、
//! 未同步的外跳与 Unresolved 保留原形。cleanup 只有在 possible-home 与改写端点相交时
//! 才由 proto 级身份门拒绝，不相交的 cleanup 原位保留。
//!
//! 例如 `local r; if c then r = s + 1 else r = s + 2 end; s = r` 会收成两臂直接更新
//! `s`；若任一路在同步前读取旧 `s`、跳出循环，或随后仍读取已经被消费的 `r`，则整项拒绝。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirAssign, HirBlock, HirExpr, HirLValue, HirStmt, HirValuePack, LocalId};
use crate::hir::promotion::ProtoPromotionFacts;

use super::super::super::expr_facts::expr_truthiness;
use super::super::super::lexical_cfg::LexicalCfg;
use super::super::super::visit::{HirVisitor, visit_expr, visit_stmts};
use super::super::super::walk::rewrite_stmts;
use super::super::binding::{
    BindingClassRewritePass, BindingProtection, CarryBinding, binding_home_slot,
    carry_binding_from_expr, carry_binding_from_lvalue,
};
use super::super::prune::{RedundantSelfAssignPrunePass, prune_empty_assign_stmts};
use super::super::reads::{BindingReadCollector, collect_binding_mentions_by_stmt};
use super::super::{HandoffIdentityFacts, RegionControlFacts};
use super::binding_facts;

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
        if writeback_region_has_barrier(&block.stmts[declaration + 1..=last_mention], control_facts)
        {
            // 候选拒绝[PolicyBoundary]：Unresolved 是 permissive 输出保留的失败证据。
            // 候选拒绝[SemanticBarrier:ControlFlow]：owner-wide label refs 证明外部入口时，
            // producer 可被绕过或重执行；self-contained edge 交给 relation CFG。
            continue;
        }
        let target_states =
            writeback_targets(&block.stmts[declaration + 1..=last_mention], result_binding)
                .into_iter()
                .filter(|state| *state != result_binding)
                .collect::<Vec<_>>();
        if target_states.is_empty() {
            continue;
        }
        let available_states = target_states
            .into_iter()
            .filter(|state| {
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
            .filter(|state| {
                identity_facts.binding_merge_preserves_identity(
                    result_binding,
                    *state,
                    promotion_facts,
                ) && !state
                    .local()
                    .is_some_and(|local| identity_facts.for_bindings.contains(&local))
                    && same_exact_home_slot(result_binding, *state, promotion_facts)
            })
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

fn writeback_targets(stmts: &[HirStmt], result: CarryBinding) -> Vec<CarryBinding> {
    let mut collector = WritebackTargetCollector {
        result,
        targets: BTreeSet::new(),
    };
    visit_stmts(stmts, &mut collector);
    collector.targets.into_iter().collect()
}

fn completed_writeback_states(
    result: CarryBinding,
    eligible_states: &[CarryBinding],
    initializer: Option<&HirValuePack>,
    stmts: &[HirStmt],
    control_facts: &RegionControlFacts,
) -> Vec<CarryBinding> {
    eligible_states
        .iter()
        .copied()
        .filter(|state| {
            let verifier = FlowVerifier {
                result,
                state: *state,
                control_facts,
                validate_rewritten_reads: true,
            };
            let Some(states) = verifier.validate_initializer(initializer) else {
                return false;
            };
            verifier
                .validate_region(stmts, states)
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
    rewrites.iter().all(|(result, state)| {
        let verifier = FlowVerifier {
            result: *result,
            state: *state,
            control_facts,
            // Whole-region plans rename every read. Loop plans rename only tracked exit
            // producers and the live-out suffix, so unrelated body reads remain untouched.
            validate_rewritten_reads: matches!(scope, ExternalTransferScope::WholeRegion),
        };
        let Ok(_) =
            LexicalCfg::analyze(stmts, &control_facts.label_refs, control_facts.expr_safety)
        else {
            return false;
        };
        let Some(outcome) = verifier.validate_block(stmts, RelationSet::only(Relation::Unproduced))
        else {
            return false;
        };
        let has_unsynced = |states: RelationSet| {
            states.contains(Relation::Unproduced) || states.contains(Relation::Pending)
        };
        let unsynced_goto = outcome
            .outgoing
            .values()
            .any(|states| has_unsynced(*states));
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
    targets: BTreeSet<CarryBinding>,
}

impl HirVisitor for WritebackTargetCollector {
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
                self.targets.insert(target);
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
struct FlowVerifier<'a> {
    result: CarryBinding,
    state: CarryBinding,
    control_facts: &'a RegionControlFacts,
    validate_rewritten_reads: bool,
}

impl FlowVerifier<'_> {
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

    fn validate_region(&self, stmts: &[HirStmt], states: RelationSet) -> Option<RelationSet> {
        LexicalCfg::analyze(
            stmts,
            &self.control_facts.label_refs,
            self.control_facts.expr_safety,
        )
        .ok()?;
        let outcome = self.validate_block(stmts, states)?;
        if outcome.breaks.contains(Relation::Pending)
            || outcome.continues.contains(Relation::Pending)
            || outcome
                .outgoing
                .values()
                .any(|states| states.contains(Relation::Pending))
        {
            // 候选拒绝[SemanticBarrier:ControlFlow]：离开候选 owner 的 Pending path 未执行
            // writeback；把 result producer 提前改成 state write 会改变目标 owner 的读取。
            return None;
        }
        Some(outcome.fallthrough)
    }

    fn validate_block(&self, stmts: &[HirStmt], states: RelationSet) -> Option<FlowOutcome> {
        if stmts.is_empty() {
            return Some(FlowOutcome::fallthrough(states));
        }
        let direct_labels = stmts
            .iter()
            .enumerate()
            .filter_map(|(index, stmt)| match stmt {
                HirStmt::Label(label) => Some((label.id, index)),
                _ => None,
            })
            .collect::<BTreeMap<_, _>>();
        let mut inputs = vec![RelationSet::EMPTY; stmts.len()];
        inputs[0] = states;
        let mut pending = vec![0usize];
        let mut exits = FlowOutcome::default();
        while let Some(index) = pending.pop() {
            let mut output = self.validate_stmt_outcome(&stmts[index], inputs[index])?;
            if index + 1 < stmts.len() {
                if !output.fallthrough.is_empty() {
                    let next = inputs[index + 1].union(output.fallthrough);
                    if next != inputs[index + 1] {
                        inputs[index + 1] = next;
                        pending.push(index + 1);
                    }
                }
            } else {
                exits.fallthrough = exits.fallthrough.union(output.fallthrough);
            }
            for (target, target_states) in std::mem::take(&mut output.outgoing) {
                if let Some(&target_index) = direct_labels.get(&target) {
                    let next = inputs[target_index].union(target_states);
                    if next != inputs[target_index] {
                        inputs[target_index] = next;
                        pending.push(target_index);
                    }
                } else {
                    exits.add_outgoing(target, target_states);
                }
            }
            exits.breaks = exits.breaks.union(output.breaks);
            exits.continues = exits.continues.union(output.continues);
        }
        Some(exits)
    }

    fn validate_stmt_outcome(&self, stmt: &HirStmt, states: RelationSet) -> Option<FlowOutcome> {
        match stmt {
            HirStmt::Assign(assign) => self
                .validate_assign(assign, states)
                .map(FlowOutcome::fallthrough),
            HirStmt::If(if_stmt) => {
                self.validate_expr(&if_stmt.cond, states)?;
                let then_outcome = self.validate_block(&if_stmt.then_block.stmts, states)?;
                let else_outcome = if let Some(else_block) = &if_stmt.else_block {
                    self.validate_block(&else_block.stmts, states)?
                } else {
                    FlowOutcome::fallthrough(states)
                };
                Some(then_outcome.union(else_outcome))
            }
            HirStmt::Block(block) => self.validate_block(&block.stmts, states),
            HirStmt::Return(return_stmt) => {
                self.validate_pack(&return_stmt.values, states)?;
                // return pack 已验证所有可观察读取，且 identity 门排除了 capture/resource；
                // 终止后未同步的旧 state 不再有 observer。
                Some(FlowOutcome::default())
            }
            HirStmt::Break => Some(FlowOutcome {
                breaks: states,
                ..FlowOutcome::default()
            }),
            HirStmt::Continue => Some(FlowOutcome {
                continues: states,
                ..FlowOutcome::default()
            }),
            HirStmt::Goto(goto_stmt) => {
                let mut outcome = FlowOutcome::default();
                outcome.add_outgoing(goto_stmt.target, states);
                Some(outcome)
            }
            HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::NumericFor(_)
            | HirStmt::GenericFor(_) => self.validate_loop_outcome(stmt, states),
            HirStmt::Label(_) => Some(FlowOutcome::fallthrough(states)),
            HirStmt::ToBeClosed(to_be_closed) => {
                // 候选形成前的 proto 身份门已经证明 result/state 与所有 TBC possible-home
                // 不相交；这里只需保留并验证 TBC value 的读取 epoch。
                self.validate_expr(&to_be_closed.value, states)?;
                Some(FlowOutcome::fallthrough(states))
            }
            HirStmt::Close(_) => Some(FlowOutcome::fallthrough(states)),
            HirStmt::LocalDecl(local_decl) => {
                if local_decl
                    .bindings
                    .iter()
                    .copied()
                    .any(|local| [self.result, self.state].contains(&CarryBinding::Local(local)))
                {
                    // 候选拒绝[SemanticBarrier:Scope]：region 内重声明 result/state 会让批量 LocalId 改名跨越 lexical owner。
                    return None;
                }
                self.validate_pack(&local_decl.values, states)?;
                Some(FlowOutcome::fallthrough(states))
            }
            HirStmt::TableSetList(_) | HirStmt::ErrNil(_) | HirStmt::CallStmt(_) => {
                self.validate_leaf(stmt, states)?;
                Some(FlowOutcome::fallthrough(states))
            }
            HirStmt::GlobalDecl(global_decl) => {
                self.validate_pack(&global_decl.values, states)?;
                Some(FlowOutcome::fallthrough(states))
            }
        }
    }

    #[cfg(test)]
    fn validate_stmt(&self, stmt: &HirStmt, states: RelationSet) -> Option<RelationSet> {
        let outcome = self.validate_stmt_outcome(stmt, states)?;
        (outcome.breaks.is_empty() && outcome.continues.is_empty() && outcome.outgoing.is_empty())
            .then_some(outcome.fallthrough)
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

    fn validate_loop_outcome(&self, stmt: &HirStmt, states: RelationSet) -> Option<FlowOutcome> {
        match stmt {
            HirStmt::While(while_stmt) => {
                self.validate_while(&while_stmt.body, &while_stmt.cond, states)
            }
            HirStmt::Repeat(repeat_stmt) => {
                self.validate_repeat(&repeat_stmt.body, &repeat_stmt.cond, states)
            }
            HirStmt::NumericFor(numeric_for) => {
                self.validate_expr(&numeric_for.start, states)?;
                self.validate_expr(&numeric_for.limit, states)?;
                self.validate_expr(&numeric_for.step, states)?;
                self.validate_zero_or_more(&numeric_for.body, states)
            }
            HirStmt::GenericFor(generic_for) => {
                self.validate_pack(&generic_for.iterator, states)?;
                self.validate_zero_or_more(&generic_for.body, states)
            }
            _ => unreachable!("validate_loop only accepts loop statements"),
        }
    }

    fn validate_zero_or_more(&self, body: &HirBlock, states: RelationSet) -> Option<FlowOutcome> {
        let mut entries = states;
        let mut exits = FlowOutcome::default();
        for _ in 0..=3 {
            exits.fallthrough = exits.fallthrough.union(entries);
            let body_outcome = self.validate_block(&body.stmts, entries)?;
            exits.fallthrough = exits.fallthrough.union(body_outcome.breaks);
            exits.add_outgoing_all(body_outcome.outgoing);
            let backedge = body_outcome.fallthrough.union(body_outcome.continues);
            let next = entries.union(backedge);
            if next == entries {
                return Some(exits);
            }
            entries = next;
        }
        panic!("three-state monotone loop relation must converge within four rounds")
    }

    fn validate_while(
        &self,
        body: &HirBlock,
        condition: &HirExpr,
        states: RelationSet,
    ) -> Option<FlowOutcome> {
        let mut entries = states;
        let mut exits = FlowOutcome::default();
        let truthiness = expr_truthiness(condition, self.control_facts.expr_safety);
        for _ in 0..=3 {
            self.validate_expr(condition, entries)?;
            if truthiness != Some(true) {
                exits.fallthrough = exits.fallthrough.union(entries);
            }
            if truthiness == Some(false) {
                return Some(exits);
            }
            let body_outcome = self.validate_block(&body.stmts, entries)?;
            exits.fallthrough = exits.fallthrough.union(body_outcome.breaks);
            exits.add_outgoing_all(body_outcome.outgoing);
            let backedge = body_outcome.fallthrough.union(body_outcome.continues);
            let next = entries.union(backedge);
            if next == entries {
                return Some(exits);
            }
            entries = next;
        }
        panic!("three-state monotone condition relation must converge within four rounds")
    }

    fn validate_repeat(
        &self,
        body: &HirBlock,
        condition: &HirExpr,
        states: RelationSet,
    ) -> Option<FlowOutcome> {
        let mut entries = states;
        let mut exits = FlowOutcome::default();
        let truthiness = expr_truthiness(condition, self.control_facts.expr_safety);
        for _ in 0..=3 {
            let body_outcome = self.validate_block(&body.stmts, entries)?;
            let reaches_condition = body_outcome.fallthrough.union(body_outcome.continues);
            self.validate_expr(condition, reaches_condition)?;
            exits.fallthrough = exits.fallthrough.union(body_outcome.breaks);
            if truthiness != Some(false) {
                exits.fallthrough = exits.fallthrough.union(reaches_condition);
            }
            exits.add_outgoing_all(body_outcome.outgoing);
            if truthiness == Some(true) {
                return Some(exits);
            }
            let next = entries.union(reaches_condition);
            if next == entries {
                return Some(exits);
            }
            entries = next;
        }
        panic!("three-state monotone repeat relation must converge within four rounds")
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
        if expr_contains_unresolved(expr) {
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
    outgoing: BTreeMap<crate::hir::common::HirLabelId, RelationSet>,
}

impl FlowOutcome {
    fn fallthrough(states: RelationSet) -> Self {
        Self {
            fallthrough: states,
            ..Self::default()
        }
    }

    fn union(mut self, other: Self) -> Self {
        self.fallthrough = self.fallthrough.union(other.fallthrough);
        self.breaks = self.breaks.union(other.breaks);
        self.continues = self.continues.union(other.continues);
        self.add_outgoing_all(other.outgoing);
        self
    }

    fn add_outgoing(&mut self, target: crate::hir::common::HirLabelId, states: RelationSet) {
        self.outgoing
            .entry(target)
            .and_modify(|current| *current = current.union(states))
            .or_insert(states);
    }

    fn add_outgoing_all(
        &mut self,
        outgoing: BTreeMap<crate::hir::common::HirLabelId, RelationSet>,
    ) {
        for (target, states) in outgoing {
            self.add_outgoing(target, states);
        }
    }
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

fn expr_contains_unresolved(expr: &HirExpr) -> bool {
    let mut collector = UnresolvedExprCollector::default();
    visit_expr(expr, &mut collector);
    collector.found
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

fn writeback_region_has_barrier(stmts: &[HirStmt], control_facts: &RegionControlFacts) -> bool {
    let mut collector = WritebackBarrierCollector::default();
    visit_stmts(stmts, &mut collector);
    collector.found
        || LexicalCfg::analyze(stmts, &control_facts.label_refs, control_facts.expr_safety).is_err()
}

#[derive(Default)]
struct WritebackBarrierCollector {
    found: bool,
}

impl HirVisitor for WritebackBarrierCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.found |= matches!(expr, HirExpr::Unresolved(_));
    }
}

pub(super) fn region_has_hard_barrier(
    stmts: &[HirStmt],
    control_facts: &RegionControlFacts,
) -> bool {
    let mut collector = RegionBarrierCollector::default();
    visit_stmts(stmts, &mut collector);
    if collector.found {
        return true;
    }
    let Ok(_) = LexicalCfg::analyze(stmts, &control_facts.label_refs, control_facts.expr_safety)
    else {
        // 候选拒绝[SemanticBarrier:ControlFlow]：owner-wide label refs 证明候选区域有外部
        // 入口或重复 label；改写 result 声明/producer 会被该入口绕过或重执行。
        return true;
    };
    false
}

pub(super) fn expr_has_hard_barrier(expr: &HirExpr) -> bool {
    let mut collector = RegionBarrierCollector::default();
    visit_expr(expr, &mut collector);
    collector.found
}

#[derive(Default)]
struct RegionBarrierCollector {
    found: bool,
}

impl HirVisitor for RegionBarrierCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.found |= matches!(expr, HirExpr::Unresolved(_));
    }
}

impl HirVisitor for UnresolvedExprCollector {
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
    if let Some(values) = candidate.initializer {
        block.stmts[candidate.declaration] = HirStmt::Assign(Box::new(HirAssign {
            targets: vec![binding_lvalue(candidate.state)],
            values,
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
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

#[cfg(test)]
mod tests {
    use super::super::super::HandoffIdentityCollector;
    use super::*;
    use std::sync::LazyLock;

    use crate::decompile::DecompileDialect;
    use crate::hir::common::{
        HirBinaryExpr, HirBinaryOpKind, HirCapture, HirCaptureMode, HirClosureExpr,
        HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirGlobalDecl,
        HirGoto, HirIf, HirLabel, HirLabelId, HirPackTail, HirRepeat, HirReturn, HirWhile, TempId,
    };
    use crate::hir::promotion::HomeSlotKey;

    static EMPTY_CONTROL_FACTS: LazyLock<RegionControlFacts> =
        LazyLock::new(|| RegionControlFacts {
            label_refs: Default::default(),
            expr_safety: crate::hir::expr_safety::HirExprSafety::for_dialect(
                DecompileDialect::Lua54,
            ),
        });

    fn verifier() -> FlowVerifier<'static> {
        FlowVerifier {
            result: CarryBinding::Local(LocalId(0)),
            state: CarryBinding::Local(LocalId(1)),
            control_facts: &EMPTY_CONTROL_FACTS,
            validate_rewritten_reads: true,
        }
    }

    fn decision(test: HirExpr) -> HirExpr {
        HirExpr::Decision(Box::new(HirDecisionExpr {
            entry: HirDecisionNodeRef(0),
            nodes: vec![HirDecisionNode {
                id: HirDecisionNodeRef(0),
                test,
                truthy: HirDecisionTarget::CurrentValue,
                falsy: HirDecisionTarget::Expr(HirExpr::Boolean(false)),
            }],
        }))
    }

    fn identity_facts() -> HandoffIdentityFacts {
        HandoffIdentityFacts {
            debug: BTreeSet::new(),
            for_bindings: BTreeSet::new(),
            physical_roots: BTreeSet::new(),
            reference_captured: BTreeSet::new(),
            to_be_closed: BTreeSet::new(),
            preserved: BTreeSet::new(),
        }
    }

    fn identity_facts_for(stmts: &[HirStmt]) -> HandoffIdentityFacts {
        let mut collector = HandoffIdentityCollector::default();
        visit_stmts(stmts, &mut collector);
        HandoffIdentityFacts {
            debug: BTreeSet::new(),
            for_bindings: collector.for_bindings,
            physical_roots: BTreeSet::new(),
            reference_captured: collector.reference_captured,
            to_be_closed: collector.to_be_closed,
            preserved: BTreeSet::new(),
        }
    }

    fn capture_closure(mode: HirCaptureMode, value: HirExpr) -> HirExpr {
        HirExpr::Closure(Box::new(HirClosureExpr {
            proto: crate::hir::common::HirProtoRef(1),
            captures: vec![HirCapture { mode, value }],
        }))
    }

    fn control_facts(stmts: &[HirStmt]) -> RegionControlFacts {
        RegionControlFacts {
            label_refs: crate::hir::simplify::label_refs::count_label_references(stmts),
            expr_safety: crate::hir::expr_safety::HirExprSafety::for_dialect(
                DecompileDialect::Lua54,
            ),
        }
    }

    #[test]
    fn owner_label_refs_distinguish_closed_flow_from_external_entry() {
        let label = HirLabelId(0);
        let owner = vec![
            HirStmt::Goto(Box::new(HirGoto { target: label })),
            HirStmt::Label(Box::new(HirLabel {
                id: label,
                tbc_barriers: Default::default(),
            })),
        ];
        let control = control_facts(&owner);

        assert!(!region_has_hard_barrier(&owner, &control));
        assert!(region_has_hard_barrier(&owner[1..], &control));
    }

    #[test]
    fn region_external_goto_requires_a_synced_relation() {
        let label = HirLabelId(0);
        let goto = HirStmt::Goto(Box::new(HirGoto { target: label }));
        let owner = vec![
            goto.clone(),
            HirStmt::Label(Box::new(HirLabel {
                id: label,
                tbc_barriers: Default::default(),
            })),
        ];
        let control = control_facts(&owner);
        let rewrites = BTreeMap::from([(
            CarryBinding::Local(LocalId(0)),
            CarryBinding::Local(LocalId(1)),
        )]);

        assert!(!region_rewrites_preserve_external_transfers(
            std::slice::from_ref(&goto),
            &rewrites,
            &control,
            ExternalTransferScope::WholeRegion,
        ));
        let pending_then_goto = vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(LocalId(0))],
                values: HirValuePack::fixed(vec![HirExpr::Integer(9)]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            })),
            goto.clone(),
        ];
        assert!(!region_rewrites_preserve_external_transfers(
            &pending_then_goto,
            &rewrites,
            &control,
            ExternalTransferScope::WholeRegion,
        ));
        let synced_then_goto = vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(LocalId(0))],
                values: HirValuePack::fixed(vec![HirExpr::Integer(9)]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(LocalId(1))],
                values: HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(0))]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            })),
            goto,
        ];
        assert!(region_rewrites_preserve_external_transfers(
            &synced_then_goto,
            &rewrites,
            &control,
            ExternalTransferScope::WholeRegion,
        ));
    }

    #[test]
    fn writeback_transaction_accepts_disjoint_decision_reads() {
        let result = LocalId(0);
        let state = LocalId(1);
        let write_result = |value| {
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(result)],
                values: HirValuePack::fixed(vec![HirExpr::Integer(value)]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            }))
        };
        let mut block = HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![state],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(0)]),
                    initializer_merge_transaction: None,
                })),
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![result],
                    values: HirValuePack::default(),
                    initializer_merge_transaction: None,
                })),
                HirStmt::If(Box::new(HirIf {
                    cond: decision(HirExpr::TempRef(TempId(0))),
                    then_block: HirBlock {
                        stmts: vec![write_result(1)],
                    },
                    else_block: Some(HirBlock {
                        stmts: vec![write_result(2)],
                    }),
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(state)],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(result)]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
            ],
        };
        let mut facts = ProtoPromotionFacts::default();
        facts.record_local_home_slot(result, HomeSlotKey::new(0, 0));
        facts.record_local_home_slot(state, HomeSlotKey::new(0, 0));
        facts.mark_entry_nil_writes_pruned(result);

        let candidate = find_candidate(
            &block,
            &BTreeSet::new(),
            &facts,
            &identity_facts(),
            &EMPTY_CONTROL_FACTS,
            &BTreeSet::new(),
        )
        .expect("all Decision paths are disjoint from the carried bindings");
        apply_candidate(&mut block, candidate, &mut facts);

        assert!(
            collect_binding_mentions_by_stmt(&block.stmts)
                .iter()
                .all(|mentions| !mentions.contains(&CarryBinding::Local(result)))
        );
        assert!(matches!(
            block.stmts.as_slice(),
            [HirStmt::LocalDecl(_), HirStmt::If(_)]
        ));
    }

    #[test]
    fn writeback_transaction_follows_a_self_contained_goto() {
        let result = LocalId(0);
        let state = LocalId(1);
        let label = HirLabelId(0);
        let mut block = HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![state],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(0)]),
                    initializer_merge_transaction: None,
                })),
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![result],
                    values: HirValuePack::default(),
                    initializer_merge_transaction: None,
                })),
                HirStmt::Goto(Box::new(HirGoto { target: label })),
                HirStmt::Label(Box::new(HirLabel {
                    id: label,
                    tbc_barriers: Default::default(),
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(result)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(9)]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(state)],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(result)]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
            ],
        };
        let mut facts = ProtoPromotionFacts::default();
        for local in [result, state] {
            facts.record_local_home_slot(local, HomeSlotKey::new(0, 0));
        }
        facts.mark_entry_nil_writes_pruned(result);
        let control = control_facts(&block.stmts);

        let candidate = find_candidate(
            &block,
            &BTreeSet::new(),
            &facts,
            &identity_facts(),
            &control,
            &BTreeSet::new(),
        )
        .expect("the internal goto reaches the unique producer and writeback");
        apply_candidate(&mut block, candidate, &mut facts);

        assert!(matches!(block.stmts[1], HirStmt::Goto(_)));
        assert!(matches!(block.stmts[2], HirStmt::Label(_)));
        assert!(
            collect_binding_mentions_by_stmt(&block.stmts)
                .iter()
                .all(|mentions| !mentions.contains(&CarryBinding::Local(result)))
        );
    }

    #[test]
    fn writeback_transaction_rejects_goto_that_bypasses_sync() {
        let result = LocalId(0);
        let state = LocalId(1);
        let label = HirLabelId(0);
        let block = HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![state],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(0)]),
                    initializer_merge_transaction: None,
                })),
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![result],
                    values: HirValuePack::default(),
                    initializer_merge_transaction: None,
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(result)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(9)]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
                HirStmt::Goto(Box::new(HirGoto { target: label })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(state)],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(result)]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
                HirStmt::Label(Box::new(HirLabel {
                    id: label,
                    tbc_barriers: Default::default(),
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(state)]),
                })),
            ],
        };
        let mut facts = ProtoPromotionFacts::default();
        for local in [result, state] {
            facts.record_local_home_slot(local, HomeSlotKey::new(0, 0));
        }
        facts.mark_entry_nil_writes_pruned(result);
        let control = control_facts(&block.stmts);

        assert!(
            find_candidate(
                &block,
                &BTreeSet::new(),
                &facts,
                &identity_facts(),
                &control,
                &BTreeSet::new(),
            )
            .is_none()
        );
    }

    #[test]
    fn writeback_transaction_accepts_a_by_value_capture_after_sync() {
        let result = LocalId(0);
        let state = LocalId(1);
        let closure = LocalId(2);
        let mut block = HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![state],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(0)]),
                    initializer_merge_transaction: None,
                })),
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![result],
                    values: HirValuePack::default(),
                    initializer_merge_transaction: None,
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(result)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(9)]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(state)],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(result)]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![closure],
                    values: HirValuePack::fixed(vec![capture_closure(
                        HirCaptureMode::ByValue,
                        HirExpr::LocalRef(result),
                    )]),
                    initializer_merge_transaction: None,
                })),
            ],
        };
        let identity = identity_facts_for(&block.stmts);
        let mut facts = ProtoPromotionFacts::default();
        for local in [result, state] {
            facts.record_local_home_slot(local, HomeSlotKey::new(0, 0));
        }
        facts.mark_entry_nil_writes_pruned(result);

        let candidate = find_candidate(
            &block,
            &BTreeSet::new(),
            &facts,
            &identity,
            &EMPTY_CONTROL_FACTS,
            &BTreeSet::new(),
        )
        .expect("the snapshot observes the already-synchronized value");
        apply_candidate(&mut block, candidate, &mut facts);

        assert!(
            collect_binding_mentions_by_stmt(&block.stmts)
                .iter()
                .all(|mentions| !mentions.contains(&CarryBinding::Local(result)))
        );
    }

    #[test]
    fn writeback_transaction_accepts_an_exact_home_reference_capture() {
        let result = LocalId(0);
        let state = LocalId(1);
        let closure = LocalId(2);
        let mut block = HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![state],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(0)]),
                    initializer_merge_transaction: None,
                })),
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![result],
                    values: HirValuePack::default(),
                    initializer_merge_transaction: None,
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(result)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(9)]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(state)],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(result)]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![closure],
                    values: HirValuePack::fixed(vec![capture_closure(
                        HirCaptureMode::ByReference,
                        HirExpr::LocalRef(result),
                    )]),
                    initializer_merge_transaction: None,
                })),
            ],
        };
        let identity = identity_facts_for(&block.stmts);
        let mut facts = ProtoPromotionFacts::default();
        for local in [result, state] {
            facts.record_local_home_slot(local, HomeSlotKey::new(0, 0));
        }
        facts.mark_entry_nil_writes_pruned(result);

        let candidate = find_candidate(
            &block,
            &BTreeSet::new(),
            &facts,
            &identity,
            &EMPTY_CONTROL_FACTS,
            &BTreeSet::new(),
        )
        .expect("both names denote the same slot and close epoch upvalue cell");
        apply_candidate(&mut block, candidate, &mut facts);
    }

    #[test]
    fn identity_merge_keeps_a_reference_capture_without_exact_shared_home() {
        let source = CarryBinding::Local(LocalId(0));
        let target = CarryBinding::Local(LocalId(1));
        let mut identity = HandoffIdentityFacts {
            debug: BTreeSet::new(),
            for_bindings: BTreeSet::new(),
            physical_roots: BTreeSet::new(),
            reference_captured: BTreeSet::from([source]),
            to_be_closed: BTreeSet::new(),
            preserved: BTreeSet::new(),
        };
        let mut facts = ProtoPromotionFacts::default();
        facts.record_local_home_slot(LocalId(0), HomeSlotKey::new(0, 0));
        facts.record_local_home_slot(LocalId(1), HomeSlotKey::new(1, 0));

        assert!(!identity.binding_merge_preserves_identity(source, target, &facts));

        identity.reference_captured.clear();
        assert!(identity.binding_merge_preserves_identity(source, target, &facts));
        identity.preserved.insert(source);
        assert!(identity.contains(LocalId(0)));
        assert!(!identity.binding_merge_preserves_identity(source, target, &facts));
        identity.preserved = BTreeSet::from([CarryBinding::Local(LocalId(9))]);
        assert!(identity.binding_merge_preserves_identity(source, target, &facts));
    }

    #[test]
    fn decision_read_of_pending_state_remains_a_barrier() {
        assert!(
            verifier()
                .validate_expr(
                    &decision(HirExpr::LocalRef(LocalId(1))),
                    RelationSet::only(Relation::Pending),
                )
                .is_none()
        );
    }

    #[test]
    fn global_declaration_preserves_a_synced_transaction() {
        let stmt = HirStmt::GlobalDecl(Box::new(HirGlobalDecl {
            names: vec!["answer".into()],
            values: HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(0))]),
        }));

        let states = verifier()
            .validate_stmt(&stmt, RelationSet::only(Relation::Synced))
            .expect("a global declaration only reads the already-synced merged value");

        assert!(states == RelationSet::only(Relation::Synced));
    }

    #[test]
    fn terminating_nested_loop_path_does_not_block_synced_state() {
        let stmt = HirStmt::While(Box::new(HirWhile {
            cond: HirExpr::Boolean(true),
            body: HirBlock {
                stmts: vec![HirStmt::Return(Box::new(HirReturn {
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(0))]),
                }))],
            },
        }));

        let states = verifier()
            .validate_stmt(&stmt, RelationSet::only(Relation::Synced))
            .expect("return validates its values and does not rejoin the surrounding loop");

        assert!(states == RelationSet::EMPTY);
    }

    #[test]
    fn inner_loop_break_is_consumed_by_its_loop_owner() {
        let stmt = HirStmt::While(Box::new(HirWhile {
            cond: HirExpr::Boolean(true),
            body: HirBlock {
                stmts: vec![
                    HirStmt::While(Box::new(HirWhile {
                        cond: HirExpr::LocalRef(LocalId(0)),
                        body: HirBlock {
                            stmts: vec![HirStmt::Break],
                        },
                    })),
                    HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Local(LocalId(1))],
                        values: HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(0))]),
                        initializer_merge_transaction: None,
                        generic_for_initializer_producer: None,
                        method_rewrite_transaction: None,
                    })),
                ],
            },
        }));

        assert!(
            verifier()
                .validate_stmt(&stmt, RelationSet::only(Relation::Pending))
                .is_some()
        );
    }

    #[test]
    fn unknown_while_rejects_pending_state_after_one_iteration() {
        let stmts = vec![
            HirStmt::While(Box::new(HirWhile {
                cond: HirExpr::TempRef(TempId(0)),
                body: HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Local(LocalId(0))],
                        values: HirValuePack::fixed(vec![HirExpr::Integer(9)]),
                        initializer_merge_transaction: None,
                        generic_for_initializer_producer: None,
                        method_rewrite_transaction: None,
                    }))],
                },
            })),
            HirStmt::Return(Box::new(HirReturn {
                values: HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(1))]),
            })),
        ];

        assert!(
            verifier()
                .validate_region(&stmts, RelationSet::only(Relation::Unproduced))
                .is_none()
        );
    }

    #[test]
    fn unknown_while_accepts_a_synced_iteration_exit() {
        let stmts = vec![
            HirStmt::While(Box::new(HirWhile {
                cond: HirExpr::TempRef(TempId(0)),
                body: HirBlock {
                    stmts: vec![
                        HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Local(LocalId(0))],
                            values: HirValuePack::fixed(vec![HirExpr::Integer(9)]),
                            initializer_merge_transaction: None,
                            generic_for_initializer_producer: None,
                            method_rewrite_transaction: None,
                        })),
                        HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Local(LocalId(1))],
                            values: HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(0))]),
                            initializer_merge_transaction: None,
                            generic_for_initializer_producer: None,
                            method_rewrite_transaction: None,
                        })),
                    ],
                },
            })),
            HirStmt::Return(Box::new(HirReturn {
                values: HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(1))]),
            })),
        ];

        assert!(
            verifier()
                .validate_region(&stmts, RelationSet::only(Relation::Unproduced))
                .is_some()
        );
    }

    #[test]
    fn zero_or_more_loop_includes_each_iteration_termination_relation() {
        let pending_body = HirBlock {
            stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(LocalId(0))],
                values: HirValuePack::fixed(vec![HirExpr::Integer(9)]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            }))],
        };
        let pending = verifier()
            .validate_zero_or_more(&pending_body, RelationSet::only(Relation::Unproduced))
            .expect("loop body itself is valid");
        assert!(pending.fallthrough.contains(Relation::Unproduced));
        assert!(pending.fallthrough.contains(Relation::Pending));

        let synced_body = HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(LocalId(0))],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(9)]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(LocalId(1))],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(0))]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
            ],
        };
        let synced = verifier()
            .validate_zero_or_more(&synced_body, RelationSet::only(Relation::Unproduced))
            .expect("synchronized loop body is valid");
        assert!(synced.fallthrough.contains(Relation::Unproduced));
        assert!(synced.fallthrough.contains(Relation::Synced));
        assert!(!synced.fallthrough.contains(Relation::Pending));
    }

    #[test]
    fn constant_loop_truthiness_does_not_create_unreachable_exits() {
        let write_pending = || {
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(LocalId(0))],
                values: HirValuePack::fixed(vec![HirExpr::Integer(9)]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            }))
        };
        let return_old_state = || {
            HirStmt::Return(Box::new(HirReturn {
                values: HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(1))]),
            }))
        };
        let true_while = vec![
            HirStmt::While(Box::new(HirWhile {
                cond: HirExpr::Boolean(true),
                body: HirBlock {
                    stmts: vec![write_pending()],
                },
            })),
            return_old_state(),
        ];
        let false_repeat = vec![
            HirStmt::Repeat(Box::new(HirRepeat {
                body: HirBlock {
                    stmts: vec![write_pending()],
                },
                cond: HirExpr::Boolean(false),
                lifetime: Default::default(),
            })),
            return_old_state(),
        ];

        for stmts in [true_while, false_repeat] {
            let exits = verifier()
                .validate_region(&stmts, RelationSet::only(Relation::Unproduced))
                .expect("unreachable suffix cannot observe the pending relation");
            assert!(exits == RelationSet::EMPTY);
        }
    }

    #[test]
    fn terminating_return_accepts_an_unobserved_pending_state() {
        let stmt = HirStmt::Return(Box::new(HirReturn {
            values: HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(0))]),
        }));

        let states = verifier()
            .validate_stmt(&stmt, RelationSet::only(Relation::Pending))
            .expect("return observes result but no longer observes the unsynced state");

        assert!(states == RelationSet::EMPTY);
    }

    #[test]
    fn initializer_uses_first_slot_but_validates_the_complete_pack() {
        let verifier = verifier();
        let initializer = HirValuePack::expanding(
            vec![HirExpr::LocalRef(LocalId(1)), HirExpr::Integer(7)],
            HirPackTail::open(HirExpr::VarArg),
        );

        let states = verifier
            .validate_initializer(Some(&initializer))
            .expect("multi-expression initializer has an exact first target slot");

        assert!(states.contains(Relation::Synced));
        assert!(!states.contains(Relation::Pending));
    }

    #[test]
    fn parallel_assignment_tracks_the_last_merged_target() {
        let verifier = verifier();
        let assign = HirAssign {
            targets: vec![HirLValue::Local(LocalId(0)), HirLValue::Local(LocalId(1))],
            values: HirValuePack::fixed(vec![HirExpr::Integer(7), HirExpr::LocalRef(LocalId(0))]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        };

        let states = verifier
            .validate_assign(&assign, RelationSet::only(Relation::Pending))
            .expect("the final merged slot retains the original state write");

        assert!(states.contains(Relation::Unproduced));
        assert!(!states.contains(Relation::Pending));
    }

    #[test]
    fn parallel_assignment_rejects_old_state_read_during_pending_epoch() {
        let verifier = verifier();
        let assign = HirAssign {
            targets: vec![HirLValue::Local(LocalId(0)), HirLValue::Local(LocalId(1))],
            values: HirValuePack::fixed(vec![HirExpr::Integer(7), HirExpr::LocalRef(LocalId(1))]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        };

        assert!(
            verifier
                .validate_assign(&assign, RelationSet::only(Relation::Pending))
                .is_none()
        );
    }

    #[test]
    fn open_tail_assignment_tracks_each_consumed_target_slot() {
        let verifier = verifier();
        let assign = HirAssign {
            targets: vec![HirLValue::Temp(TempId(0)), HirLValue::Local(LocalId(1))],
            values: HirValuePack::expanding(Vec::new(), HirPackTail::open(HirExpr::VarArg)),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        };

        let states = verifier
            .validate_assign(&assign, RelationSet::only(Relation::Pending))
            .expect("tail result positions remain unchanged by the binding rewrite");

        assert!(states.contains(Relation::Unproduced));
        assert!(!states.contains(Relation::Pending));
    }

    #[test]
    fn parallel_writeback_target_is_discovered_from_its_rhs_slot() {
        let result = CarryBinding::Local(LocalId(0));
        let assign = HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(TempId(0)), HirLValue::Local(LocalId(1))],
            values: HirValuePack::fixed(vec![HirExpr::Integer(7), HirExpr::LocalRef(LocalId(0))]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }));

        assert!(writeback_targets(&[assign], result) == vec![CarryBinding::Local(LocalId(1))]);
    }

    #[test]
    fn completed_writeback_filter_excludes_parallel_side_copy() {
        let result = CarryBinding::Local(LocalId(0));
        let first = CarryBinding::Local(LocalId(1));
        let second = CarryBinding::Local(LocalId(2));
        let stmts = vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(LocalId(0))],
                values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(LocalId(1)), HirLValue::Local(LocalId(2))],
                values: HirValuePack::fixed(vec![
                    HirExpr::LocalRef(LocalId(0)),
                    HirExpr::Binary(Box::new(HirBinaryExpr {
                        op: HirBinaryOpKind::Add,
                        lhs: HirExpr::LocalRef(LocalId(0)),
                        rhs: HirExpr::LocalRef(LocalId(2)),
                    })),
                ]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            })),
        ];
        let eligible = writeback_targets(&stmts, result);

        assert!(eligible == vec![first, second]);
        assert!(
            completed_writeback_states(result, &eligible, None, &stmts, &EMPTY_CONTROL_FACTS,)
                == vec![first]
        );
    }

    #[test]
    fn completed_writeback_filter_reports_each_fully_verified_owner() {
        let result = CarryBinding::Local(LocalId(0));
        let first = CarryBinding::Local(LocalId(1));
        let second = CarryBinding::Local(LocalId(2));
        let write_both = |targets| {
            HirStmt::Assign(Box::new(HirAssign {
                targets,
                values: HirValuePack::fixed(vec![
                    HirExpr::LocalRef(LocalId(0)),
                    HirExpr::LocalRef(LocalId(0)),
                ]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            }))
        };
        let stmts = vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(LocalId(0))],
                values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            })),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::TempRef(TempId(0)),
                then_block: HirBlock {
                    stmts: vec![write_both(vec![
                        HirLValue::Local(LocalId(1)),
                        HirLValue::Local(LocalId(2)),
                    ])],
                },
                else_block: Some(HirBlock {
                    stmts: vec![write_both(vec![
                        HirLValue::Local(LocalId(2)),
                        HirLValue::Local(LocalId(1)),
                    ])],
                }),
            })),
        ];
        let eligible = writeback_targets(&stmts, result);

        assert!(eligible == vec![first, second]);
        assert!(
            completed_writeback_states(result, &eligible, None, &stmts, &EMPTY_CONTROL_FACTS,)
                == vec![first, second]
        );
    }

    #[test]
    fn multiple_completed_targets_choose_one_fully_verified_owner() {
        let write_both = |targets| {
            HirStmt::Assign(Box::new(HirAssign {
                targets,
                values: HirValuePack::fixed(vec![
                    HirExpr::LocalRef(LocalId(0)),
                    HirExpr::LocalRef(LocalId(0)),
                ]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            }))
        };
        let mut block = HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![LocalId(1)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                    initializer_merge_transaction: None,
                })),
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![LocalId(2)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(2)]),
                    initializer_merge_transaction: None,
                })),
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![LocalId(0)],
                    values: HirValuePack::default(),
                    initializer_merge_transaction: None,
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(LocalId(0))],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::TempRef(TempId(0)),
                    then_block: HirBlock {
                        stmts: vec![write_both(vec![
                            HirLValue::Local(LocalId(1)),
                            HirLValue::Local(LocalId(2)),
                        ])],
                    },
                    else_block: Some(HirBlock {
                        stmts: vec![write_both(vec![
                            HirLValue::Local(LocalId(2)),
                            HirLValue::Local(LocalId(1)),
                        ])],
                    }),
                })),
            ],
        };
        let mut facts = ProtoPromotionFacts::default();
        for local in [LocalId(0), LocalId(1), LocalId(2)] {
            facts.record_local_home_slot(local, HomeSlotKey::new(0, 0));
        }
        let identity = HandoffIdentityFacts {
            debug: BTreeSet::new(),
            for_bindings: BTreeSet::new(),
            physical_roots: BTreeSet::new(),
            reference_captured: BTreeSet::new(),
            to_be_closed: BTreeSet::new(),
            preserved: BTreeSet::new(),
        };

        let candidate = find_candidate(
            &block,
            &BTreeSet::new(),
            &facts,
            &identity,
            &EMPTY_CONTROL_FACTS,
            &BTreeSet::new(),
        )
        .expect("each completed target is independently safe as the transaction owner");
        assert!(candidate.state == CarryBinding::Local(LocalId(1)));

        apply_candidate(&mut block, candidate, &mut facts);
        assert!(
            collect_binding_mentions_by_stmt(&block.stmts)
                .iter()
                .all(|mentions| !mentions.contains(&CarryBinding::Local(LocalId(0))))
        );
    }

    #[test]
    fn apply_keeps_parallel_last_write_after_result_merge() {
        let mut block = HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![LocalId(0)],
                    values: HirValuePack::default(),
                    initializer_merge_transaction: None,
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(LocalId(0)), HirLValue::Local(LocalId(1))],
                    values: HirValuePack::fixed(vec![
                        HirExpr::Integer(7),
                        HirExpr::LocalRef(LocalId(0)),
                    ]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
            ],
        };

        apply_candidate(
            &mut block,
            Candidate {
                declaration: 0,
                last_mention: 1,
                result: LocalId(0),
                state: CarryBinding::Local(LocalId(1)),
                initializer: None,
            },
            &mut ProtoPromotionFacts::default(),
        );

        let [HirStmt::Assign(assign)] = block.stmts.as_slice() else {
            panic!("result declaration should be removed without splitting the assignment");
        };
        assert!(assign.targets == vec![HirLValue::Local(LocalId(1)), HirLValue::Local(LocalId(1))]);
        assert!(assign.values.fixed == vec![HirExpr::Integer(7), HirExpr::LocalRef(LocalId(1))]);
    }
}
