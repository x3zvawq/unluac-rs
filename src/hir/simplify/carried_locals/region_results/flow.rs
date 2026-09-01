//! 路径敏感地消除机械 result -> carried state 交棒。
//!
//! Structure/HIR 已经提供结构化分支与循环、binding 的 `(slot, close epoch)`、capture 和
//! source debug 身份；这里在这些事实之上证明两个 HIR binding 只是同一物理状态的阶段性
//! 名称，不重新推断 CFG owner，也不移动或复制 RHS。证明只接受同一精确 home-slot，并沿
//! 每条结构化路径跟踪 `Unproduced/Pending/Synced`；Decision 的全部 test/target 读取按并集
//! 保守验证，而多值、goto、cleanup 或 Unresolved 等未建模边界会保留原形。
//!
//! 例如 `local r; if c then r = s + 1 else r = s + 2 end; s = r` 会收成两臂直接更新
//! `s`；若任一路在同步前读取旧 `s`、跳出循环，或随后仍读取已经被消费的 `r`，则整项拒绝。

use std::collections::BTreeSet;

use crate::hir::common::{HirAssign, HirBlock, HirExpr, HirLValue, HirStmt, HirValuePack, LocalId};
use crate::hir::promotion::ProtoPromotionFacts;

use super::super::super::visit::{HirVisitor, visit_expr, visit_stmts};
use super::super::super::walk::rewrite_stmts;
use super::super::HandoffIdentityFacts;
use super::super::binding::{
    BindingClassRewritePass, BindingProtection, CarryBinding, binding_home_slot,
    carry_binding_from_expr, carry_binding_from_lvalue,
};
use super::super::prune::{RedundantSelfAssignPrunePass, prune_empty_assign_stmts};
use super::super::reads::{BindingReadCollector, collect_binding_mentions_by_stmt};
use super::binding_facts;

pub(in crate::hir::simplify::carried_locals) fn collapse_result_writeback_transactions(
    block: &mut HirBlock,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &mut ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
    inherited_locals: &BTreeSet<LocalId>,
) -> bool {
    let mut changed = false;
    while let Some(candidate) = find_candidate(
        block,
        outer_bindings,
        promotion_facts,
        identity_facts,
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
        // 候选拒绝[SemanticBarrier:Capture]：captured/outer result 可在 region 外被观察，不能删除其 cell identity。
        if identity_facts.contains(result)
            || outer_bindings.contains(&result_binding)
            || identity_facts.captured.contains(&result_binding)
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
        if writeback_region_has_barrier(&block.stmts[declaration + 1..=last_mention]) {
            // 候选拒绝[PolicyBoundary]：Unresolved 是 permissive 输出保留的失败证据。
            // 候选拒绝[SemanticBarrier:ControlFlow]：goto/label 可引入未被结构化 verifier 覆盖的入口与出口。
            // 候选拒绝[SemanticBarrier:Lifetime]：跨过 TBC/Close 后合并 result/state 会改变
            // resource 所属 cell 的 close epoch；close owner 已先运行，残余节点就是活边界。
            continue;
        }
        let eligible_states =
            writeback_targets(&block.stmts[declaration + 1..=last_mention], result_binding)
                .into_iter()
                .filter(|state| {
                    *state != result_binding
                        && identity_facts.binding_merge_preserves_identity(
                            result_binding,
                            *state,
                            promotion_facts,
                        )
                        && !state
                            .local()
                            .is_some_and(|local| identity_facts.for_bindings.contains(&local))
                        && binding_available_before(
                            block,
                            declaration,
                            *state,
                            outer_bindings,
                            inherited_locals,
                        )
                        && same_exact_home_slot(result_binding, *state, promotion_facts)
                })
                .collect::<Vec<_>>();
        if eligible_states.is_empty() {
            // 候选拒绝[SemanticBarrier:Lifetime]：capture/for/不可用/异槽 state 与 result
            // 具有可区分的作用域或 root epoch。
            continue;
        }
        let completed_states = completed_writeback_states(
            result_binding,
            &eligible_states,
            initializer,
            &block.stmts[declaration + 1..=last_mention],
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
) -> Vec<CarryBinding> {
    eligible_states
        .iter()
        .copied()
        .filter(|state| {
            let verifier = FlowVerifier {
                result,
                state: *state,
            };
            let Some(states) = verifier.validate_initializer(initializer) else {
                return false;
            };
            verifier
                .validate_stmts(stmts, states)
                .is_some_and(|states| !states.contains(Relation::Pending))
        })
        .collect()
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
struct FlowVerifier {
    result: CarryBinding,
    state: CarryBinding,
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

    fn validate_stmts(&self, stmts: &[HirStmt], mut states: RelationSet) -> Option<RelationSet> {
        for stmt in stmts {
            if states.is_empty() {
                break;
            }
            states = self.validate_stmt(stmt, states)?;
        }
        Some(states)
    }

    fn validate_stmt(&self, stmt: &HirStmt, states: RelationSet) -> Option<RelationSet> {
        match stmt {
            HirStmt::Assign(assign) => self.validate_assign(assign, states),
            HirStmt::If(if_stmt) => {
                self.validate_expr(&if_stmt.cond, states)?;
                let then_states = self.validate_stmts(&if_stmt.then_block.stmts, states)?;
                let else_states = if let Some(else_block) = &if_stmt.else_block {
                    self.validate_stmts(&else_block.stmts, states)?
                } else {
                    states
                };
                Some(then_states.union(else_states))
            }
            HirStmt::Block(block) => self.validate_stmts(&block.stmts, states),
            HirStmt::Return(return_stmt) => {
                self.validate_pack(&return_stmt.values, states)?;
                // 候选拒绝[SemanticBarrier:ControlFlow]：Pending 路径 return 时原 state 仍旧，result 改名会在返回前提前覆盖 state/capture。
                (!states.contains(Relation::Pending)).then_some(RelationSet::EMPTY)
            }
            HirStmt::Break | HirStmt::Continue => {
                // 候选拒绝[SemanticBarrier:ControlFlow]：Pending 路径提前转移时没有执行 writeback，不能把 result producer 直接改成 state write。
                (!states.contains(Relation::Pending)).then_some(RelationSet::EMPTY)
            }
            HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::NumericFor(_)
            | HirStmt::GenericFor(_) => self.validate_loop(stmt, states),
            HirStmt::Goto(_) | HirStmt::Label(_) | HirStmt::ToBeClosed(_) | HirStmt::Close(_) => {
                // 候选拒绝[SemanticBarrier:ControlFlow]：goto 可从 Pending 路径跳过 writeback，
                // 或从外部 label 入口绕过 producer；三态结构流不能把这种路径当作 Synced。
                // 候选拒绝[SemanticBarrier:Lifetime]：TBC/Close 位于 result producer 与
                // writeback 之间时，合并 cell 会改变 resource 的 close/root epoch。
                None
            }
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
                Some(states)
            }
            HirStmt::TableSetList(_) | HirStmt::ErrNil(_) | HirStmt::CallStmt(_) => {
                self.validate_leaf(stmt, states)?;
                Some(states)
            }
            HirStmt::GlobalDecl(_) => None,
        }
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

    fn validate_loop(&self, stmt: &HirStmt, states: RelationSet) -> Option<RelationSet> {
        let mentions = collect_binding_mentions_by_stmt(std::slice::from_ref(stmt));
        let mentions_result = mentions[0].contains(&self.result);
        let mentions_state = mentions[0].contains(&self.state);
        if !mentions_result && !mentions_state {
            return Some(states);
        }
        if (mentions_result && states.contains(Relation::Unproduced))
            || stmt_has_nested_transfer(stmt)
        {
            // 候选拒绝[SemanticBarrier:ControlFlow]：未产出 result 进入 loop 或 nested break/continue/return 会形成当前 fixed-point 未记录的出口/回边。
            return None;
        }
        match stmt {
            HirStmt::While(while_stmt) => {
                self.validate_loop_condition(&while_stmt.body, &while_stmt.cond, states, true)
            }
            HirStmt::Repeat(repeat_stmt) => {
                self.validate_loop_condition(&repeat_stmt.body, &repeat_stmt.cond, states, false)
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

    fn validate_zero_or_more(&self, body: &HirBlock, states: RelationSet) -> Option<RelationSet> {
        let mut entries = states;
        for _ in 0..=3 {
            let exits = self.validate_stmts(&body.stmts, entries)?;
            let next = entries.union(exits);
            if next == entries {
                return Some(entries);
            }
            entries = next;
        }
        panic!("three-state monotone loop relation must converge within four rounds")
    }

    fn validate_loop_condition(
        &self,
        body: &HirBlock,
        condition: &HirExpr,
        states: RelationSet,
        may_run_zero_times: bool,
    ) -> Option<RelationSet> {
        let mut entries = states;
        let mut exits = RelationSet::EMPTY;
        for _ in 0..=3 {
            if may_run_zero_times {
                self.validate_expr(condition, entries)?;
                exits = exits.union(entries);
            }
            let body_exits = self.validate_stmts(&body.stmts, entries)?;
            if !may_run_zero_times {
                self.validate_expr(condition, body_exits)?;
                exits = exits.union(body_exits);
            }
            let next = entries.union(body_exits);
            if next == entries {
                return Some(exits);
            }
            entries = next;
        }
        panic!("three-state monotone condition relation must converge within four rounds")
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

fn writeback_region_has_barrier(stmts: &[HirStmt]) -> bool {
    let mut collector = WritebackBarrierCollector::default();
    visit_stmts(stmts, &mut collector);
    collector.found
}

#[derive(Default)]
struct WritebackBarrierCollector {
    found: bool,
}

impl HirVisitor for WritebackBarrierCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.found |= matches!(
            stmt,
            HirStmt::Goto(_) | HirStmt::Label(_) | HirStmt::ToBeClosed(_) | HirStmt::Close(_)
        );
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        self.found |= matches!(expr, HirExpr::Unresolved(_));
    }
}

pub(super) fn region_has_hard_barrier(stmts: &[HirStmt]) -> bool {
    let mut collector = RegionBarrierCollector::default();
    visit_stmts(stmts, &mut collector);
    collector.found
}

pub(super) fn expr_has_hard_barrier(expr: &HirExpr) -> bool {
    let mut collector = RegionBarrierCollector::default();
    visit_expr(expr, &mut collector);
    collector.found
}

fn stmt_has_nested_transfer(stmt: &HirStmt) -> bool {
    let mut collector = NestedTransferCollector::default();
    visit_stmts(std::slice::from_ref(stmt), &mut collector);
    collector.found
}

#[derive(Default)]
struct NestedTransferCollector {
    found: bool,
}

impl HirVisitor for NestedTransferCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.found |= matches!(
            stmt,
            HirStmt::Break | HirStmt::Continue | HirStmt::Return(_)
        );
    }
}

#[derive(Default)]
struct RegionBarrierCollector {
    found: bool,
}

impl HirVisitor for RegionBarrierCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.found |= matches!(
            stmt,
            HirStmt::Goto(_) | HirStmt::Label(_) | HirStmt::ToBeClosed(_) | HirStmt::Close(_)
        );
    }

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
    use super::*;
    use crate::hir::common::{
        HirBinaryExpr, HirBinaryOpKind, HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef,
        HirDecisionTarget, HirIf, HirPackTail, TempId,
    };
    use crate::hir::promotion::HomeSlotKey;

    fn verifier() -> FlowVerifier {
        FlowVerifier {
            result: CarryBinding::Local(LocalId(0)),
            state: CarryBinding::Local(LocalId(1)),
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
            captured: BTreeSet::new(),
            reference_captured: BTreeSet::new(),
            to_be_closed: BTreeSet::new(),
        }
    }

    #[test]
    fn writeback_transaction_accepts_disjoint_decision_reads() {
        let result = LocalId(0);
        let state = LocalId(1);
        let write_result = |value| {
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(result)],
                values: HirValuePack::fixed(vec![HirExpr::Integer(value)]),
            }))
        };
        let mut block = HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![state],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(0)]),
                })),
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![result],
                    values: HirValuePack::default(),
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
            })),
        ];
        let eligible = writeback_targets(&stmts, result);

        assert!(eligible == vec![first, second]);
        assert!(completed_writeback_states(result, &eligible, None, &stmts) == vec![first]);
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
            }))
        };
        let stmts = vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(LocalId(0))],
                values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
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
        assert!(completed_writeback_states(result, &eligible, None, &stmts) == vec![first, second]);
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
            }))
        };
        let mut block = HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![LocalId(1)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                })),
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![LocalId(2)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(2)]),
                })),
                HirStmt::LocalDecl(Box::new(crate::hir::common::HirLocalDecl {
                    bindings: vec![LocalId(0)],
                    values: HirValuePack::default(),
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(LocalId(0))],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
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
            captured: BTreeSet::new(),
            reference_captured: BTreeSet::new(),
            to_be_closed: BTreeSet::new(),
        };

        let candidate = find_candidate(
            &block,
            &BTreeSet::new(),
            &facts,
            &identity,
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
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(LocalId(0)), HirLValue::Local(LocalId(1))],
                    values: HirValuePack::fixed(vec![
                        HirExpr::Integer(7),
                        HirExpr::LocalRef(LocalId(0)),
                    ]),
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
