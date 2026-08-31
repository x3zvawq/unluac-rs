//! 路径敏感地消除机械 result -> carried state 交棒。
//!
//! Structure/HIR 已经提供结构化分支与循环、binding 的 `(slot, close epoch)`、capture 和
//! source debug 身份；这里在这些事实之上证明两个 HIR binding 只是同一物理状态的阶段性
//! 名称，不重新推断 CFG owner，也不移动或复制 RHS。证明只接受同一精确 home-slot，并沿
//! 每条结构化路径跟踪 `Unproduced/Pending/Synced`，所以多值、goto、cleanup 或残留 Decision
//! 等未建模边界会保留原形。
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
        // 候选拒绝[LayerBoundary]：debug/source identity 的 result 由 locals owner 保留。
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
        if region_has_forbidden_nodes(&block.stmts[declaration + 1..=last_mention]) {
            // 候选拒绝[LayerBoundary]：Decision/Unresolved 交给 decision/elimination owner；TBC/Close 交给资源身份 owner。
            // 候选拒绝[SemanticBarrier:ControlFlow]：goto/label 可引入未被结构化 verifier 覆盖的入口与出口。
            continue;
        }
        let state_candidates =
            writeback_targets(&block.stmts[declaration + 1..=last_mention], result_binding);
        let [state] = state_candidates.as_slice() else {
            // 候选拒绝[ProofIncomplete]：零/多个 writeback target 需要 reaching-def/phi 对应关系，当前 verifier 只建模唯一 state。
            continue;
        };
        let state = *state;
        // 候选拒绝[SemanticBarrier:Lifetime]：capture/for/不可用/异槽 state 与 result 具有可区分的作用域或 root epoch。
        if state == result_binding
            || !identity_facts.binding_merge_preserves_identity(
                result_binding,
                state,
                promotion_facts,
            )
            || state
                .local()
                .is_some_and(|local| identity_facts.for_bindings.contains(&local))
            || !binding_available_before(
                block,
                declaration,
                state,
                outer_bindings,
                inherited_locals,
            )
            || !same_exact_home_slot(result_binding, state, promotion_facts)
        {
            continue;
        }
        let verifier = FlowVerifier {
            result: result_binding,
            state,
        };
        let Some(states) = verifier.validate_initializer(initializer) else {
            // 候选拒绝[ProofIncomplete]：initializer 的宽值/opaque/候选读取关系未被三态 verifier 表达。
            continue;
        };
        let Some(states) =
            verifier.validate_stmts(&block.stmts[declaration + 1..=last_mention], states)
        else {
            // 候选拒绝[ProofIncomplete]：region 含当前三态转移表未覆盖的 assignment/loop/opaque 组合；需增强路径 relation。
            continue;
        };
        if states.contains(Relation::Pending) {
            // 候选拒绝[SemanticBarrier:Lifetime]：存在出口上 result 已产出而 state 未同步；改名会让该路径提前覆盖旧 state。
            continue;
        }
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
    if local_decl.values.tail.is_some() || local_decl.values.fixed.len() > 1 {
        return None;
    }
    Some((
        *result,
        (!local_decl.values.fixed.is_empty()).then_some(&local_decl.values),
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

struct WritebackTargetCollector {
    result: CarryBinding,
    targets: BTreeSet<CarryBinding>,
}

impl HirVisitor for WritebackTargetCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        let HirStmt::Assign(assign) = stmt else {
            return;
        };
        let ([target], [value], None) = (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail,
        ) else {
            return;
        };
        if binding_reads_in_expr(value).contains(&self.result)
            && let Some(target) = carry_binding_from_lvalue(target)
            && target != self.result
        {
            self.targets.insert(target);
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
        let [value] = initializer.fixed.as_slice() else {
            // 候选拒绝[ProofIncomplete]：多 fixed initializer 尚未建立 result 对应 value 的精确宽度映射。
            return None;
        };
        let states = RelationSet::only(Relation::Unproduced);
        self.validate_expr(value, states)?;
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
                // 候选拒绝[LayerBoundary]：非结构跳转与 close epoch 不属于三态 verifier；分别由 CFG/resource owner 消费。
                None
            }
            HirStmt::LocalDecl(local_decl) => {
                if local_decl
                    .bindings
                    .iter()
                    .copied()
                    .any(|local| [self.result, self.state].contains(&CarryBinding::Local(local)))
                    || local_decl.values.tail.is_some()
                        && self.pack_mentions_candidate(&local_decl.values)
                {
                    // 候选拒绝[SemanticBarrier:Scope]：region 内重声明 result/state 会让批量 LocalId 改名跨越 lexical owner。
                    // 候选拒绝[ProofIncomplete]：open-tail local pack 提及候选时缺逐目标 value-width 关系。
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
        let ([target], [value], None) = (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail,
        ) else {
            // 候选拒绝[ProofIncomplete]：复杂 assignment 只有在完全不提候选时可穿过；候选相关并行/value-pack 转移尚未建模。
            return (!self.assign_mentions_candidate(assign)).then_some(states);
        };
        self.validate_expr(value, states)?;
        self.validate_lvalue_address(target, states)?;
        match carry_binding_from_lvalue(target) {
            Some(target) if target == self.result => {
                if carry_binding_from_expr(value) == Some(self.result) {
                    Some(states)
                } else if carry_binding_from_expr(value) == Some(self.state) {
                    Some(RelationSet::only(Relation::Synced))
                } else {
                    Some(RelationSet::only(Relation::Pending))
                }
            }
            Some(target) if target == self.state => {
                let reads = binding_reads_in_expr(value);
                let reads_result = reads.contains(&self.result);
                let reads_state = reads.contains(&self.state);
                if reads_result && !reads_state {
                    Some(RelationSet::only(
                        if carry_binding_from_expr(value) == Some(self.result) {
                            Relation::Synced
                        } else {
                            Relation::Unproduced
                        },
                    ))
                } else if !reads_result {
                    Some(RelationSet::only(Relation::Unproduced))
                } else {
                    // 候选拒绝[ProofIncomplete]：state RHS 同时读取 pending result 与旧 state 时，改名后两者同名，需表达式级双 epoch substitution。
                    None
                }
            }
            _ => Some(states),
        }
    }

    fn validate_loop(&self, stmt: &HirStmt, states: RelationSet) -> Option<RelationSet> {
        let mentions = collect_binding_mentions_by_stmt(std::slice::from_ref(stmt));
        if mentions[0].contains(&self.state) {
            // 候选拒绝[ProofIncomplete]：loop 内 state mention 被 blanket 拒绝；需 loop-carried relation fixed-point 区分安全同步读写。
            return None;
        }
        if !mentions[0].contains(&self.result) {
            return Some(states);
        }
        if states.contains(Relation::Unproduced) || stmt_has_nested_transfer(stmt) {
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
        // 候选拒绝[ConvergenceGuard]：RelationSet 仅三位且 union 单调，四轮仍不稳定表示 transfer 不变量损坏。
        None
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
        // 候选拒绝[ConvergenceGuard]：三态单调 fixed-point 四轮仍不收敛表示 relation transfer 不变量损坏。
        None
    }

    fn validate_leaf(&self, stmt: &HirStmt, states: RelationSet) -> Option<()> {
        if stmt_contains_opaque_expr(stmt) {
            // 候选拒绝[LayerBoundary]：Decision/Unresolved 的内部读取路径由 decision owner 解析，leaf verifier 不展开。
            return None;
        }
        let mut reads = BindingReadCollector::default();
        reads.collect_stmts(std::slice::from_ref(stmt));
        self.validate_reads(&reads.reads, states)
    }

    fn validate_pack(&self, pack: &HirValuePack, states: RelationSet) -> Option<()> {
        if pack.tail.is_some() && self.pack_mentions_candidate(pack) {
            // 候选拒绝[ProofIncomplete]：open-tail 中候选值的多返回宽度与消费位置尚未建模。
            return None;
        }
        for value in pack {
            self.validate_expr(value, states)?;
        }
        Some(())
    }

    fn validate_expr(&self, expr: &HirExpr, states: RelationSet) -> Option<()> {
        if expr_contains_opaque(expr) {
            // 候选拒绝[LayerBoundary]：opaque Decision/Unresolved 的路径读取交由其 owner 消解后再审计。
            return None;
        }
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

    fn stmt_mentions_candidate(&self, stmt: &HirStmt) -> bool {
        let mentions = collect_binding_mentions_by_stmt(std::slice::from_ref(stmt));
        mentions[0].contains(&self.result) || mentions[0].contains(&self.state)
    }

    fn assign_mentions_candidate(&self, assign: &HirAssign) -> bool {
        let stmt = HirStmt::Assign(Box::new(assign.clone()));
        self.stmt_mentions_candidate(&stmt)
    }

    fn pack_mentions_candidate(&self, pack: &HirValuePack) -> bool {
        pack.into_iter().any(|expr| {
            let reads = binding_reads_in_expr(expr);
            reads.contains(&self.result) || reads.contains(&self.state)
        })
    }
}

#[derive(Clone, Copy)]
enum Relation {
    Unproduced = 1,
    Pending = 2,
    Synced = 4,
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

fn expr_contains_opaque(expr: &HirExpr) -> bool {
    let mut collector = OpaqueExprCollector::default();
    visit_expr(expr, &mut collector);
    collector.found
}

fn stmt_contains_opaque_expr(stmt: &HirStmt) -> bool {
    let mut collector = OpaqueExprCollector::default();
    visit_stmts(std::slice::from_ref(stmt), &mut collector);
    collector.found
}

#[derive(Default)]
struct OpaqueExprCollector {
    found: bool,
}

pub(super) fn region_has_forbidden_nodes(stmts: &[HirStmt]) -> bool {
    let mut collector = ForbiddenNodeCollector::default();
    visit_stmts(stmts, &mut collector);
    collector.found
}

pub(super) fn expr_has_forbidden_nodes(expr: &HirExpr) -> bool {
    let mut collector = ForbiddenNodeCollector::default();
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
struct ForbiddenNodeCollector {
    found: bool,
}

impl HirVisitor for ForbiddenNodeCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.found |= matches!(
            stmt,
            HirStmt::Goto(_) | HirStmt::Label(_) | HirStmt::ToBeClosed(_) | HirStmt::Close(_)
        );
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        self.found |= matches!(expr, HirExpr::Decision(_) | HirExpr::Unresolved(_));
    }
}

impl HirVisitor for OpaqueExprCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.found |= matches!(expr, HirExpr::Decision(_) | HirExpr::Unresolved(_));
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
