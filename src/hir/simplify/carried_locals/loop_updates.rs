//! 循环内 `next -> carried` 写回的窄化折叠。
//!
//! 结构计划会保留 SSA 中“本轮新值”和“下轮 carried 值”的独立身份。局部提升后，
//! 若循环中途 `break`/`return`，这种身份边界通常表现为
//! `local next = f(carried)`，并在循环尾写回 `carried = next`。当 local 身份在循环外
//! 已死时可以直接复用 carried；repeat 的 next-value 若只是唯一的尾部 temp，则还可在
//! 所有路径必经写回、后缀无状态改写与词法跳转的前提下，把条件和 live-out 一并归回
//! carried。
//!
//! 该规则依赖结构化 loop、binding mentions/capture/TBC 身份和 promotion 提供的精确
//! `(slot, close epoch)`；它不重新推断 loop owner，也不会跨 distinct slot 移动可观察状态。
//! 相邻 `next = carried + 1; carried = next` 可直接收回；中间若有 `guard = xs[next]` 之类
//! consumer，则只有 next/carried 同一 home-slot、consumer 不提旧 carried 且没有控制转移时，
//! 才恢复为 `carried = carried + 1; guard = xs[carried]`。capture、for binding、TBC、提前退出
//! 或 label barrier 均保留原形。旧 local 形状即使尾写回前只有提前退出，也必须有同一可信
//! home；compaction 标志和不与该 home alias 的 cleanup 不改变这项 slot/epoch 证明。
//! local fold 的 apply 会在任何修改前重验 seed 与尾写回；只有完整提交才返回 changed，避免
//! candidate 形状漂移污染 fixed-point 信号。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirLValue, HirLabelId, HirStmt, LocalId, TempId,
};
use crate::hir::expr_safety::{HirEvalEffects, HirExprSafety};
use crate::hir::promotion::{HomeSlots, ProtoPromotionFacts};

use super::super::label_refs::count_label_references;
use super::super::lexical_cfg::LexicalCfg;
use super::super::local_shapes::initialized_single_local_decl;
use super::super::mention::{stmts_captured_locals, stmts_mention_local};
use super::super::walk::{rewrite_expr, rewrite_stmts};
use super::HandoffIdentityFacts;
use super::binding::{
    BindingClassRewritePass, BindingHomeOverlap, BindingProtection, CarryBinding,
    binding_home_overlap, bindings_share_exact_home_slot, carry_binding_from_lvalue,
    record_binding_merge,
};
use super::prune::RedundantSelfAssignPrunePass;
use super::reads::{BindingMentionIndex, BindingReadCollector, BlockMentions};
use crate::hir::visit::{HirVisitor, visit_stmts};

struct LoopUpdateFold {
    seed_index: usize,
    carried: LocalId,
    next: LocalId,
    seed: HirStmt,
    writeback: HirStmt,
}

struct LoopUpdateBlockFacts<'a> {
    mentions: BlockMentions<'a>,
    label_refs: BTreeMap<HirLabelId, usize>,
    expr_safety: HirExprSafety,
}

struct RepeatUpdateSafety<'a> {
    outer_bindings: &'a dyn BindingProtection,
    captured_locals: &'a BTreeSet<LocalId>,
    identity_facts: &'a HandoffIdentityFacts,
    inherited_locals: &'a BTreeSet<LocalId>,
    expr_safety: HirExprSafety,
}

pub(super) fn collapse_dead_loop_update_handoffs(
    block: &mut HirBlock,
    stmt_mentions: Option<BlockMentions<'_>>,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &mut ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
    inherited_locals: &BTreeSet<LocalId>,
    expr_safety: HirExprSafety,
) -> bool {
    // 只有 while/repeat owner 消费这些全块事实；其它语句的子块已由后序遍历处理。
    if !block.stmts.iter().any(|stmt| loop_body(stmt).is_some()) {
        return false;
    }
    let refreshed;
    let stmt_mentions = match stmt_mentions {
        Some(mentions) => mentions,
        None => {
            refreshed = BindingMentionIndex::new(&block.stmts);
            refreshed.root()
        }
    };
    let captured_locals = stmts_captured_locals(&block.stmts);
    if collapse_repeat_tail_temp_updates(
        block,
        stmt_mentions,
        promotion_facts,
        &RepeatUpdateSafety {
            outer_bindings,
            captured_locals: &captured_locals,
            identity_facts,
            inherited_locals,
            expr_safety,
        },
    ) {
        return true;
    }

    let block_facts = LoopUpdateBlockFacts {
        mentions: stmt_mentions,
        label_refs: count_label_references(&block.stmts),
        expr_safety,
    };
    let mut changed = false;

    for index in 0..block.stmts.len() {
        let Some(fold) = find_fold(
            &block.stmts[index],
            index,
            &block_facts,
            &captured_locals,
            outer_bindings,
            promotion_facts,
            identity_facts,
        ) else {
            continue;
        };
        changed |= apply_fold(&mut block.stmts[index], fold, promotion_facts);
    }

    changed
}

fn collapse_repeat_tail_temp_updates(
    block: &mut HirBlock,
    stmt_mentions: BlockMentions<'_>,
    promotion_facts: &mut ProtoPromotionFacts,
    safety: &RepeatUpdateSafety<'_>,
) -> bool {
    let owner_label_refs = count_label_references(&block.stmts);
    let writes = collect_top_level_write_facts(&block.stmts);

    let mut rewrites = BTreeMap::new();
    let mut carried = BTreeSet::new();
    for (index, stmt) in block.stmts.iter().enumerate() {
        let HirStmt::Repeat(repeat_stmt) = stmt else {
            continue;
        };
        let Some((next, state, value, prefix, between)) =
            repeat_tail_temp_update(&repeat_stmt.body)
        else {
            continue;
        };
        let next_binding = CarryBinding::Temp(next);
        let state_binding = CarryBinding::Local(state);
        let mut reads = BindingReadCollector::default();
        reads.collect_expr(value);
        let prefix_mentions = super::reads::collect_binding_mentions_by_stmt(prefix);
        let between_mentions = super::reads::collect_binding_mentions_by_stmt(between);
        let condition_mentions = super::reads::collect_binding_mentions_in_expr(&repeat_stmt.cond);
        if reads.reads.contains(&next_binding) {
            // 候选拒绝[SemanticBarrier:ValueFlow]：RHS 读取旧 next 时，整块 rewrite 会把它改读旧 state。
            continue;
        }
        if safety.captured_locals.contains(&state) {
            // 候选拒绝[SemanticBarrier:Capture]：state capture 可区分合并前后的 cell/write epoch。
            continue;
        }
        if !local_available_before(block, index, state, safety.inherited_locals) {
            // 候选拒绝[SemanticBarrier:Scope]：state 在 repeat 入口不可见，改写会生成越界 local use。
            continue;
        }
        if safety.identity_facts.for_bindings.contains(&state) {
            // 候选拒绝[PolicyBoundary]：for binding 的迭代 identity 由 loop owner 保留。
            continue;
        }
        if safety.outer_bindings.contains(&next_binding) {
            // 候选拒绝[SemanticBarrier:ValueFlow]：loop 外仍读取 next，合并会删除其独立值 identity。
            continue;
        }
        if !safety.identity_facts.binding_merge_preserves_identity(
            next_binding,
            state_binding,
            promotion_facts,
        ) {
            continue;
        }
        match repeat_gap_safety(
            next_binding,
            state_binding,
            between,
            promotion_facts,
            safety.expr_safety,
        ) {
            Ok(()) => {}
            Err(RepeatGapFailure::ObservedDistinctHomes) => {
                // 候选拒绝[SemanticBarrier:Lifetime]：两端可能位于不同物理 home，提前写
                // state 会让旧 state root 在 between 的调用/分配/close 事件前回收。
                continue;
            }
            Err(RepeatGapFailure::AliasingWrite) => {
                // 候选拒绝[SemanticBarrier:ValueFlow]：between 的 binding 写可能命中
                // state/next home；删除尾 writeback 会让该别名写成为最终 state 值。
                continue;
            }
        }
        if !stmt_mentions.first_is(index, next_binding)
            || writes.counts.get(&next_binding).copied() != Some(1)
            || writes.last_stmt.get(&state_binding).copied() != Some(index)
        {
            // 候选拒绝[SemanticBarrier:ValueFlow]：repeat 外先读、重复写 next，或后续再写 state 会暴露被合并的 epoch。
            continue;
        }
        if !condition_mentions.contains(&next_binding)
            && !between_mentions
                .iter()
                .any(|mentions| mentions.contains(&next_binding))
        {
            continue;
        }
        if prefix.iter().any(stmt_has_candidate_loop_transfer)
            || prefix
                .iter()
                .any(|stmt| stmt_writes_binding(stmt, state_binding))
        {
            // 候选拒绝[SemanticBarrier:ControlFlow]：seed 前 transfer 或 state 写可让路径跳过新值却进入重写后的 condition。
            continue;
        }
        if between.iter().any(stmt_has_candidate_loop_transfer) {
            // 候选拒绝[SemanticBarrier:ControlFlow]：candidate-owned break/continue 或 Return
            // 可跳过原尾写回；提前写 state 会让该出口观察本轮新值。嵌套循环自有的
            // break/continue 不离开 candidate，本 guard 不再 blanket 拒绝它们。
            continue;
        }
        if stmts_have_unresolved(between) {
            // 候选拒绝[PolicyBoundary]：Unresolved 是 permissive 输出保留的失败证据。
            continue;
        }
        if prefix_mentions
            .iter()
            .any(|mentions| mentions.contains(&next_binding))
            || between_mentions
                .iter()
                .any(|mentions| mentions.contains(&state_binding))
        {
            // 候选拒绝[SemanticBarrier:ValueFlow]：seed 前读取 next 或 between 读取旧 state 会因合并改读另一 epoch。
            continue;
        }
        match local_forward_label_flow(
            &repeat_stmt.body.stmts,
            prefix.len(),
            &owner_label_refs,
            safety.expr_safety,
        ) {
            Ok(()) => {}
            Err(LabelFlowFailure::CrossesSeed) => {
                // 候选拒绝[SemanticBarrier:ControlFlow]：跨 seed 的前向边会跳过本轮 next
                // 定义；跨 seed 的后向边会在已提前写入的 state 上重算 seed，原形则始终
                // 读取 writeback 前的旧 state。
                continue;
            }
            Err(LabelFlowFailure::ExternalEdge) => {
                // 候选拒绝[SemanticBarrier:ControlFlow]：跨 owner 的入口/出口或歧义 label
                // 可绕过 seed/尾 writeback；例如 suffix goto 外层 label 会暴露提前写入的 state。
                continue;
            }
        }
        assert!(
            rewrites.insert(next_binding, state_binding).is_none(),
            "single-write next binding cannot map to multiple carried states"
        );
        carried.insert(state_binding);
    }
    if rewrites.is_empty() {
        return false;
    }

    rewrite_stmts(
        &mut block.stmts,
        &mut BindingClassRewritePass {
            rewrites,
            promotion_facts,
        },
    );
    rewrite_stmts(
        &mut block.stmts,
        &mut RedundantSelfAssignPrunePass::for_bindings(carried),
    );
    true
}

fn local_available_before(
    block: &HirBlock,
    index: usize,
    local: LocalId,
    inherited_locals: &BTreeSet<LocalId>,
) -> bool {
    inherited_locals.contains(&local)
        || block.stmts[..index].iter().any(|stmt| {
            matches!(stmt,
                HirStmt::LocalDecl(local_decl) if local_decl.bindings.contains(&local))
        })
}

type RepeatTailTempUpdate<'a> = (TempId, LocalId, &'a HirExpr, &'a [HirStmt], &'a [HirStmt]);

fn repeat_tail_temp_update(body: &HirBlock) -> Option<RepeatTailTempUpdate<'_>> {
    let (HirStmt::Assign(writeback), before_writeback) = body.stmts.split_last()? else {
        return None;
    };
    let [HirLValue::Local(state)] = writeback.targets.as_slice() else {
        return None;
    };
    let [HirExpr::TempRef(source)] = writeback.values.fixed.as_slice() else {
        return None;
    };
    if writeback.values.tail.is_some() {
        return None;
    }
    let (seed_index, next, value) =
        before_writeback
            .iter()
            .enumerate()
            .rev()
            .find_map(|(index, stmt)| {
                let HirStmt::Assign(seed) = stmt else {
                    return None;
                };
                let ([HirLValue::Temp(next)], [value], None) = (
                    seed.targets.as_slice(),
                    seed.values.fixed.as_slice(),
                    &seed.values.tail,
                ) else {
                    return None;
                };
                (*next == *source).then_some((index, *next, value))
            })?;
    Some((
        next,
        *state,
        value,
        &before_writeback[..seed_index],
        &before_writeback[seed_index + 1..],
    ))
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum RepeatGapFailure {
    ObservedDistinctHomes,
    AliasingWrite,
}

fn repeat_gap_safety(
    next: CarryBinding,
    state: CarryBinding,
    between: &[HirStmt],
    promotion_facts: &ProtoPromotionFacts,
    expr_safety: HirExprSafety,
) -> Result<(), RepeatGapFailure> {
    if between.is_empty() || bindings_share_exact_home_slot(next, state, promotion_facts) {
        return Ok(());
    }
    let next_homes = conservative_binding_homes(next, promotion_facts);
    let state_homes = conservative_binding_homes(state, promotion_facts);
    if next_homes == state_homes && next_homes.len() <= 1 {
        return Ok(());
    }
    if between_may_observe_gc_roots(between, expr_safety) {
        return Err(RepeatGapFailure::ObservedDistinctHomes);
    }

    let mut writes = PhysicalBindingWriteCollector::default();
    visit_stmts(between, &mut writes);
    for write in writes.bindings {
        for candidate in [next, state] {
            match binding_home_overlap(write, candidate, promotion_facts) {
                BindingHomeOverlap::Disjoint => {}
                BindingHomeOverlap::Overlap => return Err(RepeatGapFailure::AliasingWrite),
                BindingHomeOverlap::Unknown => {
                    let write_homes = conservative_binding_homes(write, promotion_facts);
                    let candidate_homes = conservative_binding_homes(candidate, promotion_facts);
                    if !write_homes.is_disjoint(&candidate_homes) {
                        return Err(RepeatGapFailure::AliasingWrite);
                    }
                }
            }
        }
    }
    Ok(())
}

fn conservative_binding_homes(
    binding: CarryBinding,
    promotion_facts: &ProtoPromotionFacts,
) -> HomeSlots<'_> {
    match binding {
        CarryBinding::Param(param) => promotion_facts.complete_param_home_slots(param),
        CarryBinding::Local(local) => promotion_facts.complete_local_home_slots(local),
        CarryBinding::Temp(temp) => promotion_facts.complete_temp_home_slots(temp),
    }
}

#[derive(Default)]
struct PhysicalBindingWriteCollector {
    bindings: BTreeSet<CarryBinding>,
}

impl HirVisitor<'_> for PhysicalBindingWriteCollector {
    fn visit_local_root_release(&mut self, _local: LocalId) {}

    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::LocalDecl(local_decl) => self
                .bindings
                .extend(local_decl.bindings.iter().copied().map(CarryBinding::Local)),
            HirStmt::NumericFor(numeric_for) => {
                self.bindings
                    .insert(CarryBinding::Local(numeric_for.binding));
            }
            HirStmt::GenericFor(generic_for) => self.bindings.extend(
                generic_for
                    .bindings
                    .iter()
                    .copied()
                    .map(CarryBinding::Local),
            ),
            _ => {}
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let Some(binding) = carry_binding_from_lvalue(lvalue) {
            self.bindings.insert(binding);
        }
    }
}

fn between_may_observe_gc_roots(stmts: &[HirStmt], safety: HirExprSafety) -> bool {
    let mut collector = HirEvalEffects::new(safety, |stmt| {
        matches!(stmt, HirStmt::ErrNil(_) | HirStmt::ToBeClosed(_))
    });
    visit_stmts(stmts, &mut collector);
    collector.found()
}

#[derive(Default)]
struct TopLevelWriteFacts {
    counts: BTreeMap<CarryBinding, usize>,
    last_stmt: BTreeMap<CarryBinding, usize>,
}

fn collect_top_level_write_facts(stmts: &[HirStmt]) -> TopLevelWriteFacts {
    let mut facts = TopLevelWriteFacts::default();
    for (index, stmt) in stmts.iter().enumerate() {
        let mut writes = BindingWriteCollector::default();
        visit_stmts(std::slice::from_ref(stmt), &mut writes);
        for (binding, count) in writes.counts {
            *facts.counts.entry(binding).or_default() += count;
            facts.last_stmt.insert(binding, index);
        }
    }
    facts
}

#[derive(Default)]
struct BindingWriteCollector {
    counts: BTreeMap<CarryBinding, usize>,
}

impl HirVisitor<'_> for BindingWriteCollector {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let Some(binding) = carry_binding_from_lvalue(lvalue) {
            *self.counts.entry(binding).or_default() += 1;
        }
    }
}

fn stmt_writes_binding(stmt: &HirStmt, binding: CarryBinding) -> bool {
    let mut writes = BindingWriteCollector::default();
    visit_stmts(std::slice::from_ref(stmt), &mut writes);
    writes.counts.contains_key(&binding)
}

fn stmt_has_candidate_loop_transfer(stmt: &HirStmt) -> bool {
    stmt_has_nonlocal_transfer(stmt, false)
}

fn stmt_has_nonlocal_transfer(stmt: &HirStmt, inside_nested_loop: bool) -> bool {
    match stmt {
        HirStmt::LocalRootRelease(_) => false,
        HirStmt::Return(_) => true,
        HirStmt::Break | HirStmt::Continue => !inside_nested_loop,
        HirStmt::If(if_stmt) => {
            if_stmt
                .then_block
                .stmts
                .iter()
                .any(|stmt| stmt_has_nonlocal_transfer(stmt, inside_nested_loop))
                || if_stmt.else_block.as_ref().is_some_and(|block| {
                    block
                        .stmts
                        .iter()
                        .any(|stmt| stmt_has_nonlocal_transfer(stmt, inside_nested_loop))
                })
        }
        HirStmt::Block(block) => block
            .stmts
            .iter()
            .any(|stmt| stmt_has_nonlocal_transfer(stmt, inside_nested_loop)),
        HirStmt::While(while_stmt) => while_stmt
            .body
            .stmts
            .iter()
            .any(|stmt| stmt_has_nonlocal_transfer(stmt, true)),
        HirStmt::Repeat(repeat_stmt) => repeat_stmt
            .body
            .stmts
            .iter()
            .any(|stmt| stmt_has_nonlocal_transfer(stmt, true)),
        HirStmt::NumericFor(numeric_for) => numeric_for
            .body
            .stmts
            .iter()
            .any(|stmt| stmt_has_nonlocal_transfer(stmt, true)),
        HirStmt::GenericFor(generic_for) => generic_for
            .body
            .stmts
            .iter()
            .any(|stmt| stmt_has_nonlocal_transfer(stmt, true)),
        HirStmt::Goto(_)
        | HirStmt::Label(_)
        | HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::GlobalDecl(_) => false,
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum LabelFlowFailure {
    CrossesSeed,
    ExternalEdge,
}

fn local_forward_label_flow(
    stmts: &[HirStmt],
    seed_index: usize,
    owner_label_refs: &BTreeMap<HirLabelId, usize>,
    expr_safety: HirExprSafety,
) -> Result<(), LabelFlowFailure> {
    let cfg = LexicalCfg::analyze(stmts, owner_label_refs, expr_safety)
        .map_err(|_| LabelFlowFailure::ExternalEdge)?;
    if cfg.has_external_exit() {
        return Err(LabelFlowFailure::ExternalEdge);
    }
    seed_reaches_consistent_epoch(cfg.successors(), seed_index)
}

fn seed_reaches_consistent_epoch(
    successors: &[BTreeSet<usize>],
    seed_index: usize,
) -> Result<(), LabelFlowFailure> {
    const BEFORE_SEED: u8 = 1;
    const AFTER_SEED: u8 = 2;

    if successors.is_empty() {
        return Ok(());
    }
    let mut incoming = vec![0u8; successors.len()];
    incoming[0] = BEFORE_SEED;
    let mut pending = vec![0usize];
    while let Some(index) = pending.pop() {
        let state = incoming[index];
        if (index < seed_index && state & AFTER_SEED != 0)
            || (index == seed_index && state & AFTER_SEED != 0)
            || (index > seed_index && state & BEFORE_SEED != 0)
        {
            return Err(LabelFlowFailure::CrossesSeed);
        }
        let outgoing = if index == seed_index {
            AFTER_SEED
        } else {
            state
        };
        for &successor in &successors[index] {
            let merged = incoming[successor] | outgoing;
            if merged != incoming[successor] {
                incoming[successor] = merged;
                pending.push(successor);
            }
        }
    }
    Ok(())
}

fn stmts_have_unresolved(stmts: &[HirStmt]) -> bool {
    let mut collector = UnresolvedCollector::default();
    visit_stmts(stmts, &mut collector);
    collector.found
}

#[derive(Default)]
struct UnresolvedCollector {
    found: bool,
}

impl HirVisitor<'_> for UnresolvedCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.found |= matches!(expr, HirExpr::Unresolved(_));
    }
}

fn find_fold(
    stmt: &HirStmt,
    stmt_index: usize,
    block_facts: &LoopUpdateBlockFacts<'_>,
    captured_locals: &BTreeSet<LocalId>,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
) -> Option<LoopUpdateFold> {
    let body = loop_body(stmt)?;
    let (writeback, prefix) = body.stmts.split_last()?;
    let (carried, next) = exact_local_writeback(writeback)?;
    if carried == next
        || !block_facts
            .mentions
            .last_is(stmt_index, CarryBinding::Local(carried))
        || !block_facts
            .mentions
            .last_is(stmt_index, CarryBinding::Local(next))
        || captured_locals.contains(&carried)
        || captured_locals.contains(&next)
        || outer_bindings.contains(&CarryBinding::Local(carried))
        || outer_bindings.contains(&CarryBinding::Local(next))
        || !bindings_share_exact_home_slot(
            CarryBinding::Local(carried),
            CarryBinding::Local(next),
            promotion_facts,
        )
        || !identity_facts.binding_merge_preserves_identity(
            CarryBinding::Local(next),
            CarryBinding::Local(carried),
            promotion_facts,
        )
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：loop 后仍活跃、capture/outer use、异槽或资源
        // identity 会观察 carried/next 的独立 epoch。
        return None;
    }
    if prefix.iter().any(stmt_has_candidate_loop_continue) {
        // 候选拒绝[SemanticBarrier:ControlFlow]：candidate loop 的 Continue 会绕过原尾写回；
        // 提前把 seed 写进 carried 会让下一轮观察本不应提交的新值（见本模块负例）。
        return None;
    }
    for (seed_index, seed) in prefix.iter().enumerate() {
        let Some((seed_binding, value)) = initialized_single_local_decl(seed) else {
            continue;
        };
        if seed_binding != next
            || stmts_mention_local(&prefix[..seed_index], next)
            || stmts_mention_local(&prefix[seed_index + 1..], carried)
            || !stmts_contain_terminal_exit(&prefix[seed_index + 1..])
        {
            // 候选拒绝[SemanticBarrier:ControlFlow]：seed 后若并非由 terminal exit 截断，提前写 carried 会让原本未 writeback 的路径观察新值。
            // 候选拒绝[SemanticBarrier:Lifetime]：seed 前读 next 或 seed 后读旧 carried 会因 binding 合并改读另一 epoch。
            continue;
        }
        match local_forward_label_flow(
            &body.stmts,
            seed_index,
            &block_facts.label_refs,
            block_facts.expr_safety,
        ) {
            Ok(()) => {}
            Err(LabelFlowFailure::CrossesSeed) => {
                // 候选拒绝[SemanticBarrier:ControlFlow]：跨 seed 的前向边会绕过 next
                // declaration；跨 seed 的后向边会在已更新 carried 上重复求 seed，原形仍
                // 读取尾 writeback 前的旧 carried。
                continue;
            }
            Err(LabelFlowFailure::ExternalEdge) => {
                // 候选拒绝[SemanticBarrier:ControlFlow]：跨 owner 的入口/出口或歧义 label
                // 可绕过 seed/尾 writeback；例如 suffix goto 外层 label 会跳过 carried 提交。
                continue;
            }
        }
        let mut reads = BindingReadCollector::default();
        reads.collect_expr(value);
        if reads.single_read() == Some(CarryBinding::Local(carried)) {
            return Some(LoopUpdateFold {
                seed_index,
                carried,
                next,
                seed: seed.clone(),
                writeback: writeback.clone(),
            });
        }
    }
    None
}

fn loop_body(stmt: &HirStmt) -> Option<&HirBlock> {
    match stmt {
        HirStmt::While(while_stmt) => Some(&while_stmt.body),
        HirStmt::Repeat(repeat_stmt) => Some(&repeat_stmt.body),
        _ => None,
    }
}

fn loop_body_mut(stmt: &mut HirStmt) -> Option<(&mut HirBlock, Option<&mut HirExpr>)> {
    match stmt {
        HirStmt::While(while_stmt) => Some((&mut while_stmt.body, None)),
        HirStmt::Repeat(repeat_stmt) => Some((&mut repeat_stmt.body, Some(&mut repeat_stmt.cond))),
        _ => None,
    }
}

fn exact_local_writeback(stmt: &HirStmt) -> Option<(LocalId, LocalId)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Local(target)] = assign.targets.as_slice() else {
        return None;
    };
    let [HirExpr::LocalRef(value)] = assign.values.fixed.as_slice() else {
        return None;
    };
    assign.values.tail.is_none().then_some((*target, *value))
}

fn stmt_has_candidate_loop_continue(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::LocalRootRelease(_) => false,
        HirStmt::Continue => true,
        HirStmt::If(if_stmt) => {
            if_stmt
                .then_block
                .stmts
                .iter()
                .any(stmt_has_candidate_loop_continue)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| block.stmts.iter().any(stmt_has_candidate_loop_continue))
        }
        HirStmt::Block(block) => block.stmts.iter().any(stmt_has_candidate_loop_continue),
        // These loops own every Continue in their bodies. Return/goto are handled by the
        // terminal/path gates rather than being mistaken for candidate-owned Continue.
        HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::GlobalDecl(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn stmts_contain_terminal_exit(stmts: &[HirStmt]) -> bool {
    stmts.iter().any(stmt_contains_terminal_exit)
}

fn stmt_contains_terminal_exit(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::Break | HirStmt::Return(_) => true,
        HirStmt::If(if_stmt) => {
            stmts_contain_terminal_exit(&if_stmt.then_block.stmts)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| stmts_contain_terminal_exit(&block.stmts))
        }
        HirStmt::Block(block) => stmts_contain_terminal_exit(&block.stmts),
        _ => false,
    }
}

fn apply_fold(
    stmt: &mut HirStmt,
    fold: LoopUpdateFold,
    promotion_facts: &mut ProtoPromotionFacts,
) -> bool {
    let (body, repeat_cond) =
        loop_body_mut(stmt).expect("planned loop-update candidate must retain its loop owner");

    assert!(
        body.stmts.get(fold.seed_index) == Some(&fold.seed)
            && body.stmts.last() == Some(&fold.writeback),
        "planned loop-update seed and writeback must remain unchanged before apply"
    );

    let HirStmt::LocalDecl(local_decl) = &mut body.stmts[fold.seed_index] else {
        unreachable!("exactly matched loop-update seed must remain a local declaration")
    };
    let values = std::mem::take(&mut local_decl.values);
    record_binding_merge(
        CarryBinding::Local(fold.next),
        CarryBinding::Local(fold.carried),
        promotion_facts,
    );
    body.stmts[fold.seed_index] = HirStmt::Assign(Box::new(HirAssign {
        targets: vec![HirLValue::Local(fold.carried)],
        values,
        initializer_merge_transaction: None,
        generic_for_initializer_producer: None,
        generic_for_dispatch_release: None,
        method_rewrite_transaction: None,
    }));
    body.stmts.pop();

    let mut rewrites = BTreeMap::new();
    rewrites.insert(
        CarryBinding::Local(fold.next),
        CarryBinding::Local(fold.carried),
    );
    let mut pass = BindingClassRewritePass {
        rewrites,
        promotion_facts,
    };
    rewrite_stmts(&mut body.stmts[fold.seed_index + 1..], &mut pass);
    if let Some(cond) = repeat_cond {
        rewrite_expr(cond, &mut pass);
    }
    true
}
