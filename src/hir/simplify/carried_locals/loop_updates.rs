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
use crate::hir::promotion::ProtoPromotionFacts;

use super::super::label_refs::count_label_references;
use super::super::mention::{stmts_captured_locals, stmts_mention_local};
use super::super::visit::{visit_stmts, HirVisitor};
use super::super::walk::{rewrite_expr, rewrite_stmts};
use super::binding::{
    binding_home_slot, bindings_share_exact_home_slot, carry_binding_from_lvalue,
    record_binding_merge, BindingClassRewritePass, BindingProtection, CarryBinding,
};
use super::prune::RedundantSelfAssignPrunePass;
use super::reads::BindingReadCollector;
use super::HandoffIdentityFacts;

struct LoopUpdateFold {
    seed_index: usize,
    carried: LocalId,
    next: LocalId,
    seed: HirStmt,
    writeback: HirStmt,
}

struct LoopUpdateBlockFacts {
    last_local_mentions: BTreeMap<LocalId, usize>,
    label_refs: BTreeMap<HirLabelId, usize>,
}

pub(super) fn collapse_dead_loop_update_handoffs(
    block: &mut HirBlock,
    stmt_mentions: &[BTreeSet<CarryBinding>],
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &mut ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
    inherited_locals: &BTreeSet<LocalId>,
) -> bool {
    let captured_locals = stmts_captured_locals(&block.stmts);
    if collapse_repeat_tail_temp_updates(
        block,
        stmt_mentions,
        outer_bindings,
        &captured_locals,
        promotion_facts,
        identity_facts,
        inherited_locals,
    ) {
        return true;
    }

    let block_facts = LoopUpdateBlockFacts {
        last_local_mentions: last_local_mentions(stmt_mentions),
        label_refs: count_label_references(&block.stmts),
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
    stmt_mentions: &[BTreeSet<CarryBinding>],
    outer_bindings: &dyn BindingProtection,
    captured_locals: &BTreeSet<LocalId>,
    promotion_facts: &mut ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
    inherited_locals: &BTreeSet<LocalId>,
) -> bool {
    let owner_label_refs = count_label_references(&block.stmts);
    let mut first_mentions = BTreeMap::new();
    for (index, mentions) in stmt_mentions.iter().enumerate() {
        for binding in mentions {
            first_mentions.entry(*binding).or_insert(index);
        }
    }
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
        let next_home = binding_home_slot(next_binding, promotion_facts);
        let state_home = binding_home_slot(state_binding, promotion_facts);
        let between_crosses_distinct_homes = !between.is_empty()
            && next_home
                .zip(state_home)
                .is_some_and(|(next_home, state_home)| next_home != state_home);
        let between_lacks_same_home_proof = !between.is_empty()
            && !between_crosses_distinct_homes
            && (next_home.is_none() || state_home.is_none());
        if reads.reads.contains(&next_binding) {
            // 候选拒绝[SemanticBarrier:ValueFlow]：RHS 读取旧 next 时，整块 rewrite 会把它改读旧 state。
            continue;
        }
        if captured_locals.contains(&state) {
            // 候选拒绝[SemanticBarrier:Capture]：state capture 可区分合并前后的 cell/write epoch。
            continue;
        }
        if !local_available_before(block, index, state, inherited_locals) {
            // 候选拒绝[SemanticBarrier:Scope]：state 在 repeat 入口不可见，改写会生成越界 local use。
            continue;
        }
        if identity_facts.for_bindings.contains(&state) {
            // 候选拒绝[PolicyBoundary]：for binding 的迭代 identity 由 loop owner 保留。
            continue;
        }
        if outer_bindings.contains(&next_binding) {
            // 候选拒绝[SemanticBarrier:ValueFlow]：loop 外仍读取 next，合并会删除其独立值 identity。
            continue;
        }
        if !identity_facts.binding_merge_preserves_identity(
            next_binding,
            state_binding,
            promotion_facts,
        ) {
            continue;
        }
        if between_crosses_distinct_homes {
            // 候选拒绝[SemanticBarrier:Lifetime]：异槽提前写 state 会让旧 state root 在 between 中提前回收。
            continue;
        }
        if between_lacks_same_home_proof {
            // 候选拒绝[ProofIncomplete]：between 非空时至少一端缺 promotion 提供的 trusted
            // 精确 home（包括 provenance 已失效）；possible-home overlap 只能证明可能 alias，
            // 不能证明两端必为同一 slot/epoch。若实际异槽，提前写 state 会改变 between 内
            // 可观察的 root 生命周期。
            continue;
        }
        if first_mentions.get(&next_binding).copied() != Some(index)
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
        if stmts_have_decision_or_unresolved(between) {
            // 候选拒绝[LayerBoundary]：Decision/Unresolved 由 decision owner 消解。
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
        match local_forward_label_flow(&repeat_stmt.body.stmts, prefix.len(), &owner_label_refs) {
            Ok(()) => {}
            Err(LabelFlowFailure::CrossesSeed) => {
                // 候选拒绝[SemanticBarrier:ControlFlow]：跨 seed 的前向边会跳过本轮 next
                // 定义；跨 seed 的后向边会在已提前写入的 state 上重算 seed，原形则始终
                // 读取 writeback 前的旧 state。
                continue;
            }
            Err(LabelFlowFailure::NeedsCfg) => {
                // 候选拒绝[ProofIncomplete]：owner 外重入、嵌套边或同侧后向边缺逐边
                // reaching-write/fixed-point；当前只接受 owner-complete 的顶层局部前向边。
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

impl HirVisitor for BindingWriteCollector {
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

fn stmt_has_label_or_goto(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::Goto(_) | HirStmt::Label(_) => true,
        HirStmt::If(if_stmt) => {
            if_stmt.then_block.stmts.iter().any(stmt_has_label_or_goto)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| block.stmts.iter().any(stmt_has_label_or_goto))
        }
        HirStmt::While(while_stmt) => while_stmt.body.stmts.iter().any(stmt_has_label_or_goto),
        HirStmt::Repeat(repeat_stmt) => repeat_stmt.body.stmts.iter().any(stmt_has_label_or_goto),
        HirStmt::NumericFor(numeric_for) => {
            numeric_for.body.stmts.iter().any(stmt_has_label_or_goto)
        }
        HirStmt::GenericFor(generic_for) => {
            generic_for.body.stmts.iter().any(stmt_has_label_or_goto)
        }
        HirStmt::Block(block) => block.stmts.iter().any(stmt_has_label_or_goto),
        _ => false,
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum LabelFlowFailure {
    CrossesSeed,
    NeedsCfg,
}

fn local_forward_label_flow(
    stmts: &[HirStmt],
    seed_index: usize,
    owner_label_refs: &BTreeMap<HirLabelId, usize>,
) -> Result<(), LabelFlowFailure> {
    let mut labels = BTreeMap::<HirLabelId, usize>::new();
    let mut gotos = Vec::<(usize, HirLabelId)>::new();
    for (index, stmt) in stmts.iter().enumerate() {
        match stmt {
            HirStmt::Label(label) => {
                if labels.insert(label.id, index).is_some() {
                    return Err(LabelFlowFailure::NeedsCfg);
                }
            }
            HirStmt::Goto(goto_stmt) => gotos.push((index, goto_stmt.target)),
            _ if stmt_has_label_or_goto(stmt) => return Err(LabelFlowFailure::NeedsCfg),
            _ => {}
        }
    }

    let internal_refs = count_label_references(stmts);
    for (&label, &target_index) in &labels {
        if owner_label_refs.get(&label).copied().unwrap_or_default()
            != internal_refs.get(&label).copied().unwrap_or_default()
        {
            return Err(if target_index > seed_index {
                LabelFlowFailure::CrossesSeed
            } else {
                LabelFlowFailure::NeedsCfg
            });
        }
    }

    for (source_index, target) in gotos {
        let Some(&target_index) = labels.get(&target) else {
            return Err(LabelFlowFailure::NeedsCfg);
        };
        if (source_index > seed_index) != (target_index > seed_index) {
            return Err(LabelFlowFailure::CrossesSeed);
        }
        if source_index >= target_index {
            return Err(LabelFlowFailure::NeedsCfg);
        }
    }
    Ok(())
}

fn stmts_have_decision_or_unresolved(stmts: &[HirStmt]) -> bool {
    let mut collector = OpaqueCollector::default();
    visit_stmts(stmts, &mut collector);
    collector.opaque
}

#[derive(Default)]
struct OpaqueCollector {
    opaque: bool,
}

impl HirVisitor for OpaqueCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.opaque |= matches!(expr, HirExpr::Decision(_) | HirExpr::Unresolved(_));
    }
}

fn last_local_mentions(stmt_mentions: &[BTreeSet<CarryBinding>]) -> BTreeMap<LocalId, usize> {
    let mut last_mentions = BTreeMap::new();
    for (index, mentions) in stmt_mentions.iter().enumerate() {
        for binding in mentions {
            if let CarryBinding::Local(local) = binding {
                last_mentions.insert(*local, index);
            }
        }
    }
    last_mentions
}

fn find_fold(
    stmt: &HirStmt,
    stmt_index: usize,
    block_facts: &LoopUpdateBlockFacts,
    captured_locals: &BTreeSet<LocalId>,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
) -> Option<LoopUpdateFold> {
    let body = loop_body(stmt)?;
    let (writeback, prefix) = body.stmts.split_last()?;
    let (carried, next) = exact_local_writeback(writeback)?;
    if carried == next
        || block_facts.last_local_mentions.get(&carried).copied() != Some(stmt_index)
        || block_facts.last_local_mentions.get(&next).copied() != Some(stmt_index)
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
        let Some((seed_binding, value)) = initialized_local(seed) else {
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
        match local_forward_label_flow(&body.stmts, seed_index, &block_facts.label_refs) {
            Ok(()) => {}
            Err(LabelFlowFailure::CrossesSeed) => {
                // 候选拒绝[SemanticBarrier:ControlFlow]：跨 seed 的前向边会绕过 next
                // declaration；跨 seed 的后向边会在已更新 carried 上重复求 seed，原形仍
                // 读取尾 writeback 前的旧 carried。
                continue;
            }
            Err(LabelFlowFailure::NeedsCfg) => {
                // 候选拒绝[ProofIncomplete]：owner 外重入、嵌套边或同侧后向边缺逐边
                // reaching-write/fixed-point；当前只接受 owner-complete 的顶层局部前向边。
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

fn initialized_local(stmt: &HirStmt) -> Option<(LocalId, &HirExpr)> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [value] = local_decl.values.fixed.as_slice() else {
        return None;
    };
    local_decl
        .values
        .tail
        .is_none()
        .then_some((*binding, value))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::common::{
        HirBinaryExpr, HirBinaryOpKind, HirClose, HirGlobalDecl, HirGoto, HirLabel, HirLocalDecl,
        HirRepeat, HirValuePack, HirWhile,
    };
    use crate::hir::promotion::HomeSlotKey;

    fn local_decl(local: LocalId) -> HirStmt {
        HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![local],
            values: HirValuePack::fixed(vec![HirExpr::Nil]),
        }))
    }

    fn assign(target: HirLValue, value: HirExpr) -> HirStmt {
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![target],
            values: HirValuePack::fixed(vec![value]),
        }))
    }

    fn add(lhs: HirExpr, rhs: HirExpr) -> HirExpr {
        HirExpr::Binary(Box::new(HirBinaryExpr {
            op: HirBinaryOpKind::Add,
            lhs,
            rhs,
        }))
    }

    fn goto(target: HirLabelId) -> HirStmt {
        HirStmt::Goto(Box::new(HirGoto { target }))
    }

    fn label(id: HirLabelId) -> HirStmt {
        HirStmt::Label(Box::new(HirLabel {
            id,
            tbc_barriers: Vec::new(),
        }))
    }

    fn repeat_update(state: LocalId, next: TempId, value: HirExpr) -> HirStmt {
        HirStmt::Repeat(Box::new(HirRepeat {
            body: HirBlock {
                stmts: vec![
                    assign(HirLValue::Temp(next), value),
                    assign(HirLValue::Local(state), HirExpr::TempRef(next)),
                ],
            },
            cond: HirExpr::TempRef(next),
        }))
    }

    fn empty_identity_facts() -> HandoffIdentityFacts {
        HandoffIdentityFacts {
            debug: BTreeSet::new(),
            for_bindings: BTreeSet::new(),
            physical_roots: BTreeSet::new(),
            captured: BTreeSet::new(),
            reference_captured: BTreeSet::new(),
            to_be_closed: BTreeSet::new(),
        }
    }

    fn exact_home_facts(local: LocalId, temp: TempId) -> ProtoPromotionFacts {
        let mut facts = ProtoPromotionFacts::default();
        let home = HomeSlotKey::new(0, 0);
        facts.record_local_home_slot(local, home);
        facts.record_temp_home_slot_for_test(temp, home);
        facts
    }

    fn run_fold(block: &mut HirBlock, promotion_facts: &mut ProtoPromotionFacts) -> bool {
        let stmt_mentions = super::super::reads::collect_binding_mentions_by_stmt(&block.stmts);
        collapse_dead_loop_update_handoffs(
            block,
            &stmt_mentions,
            &BTreeSet::<CarryBinding>::new(),
            promotion_facts,
            &empty_identity_facts(),
            &BTreeSet::new(),
        )
    }

    #[test]
    fn repeat_tail_update_accepts_rhs_reading_an_additional_local() {
        let state = LocalId(0);
        let extra = LocalId(1);
        let next = TempId(0);
        let mut block = HirBlock {
            stmts: vec![
                local_decl(state),
                local_decl(extra),
                repeat_update(
                    state,
                    next,
                    add(HirExpr::LocalRef(state), HirExpr::LocalRef(extra)),
                ),
            ],
        };
        let stmt_mentions = super::super::reads::collect_binding_mentions_by_stmt(&block.stmts);
        let outer_bindings = BTreeSet::<CarryBinding>::new();
        let inherited_locals = BTreeSet::new();
        let identity_facts = empty_identity_facts();
        let mut promotion_facts = ProtoPromotionFacts::default();

        let changed = collapse_dead_loop_update_handoffs(
            &mut block,
            &stmt_mentions,
            &outer_bindings,
            &mut promotion_facts,
            &identity_facts,
            &inherited_locals,
        );

        let expected = HirBlock {
            stmts: vec![
                local_decl(state),
                local_decl(extra),
                HirStmt::Repeat(Box::new(HirRepeat {
                    body: HirBlock {
                        stmts: vec![assign(
                            HirLValue::Local(state),
                            add(HirExpr::LocalRef(state), HirExpr::LocalRef(extra)),
                        )],
                    },
                    cond: HirExpr::LocalRef(state),
                })),
            ],
        };
        assert_eq!((changed, block), (true, expected));
    }

    #[test]
    fn repeat_tail_update_rejects_rhs_reading_old_next() {
        let state = LocalId(0);
        let extra = LocalId(1);
        let next = TempId(0);
        let mut block = HirBlock {
            stmts: vec![
                local_decl(state),
                local_decl(extra),
                repeat_update(
                    state,
                    next,
                    add(HirExpr::TempRef(next), HirExpr::LocalRef(extra)),
                ),
            ],
        };
        let before = block.clone();
        let stmt_mentions = super::super::reads::collect_binding_mentions_by_stmt(&block.stmts);
        let outer_bindings = BTreeSet::<CarryBinding>::new();
        let inherited_locals = BTreeSet::new();
        let identity_facts = empty_identity_facts();
        let mut promotion_facts = ProtoPromotionFacts::default();

        let changed = collapse_dead_loop_update_handoffs(
            &mut block,
            &stmt_mentions,
            &outer_bindings,
            &mut promotion_facts,
            &identity_facts,
            &inherited_locals,
        );

        assert_eq!((changed, block), (false, before));
    }

    #[test]
    fn repeat_tail_update_crosses_global_declaration_without_moving_it() {
        let state = LocalId(0);
        let next = TempId(0);
        let global = HirStmt::GlobalDecl(Box::new(HirGlobalDecl {
            names: vec!["snapshot".to_owned()],
            values: HirValuePack::fixed(vec![HirExpr::TempRef(next)]),
        }));
        let mut block = HirBlock {
            stmts: vec![
                local_decl(state),
                HirStmt::Repeat(Box::new(HirRepeat {
                    body: HirBlock {
                        stmts: vec![
                            assign(
                                HirLValue::Temp(next),
                                add(HirExpr::LocalRef(state), HirExpr::Integer(1)),
                            ),
                            global,
                            assign(HirLValue::Local(state), HirExpr::TempRef(next)),
                        ],
                    },
                    cond: HirExpr::TempRef(next),
                })),
            ],
        };
        let mut promotion_facts = exact_home_facts(state, next);

        assert!(run_fold(&mut block, &mut promotion_facts));

        let HirStmt::Repeat(repeat_stmt) = &block.stmts[1] else {
            panic!("repeat owner must remain")
        };
        assert_eq!(
            repeat_stmt.body.stmts,
            vec![
                assign(
                    HirLValue::Local(state),
                    add(HirExpr::LocalRef(state), HirExpr::Integer(1)),
                ),
                HirStmt::GlobalDecl(Box::new(HirGlobalDecl {
                    names: vec!["snapshot".to_owned()],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(state)]),
                })),
            ]
        );
        assert_eq!(repeat_stmt.cond, HirExpr::LocalRef(state));
    }

    #[test]
    fn repeat_tail_update_accepts_owner_complete_forward_goto_after_seed() {
        let state = LocalId(0);
        let next = TempId(0);
        let target = HirLabelId(0);
        let skipped = HirStmt::GlobalDecl(Box::new(HirGlobalDecl {
            names: vec!["skipped".to_owned()],
            values: HirValuePack::fixed(vec![HirExpr::TempRef(next)]),
        }));
        let mut block = HirBlock {
            stmts: vec![
                local_decl(state),
                HirStmt::Repeat(Box::new(HirRepeat {
                    body: HirBlock {
                        stmts: vec![
                            assign(
                                HirLValue::Temp(next),
                                add(HirExpr::LocalRef(state), HirExpr::Integer(1)),
                            ),
                            goto(target),
                            skipped,
                            label(target),
                            assign(HirLValue::Local(state), HirExpr::TempRef(next)),
                        ],
                    },
                    cond: HirExpr::TempRef(next),
                })),
            ],
        };
        let mut promotion_facts = exact_home_facts(state, next);

        assert!(run_fold(&mut block, &mut promotion_facts));

        let HirStmt::Repeat(repeat_stmt) = &block.stmts[1] else {
            panic!("repeat owner must remain")
        };
        assert_eq!(
            repeat_stmt.body.stmts,
            vec![
                assign(
                    HirLValue::Local(state),
                    add(HirExpr::LocalRef(state), HirExpr::Integer(1)),
                ),
                goto(target),
                HirStmt::GlobalDecl(Box::new(HirGlobalDecl {
                    names: vec!["skipped".to_owned()],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(state)]),
                })),
                label(target),
            ]
        );
        assert_eq!(repeat_stmt.cond, HirExpr::LocalRef(state));
    }

    #[test]
    fn repeat_tail_update_accepts_nested_loop_owned_continue() {
        let state = LocalId(0);
        let next = TempId(0);
        let nested = HirStmt::While(Box::new(HirWhile {
            cond: HirExpr::Boolean(false),
            body: HirBlock {
                stmts: vec![HirStmt::Continue],
            },
        }));
        let mut block = HirBlock {
            stmts: vec![
                local_decl(state),
                HirStmt::Repeat(Box::new(HirRepeat {
                    body: HirBlock {
                        stmts: vec![
                            assign(
                                HirLValue::Temp(next),
                                add(HirExpr::LocalRef(state), HirExpr::Integer(1)),
                            ),
                            nested.clone(),
                            assign(HirLValue::Local(state), HirExpr::TempRef(next)),
                        ],
                    },
                    cond: HirExpr::TempRef(next),
                })),
            ],
        };
        let mut promotion_facts = exact_home_facts(state, next);

        assert!(run_fold(&mut block, &mut promotion_facts));

        let HirStmt::Repeat(repeat_stmt) = &block.stmts[1] else {
            panic!("repeat owner must remain")
        };
        assert_eq!(repeat_stmt.body.stmts[1], nested);
        assert_eq!(repeat_stmt.cond, HirExpr::LocalRef(state));
    }

    #[test]
    fn repeat_tail_update_rejects_candidate_owned_continue() {
        let state = LocalId(0);
        let next = TempId(0);
        let mut block = HirBlock {
            stmts: vec![
                local_decl(state),
                HirStmt::Repeat(Box::new(HirRepeat {
                    body: HirBlock {
                        stmts: vec![
                            assign(
                                HirLValue::Temp(next),
                                add(HirExpr::LocalRef(state), HirExpr::Integer(1)),
                            ),
                            HirStmt::Continue,
                            assign(HirLValue::Local(state), HirExpr::TempRef(next)),
                        ],
                    },
                    cond: HirExpr::TempRef(next),
                })),
            ],
        };
        let before = block.clone();
        let mut promotion_facts = exact_home_facts(state, next);

        assert!(!run_fold(&mut block, &mut promotion_facts));
        assert_eq!(block, before);
    }

    #[test]
    fn repeat_tail_update_uses_exact_home_under_compaction_and_cleanup() {
        let state = LocalId(0);
        let next = TempId(0);
        let cleanup = HirStmt::Close(Box::new(HirClose { from_reg: 5 }));
        let mut block = HirBlock {
            stmts: vec![
                local_decl(state),
                HirStmt::Repeat(Box::new(HirRepeat {
                    body: HirBlock {
                        stmts: vec![
                            assign(
                                HirLValue::Temp(next),
                                add(HirExpr::LocalRef(state), HirExpr::Integer(1)),
                            ),
                            cleanup.clone(),
                            assign(HirLValue::Local(state), HirExpr::TempRef(next)),
                        ],
                    },
                    cond: HirExpr::TempRef(next),
                })),
            ],
        };
        let mut promotion_facts = exact_home_facts(state, next);
        promotion_facts.enable_home_slot_compaction();

        assert!(run_fold(&mut block, &mut promotion_facts));

        let HirStmt::Repeat(repeat_stmt) = &block.stmts[1] else {
            panic!("repeat owner must remain")
        };
        assert_eq!(repeat_stmt.body.stmts[1], cleanup);
        assert_eq!(repeat_stmt.cond, HirExpr::LocalRef(state));
    }

    #[test]
    fn adjacent_repeat_tail_update_does_not_need_valid_home_provenance() {
        let state = LocalId(0);
        let next = TempId(0);
        let mut block = HirBlock {
            stmts: vec![
                local_decl(state),
                repeat_update(
                    state,
                    next,
                    add(HirExpr::LocalRef(state), HirExpr::Integer(1)),
                ),
            ],
        };
        let mut promotion_facts = exact_home_facts(state, next);
        promotion_facts.invalidate_temp_home(next);

        assert!(run_fold(&mut block, &mut promotion_facts));
    }

    #[test]
    fn nonadjacent_repeat_tail_update_keeps_invalid_home_provenance() {
        let state = LocalId(0);
        let next = TempId(0);
        let mut block = HirBlock {
            stmts: vec![
                local_decl(state),
                HirStmt::Repeat(Box::new(HirRepeat {
                    body: HirBlock {
                        stmts: vec![
                            assign(
                                HirLValue::Temp(next),
                                add(HirExpr::LocalRef(state), HirExpr::Integer(1)),
                            ),
                            HirStmt::GlobalDecl(Box::new(HirGlobalDecl {
                                names: vec!["snapshot".to_owned()],
                                values: HirValuePack::fixed(vec![HirExpr::TempRef(next)]),
                            })),
                            assign(HirLValue::Local(state), HirExpr::TempRef(next)),
                        ],
                    },
                    cond: HirExpr::TempRef(next),
                })),
            ],
        };
        let before = block.clone();
        let mut promotion_facts = exact_home_facts(state, next);
        promotion_facts.invalidate_temp_home(next);

        assert!(!run_fold(&mut block, &mut promotion_facts));
        assert_eq!(block, before);
    }

    fn local_update_with_prefix(prefix: Vec<HirStmt>) -> (HirBlock, LocalId, LocalId) {
        let state = LocalId(0);
        let next = LocalId(1);
        let mut body = vec![HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![next],
            values: HirValuePack::fixed(vec![add(HirExpr::LocalRef(state), HirExpr::Integer(1))]),
        }))];
        body.extend(prefix);
        body.push(assign(HirLValue::Local(state), HirExpr::LocalRef(next)));
        (
            HirBlock {
                stmts: vec![
                    local_decl(state),
                    HirStmt::Repeat(Box::new(HirRepeat {
                        body: HirBlock { stmts: body },
                        cond: HirExpr::LocalRef(next),
                    })),
                ],
            },
            state,
            next,
        )
    }

    fn exact_local_home_facts(left: LocalId, right: LocalId) -> ProtoPromotionFacts {
        let mut facts = ProtoPromotionFacts::default();
        let home = HomeSlotKey::new(0, 0);
        facts.record_local_home_slot(left, home);
        facts.record_local_home_slot(right, home);
        facts
    }

    #[test]
    fn local_update_accepts_continue_owned_by_nested_loop() {
        let nested = HirStmt::While(Box::new(HirWhile {
            cond: HirExpr::Boolean(false),
            body: HirBlock {
                stmts: vec![HirStmt::Continue],
            },
        }));
        let (mut block, state, next) =
            local_update_with_prefix(vec![nested.clone(), HirStmt::Break]);
        let mut promotion_facts = exact_local_home_facts(state, next);

        assert!(run_fold(&mut block, &mut promotion_facts));

        let HirStmt::Repeat(repeat_stmt) = &block.stmts[1] else {
            panic!("repeat owner must remain")
        };
        assert_eq!(
            repeat_stmt.body.stmts,
            vec![
                assign(
                    HirLValue::Local(state),
                    add(HirExpr::LocalRef(state), HirExpr::Integer(1)),
                ),
                nested,
                HirStmt::Break,
            ]
        );
        assert_eq!(repeat_stmt.cond, HirExpr::LocalRef(state));
    }

    #[test]
    fn local_update_crosses_global_declaration_without_moving_it() {
        let next = LocalId(1);
        let global = HirStmt::GlobalDecl(Box::new(HirGlobalDecl {
            names: vec!["snapshot".to_owned()],
            values: HirValuePack::fixed(vec![HirExpr::LocalRef(next)]),
        }));
        let (mut block, state, next) = local_update_with_prefix(vec![global, HirStmt::Break]);
        let mut promotion_facts = exact_local_home_facts(state, next);

        assert!(run_fold(&mut block, &mut promotion_facts));

        let HirStmt::Repeat(repeat_stmt) = &block.stmts[1] else {
            panic!("repeat owner must remain")
        };
        assert_eq!(
            repeat_stmt.body.stmts,
            vec![
                assign(
                    HirLValue::Local(state),
                    add(HirExpr::LocalRef(state), HirExpr::Integer(1)),
                ),
                HirStmt::GlobalDecl(Box::new(HirGlobalDecl {
                    names: vec!["snapshot".to_owned()],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(state)]),
                })),
                HirStmt::Break,
            ]
        );
        assert_eq!(repeat_stmt.cond, HirExpr::LocalRef(state));
    }

    #[test]
    fn local_update_accepts_owner_complete_forward_goto_after_seed() {
        let target = HirLabelId(0);
        let next = LocalId(1);
        let skipped = HirStmt::GlobalDecl(Box::new(HirGlobalDecl {
            names: vec!["skipped".to_owned()],
            values: HirValuePack::fixed(vec![HirExpr::LocalRef(next)]),
        }));
        let (mut block, state, next) =
            local_update_with_prefix(vec![goto(target), skipped, label(target), HirStmt::Break]);
        let mut promotion_facts = exact_local_home_facts(state, next);

        assert!(run_fold(&mut block, &mut promotion_facts));

        let HirStmt::Repeat(repeat_stmt) = &block.stmts[1] else {
            panic!("repeat owner must remain")
        };
        assert_eq!(
            repeat_stmt.body.stmts,
            vec![
                assign(
                    HirLValue::Local(state),
                    add(HirExpr::LocalRef(state), HirExpr::Integer(1)),
                ),
                goto(target),
                HirStmt::GlobalDecl(Box::new(HirGlobalDecl {
                    names: vec!["skipped".to_owned()],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(state)]),
                })),
                label(target),
                HirStmt::Break,
            ]
        );
        assert_eq!(repeat_stmt.cond, HirExpr::LocalRef(state));
    }

    #[test]
    fn local_update_rejects_backward_reentry_across_seed() {
        let state = LocalId(0);
        let next = LocalId(1);
        let target = HirLabelId(0);
        let mut block = HirBlock {
            stmts: vec![
                local_decl(state),
                HirStmt::Repeat(Box::new(HirRepeat {
                    body: HirBlock {
                        stmts: vec![
                            label(target),
                            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                                bindings: vec![next],
                                values: HirValuePack::fixed(vec![add(
                                    HirExpr::LocalRef(state),
                                    HirExpr::Integer(1),
                                )]),
                            })),
                            goto(target),
                            HirStmt::Break,
                            assign(HirLValue::Local(state), HirExpr::LocalRef(next)),
                        ],
                    },
                    cond: HirExpr::LocalRef(next),
                })),
            ],
        };
        let before = block.clone();
        let mut promotion_facts = exact_local_home_facts(state, next);

        assert!(!run_fold(&mut block, &mut promotion_facts));
        assert_eq!(block, before);
    }

    #[test]
    fn local_update_uses_exact_home_under_compaction_and_cleanup() {
        let cleanup = HirStmt::Close(Box::new(HirClose { from_reg: 5 }));
        let (mut block, state, next) =
            local_update_with_prefix(vec![cleanup.clone(), HirStmt::Break]);
        let mut promotion_facts = exact_local_home_facts(state, next);
        promotion_facts.enable_home_slot_compaction();

        assert!(run_fold(&mut block, &mut promotion_facts));

        let HirStmt::Repeat(repeat_stmt) = &block.stmts[1] else {
            panic!("repeat owner must remain")
        };
        assert_eq!(repeat_stmt.body.stmts[1], cleanup);
        assert_eq!(repeat_stmt.cond, HirExpr::LocalRef(state));
    }

    #[test]
    fn local_update_rejects_continue_owned_by_candidate_loop() {
        let (mut block, state, next) =
            local_update_with_prefix(vec![HirStmt::Continue, HirStmt::Break]);
        let before = block.clone();
        let mut promotion_facts = exact_local_home_facts(state, next);

        assert!(!run_fold(&mut block, &mut promotion_facts));
        assert_eq!(block, before);
    }
}
