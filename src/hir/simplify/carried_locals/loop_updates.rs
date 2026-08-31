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
//! 或 label barrier 均保留原形。旧 local 形状即使尾写回前只有提前退出，也必须同槽且未启用
//! compaction；否则弱表、finalizer 或外层 cleanup 仍能观察旧 carried root 的生命周期。
//! local fold 的 apply 会在任何修改前重验 seed 与尾写回；只有完整提交才返回 changed，避免
//! candidate 形状漂移污染 fixed-point 信号。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirAssign, HirBlock, HirExpr, HirLValue, HirStmt, LocalId, TempId};
use crate::hir::promotion::ProtoPromotionFacts;

use super::super::mention::{stmts_captured_locals, stmts_mention_local};
use super::super::visit::{HirVisitor, visit_stmts};
use super::super::walk::{rewrite_expr, rewrite_stmts};
use super::HandoffIdentityFacts;
use super::binding::{
    BindingClassRewritePass, BindingProtection, CarryBinding, binding_home_slot,
    binding_home_slot_provenance_is_invalid, bindings_share_exact_home_slot,
    carry_binding_from_lvalue, record_binding_merge,
};
use super::prune::RedundantSelfAssignPrunePass;
use super::reads::BindingReadCollector;

struct LoopUpdateFold {
    seed_index: usize,
    carried: LocalId,
    next: LocalId,
    seed: HirStmt,
    writeback: HirStmt,
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

    let last_mentions = last_local_mentions(stmt_mentions);
    let mut changed = false;

    for index in 0..block.stmts.len() {
        let Some(fold) = find_fold(
            &block.stmts[index],
            index,
            &last_mentions,
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
    let mut first_mentions = BTreeMap::new();
    let mut last_mentions = BTreeMap::new();
    for (index, mentions) in stmt_mentions.iter().enumerate() {
        for binding in mentions {
            first_mentions.entry(*binding).or_insert(index);
            last_mentions.insert(*binding, index);
        }
    }
    let writes = collect_top_level_write_facts(&block.stmts);
    let mut control_prefix = Vec::with_capacity(block.stmts.len() + 1);
    control_prefix.push(0usize);
    for stmt in &block.stmts {
        control_prefix.push(
            control_prefix.last().copied().unwrap_or_default()
                + usize::from(stmt_has_label_or_goto(stmt)),
        );
    }

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
        let last_next_mention = last_mentions.get(&next_binding).copied().unwrap_or(index);
        let next_home = binding_home_slot(next_binding, promotion_facts);
        let state_home = binding_home_slot(state_binding, promotion_facts);
        let between_crosses_distinct_homes = !between.is_empty()
            && next_home
                .zip(state_home)
                .is_some_and(|(next_home, state_home)| next_home != state_home);
        let between_lacks_same_home_proof = !between.is_empty()
            && !between_crosses_distinct_homes
            && (promotion_facts.compacts_home_slots()
                || next_home.is_none()
                || state_home.is_none());
        // 候选拒绝[SemanticBarrier:ValueFlow]：RHS 读取旧 next 时，整块 rewrite 会把它改读旧 state；其它 binding 读取保持原求值。
        // 候选拒绝[SemanticBarrier:Capture]：state 被 closure 捕获时，closure 可区分合并前后的 cell/write epoch。
        // 候选拒绝[SemanticBarrier:Scope]：state 在 repeat 入口不可见时，改写会生成越界 local use。
        // 候选拒绝[PolicyBoundary]：for binding 的迭代 identity 由 loop owner 保留。
        // 候选拒绝[SemanticBarrier:Lifetime]：outer use 或重复 write/use 会暴露独立 identity；异槽的 `next=v; collectgarbage(); state=next` 若提前写 state，会让旧 state root 提前回收。
        // 候选拒绝[SemanticBarrier:EvalOrder]：between 读取旧 state、prefix 提前写 state 或存在 early transfer 时，直接写 state 会改变读取/出口顺序。
        // 候选拒绝[LayerBoundary]：Decision/Unresolved 由其 owner 消解。
        // 候选拒绝[ProofIncomplete]：invalid/缺失 home、compaction、label 区间或 blanket
        // TBC/Close 阻断目前缺精确 provenance、同槽、路径与 resource-alias 证明。
        if reads.reads.contains(&next_binding)
            || captured_locals.contains(&state)
            || !local_available_before(block, index, state, inherited_locals)
            || identity_facts.for_bindings.contains(&state)
            || outer_bindings.contains(&next_binding)
            || !identity_facts.binding_merge_preserves_identity(
                next_binding,
                state_binding,
                promotion_facts,
            )
            || binding_home_slot_provenance_is_invalid(next_binding, promotion_facts)
            || binding_home_slot_provenance_is_invalid(state_binding, promotion_facts)
            || between_crosses_distinct_homes
            || between_lacks_same_home_proof
            || first_mentions.get(&next_binding).copied() != Some(index)
            || writes.counts.get(&next_binding).copied() != Some(1)
            || writes.last_stmt.get(&state_binding).copied() != Some(index)
            || !condition_mentions.contains(&next_binding)
                && !between_mentions
                    .iter()
                    .any(|mentions| mentions.contains(&next_binding))
            || prefix.iter().any(stmt_has_early_control)
            || prefix
                .iter()
                .any(|stmt| stmt_writes_binding(stmt, state_binding))
            || between.iter().any(stmt_has_early_control)
            || stmts_have_cleanup_or_opaque(between)
            || prefix_mentions
                .iter()
                .any(|mentions| mentions.contains(&next_binding))
            || between_mentions
                .iter()
                .any(|mentions| mentions.contains(&state_binding))
            || control_prefix[last_next_mention + 1] != control_prefix[index]
            || rewrites.insert(next_binding, state_binding).is_some()
        {
            continue;
        }
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

fn stmt_has_early_control(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_) => true,
        HirStmt::If(if_stmt) => {
            if_stmt.then_block.stmts.iter().any(stmt_has_early_control)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| block.stmts.iter().any(stmt_has_early_control))
        }
        HirStmt::Block(block) => block.stmts.iter().any(stmt_has_early_control),
        _ => false,
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

fn stmts_have_cleanup_or_opaque(stmts: &[HirStmt]) -> bool {
    let mut collector = CleanupOrOpaqueCollector::default();
    visit_stmts(stmts, &mut collector);
    collector.found
}

#[derive(Default)]
struct CleanupOrOpaqueCollector {
    found: bool,
}

impl HirVisitor for CleanupOrOpaqueCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.found |= matches!(stmt, HirStmt::ToBeClosed(_) | HirStmt::Close(_));
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        self.found |= matches!(expr, HirExpr::Decision(_) | HirExpr::Unresolved(_));
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
    last_mentions: &BTreeMap<LocalId, usize>,
    captured_locals: &BTreeSet<LocalId>,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
) -> Option<LoopUpdateFold> {
    let body = loop_body(stmt)?;
    let (writeback, prefix) = body.stmts.split_last()?;
    let (carried, next) = exact_local_writeback(writeback)?;
    // 候选拒绝[SemanticBarrier:Lifetime]：loop 后仍活跃、capture/outer use、异槽或资源 identity 会观察 carried/next 的独立 epoch。
    // 候选拒绝[ProofIncomplete]：prefix 中嵌套 loop/continue/goto/cleanup 被 blanket 拒绝；需 path-complete exit/write facts。
    if carried == next
        || last_mentions.get(&carried).copied() != Some(stmt_index)
        || last_mentions.get(&next).copied() != Some(stmt_index)
        || captured_locals.contains(&carried)
        || captured_locals.contains(&next)
        || outer_bindings.contains(&CarryBinding::Local(carried))
        || outer_bindings.contains(&CarryBinding::Local(next))
        || promotion_facts.compacts_home_slots()
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
        || !stmts_allow_dead_update_fold(prefix)
    {
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

fn stmts_allow_dead_update_fold(stmts: &[HirStmt]) -> bool {
    stmts.iter().all(stmt_allows_dead_update_fold)
}

fn stmt_allows_dead_update_fold(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::If(if_stmt) => {
            stmts_allow_dead_update_fold(&if_stmt.then_block.stmts)
                && if_stmt
                    .else_block
                    .as_ref()
                    .is_none_or(|block| stmts_allow_dead_update_fold(&block.stmts))
        }
        HirStmt::Block(block) => stmts_allow_dead_update_fold(&block.stmts),
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break => true,
        HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::Continue
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
    let Some((body, repeat_cond)) = loop_body_mut(stmt) else {
        // 候选拒绝[ConvergenceGuard]：candidate 的 loop owner 已漂移；重验发生在所有修改之前。
        return false;
    };

    if body.stmts.get(fold.seed_index) != Some(&fold.seed)
        || body.stmts.last() != Some(&fold.writeback)
    {
        // 候选拒绝[ConvergenceGuard]：candidate 的 seed 或尾写回已漂移；重验发生在所有修改之前。
        return false;
    }

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
        HirBinaryExpr, HirBinaryOpKind, HirLocalDecl, HirRepeat, HirValuePack,
    };

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
}
