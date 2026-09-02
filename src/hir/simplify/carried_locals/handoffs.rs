//! carried-local seed handoff 的逐条折叠策略。
//!
//! 这个模块处理 fallback block 中形如 `assign t = local/temp`、多目标 alias handoff、
//! 以及 `assign next = state + 1; ... state = next` 的更新后交棒。它依赖当前块的
//! temp touch 索引、边界 goto 判断和 binding rewrite 工具；不负责递归遍历，也不负责
//! label/goto mesh 的全局等价类收敛。source/target 若承载 capture/TBC 身份或可能与其
//! 共用物理 home，会在父模块冻结的 proto 身份事实下保留原形。任何把 temp 的求值提前
//! 写入已有 binding 的 handoff 还必须证明两端属于相同的 `(slot, close epoch)`，避免改变
//! 弱表、`__gc` 或异常 cleanup 可观察到的旧值存活期。
//! seed 与 suffix 作为一个事务提交：seed 的替换形状先在副本上冻结，suffix rewrite 命中后
//! 才执行不可失败的替换或删除，避免 plan/apply 漂移留下半提交状态。
//!
//! 例子：
//! - 输入：`assign t = s; ... t = t + 1`
//! - 输出：`... s = s + 1`
//! - 输入：`assign tA, tB, keep = sA, sB, 0; ... assign sA, sB = tA, tB`
//! - 输出：`assign keep = 0; ...`

use std::collections::BTreeSet;

use super::super::mention::stmt_writes_temp;
use super::super::temp_touch::TempTouchIndex;
use super::super::walk::rewrite_stmts;
use super::HandoffSafety;
use super::binding::{
    BindingHomeOverlap, BindingProtection, CarryBinding, TempBindingRewrite, TempToBindingPass,
    binding_home_overlap, bindings_share_exact_home_slot, carry_binding_from_lvalue,
};
use super::boundary::LabelJumpIndex;
use super::prune::{
    RedundantSelfAssignPrunePass, collect_prunable_bindings, prune_empty_assign_stmts,
    prune_redundant_self_assigns_in_stmts,
};
use super::reads::BindingReadCollector;
use super::seeds::{
    binding_handoff_seed, direct_temp_writeback_stmt, rewrite_binding_handoff_seed,
    rewrite_update_handoff_seed, single_binding_handoff_seed, update_handoff_seed,
};
use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirStmt, TempId};

pub(super) enum HandoffAction {
    RetrySameIndex,
    AdvanceIndex,
}

pub(super) fn try_collapse_handoff_at(
    block: &mut HirBlock,
    index: usize,
    outer_bindings: &dyn BindingProtection,
    temp_touches: &TempTouchIndex<'_>,
    label_jumps: &LabelJumpIndex,
    captured_bindings: &BTreeSet<CarryBinding>,
    safety: &mut HandoffSafety<'_>,
) -> Option<HandoffAction> {
    if try_collapse_pure_binding_handoffs(
        block,
        index,
        outer_bindings,
        temp_touches,
        label_jumps,
        captured_bindings,
        safety,
    ) || try_collapse_label_loop_update_handoff(
        block,
        index,
        outer_bindings,
        temp_touches,
        label_jumps,
        safety,
    ) || try_collapse_single_binding_handoff(
        block,
        index,
        outer_bindings,
        temp_touches,
        label_jumps,
        captured_bindings,
        safety,
    ) {
        return Some(HandoffAction::RetrySameIndex);
    }
    if try_collapse_binding_update_handoff(
        block,
        index,
        outer_bindings,
        temp_touches,
        label_jumps,
        captured_bindings,
        safety,
    ) {
        return Some(HandoffAction::AdvanceIndex);
    }
    None
}

fn try_collapse_pure_binding_handoffs(
    block: &mut HirBlock,
    index: usize,
    outer_bindings: &dyn BindingProtection,
    temp_touches: &TempTouchIndex<'_>,
    label_jumps: &LabelJumpIndex,
    captured_bindings: &BTreeSet<CarryBinding>,
    safety: &mut HandoffSafety<'_>,
) -> bool {
    let Some(seed) = binding_handoff_seed(&block.stmts[index]) else {
        return false;
    };

    if effectful_retained_target_precedes_rewrite_commit(&block.stmts[index], &seed.rewrites) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：Lua 逆序提交并行 targets；后置 global/table target 可先通过 `__newindex` 改写 carried home，原 self-copy 随后会恢复 RHS 快照，删除 rewrite pair 则会留下该改写。
        return false;
    }
    if seed.rewrites.iter().any(|rewrite| {
        seed.retained_pairs.iter().any(|(target, _)| {
            retained_target_conflicts_with_rewrite(*rewrite, target, safety.promotion_facts)
        })
    }) {
        return false;
    }

    // 外层仍提及的 source/target，或 seed 前已有路径触碰的 temp，都不是当前块私有身份。
    // 候选拒绝[SemanticBarrier:Lifetime]：外层/seed 前已活跃的 temp 或 source 是独立快照，改名会把旧 epoch 与 carried 状态合并。
    // 候选拒绝[SemanticBarrier:Capture]：source 被引用捕获时，closure 调用可在无显式 suffix 读取处改写/观察它。
    // 候选拒绝[SemanticBarrier:Lifetime]：异槽、compaction 或资源 identity 合并会改变 weak-root/finalizer/close 可见存活期。
    if seed.rewrites.iter().any(|rewrite| {
        outer_bindings.contains(&CarryBinding::Temp(rewrite.from))
            || outer_bindings.contains(&rewrite.to)
            || temp_touches.touches_before(index, rewrite.from)
            || captured_bindings.contains(&rewrite.to)
            || !temp_handoff_preserves_storage(rewrite.from, rewrite.to, safety)
    }) {
        return false;
    }
    // 候选拒绝[SemanticBarrier:ControlFlow]：prior goto 可从 seed 之前直达 suffix 内任一
    // label；删除 seed 后该入口会使用未初始化的重写 binding。
    if label_jumps.suffix_has_prior_goto(&block.stmts, index) {
        return false;
    }

    let active_rewrites = seed
        .rewrites
        .iter()
        .copied()
        .filter(|rewrite| temp_touches.touches_after(index + 1, rewrite.from))
        .collect::<Vec<_>>();
    let suffix = &block.stmts[index + 1..];
    // suffix 未触碰的 rewrite 只是把 binding 当前值写回已证明相同的物理 cell；它没有
    // 创建独立 value epoch，也没有可被后文消费的 temp identity，因此可随 seed pair
    // 直接删除。只有仍有 temp use 的 handoff 才需要证明 suffix 不观察旧 binding epoch，
    // 且对 binding 的写入全部是该 temp 的直接写回。
    if active_rewrites.iter().any(|rewrite| {
        suffix_reads_binding(suffix, rewrite.to)
            || !suffix_writes_binding_only_via_direct_writeback(suffix, rewrite.to, rewrite.from)
    }) {
        return false;
    }

    let rewritten_seed = if seed.retained_pairs.is_empty() {
        None
    } else {
        let mut rewritten_seed = block.stmts[index].clone();
        assert!(
            rewrite_binding_handoff_seed(&mut rewritten_seed, &seed.retained_pairs),
            "parsed binding handoff seed must remain rewritable while planning"
        );
        Some(rewritten_seed)
    };

    if !active_rewrites.is_empty() {
        let mut pass = TempToBindingPass {
            rewrites: active_rewrites.clone(),
            promotion_facts: safety.promotion_facts,
        };
        assert!(
            rewrite_stmts(&mut block.stmts[index + 1..], &mut pass),
            "binding handoff suffix must contain a planned temp rewrite"
        );
    }

    let rewritten_suffix_start = if rewritten_seed.is_some() {
        index + 1
    } else {
        index
    };
    if let Some(rewritten_seed) = rewritten_seed {
        block.stmts[index] = rewritten_seed;
    } else {
        block.stmts.remove(index);
    }

    prune_redundant_self_assigns_in_stmts(
        &mut block.stmts[rewritten_suffix_start..],
        collect_prunable_bindings(active_rewrites.iter().map(|rewrite| rewrite.to)),
    );
    prune_empty_assign_stmts(block);
    true
}

fn try_collapse_label_loop_update_handoff(
    block: &mut HirBlock,
    index: usize,
    outer_bindings: &dyn BindingProtection,
    temp_touches: &TempTouchIndex<'_>,
    label_jumps: &LabelJumpIndex,
    safety: &mut HandoffSafety<'_>,
) -> bool {
    let Some((carried, update_temp)) = direct_temp_writeback_stmt(&block.stmts[index]) else {
        return false;
    };
    // 候选拒绝[SemanticBarrier:Lifetime]：update temp 有 seed 前入口 use 或与 carried 不同 storage identity 时，改名会合并不同 epoch/root。
    if outer_bindings.contains(&CarryBinding::Temp(update_temp))
        || temp_touches.touches_before(index, update_temp)
        || !temp_handoff_preserves_storage(update_temp, carried, safety)
    {
        return false;
    }
    // 候选拒绝[SemanticBarrier:ControlFlow]：此 owner 只处理回到 prior label 的 handoff；没有该回边时 writeback 是普通顺序赋值。
    if !label_jumps.next_label_has_prior_goto(&block.stmts, index) {
        return false;
    }
    let Some(handoff_label) = label_jumps.nearest_prior_label(index) else {
        return false;
    };
    if !label_jumps.has_goto_at_or_after(index + 1, handoff_label) {
        return false;
    }

    let suffix = &block.stmts[index + 1..];
    let Some(relative_update_index) = find_label_loop_update(suffix, carried, update_temp) else {
        return false;
    };
    let update_index = index + 1 + relative_update_index;
    if block.stmts[update_index + 1..]
        .iter()
        .any(|stmt| stmt_writes_temp(stmt, update_temp))
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：update 后再次写 temp 时，全 suffix 改名会把后续独立 temp epoch 覆盖到 carried。
        return false;
    }

    let mut pass = TempToBindingPass {
        rewrites: vec![TempBindingRewrite {
            from: update_temp,
            to: carried,
        }],
        promotion_facts: safety.promotion_facts,
    };
    assert!(
        rewrite_stmts(&mut block.stmts[index..], &mut pass),
        "label-loop handoff must contain its planned temp rewrite"
    );

    prune_redundant_self_assigns_in_stmts(
        &mut block.stmts[index..],
        collect_prunable_bindings([carried]),
    );
    prune_empty_assign_stmts(block);
    true
}

fn find_label_loop_update(
    stmts: &[HirStmt],
    carried: CarryBinding,
    update_temp: TempId,
) -> Option<usize> {
    for (index, stmt) in stmts.iter().enumerate() {
        if stmt_writes_temp(stmt, update_temp) {
            return matches!(update_handoff_seed(stmt), Some((target, source)) if target == update_temp && source == carried)
                .then_some(index);
        }
        if stmt_reads_binding(stmt, CarryBinding::Temp(update_temp)) {
            return None;
        }
    }
    None
}

fn try_collapse_single_binding_handoff(
    block: &mut HirBlock,
    index: usize,
    outer_bindings: &dyn BindingProtection,
    temp_touches: &TempTouchIndex<'_>,
    label_jumps: &LabelJumpIndex,
    captured_bindings: &BTreeSet<CarryBinding>,
    safety: &mut HandoffSafety<'_>,
) -> bool {
    let Some((temp, binding)) = single_binding_handoff_seed(&block.stmts[index]) else {
        return false;
    };

    // 外层仍提及 source/target 时，这只是当前块的值快照，不能升级成同一状态身份。
    // 候选拒绝[SemanticBarrier:Lifetime]：outer/source 前 touch 证明 temp 是独立快照；合并会让跨块读取看到 binding 的后续 epoch。
    if outer_bindings.contains(&CarryBinding::Temp(temp))
        || outer_bindings.contains(&binding)
        || temp_touches.touches_before(index, temp)
    {
        return false;
    }
    if captured_bindings.contains(&binding) {
        // 候选拒绝[SemanticBarrier:Capture]：closure 可在 suffix 中隐式读写 binding，文本 mention 不能证明快照等价。
        return false;
    }
    if !temp_handoff_preserves_storage(temp, binding, safety) {
        // 候选拒绝[SemanticBarrier:Lifetime]：异槽或资源 identity 的 temp/binding 同值仍是两个可被 GC/close 观察的 root。
        return false;
    }
    if label_jumps.suffix_has_prior_goto(&block.stmts, index) {
        // 候选拒绝[SemanticBarrier:ControlFlow]：外部 goto 可绕过 seed 后进入 suffix，改名会把未定义 temp 路径变成已有 binding。
        return false;
    }

    if !temp_touches.touches_after(index + 1, temp) {
        // exact-home 与 identity guards 已证明该赋值是同一 cell 的 self-copy；suffix 没有
        // temp use，删除 seed 不会消除值、root 或 close epoch 的消费者。
        block.stmts.remove(index);
        return true;
    }

    let suffix = &block.stmts[index + 1..];
    // 候选拒绝[SemanticBarrier:Lifetime]：suffix 仍 mention binding 时，重写 temp 的读写会与 binding 原有 epoch 干涉。
    if suffix_mentions_binding(suffix, binding) {
        return false;
    }

    let rewritten = rewrite_stmts(
        &mut block.stmts[index + 1..],
        &mut TempToBindingPass {
            rewrites: vec![TempBindingRewrite {
                from: temp,
                to: binding,
            }],
            promotion_facts: safety.promotion_facts,
        },
    );
    assert!(
        rewritten,
        "single binding handoff suffix must contain its planned temp rewrite"
    );

    block.stmts.remove(index);
    true
}

fn try_collapse_binding_update_handoff(
    block: &mut HirBlock,
    index: usize,
    outer_bindings: &dyn BindingProtection,
    temp_touches: &TempTouchIndex<'_>,
    label_jumps: &LabelJumpIndex,
    captured_bindings: &BTreeSet<CarryBinding>,
    safety: &mut HandoffSafety<'_>,
) -> bool {
    let Some((target_temp, carried)) = update_handoff_seed(&block.stmts[index]) else {
        return false;
    };

    // 如果被折叠的 temp 在外层作用域中仍被引用，不能消除。
    // 候选拒绝[SemanticBarrier:Lifetime]：outer temp use 或异槽/resource identity 会观察被删除 target temp 的独立 epoch/root。
    // 候选拒绝[SemanticBarrier:Capture]：carried 被 closure 隐式访问时，把 update 提前写入 carried 会改变 closure 观察值。
    if outer_bindings.contains(&CarryBinding::Temp(target_temp))
        || captured_bindings.contains(&carried)
        || !temp_handoff_preserves_storage(target_temp, carried, safety)
    {
        return false;
    }
    if label_jumps.suffix_has_prior_goto(&block.stmts, index) {
        // 候选拒绝[SemanticBarrier:ControlFlow]：prior goto 绕过 update seed 后进入 suffix，不能把未定义 temp 替换成 carried。
        return false;
    }

    // exact-home + identity proof 意味着 seed 的 temp target 本来就写入 carried 的物理
    // cell；末尾 writeback 只是机械名字交接，不是运行语义前提。排除外部入边后，把
    // suffix 中该 temp 的所有嵌套读写统一命名为 carried 不会移动求值、写入或 root
    // 生命周期，因此结构化分支不需要额外的 path-complete writeback 形状。
    let mut rewritten_seed = block.stmts[index].clone();
    assert!(
        rewrite_update_handoff_seed(&mut rewritten_seed, carried),
        "parsed update handoff seed must remain rewritable while planning"
    );

    if temp_touches.touches_after(index + 1, target_temp) {
        assert!(
            rewrite_stmts(
                &mut block.stmts[index + 1..],
                &mut TempToBindingPass {
                    rewrites: vec![TempBindingRewrite {
                        from: target_temp,
                        to: carried,
                    }],
                    promotion_facts: safety.promotion_facts,
                },
            ),
            "binding update suffix must contain its planned temp rewrite"
        );
    }
    block.stmts[index] = rewritten_seed;

    rewrite_stmts(
        &mut block.stmts[index + 1..],
        &mut RedundantSelfAssignPrunePass::for_bindings([carried]),
    );
    prune_empty_assign_stmts(block);
    true
}

fn temp_handoff_preserves_storage(
    temp: TempId,
    target: CarryBinding,
    safety: &HandoffSafety<'_>,
) -> bool {
    let source = CarryBinding::Temp(temp);
    !safety.promotion_facts.compacts_home_slots()
        && bindings_share_exact_home_slot(source, target, safety.promotion_facts)
        && safety.identity_facts.binding_merge_preserves_identity(
            source,
            target,
            safety.promotion_facts,
        )
}

fn retained_target_conflicts_with_rewrite(
    rewrite: TempBindingRewrite,
    target: &HirLValue,
    promotion_facts: &crate::hir::promotion::ProtoPromotionFacts,
) -> bool {
    let Some(target) = carry_binding_from_lvalue(target) else {
        return false;
    };
    if target == rewrite.to || bindings_share_exact_home_slot(target, rewrite.to, promotion_facts) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：删除 rewrite pair 会移除同一物理 target 的一次并行写，改变重复 target 的覆盖顺序。
        return true;
    }
    match binding_home_overlap(target, rewrite.to, promotion_facts) {
        BindingHomeOverlap::Overlap => {
            // 候选拒绝[SemanticBarrier:EvalOrder]：retained target 的完整可能 home 集与 rewrite destination 相交；删除 pair 可能移除同一物理 target 的一次并行写。
            true
        }
        BindingHomeOverlap::Unknown => {
            // 候选拒绝[SemanticBarrier:EvalOrder]：`t(slot0), l(slot0) = p0, other`
            // 先以逆序 target 写入 other、再由 self-copy 恢复 p0；任一端 provenance
            // 不完整时仍可能是该同槽反例，删除 rewrite pair 会把最终值改成 other。
            true
        }
        BindingHomeOverlap::Disjoint => false,
    }
}

fn effectful_retained_target_precedes_rewrite_commit(
    stmt: &HirStmt,
    rewrites: &[TempBindingRewrite],
) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    let mut earlier_rewrite = false;
    for target in &assign.targets {
        match target {
            HirLValue::Temp(temp) => {
                earlier_rewrite |= rewrites.iter().any(|rewrite| rewrite.from == *temp);
            }
            HirLValue::Global(_) | HirLValue::TableAccess(_) if earlier_rewrite => return true,
            HirLValue::Param(_)
            | HirLValue::Local(_)
            | HirLValue::Upvalue(_)
            | HirLValue::Global(_)
            | HirLValue::TableAccess(_) => {}
        }
    }
    false
}

fn suffix_reads_binding(stmts: &[HirStmt], binding: CarryBinding) -> bool {
    let mut collector = BindingReadCollector::default();
    collector.collect_stmts(stmts);
    collector.reads.contains(&binding)
}

fn suffix_writes_binding_only_via_direct_writeback(
    stmts: &[HirStmt],
    binding: CarryBinding,
    target_temp: TempId,
) -> bool {
    stmts
        .iter()
        .all(|stmt| stmt_writes_binding_only_via_direct_writeback(stmt, binding, target_temp))
}

fn stmt_writes_binding_only_via_direct_writeback(
    stmt: &HirStmt,
    binding: CarryBinding,
    target_temp: TempId,
) -> bool {
    match stmt {
        HirStmt::Assign(assign) => {
            if assign.values.tail.is_some() || assign.targets.len() != assign.values.fixed.len() {
                return !assign
                    .targets
                    .iter()
                    .any(|target| binding_matches_lvalue(target, binding));
            }
            assign
                .targets
                .iter()
                .zip(&assign.values.fixed)
                .all(|(target, value)| {
                    !binding_matches_lvalue(target, binding)
                        || matches_direct_writeback_pair(target, value, binding, target_temp)
                })
        }
        HirStmt::If(if_stmt) => {
            suffix_writes_binding_only_via_direct_writeback(
                &if_stmt.then_block.stmts,
                binding,
                target_temp,
            ) && if_stmt.else_block.as_ref().is_none_or(|else_block| {
                suffix_writes_binding_only_via_direct_writeback(
                    &else_block.stmts,
                    binding,
                    target_temp,
                )
            })
        }
        HirStmt::While(while_stmt) => suffix_writes_binding_only_via_direct_writeback(
            &while_stmt.body.stmts,
            binding,
            target_temp,
        ),
        HirStmt::Repeat(repeat_stmt) => suffix_writes_binding_only_via_direct_writeback(
            &repeat_stmt.body.stmts,
            binding,
            target_temp,
        ),
        HirStmt::NumericFor(numeric_for) => suffix_writes_binding_only_via_direct_writeback(
            &numeric_for.body.stmts,
            binding,
            target_temp,
        ),
        HirStmt::GenericFor(generic_for) => suffix_writes_binding_only_via_direct_writeback(
            &generic_for.body.stmts,
            binding,
            target_temp,
        ),
        HirStmt::Block(block) => {
            suffix_writes_binding_only_via_direct_writeback(&block.stmts, binding, target_temp)
        }
        HirStmt::LocalDecl(_)
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
        HirStmt::GlobalDecl(_) => false,
    }
}

fn binding_matches_lvalue(lvalue: &HirLValue, binding: CarryBinding) -> bool {
    match (binding, lvalue) {
        (CarryBinding::Param(binding), HirLValue::Param(param)) => binding == *param,
        (CarryBinding::Local(binding), HirLValue::Local(local)) => binding == *local,
        (CarryBinding::Temp(binding), HirLValue::Temp(temp)) => binding == *temp,
        _ => false,
    }
}

fn matches_direct_writeback_pair(
    target: &HirLValue,
    value: &HirExpr,
    binding: CarryBinding,
    target_temp: TempId,
) -> bool {
    matches!(value, HirExpr::TempRef(temp) if *temp == target_temp)
        && match (binding, target) {
            (CarryBinding::Param(binding), HirLValue::Param(target)) => binding == *target,
            (CarryBinding::Local(binding), HirLValue::Local(target)) => binding == *target,
            (CarryBinding::Temp(binding), HirLValue::Temp(target)) => binding == *target,
            _ => false,
        }
}

fn suffix_mentions_binding(stmts: &[HirStmt], binding: CarryBinding) -> bool {
    super::reads::collect_binding_mentions_by_stmt(stmts)
        .iter()
        .any(|mentions| mentions.contains(&binding))
}

fn stmt_reads_binding(stmt: &HirStmt, binding: CarryBinding) -> bool {
    let mut collector = BindingReadCollector::default();
    collector.collect_stmts(std::slice::from_ref(stmt));
    collector.reads.contains(&binding)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::common::{
        HirAssign, HirBinaryExpr, HirBinaryOpKind, HirGoto, HirIf, HirLabel, HirLabelId,
        HirTableAccess, HirValuePack, LocalId, ParamId,
    };
    use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

    struct PanickingBindingProtection;

    impl BindingProtection for PanickingBindingProtection {
        fn contains(&self, _binding: &CarryBinding) -> bool {
            panic!("effectful retained-target guard must run before suffix/storage proofs");
        }
    }

    fn empty_identity_facts() -> super::super::HandoffIdentityFacts {
        super::super::HandoffIdentityFacts {
            debug: BTreeSet::new(),
            for_bindings: BTreeSet::new(),
            physical_roots: BTreeSet::new(),
            reference_captured: BTreeSet::new(),
            to_be_closed: BTreeSet::new(),
            preserved: BTreeSet::new(),
        }
    }

    fn assign(targets: Vec<HirLValue>, values: Vec<HirExpr>) -> HirStmt {
        HirStmt::Assign(Box::new(HirAssign {
            targets,
            values: HirValuePack::fixed(values),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }))
    }

    fn effectful_parallel_seed(rewrite_first: bool) -> HirStmt {
        let rewrite = (HirLValue::Temp(TempId(0)), HirExpr::LocalRef(LocalId(0)));
        let table_write = (
            HirLValue::TableAccess(Box::new(HirTableAccess {
                base: HirExpr::LocalRef(LocalId(1)),
                key: HirExpr::Integer(1),
                method_setup_protocol: None,
            })),
            HirExpr::Integer(0),
        );
        let pairs = if rewrite_first {
            [rewrite, table_write]
        } else {
            [table_write, rewrite]
        };
        HirStmt::Assign(Box::new(HirAssign {
            targets: pairs.iter().map(|(target, _)| target.clone()).collect(),
            values: HirValuePack::fixed(pairs.into_iter().map(|(_, value)| value).collect()),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }))
    }

    #[test]
    fn retained_target_conflicts_with_rewrite_when_different_bindings_share_exact_home() {
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(LocalId(0), HomeSlotKey::new(0, 0));
        let rewrite = TempBindingRewrite {
            from: TempId(0),
            to: CarryBinding::Param(ParamId(0)),
        };

        assert!(retained_target_conflicts_with_rewrite(
            rewrite,
            &HirLValue::Local(LocalId(0)),
            &promotion_facts,
        ));
    }

    #[test]
    fn retained_target_conflicts_with_rewrite_when_physical_home_relation_is_unknown() {
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(LocalId(0), HomeSlotKey::new(0, 0));
        promotion_facts.record_local_home_merge(LocalId(0), None);
        let rewrite = TempBindingRewrite {
            from: TempId(0),
            to: CarryBinding::Param(ParamId(0)),
        };

        assert!(retained_target_conflicts_with_rewrite(
            rewrite,
            &HirLValue::Local(LocalId(0)),
            &promotion_facts,
        ));
    }

    #[test]
    fn retained_home_free_target_does_not_conflict_with_physical_rewrite_destination() {
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_home_free_local(LocalId(0));
        let rewrite = TempBindingRewrite {
            from: TempId(0),
            to: CarryBinding::Param(ParamId(0)),
        };

        assert!(!retained_target_conflicts_with_rewrite(
            rewrite,
            &HirLValue::Local(LocalId(0)),
            &promotion_facts,
        ));
    }

    #[test]
    fn retained_invalidated_target_does_not_conflict_when_complete_home_union_is_disjoint() {
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(LocalId(0), HomeSlotKey::new(1, 0));
        promotion_facts
            .record_local_home_merge(LocalId(0), Some(BTreeSet::from([HomeSlotKey::new(2, 0)])));
        let rewrite = TempBindingRewrite {
            from: TempId(0),
            to: CarryBinding::Param(ParamId(0)),
        };

        assert!(!retained_target_conflicts_with_rewrite(
            rewrite,
            &HirLValue::Local(LocalId(0)),
            &promotion_facts,
        ));
    }

    #[test]
    fn retained_invalidated_target_conflicts_when_complete_home_union_intersects() {
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(LocalId(0), HomeSlotKey::new(1, 0));
        promotion_facts
            .record_local_home_merge(LocalId(0), Some(BTreeSet::from([HomeSlotKey::new(0, 0)])));
        let rewrite = TempBindingRewrite {
            from: TempId(0),
            to: CarryBinding::Param(ParamId(0)),
        };

        assert!(retained_target_conflicts_with_rewrite(
            rewrite,
            &HirLValue::Local(LocalId(0)),
            &promotion_facts,
        ));
    }

    #[test]
    fn retained_target_does_not_conflict_with_rewrite_when_homes_are_distinct() {
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(LocalId(0), HomeSlotKey::new(1, 0));
        let rewrite = TempBindingRewrite {
            from: TempId(0),
            to: CarryBinding::Param(ParamId(0)),
        };

        assert!(!retained_target_conflicts_with_rewrite(
            rewrite,
            &HirLValue::Local(LocalId(0)),
            &promotion_facts,
        ));
    }

    #[test]
    fn effectful_retained_target_precedes_rewrite_commit_when_it_is_later_in_target_list() {
        let stmt = effectful_parallel_seed(true);
        let seed = binding_handoff_seed(&stmt).expect("parallel seed should parse");

        assert!(effectful_retained_target_precedes_rewrite_commit(
            &stmt,
            &seed.rewrites,
        ));
    }

    #[test]
    fn effectful_retained_target_follows_rewrite_commit_when_it_is_earlier_in_target_list() {
        let stmt = effectful_parallel_seed(false);
        let seed = binding_handoff_seed(&stmt).expect("parallel seed should parse");

        assert!(!effectful_retained_target_precedes_rewrite_commit(
            &stmt,
            &seed.rewrites,
        ));
    }

    #[test]
    fn pure_handoff_rejects_effectful_retained_target_before_other_proofs() {
        let mut block = HirBlock {
            stmts: vec![effectful_parallel_seed(true)],
        };
        let stmt_temp_refs =
            super::super::super::temp_touch::collect_temp_refs_by_stmt(&block.stmts);
        let temp_touches = TempTouchIndex::new(&stmt_temp_refs);
        let label_jumps = LabelJumpIndex::new(&block.stmts);
        let identity_facts = empty_identity_facts();
        let mut promotion_facts = ProtoPromotionFacts::default();
        let mut safety = HandoffSafety {
            promotion_facts: &mut promotion_facts,
            identity_facts: &identity_facts,
        };

        assert!(!try_collapse_pure_binding_handoffs(
            &mut block,
            0,
            &PanickingBindingProtection,
            &temp_touches,
            &label_jumps,
            &BTreeSet::new(),
            &mut safety,
        ));
    }

    #[test]
    fn single_handoff_deletes_exact_home_seed_without_temp_consumer() {
        let mut block = HirBlock {
            stmts: vec![
                assign(
                    vec![HirLValue::Temp(TempId(0))],
                    vec![HirExpr::ParamRef(ParamId(0))],
                ),
                HirStmt::Return(Box::new(crate::hir::common::HirReturn {
                    values: HirValuePack::fixed(vec![HirExpr::ParamRef(ParamId(0))]),
                })),
            ],
        };
        let stmt_temp_refs =
            super::super::super::temp_touch::collect_temp_refs_by_stmt(&block.stmts);
        let temp_touches = TempTouchIndex::new(&stmt_temp_refs);
        let label_jumps = LabelJumpIndex::new(&block.stmts);
        let identity_facts = empty_identity_facts();
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_temp_home_slot_for_test(TempId(0), HomeSlotKey::new(0, 0));
        let mut safety = HandoffSafety {
            promotion_facts: &mut promotion_facts,
            identity_facts: &identity_facts,
        };

        assert!(try_collapse_single_binding_handoff(
            &mut block,
            0,
            &BTreeSet::new(),
            &temp_touches,
            &label_jumps,
            &BTreeSet::new(),
            &mut safety,
        ));
        assert_eq!(block.stmts.len(), 1);
        assert!(matches!(block.stmts[0], HirStmt::Return(_)));
    }

    #[test]
    fn pure_handoff_partitions_live_rewrite_from_dead_exact_home_seed() {
        let mut block = HirBlock {
            stmts: vec![
                assign(
                    vec![HirLValue::Temp(TempId(0)), HirLValue::Temp(TempId(1))],
                    vec![HirExpr::ParamRef(ParamId(0)), HirExpr::LocalRef(LocalId(1))],
                ),
                assign(
                    vec![HirLValue::Param(ParamId(0))],
                    vec![HirExpr::TempRef(TempId(0))],
                ),
            ],
        };
        let stmt_temp_refs =
            super::super::super::temp_touch::collect_temp_refs_by_stmt(&block.stmts);
        let temp_touches = TempTouchIndex::new(&stmt_temp_refs);
        let label_jumps = LabelJumpIndex::new(&block.stmts);
        let identity_facts = empty_identity_facts();
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_temp_home_slot_for_test(TempId(0), HomeSlotKey::new(0, 0));
        promotion_facts.record_temp_home_slot_for_test(TempId(1), HomeSlotKey::new(1, 0));
        promotion_facts.record_local_home_slot(LocalId(1), HomeSlotKey::new(1, 0));
        let mut safety = HandoffSafety {
            promotion_facts: &mut promotion_facts,
            identity_facts: &identity_facts,
        };

        assert!(try_collapse_pure_binding_handoffs(
            &mut block,
            0,
            &BTreeSet::new(),
            &temp_touches,
            &label_jumps,
            &BTreeSet::new(),
            &mut safety,
        ));
        assert!(block.stmts.is_empty());
    }

    #[test]
    fn update_handoff_rewrites_exact_home_temp_through_structured_suffix() {
        let update = HirExpr::Binary(Box::new(HirBinaryExpr {
            op: HirBinaryOpKind::Add,
            lhs: HirExpr::ParamRef(ParamId(0)),
            rhs: HirExpr::Integer(1),
        }));
        let mut block = HirBlock {
            stmts: vec![
                assign(vec![HirLValue::Temp(TempId(0))], vec![update]),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::Boolean(true),
                    then_block: HirBlock {
                        stmts: vec![HirStmt::Return(Box::new(crate::hir::common::HirReturn {
                            values: HirValuePack::fixed(vec![HirExpr::TempRef(TempId(0))]),
                        }))],
                    },
                    else_block: Some(HirBlock {
                        stmts: vec![HirStmt::Return(Box::new(crate::hir::common::HirReturn {
                            values: HirValuePack::fixed(vec![HirExpr::TempRef(TempId(0))]),
                        }))],
                    }),
                })),
            ],
        };
        let stmt_temp_refs =
            super::super::super::temp_touch::collect_temp_refs_by_stmt(&block.stmts);
        let temp_touches = TempTouchIndex::new(&stmt_temp_refs);
        let label_jumps = LabelJumpIndex::new(&block.stmts);
        let identity_facts = empty_identity_facts();
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_temp_home_slot_for_test(TempId(0), HomeSlotKey::new(0, 0));
        let mut safety = HandoffSafety {
            promotion_facts: &mut promotion_facts,
            identity_facts: &identity_facts,
        };

        assert!(try_collapse_binding_update_handoff(
            &mut block,
            0,
            &BTreeSet::new(),
            &temp_touches,
            &label_jumps,
            &BTreeSet::new(),
            &mut safety,
        ));
        let refs = super::super::super::temp_touch::collect_temp_refs_by_stmt(&block.stmts);
        assert!(refs.iter().all(BTreeSet::is_empty));
        let HirStmt::Assign(seed) = &block.stmts[0] else {
            panic!("expected rewritten update seed");
        };
        assert_eq!(seed.targets, vec![HirLValue::Param(ParamId(0))]);
    }

    #[test]
    fn update_handoff_rejects_non_adjacent_suffix_label_with_prior_goto() {
        let label = HirLabelId(0);
        let update = HirExpr::Binary(Box::new(HirBinaryExpr {
            op: HirBinaryOpKind::Add,
            lhs: HirExpr::ParamRef(ParamId(0)),
            rhs: HirExpr::Integer(1),
        }));
        let mut block = HirBlock {
            stmts: vec![
                HirStmt::Goto(Box::new(HirGoto { target: label })),
                assign(vec![HirLValue::Temp(TempId(0))], vec![update]),
                assign(
                    vec![HirLValue::Local(LocalId(1))],
                    vec![HirExpr::Integer(0)],
                ),
                HirStmt::Label(Box::new(HirLabel {
                    id: label,
                    tbc_barriers: Vec::new(),
                })),
                HirStmt::Return(Box::new(crate::hir::common::HirReturn {
                    values: HirValuePack::fixed(vec![HirExpr::TempRef(TempId(0))]),
                })),
            ],
        };
        let stmt_temp_refs =
            super::super::super::temp_touch::collect_temp_refs_by_stmt(&block.stmts);
        let temp_touches = TempTouchIndex::new(&stmt_temp_refs);
        let label_jumps = LabelJumpIndex::new(&block.stmts);
        let identity_facts = empty_identity_facts();
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_temp_home_slot_for_test(TempId(0), HomeSlotKey::new(0, 0));
        let mut safety = HandoffSafety {
            promotion_facts: &mut promotion_facts,
            identity_facts: &identity_facts,
        };

        assert!(!try_collapse_binding_update_handoff(
            &mut block,
            1,
            &BTreeSet::new(),
            &temp_touches,
            &label_jumps,
            &BTreeSet::new(),
            &mut safety,
        ));
    }
}
