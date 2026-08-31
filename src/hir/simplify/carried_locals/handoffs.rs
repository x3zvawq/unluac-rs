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
    BindingProtection, CarryBinding, TempBindingRewrite, TempToBindingPass,
    bindings_share_exact_home_slot,
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
    // 候选拒绝[SemanticBarrier:ControlFlow]：prior goto 可从 seed 之前直达下一 label；删除 seed 后该入口会使用未初始化的重写 binding。
    if label_jumps.next_label_has_prior_goto(&block.stmts, index) {
        return false;
    }

    let suffix = &block.stmts[index + 1..];
    // 候选拒绝[SemanticBarrier:Lifetime]：suffix 仍读取 source 或以非直接写回改写 source 时，temp 快照与 source epoch 不再等价。
    // 候选拒绝[ProofIncomplete]：temp 在 suffix 无 touch 时 seed 常可直接死写删除；当前 owner 没有独立 dead-seed 证明。
    if suffix.is_empty()
        || seed.rewrites.iter().any(|rewrite| {
            suffix_reads_binding(suffix, rewrite.to)
                || !suffix_writes_binding_only_via_direct_writeback(
                    suffix,
                    rewrite.to,
                    rewrite.from,
                )
                || !temp_touches.touches_after(index + 1, rewrite.from)
        })
    {
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

    let mut pass = TempToBindingPass {
        rewrites: seed.rewrites.clone(),
        promotion_facts: safety.promotion_facts,
    };
    if !rewrite_stmts(&mut block.stmts[index + 1..], &mut pass) {
        // 候选拒绝[ConvergenceGuard]：touch/writeback facts 已证明 suffix 存在 temp；rewrite 无命中表示 collector 与 rewriter 不变量漂移。
        return false;
    }

    if let Some(rewritten_seed) = rewritten_seed {
        block.stmts[index] = rewritten_seed;
    } else {
        block.stmts.remove(index);
    }

    prune_redundant_self_assigns_in_stmts(
        &mut block.stmts[index + 1..],
        collect_prunable_bindings(seed.rewrites.iter().map(|rewrite| rewrite.to)),
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
    if !rewrite_stmts(&mut block.stmts[index..], &mut pass) {
        // 候选拒绝[ConvergenceGuard]：已定位 seed/update/writeback；无 rewrite 命中表示 touch index 与 rewriter 契约漂移。
        return false;
    }

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
    if label_jumps.next_label_has_prior_goto(&block.stmts, index) {
        // 候选拒绝[SemanticBarrier:ControlFlow]：外部 goto 可绕过 seed 后进入 suffix，改名会把未定义 temp 路径变成已有 binding。
        return false;
    }

    let suffix = &block.stmts[index + 1..];
    // 候选拒绝[SemanticBarrier:Lifetime]：suffix 仍 mention binding 时，重写 temp 的读写会与 binding 原有 epoch 干涉。
    // 候选拒绝[ProofIncomplete]：suffix 无 temp touch 时可考虑 dead seed 删除，但当前 handoff owner 不拥有该证明。
    if suffix.is_empty()
        || suffix_mentions_binding(suffix, binding)
        || !temp_touches.touches_after(index + 1, temp)
    {
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
    if !rewritten {
        // 候选拒绝[ConvergenceGuard]：touch facts 已证明 suffix 命中 temp；无 rewrite 表示索引/visitor 不变量漂移。
        return false;
    }

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
    if label_jumps.next_label_has_prior_goto(&block.stmts, index) {
        // 候选拒绝[SemanticBarrier:ControlFlow]：prior goto 绕过 update seed 后进入 suffix，不能把未定义 temp 替换成 carried。
        return false;
    }

    let suffix = &block.stmts[index + 1..];
    // 候选拒绝[SemanticBarrier:EvalOrder]：suffix 读取旧 carried 时，将 seed RHS 直接写 carried 会让该读取提前看到 next 值。
    // 候选拒绝[ProofIncomplete]：只接受线性前缀+末尾直接写回；一般结构化路径需 path-complete writeback facts。
    if suffix.is_empty()
        || suffix_reads_binding(suffix, carried)
        || !suffix_ends_with_linear_direct_writeback(suffix, carried, target_temp)
        || !temp_touches.touches_after(index + 1, target_temp)
    {
        return false;
    }

    let mut rewritten_seed = block.stmts[index].clone();
    assert!(
        rewrite_update_handoff_seed(&mut rewritten_seed, carried),
        "parsed update handoff seed must remain rewritable while planning"
    );

    let rewritten = rewrite_stmts(
        &mut block.stmts[index + 1..],
        &mut TempToBindingPass {
            rewrites: vec![TempBindingRewrite {
                from: target_temp,
                to: carried,
            }],
            promotion_facts: safety.promotion_facts,
        },
    );
    if !rewritten {
        // 候选拒绝[ConvergenceGuard]：suffix touch/writeback 已证明 temp 存在；无 rewrite 命中表示 plan facts 漂移。
        return false;
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

fn suffix_reads_binding(stmts: &[HirStmt], binding: CarryBinding) -> bool {
    let mut collector = BindingReadCollector::default();
    collector.collect_stmts(stmts);
    collector.reads.contains(&binding)
}

fn suffix_ends_with_linear_direct_writeback(
    stmts: &[HirStmt],
    binding: CarryBinding,
    target_temp: TempId,
) -> bool {
    let Some((writeback, prefix)) = stmts.split_last() else {
        return false;
    };
    prefix.iter().all(stmt_is_linear_handoff_prefix)
        && direct_temp_writeback_stmt(writeback) == Some((binding, target_temp))
}

fn stmt_is_linear_handoff_prefix(stmt: &HirStmt) -> bool {
    matches!(
        stmt,
        HirStmt::LocalDecl(_)
            | HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_)
    )
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
