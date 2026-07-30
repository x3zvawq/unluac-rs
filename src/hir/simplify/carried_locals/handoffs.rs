//! carried-local seed handoff 的逐条折叠策略。
//!
//! 这个模块处理 fallback block 中形如 `assign t = local/temp`、多目标 alias handoff、
//! 以及 `assign next = state + 1; ... state = next` 的更新后交棒。它依赖当前块的
//! temp touch 索引、边界 goto 判断和 binding rewrite 工具；不负责递归遍历，也不负责
//! label/goto mesh 的全局等价类收敛。
//!
//! 例子：
//! - 输入：`assign t = s; ... t = t + 1`
//! - 输出：`... s = s + 1`
//! - 输入：`assign tA, tB, keep = sA, sB, 0; ... assign sA, sB = tA, tB`
//! - 输出：`assign keep = 0; ...`

use std::collections::BTreeSet;

use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirStmt, TempId};

use super::super::mention::stmt_writes_temp;
use super::super::temp_touch::TempTouchIndex;
use super::super::walk::rewrite_stmts;
use super::binding::{BindingProtection, CarryBinding, TempBindingRewrite, TempToBindingPass};
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
) -> Option<HandoffAction> {
    if try_collapse_pure_binding_handoffs(
        block,
        index,
        outer_bindings,
        temp_touches,
        label_jumps,
        captured_bindings,
    ) || try_collapse_label_loop_update_handoff(
        block,
        index,
        outer_bindings,
        temp_touches,
        label_jumps,
    ) || try_collapse_single_binding_handoff(
        block,
        index,
        outer_bindings,
        temp_touches,
        label_jumps,
        captured_bindings,
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
) -> bool {
    let Some(seed) = binding_handoff_seed(&block.stmts[index]) else {
        return false;
    };

    // 外层仍提及的 source/target，或 seed 前已有路径触碰的 temp，都不是当前块私有身份。
    if seed.rewrites.iter().any(|rewrite| {
        outer_bindings.contains(&CarryBinding::Temp(rewrite.from))
            || outer_bindings.contains(&rewrite.to)
            || temp_touches.touches_before(index, rewrite.from)
            || captured_bindings.contains(&rewrite.to)
    }) {
        return false;
    }
    if label_jumps.next_label_has_prior_goto(&block.stmts, index) {
        return false;
    }

    let suffix = &block.stmts[index + 1..];
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

    let mut pass = TempToBindingPass {
        rewrites: seed.rewrites.clone(),
    };
    if !rewrite_stmts(&mut block.stmts[index + 1..], &mut pass) {
        return false;
    }

    if seed.retained_pairs.is_empty() {
        block.stmts.remove(index);
    } else if !rewrite_binding_handoff_seed(&mut block.stmts[index], &seed.retained_pairs) {
        return false;
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
) -> bool {
    let Some((carried, update_temp)) = direct_temp_writeback_stmt(&block.stmts[index]) else {
        return false;
    };
    if outer_bindings.contains(&CarryBinding::Temp(update_temp))
        || temp_touches.touches_before(index, update_temp)
    {
        return false;
    }
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
        return false;
    }

    let mut pass = TempToBindingPass {
        rewrites: vec![TempBindingRewrite {
            from: update_temp,
            to: carried,
        }],
    };
    if !rewrite_stmts(&mut block.stmts[index..], &mut pass) {
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
) -> bool {
    let Some((temp, binding)) = single_binding_handoff_seed(&block.stmts[index]) else {
        return false;
    };

    // 外层仍提及 source/target 时，这只是当前块的值快照，不能升级成同一状态身份。
    if outer_bindings.contains(&CarryBinding::Temp(temp))
        || outer_bindings.contains(&binding)
        || temp_touches.touches_before(index, temp)
    {
        return false;
    }
    if captured_bindings.contains(&binding) {
        return false;
    }
    if label_jumps.next_label_has_prior_goto(&block.stmts, index) {
        return false;
    }

    let suffix = &block.stmts[index + 1..];
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
        },
    );
    if !rewritten {
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
) -> bool {
    let Some((target_temp, carried)) = update_handoff_seed(&block.stmts[index]) else {
        return false;
    };

    // 如果被折叠的 temp 在外层作用域中仍被引用，不能消除。
    if outer_bindings.contains(&CarryBinding::Temp(target_temp))
        || captured_bindings.contains(&carried)
    {
        return false;
    }
    if label_jumps.next_label_has_prior_goto(&block.stmts, index) {
        return false;
    }

    let suffix = &block.stmts[index + 1..];
    if suffix.is_empty()
        || suffix_reads_binding(suffix, carried)
        || !suffix_ends_with_linear_direct_writeback(suffix, carried, target_temp)
        || !temp_touches.touches_after(index + 1, target_temp)
    {
        return false;
    }

    let rewritten = rewrite_stmts(
        &mut block.stmts[index + 1..],
        &mut TempToBindingPass {
            rewrites: vec![TempBindingRewrite {
                from: target_temp,
                to: carried,
            }],
        },
    );
    if !rewritten {
        return false;
    }
    if !rewrite_update_handoff_seed(&mut block.stmts[index], carried) {
        return false;
    }

    rewrite_stmts(
        &mut block.stmts[index + 1..],
        &mut RedundantSelfAssignPrunePass::for_bindings([carried]),
    );
    prune_empty_assign_stmts(block);
    true
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
