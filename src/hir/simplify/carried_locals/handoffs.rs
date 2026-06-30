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

use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirLabelId, HirStmt, LocalId, TempId};

use super::super::mention::{stmt_writes_temp, stmts_mention_local, stmts_mention_temp};
use super::super::temp_touch::TempTouchIndex;
use super::super::visit::{HirVisitor, visit_stmts};
use super::super::walk::rewrite_stmts;
use super::binding::{
    CarryBinding, TempBindingRewrite, TempToBindingPass, TempToLocalPass, TempToTempPass,
};
use super::boundary::{next_label_has_prior_goto, stmt_contains_goto_to_label};
use super::prune::{
    RedundantSelfAssignPrunePass, collect_prunable_bindings, prune_empty_assign_stmts,
    prune_redundant_self_assigns_in_stmts,
};
use super::reads::BindingReadCollector;
use super::seeds::{
    binding_handoff_seed, direct_temp_writeback_stmt, local_handoff_seed,
    rewrite_binding_handoff_seed, rewrite_update_handoff_seed, single_binding_handoff_seed,
    update_handoff_seed,
};

pub(super) enum HandoffAction {
    RetrySameIndex,
    AdvanceIndex,
}

pub(super) fn try_collapse_handoff_at(
    block: &mut HirBlock,
    index: usize,
    outer_temps: &BTreeSet<TempId>,
    temp_touches: &TempTouchIndex<'_>,
) -> Option<HandoffAction> {
    if try_collapse_pure_binding_handoffs(block, index, outer_temps, temp_touches)
        || try_collapse_label_loop_update_handoff(block, index, outer_temps, temp_touches)
        || try_collapse_single_binding_handoff(block, index, outer_temps, temp_touches)
        || try_collapse_pure_local_handoff(block, index, outer_temps, temp_touches)
    {
        return Some(HandoffAction::RetrySameIndex);
    }
    if try_collapse_binding_update_handoff(block, index, outer_temps, temp_touches) {
        return Some(HandoffAction::AdvanceIndex);
    }
    None
}

fn try_collapse_pure_binding_handoffs(
    block: &mut HirBlock,
    index: usize,
    outer_temps: &BTreeSet<TempId>,
    temp_touches: &TempTouchIndex<'_>,
) -> bool {
    let Some(seed) = binding_handoff_seed(&block.stmts[index]) else {
        return false;
    };

    // 如果被折叠的 temp 在外层作用域中仍被引用，不能消除。
    if seed
        .rewrites
        .iter()
        .any(|rewrite| outer_temps.contains(&rewrite.from))
    {
        return false;
    }
    if next_label_has_prior_goto(&block.stmts, index) {
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
    outer_temps: &BTreeSet<TempId>,
    temp_touches: &TempTouchIndex<'_>,
) -> bool {
    let Some((carried, update_temp)) = direct_temp_writeback_stmt(&block.stmts[index]) else {
        return false;
    };
    if outer_temps.contains(&update_temp) || temp_touches.touches_before(index, update_temp) {
        return false;
    }
    if !next_label_has_prior_goto(&block.stmts, index) {
        return false;
    }
    let Some(handoff_label) = nearest_prior_label(&block.stmts, index) else {
        return false;
    };
    if !block.stmts[index + 1..]
        .iter()
        .any(|stmt| stmt_contains_goto_to_label(stmt, handoff_label))
    {
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

fn nearest_prior_label(stmts: &[HirStmt], index: usize) -> Option<HirLabelId> {
    stmts[..index].iter().rev().find_map(|stmt| match stmt {
        HirStmt::Label(label) => Some(label.id),
        _ => None,
    })
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

fn try_collapse_pure_local_handoff(
    block: &mut HirBlock,
    index: usize,
    outer_temps: &BTreeSet<TempId>,
    temp_touches: &TempTouchIndex<'_>,
) -> bool {
    let Some((temp, local)) = local_handoff_seed(&block.stmts[index]) else {
        return false;
    };

    // 如果被折叠的 temp 在外层作用域中仍被引用，不能消除。
    if outer_temps.contains(&temp) {
        return false;
    }
    if next_label_has_prior_goto(&block.stmts, index) {
        return false;
    }

    let suffix = &block.stmts[index + 1..];
    if suffix.is_empty()
        || suffix_mentions_local(suffix, local)
        || !temp_touches.touches_after(index + 1, temp)
    {
        return false;
    }

    let mut pass = TempToLocalPass { temp, local };
    if !rewrite_stmts(&mut block.stmts[index + 1..], &mut pass) {
        return false;
    }

    block.stmts.remove(index);
    true
}

fn try_collapse_single_binding_handoff(
    block: &mut HirBlock,
    index: usize,
    outer_temps: &BTreeSet<TempId>,
    temp_touches: &TempTouchIndex<'_>,
) -> bool {
    let Some((temp, binding)) = single_binding_handoff_seed(&block.stmts[index]) else {
        return false;
    };

    // 如果被折叠的 temp 在外层作用域中仍被引用，不能消除。
    if outer_temps.contains(&temp) {
        return false;
    }
    if next_label_has_prior_goto(&block.stmts, index) {
        return false;
    }

    let suffix = &block.stmts[index + 1..];
    if suffix.is_empty()
        || suffix_mentions_binding(suffix, binding)
        || !temp_touches.touches_after(index + 1, temp)
    {
        return false;
    }

    let rewritten = match binding {
        CarryBinding::Local(local) => {
            let mut pass = TempToLocalPass { temp, local };
            rewrite_stmts(&mut block.stmts[index + 1..], &mut pass)
        }
        CarryBinding::Temp(to) => {
            let mut pass = TempToTempPass { from: temp, to };
            rewrite_stmts(&mut block.stmts[index + 1..], &mut pass)
        }
    };
    if !rewritten {
        return false;
    }

    block.stmts.remove(index);
    true
}

fn try_collapse_binding_update_handoff(
    block: &mut HirBlock,
    index: usize,
    outer_temps: &BTreeSet<TempId>,
    temp_touches: &TempTouchIndex<'_>,
) -> bool {
    let Some((target_temp, carried)) = update_handoff_seed(&block.stmts[index]) else {
        return false;
    };

    // 如果被折叠的 temp 在外层作用域中仍被引用，不能消除。
    if outer_temps.contains(&target_temp) {
        return false;
    }
    if next_label_has_prior_goto(&block.stmts, index) {
        return false;
    }

    let suffix = &block.stmts[index + 1..];
    if suffix.is_empty()
        || suffix_reads_binding(suffix, carried)
        || !suffix_contains_direct_writeback(suffix, carried, target_temp)
        || !temp_touches.touches_after(index + 1, target_temp)
    {
        return false;
    }

    let rewritten = match carried {
        CarryBinding::Local(local) => {
            let mut pass = TempToLocalPass {
                temp: target_temp,
                local,
            };
            rewrite_stmts(&mut block.stmts[index + 1..], &mut pass)
        }
        CarryBinding::Temp(temp) => {
            let mut pass = TempToTempPass {
                from: target_temp,
                to: temp,
            };
            rewrite_stmts(&mut block.stmts[index + 1..], &mut pass)
        }
    };
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

fn suffix_contains_direct_writeback(
    stmts: &[HirStmt],
    binding: CarryBinding,
    target_temp: TempId,
) -> bool {
    let mut collector = DirectWritebackCollector {
        binding,
        target_temp,
        found: false,
    };
    visit_stmts(stmts, &mut collector);
    collector.found
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
            assign
                .targets
                .iter()
                .zip(&assign.values)
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
        HirStmt::Unstructured(unstructured) => suffix_writes_binding_only_via_direct_writeback(
            &unstructured.body.stmts,
            binding,
            target_temp,
        ),
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
        (CarryBinding::Local(binding), HirLValue::Local(local)) => binding == *local,
        (CarryBinding::Temp(binding), HirLValue::Temp(temp)) => binding == *temp,
        _ => false,
    }
}

struct DirectWritebackCollector {
    binding: CarryBinding,
    target_temp: TempId,
    found: bool,
}

impl HirVisitor for DirectWritebackCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        let HirStmt::Assign(assign) = stmt else {
            return;
        };
        self.found |= assign
            .targets
            .iter()
            .zip(&assign.values)
            .any(|(target, value)| {
                matches_direct_writeback_pair(target, value, self.binding, self.target_temp)
            });
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
            (CarryBinding::Local(binding), HirLValue::Local(target)) => binding == *target,
            (CarryBinding::Temp(binding), HirLValue::Temp(target)) => binding == *target,
            _ => false,
        }
}

fn suffix_mentions_local(stmts: &[HirStmt], local: LocalId) -> bool {
    stmts_mention_local(stmts, local)
}

fn suffix_mentions_binding(stmts: &[HirStmt], binding: CarryBinding) -> bool {
    match binding {
        CarryBinding::Local(local) => stmts_mention_local(stmts, local),
        CarryBinding::Temp(temp) => stmts_mention_temp(stmts, temp),
    }
}

fn stmt_reads_binding(stmt: &HirStmt, binding: CarryBinding) -> bool {
    let mut collector = BindingReadCollector::default();
    collector.collect_stmts(std::slice::from_ref(stmt));
    collector.reads.contains(&binding)
}
