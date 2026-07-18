//! carried-local handoff 折叠 pass 的编排入口。
//!
//! 这个 pass 把 fallback label/goto 区域里“交棒出去的 carried 状态”认回原绑定，
//! 也会收敛结构化分支/循环里相邻的 `seed local + empty carried local`。它只负责
//! 后序遍历、外层 binding 活跃性保护，以及在当前 block 内按既定顺序调用各类 owner：
//! `adjacent.rs` 处理相邻 local seed，`boundary.rs` 索引 label/goto 边界，
//! `handoffs.rs` 处理具体 seed/update handoff，`binding.rs` 和 `prune.rs` 提供共享工具。
//!
//! 它不会发明新 local，也不会在原 local 仍然活跃时强行合并两段状态；所有折叠都必须
//! 先证明 seed 在后续不再可观察、temp 不被外层作用域消费，并且写回形状可证明。
//! captured local 也不能作为纯 alias handoff 的来源：闭包调用可能在后缀没有显式提及
//! 该 local 时写回它，跨过这类调用消除快照会改变后续读值。
//!
//! 例子：
//! - 输入：`local l0 = 1; do t4 = l0; ::L1:: if t4 < 3 then t4 = t4 + 1; goto L1 end end`
//! - 输出：`local l0 = 1; do ::L1:: if l0 < 3 then l0 = l0 + 1; goto L1 end end`
//! - 输入：`assign t8, t9, t10 = t1, t2, 0; ... assign t1, t2 = t8, t9`
//! - 输出：`assign t10 = 0; ...`

mod adjacent;
mod binding;
mod boundary;
mod handoffs;
mod prune;
mod reads;
mod seeds;

use std::collections::BTreeSet;

use crate::hir::common::{HirBlock, HirProto, HirStmt};

use super::temp_touch::{RefScopeTracker, TempTouchIndex, collect_temp_refs_by_stmt};
use super::walk::for_each_nested_block_mut;

use self::adjacent::try_collapse_adjacent_local_seed_handoff;
use self::binding::CarryBinding;
use self::boundary::LabelJumpIndex;
use self::handoffs::{HandoffAction, try_collapse_handoff_at};
use self::reads::{collect_binding_mentions_by_stmt, collect_binding_mentions_in_expr};
use super::mention::stmts_captured_locals;

pub(super) fn collapse_carried_local_handoffs_in_proto(proto: &mut HirProto) -> bool {
    collapse_handoffs_recursive(&mut proto.body, &BTreeSet::new())
}

/// 自定义后序遍历：先递归处理子块（同时把外层 binding 引用集传下去），再在当前块做
/// handoff 折叠。外层仍提及的 source 或 target 不能在当前块内被当成私有快照消除。
fn collapse_handoffs_recursive(
    block: &mut HirBlock,
    outer_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    let mut changed = false;

    // 跟踪每个嵌套语句“进入该子块时需要保护的 binding 集”。
    // 对于 index 处的语句，保护集 = 继承的 outer_bindings ∪ 本块中其他语句的 mentions。
    // 注意不能用 `all - self` 来近似：如果某个 binding 同时出现在当前语句和其他语句中，
    // 差集会把它减掉，导致跨作用域的引用失去保护。这里用前缀+后缀并集来精确计算。
    let stmt_binding_refs = collect_binding_mentions_by_stmt(&block.stmts);
    let mut binding_refs = RefScopeTracker::new(&stmt_binding_refs);
    for index in 0..binding_refs.len() {
        binding_refs.enter_stmt(index);
        let repeat_cond_refs = match &block.stmts[index] {
            HirStmt::Repeat(repeat_stmt) => {
                Some(collect_binding_mentions_in_expr(&repeat_stmt.cond))
            }
            _ => None,
        };
        let mut child_outer = None;

        for_each_nested_block_mut(&mut block.stmts[index], &mut |nested_block| {
            let child_outer = child_outer.get_or_insert_with(|| {
                let mut child_outer = binding_refs.outer_with_prefix_and_suffix(outer_bindings);
                if let Some(repeat_cond_refs) = &repeat_cond_refs {
                    child_outer.extend(repeat_cond_refs.iter().copied());
                }
                child_outer
            });
            changed |= collapse_handoffs_recursive(nested_block, child_outer);
        });

        binding_refs.leave_stmt(index);
    }

    // 后序：子块都处理完之后，再处理当前块的 handoff。
    changed |= collapse_block_handoffs(block, outer_bindings);
    changed
}

fn collapse_block_handoffs(block: &mut HirBlock, outer_bindings: &BTreeSet<CarryBinding>) -> bool {
    let mut changed = false;
    let mut index = 0;
    let mut stmt_temp_refs = collect_temp_refs_by_stmt(&block.stmts);

    loop {
        let action = {
            let temp_touches = TempTouchIndex::new(&stmt_temp_refs);
            let label_jumps = LabelJumpIndex::new(&block.stmts);
            let captured_locals = stmts_captured_locals(&block.stmts);
            let mut action = None;
            while index < block.stmts.len() {
                if try_collapse_adjacent_local_seed_handoff(block, index) {
                    action = Some(HandoffAction::RetrySameIndex);
                    break;
                }
                if let Some(handoff_action) = try_collapse_handoff_at(
                    block,
                    index,
                    outer_bindings,
                    &temp_touches,
                    &label_jumps,
                    &captured_locals,
                ) {
                    action = Some(handoff_action);
                    break;
                }

                index += 1;
            }
            action
        };

        let Some(action) = action else {
            break;
        };
        changed = true;
        if matches!(action, HandoffAction::AdvanceIndex) {
            index += 1;
        }
        stmt_temp_refs = collect_temp_refs_by_stmt(&block.stmts);
    }

    changed
}
