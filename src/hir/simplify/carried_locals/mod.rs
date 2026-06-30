//! carried-local handoff 折叠 pass 的编排入口。
//!
//! 这个 pass 把 fallback label/goto 区域里“交棒出去的 carried 状态”认回原绑定，
//! 也会收敛结构化分支/循环里相邻的 `seed local + empty carried local`。它只负责
//! 后序遍历、外层 temp 活跃性保护，以及在当前 block 内按既定顺序调用各类 owner：
//! `adjacent.rs` 处理相邻 local seed，`boundary.rs` 处理 label/goto 边界快照等价类，
//! `handoffs.rs` 处理具体 seed/update handoff，`binding.rs` 和 `prune.rs` 提供共享工具。
//!
//! 它不会发明新 local，也不会在原 local 仍然活跃时强行合并两段状态；所有折叠都必须
//! 先证明 seed 在后续不再可观察、temp 不被外层作用域消费，并且写回形状可证明。
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

use crate::hir::common::{HirBlock, HirProto, TempId};

use super::temp_touch::{TempRefScopeTracker, TempTouchIndex, collect_temp_refs_by_stmt};
use super::walk::for_each_nested_block_mut;

use self::adjacent::try_collapse_adjacent_local_seed_handoff;
use self::boundary::collapse_boundary_alias_classes;
use self::handoffs::{HandoffAction, try_collapse_handoff_at};

pub(super) fn collapse_carried_local_handoffs_in_proto(proto: &mut HirProto) -> bool {
    collapse_handoffs_recursive(&mut proto.body, &BTreeSet::new())
}

/// 自定义后序遍历：先递归处理子块（同时把外层 temp 引用集传下去），再在当前块做 handoff 折叠。
/// `outer_temps` 包含当前块的所有祖先作用域中引用过的 temp，如果一个 temp 在 `outer_temps` 中，
/// 说明它在当前块外部仍被消费，不能在当前块内被折叠消除。
fn collapse_handoffs_recursive(block: &mut HirBlock, outer_temps: &BTreeSet<TempId>) -> bool {
    let mut changed = false;

    // 为每个嵌套语句预计算“进入该子块时需要保护的 temp 集”。
    // 对于 index 处的语句，保护集 = 继承的 outer_temps ∪ 本块中「其他语句」引用的 temps。
    // 注意不能用 `all - self` 来近似：如果某个 temp 同时出现在当前语句和其他语句中，
    // 差集会把它减掉，导致跨作用域的引用失去保护。这里用前缀+后缀并集来精确计算。
    let stmt_temp_refs = collect_temp_refs_by_stmt(&block.stmts);
    let mut temp_refs = TempRefScopeTracker::new(&stmt_temp_refs);
    for index in 0..temp_refs.len() {
        temp_refs.enter_stmt(index);
        let child_outer = temp_refs.outer_with_prefix_and_suffix(outer_temps);

        for_each_nested_block_mut(&mut block.stmts[index], &mut |nested_block| {
            changed |= collapse_handoffs_recursive(nested_block, &child_outer);
        });

        temp_refs.leave_stmt(index);
    }

    // 后序：子块都处理完之后，再处理当前块的 handoff。
    changed |= collapse_block_handoffs(block, outer_temps);
    changed
}

fn collapse_block_handoffs(block: &mut HirBlock, outer_temps: &BTreeSet<TempId>) -> bool {
    let mut changed = collapse_boundary_alias_classes(block);
    let mut index = 0;
    let mut stmt_temp_refs = collect_temp_refs_by_stmt(&block.stmts);

    loop {
        let action = {
            let temp_touches = TempTouchIndex::new(&stmt_temp_refs);
            let mut action = None;
            while index < block.stmts.len() {
                if try_collapse_adjacent_local_seed_handoff(block, index) {
                    action = Some(HandoffAction::RetrySameIndex);
                    break;
                }
                if let Some(handoff_action) =
                    try_collapse_handoff_at(block, index, outer_temps, &temp_touches)
                {
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
