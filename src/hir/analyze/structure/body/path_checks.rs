//! 这个文件承载 structured body lowering 里的路径边界判定。
//!
//! `body/mod.rs` 负责按 region 顺序实际降 HIR，`branches.rs` 负责选择某种 branch
//! 降低策略；本文件只回答“某条 arm 的所有路径是否都会到达指定边界、终止，或离开
//! 当前 active loop”。这些查询消费 CFG、StructureFacts 里的 loop/branch region 事实
//! 以及当前 lowerer 的 active loop 栈，不生成 HIR 语句，也不重新发明结构候选。
//!
//! 输入形状：`then_entry` 所有非终止路径都到达 `shared`，另一条路径 return。
//! 输出形状：返回 `true`，调用方可以把 `shared` 留给外层 continuation，而不是复制 tail。

use std::collections::{BTreeMap, BTreeSet};

use super::*;

impl StructuredBodyLowerer<'_, '_> {
    pub(super) fn can_reach_avoiding_block(
        &self,
        from: BlockRef,
        to: BlockRef,
        avoided: BlockRef,
    ) -> bool {
        if from == avoided || to == avoided {
            return false;
        }
        let mut allowed_blocks = self.lowering.cfg.reachable_blocks.clone();
        allowed_blocks.remove(&avoided);
        self.lowering
            .cfg
            .can_reach_within(from, to, &allowed_blocks)
    }

    pub(super) fn branch_arm_reaches_shared_continuation_or_terminate(
        &self,
        entry: BlockRef,
        continuation: BlockRef,
        boundary: BlockRef,
    ) -> bool {
        self.branch_arm_paths_all_match(entry, |block| {
            if block == continuation {
                return Some(true);
            }
            if block == boundary || !self.lowering.cfg.reachable_blocks.contains(&block) {
                return Some(false);
            }
            (block == self.lowering.cfg.exit_block || self.block_is_terminal_exit(block))
                .then_some(true)
        })
    }

    pub(super) fn branch_arm_reaches_loop_continuation_or_escape(
        &self,
        entry: BlockRef,
        continuation: BlockRef,
        stop: BlockRef,
    ) -> bool {
        self.branch_arm_paths_all_match(entry, |block| {
            if block == continuation {
                return Some(true);
            }
            if block == stop || block == self.lowering.cfg.exit_block {
                return Some(false);
            }
            if self.block_is_active_loop_escape(block) {
                return Some(true);
            }
            (!self.lowering.cfg.reachable_blocks.contains(&block)).then_some(false)
        })
    }

    pub(super) fn branch_can_truncate_to_stop_or_loop_escape(
        &self,
        then_entry: BlockRef,
        else_entry: Option<BlockRef>,
        stop: BlockRef,
        boundary: BlockRef,
    ) -> bool {
        self.branch_arm_reaches_stop_or_loop_escape(then_entry, stop, boundary)
            && else_entry.is_none_or(|else_entry| {
                self.branch_arm_reaches_stop_or_loop_escape(else_entry, stop, boundary)
            })
    }

    pub(super) fn branch_arm_reaches_stop_or_loop_escape(
        &self,
        entry: BlockRef,
        stop: BlockRef,
        boundary: BlockRef,
    ) -> bool {
        self.branch_arm_paths_all_match(entry, |block| {
            if block == stop {
                return Some(true);
            }
            if block == boundary {
                return Some(self.block_is_active_loop_escape(block));
            }
            if block == self.lowering.cfg.exit_block || self.block_is_terminal_exit(block) {
                return Some(true);
            }
            (!self.lowering.cfg.reachable_blocks.contains(&block)).then_some(false)
        })
    }

    fn branch_arm_paths_all_match(
        &self,
        entry: BlockRef,
        classify_boundary: impl Fn(BlockRef) -> Option<bool>,
    ) -> bool {
        fn visit(
            lowerer: &StructuredBodyLowerer<'_, '_>,
            block: BlockRef,
            classify_boundary: &impl Fn(BlockRef) -> Option<bool>,
            visiting: &mut BTreeSet<BlockRef>,
            memo: &mut BTreeMap<BlockRef, bool>,
        ) -> bool {
            if let Some(result) = classify_boundary(block) {
                return result;
            }
            if let Some(result) = memo.get(&block).copied() {
                return result;
            }
            if let Some(loop_candidate) = lowerer.loop_by_header.get(&block).copied()
                && loop_candidate.reducible
            {
                let result = loop_candidate
                    .exits
                    .iter()
                    .all(|exit| visit(lowerer, *exit, classify_boundary, visiting, memo));
                memo.insert(block, result);
                return result;
            }
            if !visiting.insert(block) {
                // 已分类的 loop escape/continuation 会在 classify_boundary 里返回。
                // 走到这里的回环还没有结构化 owner，不能证明所有路径都到达目标边界。
                return false;
            }

            let result = lowerer.lowering.cfg.succs[block.index()]
                .iter()
                .all(|edge_ref| {
                    let successor = lowerer.lowering.cfg.edges[edge_ref.index()].to;
                    visit(lowerer, successor, classify_boundary, visiting, memo)
                });
            visiting.remove(&block);
            memo.insert(block, result);
            result
        }

        visit(
            self,
            entry,
            &classify_boundary,
            &mut BTreeSet::new(),
            &mut BTreeMap::new(),
        )
    }

    pub(super) fn block_is_active_loop_escape(&self, block: BlockRef) -> bool {
        self.active_loops.last().is_some_and(|loop_context| {
            loop_context.continue_target == Some(block)
                || loop_context.post_loop == block
                || loop_context.downstream_post_loop == Some(block)
                || loop_context.break_exits.contains_key(&block)
        })
    }

    pub(super) fn block_exits_outer_active_loop(&self, block: BlockRef) -> bool {
        self.active_loops.iter().rev().skip(1).any(|loop_context| {
            loop_context.post_loop == block
                || loop_context.downstream_post_loop == Some(block)
                || loop_context.break_exits.contains_key(&block)
        })
    }

    pub(super) fn loop_continue_target_is_empty(&self, block: BlockRef) -> bool {
        if self.branch_by_header.contains_key(&block) {
            return false;
        }
        let terminator = self.block_terminator(block).map(|(instr_ref, _)| instr_ref);
        let range = self.lowering.cfg.blocks[block.index()].instrs;
        (range.start.index()..range.end()).all(|instr_idx| {
            let instr_ref = InstrRef(instr_idx);
            Some(instr_ref) == terminator
                || self
                    .lowering
                    .proto
                    .instrs
                    .get(instr_idx)
                    .is_some_and(is_control_terminator)
        })
    }

    pub(super) fn terminal_exit_block_is_clone_safe(&self, block: BlockRef) -> bool {
        if !self.block_is_terminal_exit(block) {
            return false;
        }
        let terminator = self.block_terminator(block).map(|(instr_ref, _)| instr_ref);
        let range = self.lowering.cfg.blocks[block.index()].instrs;
        (range.start.index()..range.end()).all(|instr_idx| {
            let instr_ref = InstrRef(instr_idx);
            // Closure capture 记录的是父级词法槽位身份；复制同一条 raw CLOSURE 会把
            // 一个 child proto 伪造成多个创建点，后续 naming 无法得到单一 provenance。
            Some(instr_ref) == terminator
                || !matches!(
                    self.lowering.proto.instrs.get(instr_idx),
                    Some(LowInstr::Closure(_))
                )
        })
    }

    pub(super) fn branch_can_truncate_to_stop(
        &self,
        block: BlockRef,
        then_entry: BlockRef,
        else_entry: Option<BlockRef>,
        stop: BlockRef,
    ) -> bool {
        let Some(region) = self.branch_regions_by_header.get(&block).copied() else {
            return false;
        };
        if !region.structured_blocks.contains(&stop) {
            return false;
        }

        let mut allowed_blocks = region.structured_blocks.clone();
        allowed_blocks.insert(stop);
        let arm_can_truncate_to_stop =
            |entry| self.branch_arm_can_truncate_to_stop(entry, stop, &allowed_blocks);

        // `if-then` / guard 没有显式 else 臂时，缺席的那一臂本来就代表“当前 region 不再
        // 产生额外语句，直接把控制权交回外层 stop”。这里如果仍然要求 else_entry 存在，
        // 嵌套 guard 会被错误地强推到自己的 merge 上，跨出外层 region，最后在更深的
        // merge block 上重入并把整片结构化打回失败。
        arm_can_truncate_to_stop(then_entry) && else_entry.is_none_or(arm_can_truncate_to_stop)
    }

    fn branch_arm_can_truncate_to_stop(
        &self,
        entry: BlockRef,
        stop: BlockRef,
        allowed_blocks: &BTreeSet<BlockRef>,
    ) -> bool {
        if entry == stop {
            return true;
        }

        if self.branch_arm_crosses_live_continuation(entry, stop) {
            return false;
        }

        self.lowering
            .cfg
            .can_reach_within(entry, stop, allowed_blocks)
            || self.branch_arm_terminates_before_stop(entry, stop)
    }

    fn branch_arm_crosses_live_continuation(&self, entry: BlockRef, stop: BlockRef) -> bool {
        let mut visited = BTreeSet::new();
        let mut stack = vec![entry];

        while let Some(block) = stack.pop() {
            if block == stop
                || block == self.lowering.cfg.exit_block
                || !self.lowering.cfg.reachable_blocks.contains(&block)
                || !visited.insert(block)
            {
                continue;
            }

            // 如果某条内层分支绕过外层 stop 直接进入 stop 之后的普通延续块，
            // 把它截断到外层 stop 会把后续语句吸进当前分支臂，破坏外层 region。
            // 但 Lua 5.1 的 guard/elseif 链常会让“处理完的路径”直接跳到函数尾
            // return；这种终止块没有可继续结构化的 fallthrough，可以安全地留在臂内。
            if self.can_reach(stop, block) && !self.block_is_terminal_exit(block) {
                return true;
            }

            for edge_ref in &self.lowering.cfg.succs[block.index()] {
                stack.push(self.lowering.cfg.edges[edge_ref.index()].to);
            }
        }

        false
    }

    pub(super) fn branch_arm_terminates_before_stop(
        &self,
        entry: BlockRef,
        stop: BlockRef,
    ) -> bool {
        let mut visited = BTreeSet::new();
        let mut stack = vec![entry];
        let mut saw_terminal = false;

        while let Some(block) = stack.pop() {
            if block == stop || block == self.lowering.cfg.exit_block {
                return true;
            }
            if !self.lowering.cfg.reachable_blocks.contains(&block) || !visited.insert(block) {
                continue;
            }
            if self.block_is_terminal_exit(block) {
                saw_terminal = true;
                continue;
            }

            for edge_ref in &self.lowering.cfg.succs[block.index()] {
                let successor = self.lowering.cfg.edges[edge_ref.index()].to;
                if successor != stop {
                    stack.push(successor);
                }
            }
        }

        saw_terminal
    }

    pub(super) fn block_is_terminal_exit(&self, block: BlockRef) -> bool {
        let succs = &self.lowering.cfg.succs[block.index()];
        !succs.is_empty()
            && succs.iter().all(|edge_ref| {
                let edge = self.lowering.cfg.edges[edge_ref.index()];
                edge.to == self.lowering.cfg.exit_block
                    && matches!(
                        edge.kind,
                        crate::structure::EdgeKind::Return | crate::structure::EdgeKind::TailCall
                    )
            })
    }
}
