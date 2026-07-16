//! 这个文件承载 loop break/backedge pad 的局部 lowering。
//!
//! `state.rs` 负责决定 loop state 身份；break pad 则负责把已被 `StructureFacts`
//! 归入 loop 局部出口的 cleanup block 降成 `...; break`。这里只消费已有 branch /
//! short-circuit plan 来处理 pad 内的小型结构，不重新识别任意跨 loop 的 exit 拼图。
//!
//! 输入形状：`if found then cleanup end; jump post_loop`
//! 输出形状：`if found then cleanup end; break`

use super::*;

#[derive(Clone, Copy)]
struct BreakExitPadArmContext<'a> {
    post_loop: BlockRef,
    downstream_post_loop: Option<BlockRef>,
    target_overrides: &'a BTreeMap<TempId, HirLValue>,
    states: &'a [LoopStateSlot],
    region: &'a BranchRegionFact,
}

impl StructuredBodyLowerer<'_, '_> {
    pub(super) fn repeat_backedge_pad(
        &self,
        header: BlockRef,
        loop_backedge_target: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        if loop_backedge_target == header {
            return Some(None);
        }
        if self
            .lowering
            .cfg
            .unique_reachable_successor(loop_backedge_target)
            != Some(header)
        {
            return None;
        }
        // 有些 repeat-like loop 会把“继续下一轮”拆成一个线性 jump pad，
        // pad 里最多只剩已经被 scope 结构吸收的 close。这里显式接受这种形状，
        // 避免因为一块纯回边垫片没有被 visit 就把整片 loop 打回 fallback。
        if !self
            .lower_block_prefix(loop_backedge_target, false, target_overrides)?
            .is_empty()
        {
            return None;
        }

        Some(Some(loop_backedge_target))
    }

    pub(super) fn lower_break_exit_pad(
        &self,
        block: BlockRef,
        post_loop: BlockRef,
        downstream_post_loop: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
        states: &[LoopStateSlot],
    ) -> Option<BreakExitBlock> {
        // break 垫片允许是线性 cleanup，也允许是一个小型 if cleanup，再统一跳到
        // 循环之后的 continuation。继续限制在单入口、单 merge 的 pad 内，是为了只消费
        // StructureFacts 已能证明属于 break 出口的局部结构，避免退化成任意 exit 拼图。
        //
        // break pad 里的赋值（如 `found = true; idx = i`）写入的 def temp 与 loop 回边
        // 上的 phi temp 不同，因此仅靠 combined_target_overrides 无法将它们重定向到
        // 循环 state 变量。这里额外扫描 pad 的 def，把匹配 state 寄存器的 def temp
        // 也加入 override map，使 apply_loop_rewrites 能正确替换。
        if matches!(
            self.block_terminator(block),
            Some((_instr_ref, LowInstr::Branch(_)))
        ) {
            let combined = self.break_pad_target_overrides(block, target_overrides, states);
            return self.lower_branch_break_exit_pad(
                block,
                post_loop,
                downstream_post_loop,
                &combined,
                states,
            );
        }

        let mut current = block;
        let mut blocks = BTreeSet::new();
        let mut stmts = Vec::new();
        loop {
            if !blocks.insert(current) {
                return None;
            }
            let combined = self.break_pad_target_overrides(current, target_overrides, states);
            stmts.extend(self.lower_block_prefix(current, false, &combined)?);
            let target = match self.block_terminator(current) {
                Some((_instr_ref, LowInstr::Jump(jump))) => {
                    self.lowering.cfg.instr_to_block[jump.target.index()]
                }
                // Lua 5.4 的 close/capture cleanup pad 可以直接 fallthrough 到后续块。
                Some((_instr_ref, instr)) if !instr.is_control_terminator() => {
                    self.lowering.cfg.unique_reachable_successor(current)?
                }
                None => self.lowering.cfg.unique_reachable_successor(current)?,
                Some(_) => return None,
            };
            if target == post_loop || Some(target) == downstream_post_loop {
                stmts.push(HirStmt::Break);
                return Some(BreakExitBlock {
                    block: HirBlock { stmts },
                    blocks,
                });
            }
            if self
                .lowering
                .cfg
                .unique_reachable_predecessor_matching(target, |_| true)
                != Some(current)
            {
                return None;
            }
            current = target;
        }
    }

    fn break_pad_target_overrides(
        &self,
        block: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
        states: &[LoopStateSlot],
    ) -> BTreeMap<TempId, HirLValue> {
        let mut combined = target_overrides.clone();
        if states.is_empty() {
            return combined;
        }

        let state_by_reg = state_slots_by_reg(states);
        let range = self.lowering.cfg.blocks[block.index()].instrs;
        for instr_index in range.start.index()..range.end() {
            for def_id in &self.lowering.dataflow.instr_defs[instr_index] {
                let def = &self.lowering.dataflow.defs[def_id.index()];
                if let Some(state) = state_by_reg.get(&def.reg) {
                    let temp = self.lowering.bindings.fixed_temps[def_id.index()];
                    combined.insert(temp, state.target.clone());
                }
            }
        }

        combined
    }

    fn lower_branch_break_exit_pad(
        &self,
        block: BlockRef,
        post_loop: BlockRef,
        downstream_post_loop: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
        states: &[LoopStateSlot],
    ) -> Option<BreakExitBlock> {
        // break pad 不一定只是单层 if；`elseif x then ... if a or b then ... end; break`
        // 这种形状会把短路 header 放在 break 前的 cleanup 里。这里复用 branch lowering
        // 已有的 short-circuit plan，只要求整段 pad 最终汇到 post-loop，不重新在 loop
        // 层手写短路识别。
        let plan = self
            .try_build_short_circuit_plan(block, Some(post_loop))?
            .or_else(|| self.build_plain_branch_plan(block))?;
        if plan.merge.is_none() {
            return self.lower_terminal_or_break_split(
                block,
                plan,
                post_loop,
                downstream_post_loop,
                target_overrides,
                states,
            );
        }
        let merge = plan.merge?;
        let region = self.branch_regions_by_header.get(&block)?;
        let arm_context = BreakExitPadArmContext {
            post_loop,
            downstream_post_loop,
            target_overrides,
            states,
            region,
        };
        let tail = if merge == post_loop || Some(merge) == downstream_post_loop {
            BreakExitBlock {
                block: HirBlock {
                    stmts: vec![HirStmt::Break],
                },
                blocks: BTreeSet::new(),
            }
        } else {
            // break pad 可能先做一个局部 if-cleanup，再落到一段线性 tail
            // （例如 `if registered then unregister end; table.remove(...); break`）。
            // 这段 tail 仍然只允许通过已有的 break-pad 校验通往 post-loop，
            // 不能把任意 branch merge 都吞进循环出口。
            self.lower_break_exit_pad(
                merge,
                post_loop,
                downstream_post_loop,
                target_overrides,
                states,
            )?
        };

        let mut blocks = plan
            .consumed_headers
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        let mut stmts = self.lower_block_prefix(block, true, target_overrides)?;
        let mut cond = plan.cond;
        if let Some(entry_expr_overrides) = self.block_entry_expr_overrides(block) {
            rewrite_expr_temps(&mut cond, entry_expr_overrides);
        }

        let then_pad = self.lower_break_exit_pad_arm(plan.then_entry, merge, &arm_context)?;
        blocks.extend(then_pad.blocks.iter().copied());
        let else_pad = match plan.else_entry {
            Some(else_entry) => {
                let pad = self.lower_break_exit_pad_arm(else_entry, merge, &arm_context)?;
                blocks.extend(pad.blocks.iter().copied());
                Some(pad.block)
            }
            None => None,
        };

        stmts.push(branch_stmt(cond, then_pad.block, else_pad));
        stmts.extend(tail.block.stmts);
        blocks.extend(tail.blocks);
        Some(BreakExitBlock {
            block: HirBlock { stmts },
            blocks,
        })
    }

    fn lower_terminal_or_break_split(
        &self,
        block: BlockRef,
        plan: StructuredBranchPlan,
        post_loop: BlockRef,
        downstream_post_loop: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
        states: &[LoopStateSlot],
    ) -> Option<BreakExitBlock> {
        let else_entry = plan.else_entry?;
        let (then_block, then_blocks) = self.lower_direct_terminal_or_break_arm(
            plan.then_entry,
            post_loop,
            downstream_post_loop,
            target_overrides,
            states,
        )?;
        let (else_block, else_blocks) = self.lower_direct_terminal_or_break_arm(
            else_entry,
            post_loop,
            downstream_post_loop,
            target_overrides,
            states,
        )?;

        let mut cond = plan.cond;
        if let Some(entry_expr_overrides) = self.block_entry_expr_overrides(block) {
            rewrite_expr_temps(&mut cond, entry_expr_overrides);
        }
        let mut stmts = self.lower_block_prefix(block, true, target_overrides)?;
        stmts.push(branch_stmt(cond, then_block, Some(else_block)));
        let mut blocks = plan.consumed_headers.into_iter().collect::<BTreeSet<_>>();
        blocks.extend(then_blocks);
        blocks.extend(else_blocks);
        Some(BreakExitBlock {
            block: HirBlock { stmts },
            blocks,
        })
    }

    fn lower_direct_terminal_or_break_arm(
        &self,
        block: BlockRef,
        post_loop: BlockRef,
        downstream_post_loop: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
        states: &[LoopStateSlot],
    ) -> Option<(HirBlock, BTreeSet<BlockRef>)> {
        if block == post_loop || Some(block) == downstream_post_loop {
            return Some((
                HirBlock {
                    stmts: vec![HirStmt::Break],
                },
                BTreeSet::new(),
            ));
        }
        if !block_is_terminal_exit(self.lowering, block) {
            return None;
        }
        let overrides = self.break_pad_target_overrides(block, target_overrides, states);
        Some((
            self.lower_terminal_exit_block_clone(block, &overrides)?,
            BTreeSet::from([block]),
        ))
    }

    fn lower_break_exit_pad_arm(
        &self,
        block: BlockRef,
        merge: BlockRef,
        context: &BreakExitPadArmContext<'_>,
    ) -> Option<BreakExitBlock> {
        if block == merge
            || block == context.post_loop
            || Some(block) == context.downstream_post_loop
        {
            return Some(BreakExitBlock {
                block: HirBlock::default(),
                blocks: BTreeSet::new(),
            });
        }
        if !self.branch_region_contains(context.region, block) {
            return None;
        }

        if matches!(self.block_terminator(block), Some((_, LowInstr::Branch(_)))) {
            let mut nested = self.lower_branch_break_exit_pad(
                block,
                merge,
                None,
                context.target_overrides,
                context.states,
            )?;
            if !matches!(nested.block.stmts.pop(), Some(HirStmt::Break)) {
                return None;
            }
            return Some(nested);
        }

        let target_overrides =
            self.break_pad_target_overrides(block, context.target_overrides, context.states);
        let mut stmts = self.lower_block_prefix(block, false, &target_overrides)?;
        let target = match self.block_terminator(block) {
            Some((_instr_ref, LowInstr::Jump(jump))) => {
                self.lowering.cfg.instr_to_block[jump.target.index()]
            }
            Some((_instr_ref, instr)) if !instr.is_control_terminator() => {
                self.lowering.cfg.unique_reachable_successor(block)?
            }
            None => self.lowering.cfg.unique_reachable_successor(block)?,
            Some(_) => return None,
        };
        let mut blocks = BTreeSet::from([block]);
        if target != merge
            && target != context.post_loop
            && Some(target) != context.downstream_post_loop
        {
            let nested_context = BreakExitPadArmContext {
                target_overrides: &target_overrides,
                ..*context
            };
            let tail = self.lower_break_exit_pad_arm(target, merge, &nested_context)?;
            stmts.extend(tail.block.stmts);
            blocks.extend(tail.blocks);
        }

        Some(BreakExitBlock {
            block: HirBlock { stmts },
            blocks,
        })
    }
}
