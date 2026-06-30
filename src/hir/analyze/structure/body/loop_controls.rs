//! 这个文件承载 loop 内 branch-control 的专用恢复。
//!
//! 普通 `if` lowering 只关心分支 region 如何收束；这里处理的则是当前 active loop
//! 语境下的 break/continue、loop terminal else，以及跨层 escape 判定。把它们从
//! `branches.rs` 拆出来，是为了让普通 branch 结构和 loop 控制流策略分开演进。

use super::*;

impl StructuredBodyLowerer<'_, '_> {
    pub(super) fn try_lower_loop_break_branch(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        // 多出口 loop 里最常见、也最值得先吃掉的形状是“主体继续跑，另一臂经 cleanup pad
        // 直接离开循环”。这里不把这类 pad 留给 fallback，而是在 HIR 里直接恢复成 break，
        // 这样后面的 AST/readability 就不用再对着 `close + jump` 反推源码意图。
        let loop_context = self.active_loops.last()?.clone();
        let candidate = *self.branch_by_header.get(&block)?;
        let break_exit = candidate.merge.filter(|merge| {
            loop_context.break_exits.contains_key(merge)
                || *merge == loop_context.post_loop
                || Some(*merge) == loop_context.downstream_post_loop
        })?;
        // 当前 region 已经给出更近的结构边界时，break 快捷路径不能跨过它去消费
        // loop 的 post block；否则共享 tail 会被提前塞进某个分支臂，外层结构就无法
        // 再把 tail 作为单一 continuation 恢复出来。
        if let Some(stop) = stop
            && stop != break_exit
            && loop_context.continue_target != Some(stop)
            && self
                .branch_regions_by_header
                .get(&block)
                .is_some_and(|region| region.structured_blocks.contains(&stop))
        {
            return None;
        }
        if self.block_exits_outer_active_loop(break_exit) {
            return None;
        }
        let pad_stmts = match candidate.else_entry {
            Some(else_entry)
                if else_entry != break_exit
                    && Some(else_entry) != loop_context.downstream_post_loop =>
            {
                let is_direct_jump = self.block_terminator(else_entry).is_some_and(|(_, instr)| {
                    if let LowInstr::Jump(jump) = instr {
                        let target = self.lowering.cfg.instr_to_block[jump.target.index()];
                        target == break_exit || Some(target) == loop_context.downstream_post_loop
                    } else {
                        false
                    }
                });
                if !is_direct_jump {
                    return None;
                }
                let pad_stmts = self.lower_block_prefix(else_entry, false, target_overrides)?;
                self.visited.insert(else_entry);
                pad_stmts
            }
            _ => Vec::new(),
        };
        let break_block = if break_exit == loop_context.post_loop
            || Some(break_exit) == loop_context.downstream_post_loop
        {
            // 当 break 路径上存在中间块（如 `found = {i,j}; break`），需要提取
            // 中间块的指令前缀到 break 之前，避免丢失赋值等副作用。若 else 臂
            // 不是这种单块线性 break pad，上面的校验会退让给普通分支 lowering。
            let mut stmts = pad_stmts;
            stmts.push(HirStmt::Break);
            HirBlock { stmts }
        } else {
            loop_context.break_exits[&break_exit].block.clone()
        };
        // break 臂之外的那一臂，很多时候只是继续执行当前 loop body，最后再回到
        // continue target。如果这里一口气把它降到 break pad 的出口，repeat/for 的
        // loop tail 就会被一起吞进去，随后整片 region 只能 fallback。这里优先把
        // 非 break 臂截到当前 loop 的 continue target；只有确实没有这条稳定回路时，
        // 才继续沿用 break exit 作为边界。
        let body_stop = loop_context
            .continue_target
            .filter(|target| {
                *target != break_exit
                    && (candidate.then_entry == *target
                        || self.can_reach(candidate.then_entry, *target))
            })
            .or(Some(break_exit));
        let then_block = self.lower_region(candidate.then_entry, body_stop, target_overrides)?;
        let mut cond = self.lower_candidate_cond(block, candidate)?;
        rewrite_expr_temps(&mut cond, &temp_expr_overrides(target_overrides));

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        self.visited.insert(block);
        if break_exit != loop_context.post_loop
            && Some(break_exit) != loop_context.downstream_post_loop
        {
            self.visited.insert(break_exit);
        }

        if body_stop == Some(break_exit)
            && break_block.stmts.last() == Some(&HirStmt::Break)
            && then_block.stmts == break_block.stmts[..break_block.stmts.len() - 1]
        {
            stmts.extend(then_block.stmts);
            stmts.push(branch_stmt(
                cond.negate(),
                HirBlock {
                    stmts: vec![HirStmt::Break],
                },
                None,
            ));
            return Some(None);
        }

        if then_block.stmts.is_empty() {
            stmts.push(branch_stmt(cond.negate(), break_block, None));
        } else {
            stmts.push(branch_stmt(cond, then_block, Some(break_block)));
        }

        match body_stop {
            Some(next) if next == break_exit => Some(None),
            Some(next) if next == self.lowering.cfg.exit_block => Some(None),
            Some(next) => Some(Some(next)),
            None => Some(None),
        }
    }

    pub(super) fn try_lower_loop_terminal_else_branch(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let loop_context = self.active_loops.last()?.clone();
        let stop = stop?;
        if loop_context.continue_target != Some(stop) {
            return None;
        }
        let candidate = *self.branch_by_header.get(&block)?;
        let merge = candidate.merge?;
        if candidate.else_entry.is_some()
            || merge == stop
            || self.branch_value_merges_by_header.contains_key(&block)
            || !self.can_reach_avoiding_block(candidate.then_entry, stop, merge)
            || !self.branch_arm_terminates_before_stop(merge, stop)
        {
            return None;
        }

        let then_target_overrides =
            self.branch_entry_target_overrides(block, Some(candidate.then_entry), target_overrides);
        let then_block =
            self.lower_region(candidate.then_entry, Some(stop), &then_target_overrides)?;
        let else_block = self.lower_region(merge, Some(stop), target_overrides)?;
        let mut cond = self.lower_candidate_cond(block, candidate)?;
        rewrite_expr_temps(&mut cond, &temp_expr_overrides(target_overrides));

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        self.visited.insert(block);
        stmts.push(branch_stmt(cond, then_block, Some(else_block)));
        Some(Some(stop))
    }

    pub(super) fn cross_structure_escape_target(&self, block: BlockRef) -> Option<BlockRef> {
        let loop_context = self.active_loops.last()?;
        let candidate = self.branch_by_header.get(&block).copied()?;
        let merge = candidate.merge?;
        let continue_target = loop_context.continue_target?;
        if self.block_exits_outer_active_loop(merge)
            && (candidate.then_entry == continue_target
                || self.can_reach(candidate.then_entry, continue_target))
        {
            return Some(merge);
        }

        // 这类形状常见于 `if cond then goto after_outer_loop end`：
        // 分支的一臂仍然沿当前 loop 继续跑，另一臂却直接跳到当前 loop 之外更远的 merge。
        // 如果这里继续把它硬恢复成普通 `if-then`，缺席的那一臂会被误当成
        // “自然回到当前 region 的 stop”，最终把跨层 `goto` 偷偷降成错误的 loop fallthrough。
        //
        // 对这种跨层退出，当前 structured HIR 没有等价的 `break/continue` 语义可承载；
        // 与其在局部生成半真半假的结构，不如让整片 proto 退回显式 label/goto 形态，
        // 由更保守但语义直观的 fallback 接手。
        if candidate.else_entry.is_some()
            || merge == loop_context.post_loop
            || Some(merge) == loop_context.downstream_post_loop
            || loop_context.break_exits.contains_key(&merge)
            || self.block_is_terminal_exit(merge)
        {
            return None;
        }

        let loop_candidate = self.loop_by_header.get(&loop_context.header).copied()?;
        if loop_candidate.blocks.contains(&merge) {
            return None;
        }

        (candidate.then_entry == continue_target
            || self.can_reach(candidate.then_entry, continue_target))
        .then_some(merge)
    }

    pub(super) fn lower_cross_structure_escape_branch(
        &mut self,
        block: BlockRef,
        escape_target: BlockRef,
        _stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let loop_context = self.active_loops.last()?.clone();
        let continue_target = loop_context.continue_target?;
        let candidate = *self.branch_by_header.get(&block)?;

        let mut keep_cond = self.lower_candidate_cond(block, candidate)?;
        rewrite_expr_temps(&mut keep_cond, &temp_expr_overrides(target_overrides));

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        self.visited.insert(block);

        let escape_block = self.lower_escape_edge(block, escape_target, target_overrides)?;
        let continue_block = if candidate.then_entry == continue_target {
            HirBlock::default()
        } else {
            self.lower_region(
                candidate.then_entry,
                Some(continue_target),
                target_overrides,
            )?
        };
        let continue_else = (!continue_block.stmts.is_empty()).then_some(continue_block);
        stmts.push(branch_stmt(keep_cond.negate(), escape_block, continue_else));

        Some(Some(continue_target))
    }

    pub(super) fn try_lower_loop_continue_branch(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        // continue-like requirement 既可能来自未来 dialect 的显式 continue，也可能只是
        // 当前循环内部一条“提前回到 continue target”的控制边。这里只在它确实是当前
        // active loop 的本地语义时才吸收；否则宁可保持 fallback，也不把跨结构跳转误判成 continue。
        let loop_context = self.active_loops.last()?.clone();
        let continue_target = loop_context.continue_target?;
        let continue_target_is_empty = self.loop_continue_target_is_empty(continue_target);
        let can_fallthrough_to_non_empty_continue = self
            .loop_by_header
            .get(&loop_context.header)
            .is_some_and(|candidate| {
                matches!(
                    candidate.kind_hint,
                    LoopKindHint::NumericForLike
                        | LoopKindHint::GenericForLike
                        | LoopKindHint::Unknown
                )
            });
        if !continue_target_is_empty && !can_fallthrough_to_non_empty_continue {
            return None;
        }
        if let Some(short_plan) = self.try_build_short_circuit_plan(block, stop).flatten() {
            let short_plan_has_continue_edge = short_plan.then_entry == continue_target
                || short_plan.else_entry == Some(continue_target);
            if !short_plan_has_continue_edge {
                return None;
            }
        }
        let branch_points_to_continue =
            self.branch_by_header.get(&block).is_some_and(|candidate| {
                candidate.then_entry == continue_target
                    || candidate.else_entry == Some(continue_target)
                    || candidate.merge == Some(continue_target)
            });
        if !loop_context.continue_sources.contains(&block) && !branch_points_to_continue {
            return None;
        }

        let candidate = *self.branch_by_header.get(&block)?;
        if candidate.then_entry != continue_target
            && candidate.else_entry != Some(continue_target)
            && candidate.merge != Some(continue_target)
        {
            return None;
        }
        if candidate.merge == Some(continue_target)
            && candidate.else_entry.is_some()
            && candidate.then_entry != continue_target
            && candidate.else_entry != Some(continue_target)
        {
            // 显式 if/else 的两条臂都先执行自己的 body，再共同落到当前 loop latch 时，
            // 这不是源码层的 early-continue，而是普通分支的自然收束。交给普通 branch
            // lowering 才能把剩余 loop body 保留在 else 臂里；否则 Lua 5.1 目标会被
            // 平白制造出 `continue`/`goto`。
            return None;
        }
        if self
            .non_continue_entry_for_continue_candidate(candidate, continue_target)
            .is_some_and(|entry| self.entry_is_direct_loop_break(entry, &loop_context))
        {
            return None;
        }
        let mut continue_cond = self.lower_branch_cond_for_target(block, continue_target)?;
        rewrite_expr_temps(&mut continue_cond, &temp_expr_overrides(target_overrides));
        let prefer_natural_fallthrough = self.prefer_natural_fallthrough_over_continue(
            block,
            candidate,
            continue_target,
            &loop_context,
        );
        if !continue_target_is_empty
            && !prefer_natural_fallthrough
            && candidate.merge != Some(continue_target)
        {
            return None;
        }
        let then_target_overrides =
            self.branch_entry_target_overrides(block, Some(candidate.then_entry), target_overrides);

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        self.visited.insert(block);

        if let Some(break_exit) = candidate
            .merge
            .filter(|merge| loop_context.break_exits.contains_key(merge))
        {
            self.visited
                .extend(loop_context.break_exits[&break_exit].blocks.iter().copied());
            stmts.push(branch_stmt(
                continue_cond.negate(),
                loop_context.break_exits[&break_exit].block.clone(),
                None,
            ));
            return Some(None);
        }

        if let Some(else_entry) = candidate.else_entry {
            let non_continue_entry = if candidate.then_entry == continue_target {
                else_entry
            } else {
                candidate.then_entry
            };
            if let Some(break_block) = loop_context.break_exits.get(&non_continue_entry) {
                self.visited.extend(break_block.blocks.iter().copied());
                // 当前 branch 本身如果没有“主动提前跳到 continue target”的证据，
                // 那它更像 loop tail 上的“否则 break”判定：继续这一臂只是自然回到
                // 下一轮，不应该硬提升成显式 `continue`。否则像 Lua 5.1 这种没有
                // `continue` / `goto` 的 target dialect 会被我们平白制造出无法落地的语义。
                if prefer_natural_fallthrough {
                    stmts.push(branch_stmt(
                        continue_cond.negate(),
                        break_block.block.clone(),
                        None,
                    ));
                    return Some(None);
                }
                let continue_block = self.explicit_continue_block()?;
                let stmt = if candidate.then_entry == continue_target {
                    branch_stmt(
                        continue_cond,
                        continue_block,
                        Some(break_block.block.clone()),
                    )
                } else {
                    branch_stmt(
                        continue_cond.negate(),
                        break_block.block.clone(),
                        Some(continue_block),
                    )
                };
                stmts.push(stmt);
                return Some(None);
            }

            if prefer_natural_fallthrough {
                let non_continue_target_overrides = self.branch_entry_target_overrides(
                    block,
                    Some(non_continue_entry),
                    target_overrides,
                );
                let non_continue_block = self.lower_region(
                    non_continue_entry,
                    Some(continue_target),
                    &non_continue_target_overrides,
                )?;
                stmts.push(branch_stmt(
                    continue_cond.negate(),
                    non_continue_block,
                    None,
                ));
                return if !continue_target_is_empty && continue_target == loop_context.header {
                    Some(None)
                } else {
                    Some(Some(continue_target))
                };
            }

            let continue_block = self.explicit_continue_block()?;
            let branch_stop = self.branch_stop_for_region(
                block,
                candidate.then_entry,
                candidate.else_entry,
                candidate.merge,
                stop,
            );
            let non_continue_target_overrides = self.branch_entry_target_overrides(
                block,
                Some(non_continue_entry),
                target_overrides,
            );
            let non_continue_block = self.lower_region(
                non_continue_entry,
                branch_stop,
                &non_continue_target_overrides,
            )?;
            let stmt = if candidate.then_entry == continue_target {
                branch_stmt(continue_cond, continue_block, Some(non_continue_block))
            } else {
                branch_stmt(
                    continue_cond.negate(),
                    non_continue_block,
                    Some(continue_block),
                )
            };
            stmts.push(stmt);
            return match branch_stop {
                Some(next) if next == self.lowering.cfg.exit_block => Some(None),
                Some(next) => Some(Some(next)),
                None => Some(None),
            };
        }

        if candidate.then_entry == continue_target {
            // `if cond then continue end` 这类分支在 CFG 里会表现成“显式 continue 臂 +
            // 隐式 merge 臂”。这里把 merge 臂显式降成 else block，避免 loop body 因为
            // “只有 then、没有 else” 被迫整片 fallback。
            let non_continue_entry = candidate.merge?;
            if self.prefer_natural_fallthrough_over_continue(
                block,
                candidate,
                continue_target,
                &loop_context,
            ) {
                let branch_stop = if continue_target_is_empty {
                    stop
                } else {
                    Some(continue_target)
                };
                let non_continue_block =
                    self.lower_region(non_continue_entry, branch_stop, target_overrides)?;
                stmts.push(branch_stmt(
                    continue_cond.negate(),
                    non_continue_block,
                    None,
                ));
                return Some(None);
            }
            let non_continue_block =
                self.lower_region(non_continue_entry, stop, target_overrides)?;
            let continue_block = self.explicit_continue_block()?;
            stmts.push(branch_stmt(
                continue_cond,
                continue_block,
                Some(non_continue_block),
            ));
            return Some(None);
        }

        if candidate.merge == Some(continue_target) {
            // `if cond then body end` 这类 loop-tail guard 在 CFG 里会表现成
            // “显式一臂 + 隐式 merge”，而 merge 正好就是当前 loop 的 continue target。
            // 这种形状本质上是“条件满足时执行 body，否则自然落回 loop latch”，
            // 并不需要显式 `continue`。如果这里仍然强行提升成 `if ... then continue else ... end`，
            // Lua 5.1 这类没有 `continue` / `goto` 的 dialect 就会被我们凭空制造出
            // 无法落地的语义。
            // 这里虽然 merge 臂本身只是自然落回 continue target，但 header 上若已经有
            // branch-value merge，就仍然需要把“执行 body 的那一臂”接回共享状态槽位。
            // 否则 arm 内新算出来的 carried 值只会停留在 branch-local temp 上，等不到
            // continue target 就已经丢掉了写回。
            let non_continue_block = self.lower_region(
                candidate.then_entry,
                Some(continue_target),
                &then_target_overrides,
            )?;
            stmts.push(branch_stmt(
                continue_cond.negate(),
                non_continue_block,
                None,
            ));
            return Some(Some(continue_target));
        }

        let merge = candidate.merge.or(stop)?;
        let continue_block = self.explicit_continue_block()?;
        stmts.push(branch_stmt(continue_cond, continue_block, None));
        if merge == self.lowering.cfg.exit_block
            || (!continue_target_is_empty && continue_target == loop_context.header)
        {
            Some(None)
        } else {
            Some(Some(merge))
        }
    }

    fn prefer_natural_fallthrough_over_continue(
        &self,
        block: BlockRef,
        candidate: &BranchCandidate,
        continue_target: BlockRef,
        loop_context: &ActiveLoopContext,
    ) -> bool {
        if candidate.merge == Some(continue_target) {
            return false;
        }
        let Some(non_continue_entry) =
            self.non_continue_entry_for_continue_candidate(candidate, continue_target)
        else {
            return false;
        };
        // 当 structure 层的 goto 分析没有把该 block 标记为 continue source 时，
        // 说明这条指向 continue_target 的边完全可以被结构化 branch 自然吸收
        // （比如 `if cond then body end` 的隐式落回到循环头），不需要提升为显式
        // continue。只有 goto 分析确认了 unstructured continue-like 的 block 才
        // 需要后续的 terminal-exit / break-funnel 判定。
        if !loop_context.continue_sources.contains(&block) {
            return true;
        }
        // 只有当非 continue 臂本身就是 terminal exit，且从 CFG 上根本到不了当前
        // continue target 时，才能确定它是“提前结束本轮/本函数”的 guard 分支。
        // 像 repeat 里的 break funnel 虽然最终也可能不回到 continue target，但它本身
        // 仍然是一个需要继续展开的控制块，不能在这里过早压平成 guard-return。
        if matches!(
            self.block_terminator(non_continue_entry),
            Some((_instr_ref, LowInstr::Return(_) | LowInstr::TailCall(_)))
        ) && !self.can_reach(non_continue_entry, continue_target)
        {
            return true;
        }

        self.entry_is_break_funnel_to_continue(
            non_continue_entry,
            continue_target,
            loop_context,
            &mut BTreeSet::new(),
        )
    }

    fn non_continue_entry_for_continue_candidate(
        &self,
        candidate: &BranchCandidate,
        continue_target: BlockRef,
    ) -> Option<BlockRef> {
        if candidate.then_entry == continue_target {
            candidate.else_entry.or(candidate.merge)
        } else if candidate.else_entry == Some(continue_target) {
            Some(candidate.then_entry)
        } else {
            None
        }
    }

    fn entry_is_break_funnel_to_continue(
        &self,
        entry: BlockRef,
        continue_target: BlockRef,
        loop_context: &ActiveLoopContext,
        visited: &mut BTreeSet<BlockRef>,
    ) -> bool {
        if !visited.insert(entry) {
            return false;
        }
        if self.entry_is_direct_loop_break(entry, loop_context) {
            return true;
        }

        let Some(candidate) = self.branch_by_header.get(&entry).copied() else {
            return false;
        };
        let Some(non_continue_entry) =
            self.non_continue_entry_for_continue_candidate(candidate, continue_target)
        else {
            return false;
        };

        self.entry_is_break_funnel_to_continue(
            non_continue_entry,
            continue_target,
            loop_context,
            visited,
        )
    }

    fn entry_is_direct_loop_break(
        &self,
        entry: BlockRef,
        loop_context: &ActiveLoopContext,
    ) -> bool {
        loop_context.break_exits.contains_key(&entry)
            || entry == loop_context.post_loop
            || Some(entry) == loop_context.downstream_post_loop
    }
}
