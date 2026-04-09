//! 这个文件承载 structured body lowering 里的分支恢复细节。
//!
//! `body.rs` 里既有 region 主循环，也有各种 branch/value-merge/loop-control 的细分
//! 恢复逻辑。把后者单独拆出来，是为了让“主流程如何行走 block”与“某个分支具体怎么
//! 降”分开维护；后面继续打磨 branch merge 或 continue/break 语义时，不需要在一个
//! 超大文件里来回跳转。

use super::*;

impl<'a, 'b> StructuredBodyLowerer<'a, 'b> {
    pub(super) fn lower_branch(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        if let Some(next) =
            self.try_lower_conditional_reassign_branch(block, stop, stmts, target_overrides)
        {
            return Some(next);
        }

        if let Some(next) =
            self.try_lower_statement_value_merge_branch(block, stop, stmts, target_overrides)
        {
            return Some(next);
        }

        if let Some(next) = self.try_lower_value_merge_branch(block, stop, stmts, target_overrides)
        {
            return Some(next);
        }

        if let Some(next) =
            self.try_lower_loop_continue_branch(block, stop, stmts, target_overrides)
        {
            return Some(next);
        }

        if let Some(next) = self.try_lower_loop_break_branch(block, stop, stmts, target_overrides) {
            return Some(next);
        }

        if let Some(escape_target) = self.cross_structure_escape_target(block) {
            return self.lower_cross_structure_escape_branch(
                block,
                escape_target,
                stop,
                stmts,
                target_overrides,
            );
        }

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);

        let short_plan = self.try_build_short_circuit_plan(block, stop)?;
        let plan = short_plan.or_else(|| self.build_plain_branch_plan(block))?;

        for header in &plan.consumed_headers {
            self.visited.insert(*header);
        }

        let branch_stop =
            self.branch_stop_for_region(block, plan.then_entry, plan.else_entry, plan.merge, stop);
        let branch_target_overrides = self
            .branch_value_merges_by_header
            .contains_key(&block)
            .then(|| {
                // branch value merge 一旦存在，先把两臂里对应的 def 统一接到 merge target 身份。
                // 这样即便 merge 值来源是 impure call / method call，后面没法折回 decision expr，
                // HIR 也仍然能保住“分支里显式写值，merge 后继续读同一状态槽位”的结构。
                self.branch_value_target_overrides(block, target_overrides)
            });
        if let Some(branch_target_overrides) = branch_target_overrides.as_ref() {
            stmts.extend(self.branch_value_preserved_entry_stmts(block, branch_target_overrides));
        }
        let then_target_overrides = branch_target_overrides
            .as_ref()
            .map(|branch_target_overrides| {
                self.branch_value_then_target_overrides(block, branch_target_overrides)
            })
            .unwrap_or_else(|| target_overrides.clone());
        let else_target_overrides = branch_target_overrides
            .as_ref()
            .map(|branch_target_overrides| {
                self.branch_value_else_target_overrides(block, branch_target_overrides)
            })
            .unwrap_or_else(|| target_overrides.clone());
        let then_block = self.lower_region(plan.then_entry, branch_stop, &then_target_overrides)?;
        let else_block = match plan.else_entry {
            Some(else_entry) => {
                Some(self.lower_region(else_entry, branch_stop, &else_target_overrides)?)
            }
            None if branch_target_overrides.is_none() => {
                self.build_implicit_else_phi_copies(block, plan.merge)
            }
            None => None,
        };
        stmts.push(branch_stmt(plan.cond, then_block, else_block));
        self.install_stop_boundary_value_merge_override(block, branch_stop, target_overrides);
        for header in &plan.consumed_headers {
            let branch_value_overrides = if *header == block {
                branch_target_overrides
                    .clone()
                    .unwrap_or_else(|| target_overrides.clone())
            } else {
                self.branch_value_target_overrides(*header, target_overrides)
            };
            self.install_branch_value_merge_overrides(*header, &branch_value_overrides);
        }

        match branch_stop {
            Some(next) if next == self.lowering.cfg.exit_block => Some(None),
            Some(next) => Some(Some(next)),
            None => Some(None),
        }
    }

    /// IfThen（无 else 臂）且 merge block 上有未覆盖 phi 时，显式发出
    /// header→merge 边的 phi 初值赋值，确保 merge 之后读到的是正确的"保留原值"
    /// 而不是未初始化的临时值。
    fn build_implicit_else_phi_copies(
        &self,
        header: BlockRef,
        merge: Option<BlockRef>,
    ) -> Option<HirBlock> {
        let merge = merge.filter(|&m| m != self.lowering.cfg.exit_block)?;
        let phis = self.lowering.dataflow.phi_candidates_in_block(merge);
        if phis.is_empty() {
            return None;
        }

        let mut targets = Vec::new();
        let mut values = Vec::new();
        for phi in phis {
            if self.overrides.phi_is_suppressed_for_block(merge, phi.id) {
                continue;
            }
            targets.push(HirLValue::Temp(self.lowering.bindings.phi_temps[phi.id.index()]));
            values.push(expr_for_reg_at_block_exit(self.lowering, header, phi.reg));
        }

        if targets.is_empty() {
            None
        } else {
            Some(HirBlock {
                stmts: vec![assign_stmt(targets, values)],
            })
        }
    }

    fn try_lower_conditional_reassign_branch(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let short = value_merge_candidate_by_header(self.lowering, block)?;
        let ShortCircuitExit::ValueMerge(merge) = short.exit else {
            return None;
        };
        // merge 恰好就是当前 region 的 stop 时，后面不会再真正进入 merge block。
        // 这类情况下如果继续走“先跳过分支、再靠 merge 点物化 phi”的快捷路径，
        // loop-carried/branch-carried 的写回就会直接丢掉。这里宁可退回普通 branch
        // lowering，让两臂里的赋值在当前结构里显式发生，也不把边界语义悄悄吞掉。
        if Some(merge) == stop {
            return None;
        }
        let plan = build_conditional_reassign_plan(self.lowering, block)?;

        if let Some(stop) = stop
            && stop != merge
            && short.blocks.contains(&stop)
        {
            return None;
        }

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        self.visited.insert(block);
        self.visited.extend(value_merge_skipped_blocks(short));
        self.overrides.suppress_phi(plan.phi_id);

        stmts.push(assign_stmt(
            vec![HirLValue::Temp(plan.target_temp)],
            vec![plan.init_value],
        ));
        stmts.push(branch_stmt(
            plan.cond,
            HirBlock {
                stmts: vec![assign_stmt(
                    vec![HirLValue::Temp(plan.target_temp)],
                    vec![plan.assigned_value],
                )],
            },
            None,
        ));

        Some(Some(plan.merge))
    }

    fn try_lower_statement_value_merge_branch(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let short = value_merge_candidate_by_header(self.lowering, block)?;
        let ShortCircuitExit::ValueMerge(merge) = short.exit else {
            return None;
        };
        if Some(merge) == stop {
            return None;
        }
        let allowed_blocks = BTreeSet::from([block]);
        if recover_short_value_merge_expr_with_allowed_blocks(self.lowering, short, &allowed_blocks)
            .is_some()
        {
            return None;
        }

        if let Some(stop) = stop
            && stop != merge
            && short.blocks.contains(&stop)
        {
            return None;
        }

        let target_temp = *self
            .lowering
            .bindings
            .phi_temps
            .get(short.result_phi_id?.index())?;
        let mut short_stmts = self.lower_block_prefix(block, true, target_overrides)?;
        short_stmts.extend(
            self.lower_value_merge_node(short, short.entry, target_temp, true)?
                .stmts,
        );

        self.visited.insert(block);
        self.visited.extend(value_merge_skipped_blocks(short));
        self.overrides.suppress_phi(short.result_phi_id?);
        stmts.extend(short_stmts);

        Some(Some(merge))
    }

    fn try_lower_value_merge_branch(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let short = value_merge_candidate_by_header(self.lowering, block)?;
        let ShortCircuitExit::ValueMerge(merge) = short.exit else {
            return None;
        };
        if Some(merge) == stop {
            return None;
        }
        let allowed_blocks = BTreeSet::from([block]);
        let recovery = recover_short_value_merge_expr_recovery_with_allowed_blocks(
            self.lowering,
            short,
            &allowed_blocks,
        )?;

        if let Some(stop) = stop
            && stop != merge
            && short.blocks.contains(&stop)
        {
            return None;
        }

        if recovery.consumes_header_subject() {
            self.overrides
                .suppress_instrs(consumed_value_merge_subject_instrs(self.lowering, block));
        }
        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        self.visited.insert(block);
        self.visited.extend(value_merge_skipped_blocks(short));
        self.merge_allowed_blocks
            .entry(merge)
            .or_default()
            .insert(block);
        Some(Some(merge))
    }

    fn try_lower_loop_break_branch(
        &mut self,
        block: BlockRef,
        _stop: Option<BlockRef>,
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
        let break_block = if break_exit == loop_context.post_loop
            || Some(break_exit) == loop_context.downstream_post_loop
        {
            HirBlock {
                stmts: vec![HirStmt::Break],
            }
        } else {
            loop_context.break_exits[&break_exit].clone()
        };
        // break 臂之外的那一臂，很多时候只是继续执行当前 loop body，最后再回到
        // continue target。如果这里一口气把它降到 break pad 的出口，repeat/for 的
        // loop tail 就会被一起吞进去，随后整片 region 只能 fallback。这里优先把
        // 非 break 臂截到当前 loop 的 continue target；只有确实没有这条稳定回路时，
        // 才继续沿用 break exit 作为边界。
        let body_stop = loop_context
            .continue_target
            .filter(|target| {
                *target != break_exit && self.lowering.cfg.can_reach(candidate.then_entry, *target)
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

    fn cross_structure_escape_target(&self, block: BlockRef) -> Option<BlockRef> {
        let loop_context = self.active_loops.last()?;
        let candidate = self.branch_by_header.get(&block).copied()?;
        let merge = candidate.merge?;
        let continue_target = loop_context.continue_target?;

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
        {
            return None;
        }

        let loop_candidate = self.loop_by_header.get(&loop_context.header).copied()?;
        if loop_candidate.blocks.contains(&merge) {
            return None;
        }

        (candidate.then_entry == continue_target
            || self
                .lowering
                .cfg
                .can_reach(candidate.then_entry, continue_target))
        .then_some(merge)
    }

    fn lower_cross_structure_escape_branch(
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
        stmts.push(branch_stmt(
            keep_cond.negate(),
            escape_block,
            continue_else,
        ));

        Some(Some(continue_target))
    }

    fn try_lower_loop_continue_branch(
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
        let then_target_overrides =
            self.branch_entry_target_overrides(block, Some(candidate.then_entry), target_overrides);

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        self.visited.insert(block);

        if let Some(break_exit) = candidate
            .merge
            .filter(|merge| loop_context.break_exits.contains_key(merge))
        {
            self.visited.insert(break_exit);
            stmts.push(branch_stmt(
                continue_cond.negate(),
                loop_context.break_exits[&break_exit].clone(),
                None,
            ));
            return Some(None);
        }

        let continue_block = HirBlock {
            stmts: vec![HirStmt::Continue],
        };
        if let Some(else_entry) = candidate.else_entry {
            let non_continue_entry = if candidate.then_entry == continue_target {
                else_entry
            } else {
                candidate.then_entry
            };
            if let Some(break_block) = loop_context.break_exits.get(&non_continue_entry) {
                self.visited.insert(non_continue_entry);
                // 当前 branch 本身如果没有“主动提前跳到 continue target”的证据，
                // 那它更像 loop tail 上的“否则 break”判定：继续这一臂只是自然回到
                // 下一轮，不应该硬提升成显式 `continue`。否则像 Lua 5.1 这种没有
                // `continue` / `goto` 的 target dialect 会被我们平白制造出无法落地的语义。
                if prefer_natural_fallthrough {
                    stmts.push(branch_stmt(
                        continue_cond.negate(),
                        break_block.clone(),
                        None,
                    ));
                    return Some(None);
                }
                let stmt = if candidate.then_entry == continue_target {
                    branch_stmt(continue_cond, continue_block, Some(break_block.clone()))
                } else {
                    branch_stmt(
                        continue_cond.negate(),
                        break_block.clone(),
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
                return Some(Some(continue_target));
            }

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
                let non_continue_block =
                    self.lower_region(non_continue_entry, stop, target_overrides)?;
                stmts.push(branch_stmt(
                    continue_cond.negate(),
                    non_continue_block,
                    None,
                ));
                return Some(None);
            }
            let non_continue_block =
                self.lower_region(non_continue_entry, stop, target_overrides)?;
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
        stmts.push(branch_stmt(continue_cond, continue_block, None));
        if merge == self.lowering.cfg.exit_block {
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
        // 只有当非 continue 臂本身就是 terminal exit，且从 CFG 上根本到不了当前
        // continue target 时，才能确定它是“提前结束本轮/本函数”的 guard 分支。
        // 像 repeat 里的 break funnel 虽然最终也可能不回到 continue target，但它本身
        // 仍然是一个需要继续展开的控制块，不能在这里过早压平成 guard-return。
        if !loop_context.continue_sources.contains(&block)
            && matches!(
                self.block_terminator(non_continue_entry),
                Some((_instr_ref, LowInstr::Return(_) | LowInstr::TailCall(_)))
            )
            && !self
                .lowering
                .cfg
                .can_reach(non_continue_entry, continue_target)
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

    fn lower_value_merge_node(
        &self,
        short: &ShortCircuitCandidate,
        node_ref: ShortCircuitNodeRef,
        target_temp: TempId,
        prefix_emitted: bool,
    ) -> Option<HirBlock> {
        let node = short.nodes.get(node_ref.index())?;
        let mut stmts = Vec::new();

        if !prefix_emitted {
            stmts.extend(self.lower_block_prefix(node.header, true, &BTreeMap::new())?);
        }

        let cond = lower_short_circuit_subject(self.lowering, node.header)?;
        let truthy =
            self.lower_value_merge_target(short, node.header, &node.truthy, target_temp)?;
        let falsy = self.lower_value_merge_target(short, node.header, &node.falsy, target_temp)?;
        stmts.push(branch_stmt(cond, truthy, Some(falsy)));

        Some(HirBlock { stmts })
    }

    fn branch_entry_target_overrides(
        &self,
        header: BlockRef,
        entry: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> BTreeMap<TempId, HirLValue> {
        let Some(entry) = entry else {
            return target_overrides.clone();
        };
        let Some(candidate) = self.branch_by_header.get(&header).copied() else {
            return target_overrides.clone();
        };

        if entry == candidate.then_entry {
            return self.branch_value_then_target_overrides(header, target_overrides);
        }
        if Some(entry) == candidate.else_entry {
            return self.branch_value_else_target_overrides(header, target_overrides);
        }

        target_overrides.clone()
    }

    fn lower_value_merge_target(
        &self,
        short: &ShortCircuitCandidate,
        current_header: BlockRef,
        target: &ShortCircuitTarget,
        target_temp: TempId,
    ) -> Option<HirBlock> {
        match target {
            ShortCircuitTarget::Node(next_ref) => {
                self.lower_value_merge_node(short, *next_ref, target_temp, false)
            }
            ShortCircuitTarget::Value(block) => {
                self.lower_value_merge_leaf(short, current_header, *block, target_temp)
            }
            ShortCircuitTarget::TruthyExit | ShortCircuitTarget::FalsyExit => None,
        }
    }

    fn lower_value_merge_leaf(
        &self,
        short: &ShortCircuitCandidate,
        current_header: BlockRef,
        block: BlockRef,
        target_temp: TempId,
    ) -> Option<HirBlock> {
        let mut stmts = if block == current_header {
            Vec::new()
        } else {
            self.lower_block_prefix(block, false, &BTreeMap::new())?
        };
        let value = if block == current_header {
            lower_short_circuit_subject(self.lowering, block)?
        } else {
            lower_materialized_value_leaf_expr(self.lowering, short, block)?
        };
        stmts.push(assign_stmt(vec![HirLValue::Temp(target_temp)], vec![value]));

        Some(HirBlock { stmts })
    }

    fn install_stop_boundary_value_merge_override(
        &mut self,
        header: BlockRef,
        branch_stop: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) {
        let Some(merge) = branch_stop else {
            return;
        };
        let Some(short) = value_merge_candidate_by_header(self.lowering, header) else {
            return;
        };
        let ShortCircuitExit::ValueMerge(short_merge) = short.exit else {
            return;
        };
        if short_merge != merge {
            return;
        }

        let Some(phi_id) = short.result_phi_id else {
            return;
        };
        let Some(reg) = short.result_reg else {
            return;
        };
        let Some(expr) = shared_target_expr_from_overrides(self.lowering, short, target_overrides)
        else {
            return;
        };

        self.replace_phi_with_entry_expr(merge, phi_id, reg, expr);
    }
}
