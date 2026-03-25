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

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);

        let short_plan = self.try_build_short_circuit_plan(block, stop)?;
        let plan = short_plan.or_else(|| self.build_plain_branch_plan(block))?;

        for header in &plan.consumed_headers {
            self.visited.insert(*header);
        }

        let branch_stop =
            self.branch_stop_for_region(block, plan.then_entry, plan.else_entry, plan.merge, stop);
        let then_block = self.lower_region(plan.then_entry, branch_stop, target_overrides)?;
        let else_block = match plan.else_entry {
            Some(else_entry) => {
                Some(self.lower_region(else_entry, branch_stop, target_overrides)?)
            }
            None => None,
        };
        stmts.push(branch_stmt(plan.cond, then_block, else_block));
        self.install_stop_boundary_value_merge_override(block, branch_stop, target_overrides);
        for header in &plan.consumed_headers {
            self.install_branch_value_merge_overrides(*header, target_overrides);
        }

        match branch_stop {
            Some(next) if next == self.lowering.cfg.exit_block => Some(None),
            Some(next) => Some(Some(next)),
            None => Some(None),
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
        self.suppressed_phis.insert(plan.phi_id);

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
        let reg = short.result_reg?;
        let phi = self
            .lowering
            .dataflow
            .phi_candidates
            .iter()
            .find(|phi| phi.block == merge && phi.reg == reg)?;
        let allowed_blocks = BTreeSet::from([block]);
        if recover_value_phi_expr_with_allowed_blocks(self.lowering, phi, &allowed_blocks).is_some()
        {
            return None;
        }

        if let Some(stop) = stop
            && stop != merge
            && short.blocks.contains(&stop)
        {
            return None;
        }

        let target_temp = *self.lowering.bindings.phi_temps.get(phi.id.index())?;
        let mut short_stmts = self.lower_block_prefix(block, true, target_overrides)?;
        short_stmts.extend(
            self.lower_value_merge_node(short, short.entry, target_temp, true)?
                .stmts,
        );

        self.visited.insert(block);
        self.visited.extend(value_merge_skipped_blocks(short));
        self.suppressed_phis.insert(phi.id);
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
        let reg = short.result_reg?;
        let phi = self
            .lowering
            .dataflow
            .phi_candidates
            .iter()
            .find(|phi| phi.block == merge && phi.reg == reg)?;
        let allowed_blocks = BTreeSet::from([block]);
        let _ = recover_value_phi_expr_with_allowed_blocks(self.lowering, phi, &allowed_blocks)?;

        if let Some(stop) = stop
            && stop != merge
            && short.blocks.contains(&stop)
        {
            return None;
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
        let break_exit = candidate
            .merge
            .filter(|merge| loop_context.break_exits.contains_key(merge))?;
        // break 臂之外的那一臂，很多时候只是继续执行当前 loop body，最后再回到
        // continue target。如果这里一口气把它降到 break pad 的出口，repeat/for 的
        // loop tail 就会被一起吞进去，随后整片 region 只能 fallback。这里优先把
        // 非 break 臂截到当前 loop 的 continue target；只有确实没有这条稳定回路时，
        // 才继续沿用 break exit 作为边界。
        let body_stop = loop_context
            .continue_target
            .filter(|target| {
                *target != break_exit && can_reach(self.lowering.cfg, candidate.then_entry, *target)
            })
            .or(Some(break_exit));
        let then_block = self.lower_region(candidate.then_entry, body_stop, target_overrides)?;
        let break_block = loop_context.break_exits[&break_exit].clone();
        let mut cond = self.lower_candidate_cond(block, candidate)?;
        rewrite_expr_temps(&mut cond, &temp_expr_overrides(target_overrides));

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        self.visited.insert(block);
        self.visited.insert(break_exit);

        if body_stop == Some(break_exit)
            && break_block.stmts.last() == Some(&HirStmt::Break)
            && then_block.stmts == break_block.stmts[..break_block.stmts.len() - 1]
        {
            stmts.extend(then_block.stmts);
            stmts.push(branch_stmt(
                negate_expr(cond),
                HirBlock {
                    stmts: vec![HirStmt::Break],
                },
                None,
            ));
            return Some(None);
        }

        if then_block.stmts.is_empty() {
            stmts.push(branch_stmt(negate_expr(cond), break_block, None));
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
        let mut continue_cond = self.lower_branch_cond_for_target(block, continue_target)?;
        rewrite_expr_temps(&mut continue_cond, &temp_expr_overrides(target_overrides));

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        self.visited.insert(block);

        if let Some(break_exit) = candidate
            .merge
            .filter(|merge| loop_context.break_exits.contains_key(merge))
        {
            self.visited.insert(break_exit);
            stmts.push(branch_stmt(
                negate_expr(continue_cond),
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
                let stmt = if candidate.then_entry == continue_target {
                    branch_stmt(continue_cond, continue_block, Some(break_block.clone()))
                } else {
                    branch_stmt(
                        negate_expr(continue_cond),
                        break_block.clone(),
                        Some(continue_block),
                    )
                };
                stmts.push(stmt);
                return Some(None);
            }

            let branch_stop = self.branch_stop_for_region(
                block,
                candidate.then_entry,
                candidate.else_entry,
                candidate.merge,
                stop,
            );
            let non_continue_block =
                self.lower_region(non_continue_entry, branch_stop, target_overrides)?;
            let stmt = if candidate.then_entry == continue_target {
                branch_stmt(continue_cond, continue_block, Some(non_continue_block))
            } else {
                branch_stmt(
                    negate_expr(continue_cond),
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
            // `if cond then body end` 这类源码在 CFG 里会表现成“显式一臂 + 隐式 merge”，
            // 如果 merge 恰好就是当前 loop 的 continue target，这里应该继续保留源码级
            // loop 控制语义，而不是因为缺少显式 else 边就整段 fallback。
            let non_continue_block = self.lower_region(
                candidate.then_entry,
                Some(continue_target),
                target_overrides,
            )?;
            stmts.push(branch_stmt(
                continue_cond,
                continue_block,
                Some(non_continue_block),
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

        let Some(reg) = short.result_reg else {
            return;
        };
        let Some(phi) = self
            .lowering
            .dataflow
            .phi_candidates
            .iter()
            .find(|phi| phi.block == merge && phi.reg == reg)
        else {
            return;
        };
        let Some(expr) = shared_target_expr_from_overrides(self.lowering, phi, target_overrides)
        else {
            return;
        };

        self.suppressed_phis.insert(phi.id);
        self.entry_overrides
            .entry(merge)
            .or_default()
            .insert(reg, expr);
    }
}
