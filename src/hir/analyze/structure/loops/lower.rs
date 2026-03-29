//! 这个子模块负责把已确认的 `LoopCandidate` 真正降成 HIR 循环语句。
//!
//! 它依赖 StructureFacts 已区分好的 while/repeat/numeric-for/generic-for 形态和 override
//! 状态，不会在这里重新识别循环种类。
//! 例如：`NumericForLike` 的候选会在这里降成 `HirStmt::NumericFor`。

use super::*;

impl<'a, 'b> StructuredBodyLowerer<'a, 'b> {
    pub(crate) fn lower_loop(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let candidate = *self.loop_by_header.get(&block)?;
        if !candidate.reducible {
            return None;
        }

        match candidate.kind_hint {
            LoopKindHint::WhileLike => {
                self.lower_while_loop(candidate, stop, stmts, target_overrides)
            }
            LoopKindHint::RepeatLike => {
                self.lower_repeat_loop(candidate, stop, stmts, target_overrides)
            }
            LoopKindHint::NumericForLike => {
                self.try_lower_numeric_for_init(block, stop, stmts, target_overrides)
            }
            LoopKindHint::GenericForLike => {
                self.try_lower_generic_for_preheader(block, stop, stmts, target_overrides)
            }
            LoopKindHint::Unknown => None,
        }
    }

    fn lower_while_loop(
        &mut self,
        candidate: &LoopCandidate,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let preheader = unique_loop_preheader(candidate)?;
        let (body_entry, branch_exit) =
            loop_branch_body_and_exit(self.lowering, candidate.header, &candidate.blocks)?;
        let exit = branch_exit;
        if let Some(stop) = stop
            && stop != exit
            && candidate.blocks.contains(&stop)
        {
            return None;
        }

        let plan = self.build_loop_state_plan(candidate, preheader, exit, &[], target_overrides)?;
        let loop_context = self.build_active_loop_context(candidate, exit)?;
        let combined_target_overrides =
            merge_target_overrides(target_overrides, &plan.backedge_target_overrides);
        stmts.extend(loop_state_init_stmts(&plan));
        self.visited.insert(candidate.header);
        self.install_loop_exit_bindings(candidate, exit, &plan, target_overrides);

        self.active_loops.push(loop_context.clone());
        let body = self.lower_region(
            body_entry,
            Some(candidate.header),
            &combined_target_overrides,
        )?;
        self.active_loops.pop();
        self.visited
            .extend(loop_context.break_exits.keys().copied());
        if let Some(continue_target) = loop_context.continue_target {
            self.visited.insert(continue_target);
        }
        let mut cond = self.lower_branch_cond_for_target(candidate.header, body_entry)?;
        let mut cond_expr_overrides = self.block_prefix_temp_expr_overrides(candidate.header);
        cond_expr_overrides.extend(temp_expr_overrides(&combined_target_overrides));
        rewrite_expr_temps(&mut cond, &cond_expr_overrides);
        stmts.push(HirStmt::While(Box::new(HirWhile { cond, body })));

        Some(Some(exit))
    }

    fn lower_repeat_loop(
        &mut self,
        candidate: &LoopCandidate,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let preheader = unique_loop_preheader(candidate)?;
        let continue_block = candidate.continue_target?;
        let (loop_backedge_target, exit) =
            loop_branch_body_and_exit(self.lowering, continue_block, &candidate.blocks)?;
        if let Some(stop) = stop
            && stop != exit
            && candidate.blocks.contains(&stop)
        {
            return None;
        }

        let plan = self.build_loop_state_plan(candidate, preheader, exit, &[], target_overrides)?;
        let loop_context = self.build_active_loop_context(candidate, exit)?;
        let combined_target_overrides =
            merge_target_overrides(target_overrides, &plan.backedge_target_overrides);
        let backedge_pad = self.repeat_backedge_pad(
            candidate.header,
            loop_backedge_target,
            &combined_target_overrides,
        )?;
        let suppressed = plan
            .states
            .iter()
            .map(|state| state.phi_id)
            .collect::<Vec<_>>();
        for phi_id in &suppressed {
            self.overrides.suppress_phi(*phi_id);
        }

        self.active_loops.push(loop_context.clone());
        let mut body = self
            .lower_region_with_suppressed_loop(
                candidate.header,
                Some(continue_block),
                &combined_target_overrides,
                Some(candidate.header),
            )?
            .stmts;
        body.extend(self.lower_block_prefix(continue_block, true, &combined_target_overrides)?);
        self.active_loops.pop();
        for phi_id in suppressed {
            self.overrides.unsuppress_phi(phi_id);
        }

        stmts.extend(loop_state_init_stmts(&plan));
        self.visited.insert(continue_block);
        if let Some(backedge_pad) = backedge_pad {
            self.visited.insert(backedge_pad);
        }
        self.visited
            .extend(loop_context.break_exits.keys().copied());
        self.install_loop_exit_bindings(candidate, exit, &plan, target_overrides);
        stmts.push(HirStmt::Repeat(Box::new(HirRepeat {
            body: HirBlock { stmts: body },
            cond: {
                let mut cond = self.lower_branch_cond_for_target(continue_block, exit)?;
                rewrite_expr_temps(&mut cond, &temp_expr_overrides(&combined_target_overrides));
                cond
            },
        })));

        Some(Some(exit))
    }

    pub(crate) fn try_lower_numeric_for_init(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let (instr_ref, instr) = self.block_terminator(block)?;
        let LowInstr::NumericForInit(init) = instr else {
            return None;
        };
        let init = *init;

        let header = self.lowering.cfg.instr_to_block[init.body_target.index()];
        let candidate = *self.loop_by_header.get(&header)?;
        if !candidate.reducible || candidate.kind_hint != LoopKindHint::NumericForLike {
            return None;
        }

        let exit = self.lowering.cfg.instr_to_block[init.exit_target.index()];
        if !candidate.exits.contains(&exit) {
            return None;
        }
        if let Some(stop) = stop
            && stop != exit
            && candidate.blocks.contains(&stop)
        {
            return None;
        }

        let binding = self
            .lowering
            .bindings
            .numeric_for_locals
            .get(&header)
            .copied()?;
        let plan =
            self.build_loop_state_plan(candidate, block, exit, &[init.index], target_overrides)?;
        let combined_target_overrides =
            merge_target_overrides(target_overrides, &plan.backedge_target_overrides);
        let mut suppressed = plan
            .states
            .iter()
            .map(|state| state.phi_id)
            .collect::<Vec<_>>();
        suppressed.extend(
            Self::header_values(candidate)
                .filter(|value| value.reg == init.index)
                .map(|value| value.phi_id),
        );

        self.visited.insert(block);
        stmts.extend(self.lower_block_prefix(block, false, target_overrides)?);
        stmts.extend(loop_state_init_stmts(&plan));

        for phi_id in &suppressed {
            self.overrides.suppress_phi(*phi_id);
        }
        let continue_block = candidate.continue_target.unwrap_or(header);
        let loop_context = self.build_active_loop_context(candidate, exit)?;
        self.active_loops.push(loop_context.clone());
        let body = if continue_block == header {
            let stmts = self.lower_block_prefix(header, false, &combined_target_overrides)?;
            HirBlock { stmts }
        } else {
            let mut stmts = self
                .lower_region_with_suppressed_loop(
                    header,
                    Some(continue_block),
                    &combined_target_overrides,
                    Some(header),
                )?
                .stmts;
            let prefix =
                self.lower_block_prefix(continue_block, false, &combined_target_overrides)?;
            stmts.extend(prefix);
            HirBlock { stmts }
        };
        self.active_loops.pop();
        for phi_id in suppressed {
            self.overrides.unsuppress_phi(phi_id);
        }

        self.visited.insert(continue_block);
        self.visited
            .extend(loop_context.break_exits.keys().copied());
        self.install_loop_exit_bindings(candidate, exit, &plan, target_overrides);
        stmts.push(HirStmt::NumericFor(Box::new(HirNumericFor {
            binding,
            start: expr_for_reg_use(self.lowering, block, instr_ref, init.index),
            limit: expr_for_reg_use(self.lowering, block, instr_ref, init.limit),
            step: expr_for_reg_use(self.lowering, block, instr_ref, init.step),
            body,
        })));

        Some(Some(exit))
    }

    pub(crate) fn try_lower_generic_for_preheader(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let header = self.lowering.cfg.unique_reachable_successor(block)?;
        let candidate = *self.loop_by_header.get(&header)?;
        if !candidate.reducible
            || candidate.kind_hint != LoopKindHint::GenericForLike
            || candidate.continue_target != Some(header)
            || unique_loop_preheader(candidate)? != block
        {
            return None;
        }

        let (call_instr_ref, call, loop_instr) = self.generic_for_header_instrs(header)?;
        let exit = self.lowering.cfg.instr_to_block[loop_instr.exit_target.index()];
        if !candidate.exits.contains(&exit) {
            return None;
        }
        if let Some(stop) = stop
            && stop != exit
            && candidate.blocks.contains(&stop)
        {
            return None;
        }

        let body_entry = self.lowering.cfg.instr_to_block[loop_instr.body_target.index()];
        if !candidate.blocks.contains(&body_entry) || body_entry == header {
            return None;
        }

        let bindings = self
            .lowering
            .bindings
            .generic_for_locals
            .get(&header)?
            .clone();
        if bindings.len() != loop_instr.bindings.len {
            return None;
        }

        let mut excluded_regs = vec![loop_instr.control];
        excluded_regs.extend(
            (0..loop_instr.bindings.len)
                .map(|offset| Reg(loop_instr.bindings.start.index() + offset)),
        );
        let plan =
            self.build_loop_state_plan(candidate, block, exit, &excluded_regs, target_overrides)?;
        let combined_target_overrides =
            merge_target_overrides(target_overrides, &plan.backedge_target_overrides);

        self.visited.insert(block);
        stmts.extend(self.lower_block_prefix(block, false, target_overrides)?);
        stmts.extend(loop_state_init_stmts(&plan));

        let loop_context = self.build_active_loop_context(candidate, exit)?;
        self.active_loops.push(loop_context.clone());
        let body = self.lower_region(body_entry, Some(header), &combined_target_overrides)?;
        self.active_loops.pop();
        self.visited.insert(header);
        self.visited
            .extend(loop_context.break_exits.keys().copied());
        self.install_loop_exit_bindings(candidate, exit, &plan, target_overrides);
        stmts.push(HirStmt::GenericFor(Box::new(HirGenericFor {
            bindings,
            iterator: self.lower_generic_for_iterator(header, call_instr_ref, call),
            body,
        })));

        Some(Some(exit))
    }
}
