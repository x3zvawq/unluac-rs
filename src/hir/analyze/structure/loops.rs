//! 这个文件承载 HIR 结构恢复里的 loop 专项逻辑。
//!
//! `while / repeat / numeric-for / generic-for` 的恢复需要同时处理 header phi、
//! backedge 重写、多出口 break pad 和 Lua VM 特有的 for 头部形状。如果这些逻辑继续
//! 混在 `structure.rs` 入口文件里，很快就会把“分支恢复”和“循环恢复”搅成一团，
//! 也更难看出每一步为什么安全。

use super::rewrites::lvalue_as_expr;
use super::*;

impl<'a, 'b> StructuredBodyLowerer<'a, 'b> {
    pub(super) fn lower_loop(
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
        let preheader = unique_loop_preheader(self.lowering.cfg, candidate)?;
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
        self.install_loop_exit_bindings(candidate, exit, &plan);

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
        rewrite_expr_temps(&mut cond, &temp_expr_overrides(&combined_target_overrides));
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
        let preheader = unique_loop_preheader(self.lowering.cfg, candidate)?;
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
            self.suppressed_phis.insert(*phi_id);
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
            self.suppressed_phis.remove(&phi_id);
        }

        stmts.extend(loop_state_init_stmts(&plan));
        self.visited.insert(continue_block);
        if let Some(backedge_pad) = backedge_pad {
            self.visited.insert(backedge_pad);
        }
        self.visited
            .extend(loop_context.break_exits.keys().copied());
        self.install_loop_exit_bindings(candidate, exit, &plan);
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

    pub(super) fn try_lower_numeric_for_init(
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

        let binding = *self.lowering.bindings.numeric_for_locals.get(&header)?;
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
            self.header_phis(header)
                .filter(|phi| phi.reg == init.index)
                .map(|phi| phi.id),
        );

        self.visited.insert(block);
        stmts.extend(self.lower_block_prefix(block, false, target_overrides)?);
        stmts.extend(loop_state_init_stmts(&plan));

        for phi_id in &suppressed {
            self.suppressed_phis.insert(*phi_id);
        }
        let continue_block = candidate.continue_target.unwrap_or(header);
        let loop_context = self.build_active_loop_context(candidate, exit)?;
        self.active_loops.push(loop_context.clone());
        let body = if continue_block == header {
            HirBlock {
                stmts: self.lower_block_prefix(header, false, &combined_target_overrides)?,
            }
        } else {
            let mut stmts = self
                .lower_region_with_suppressed_loop(
                    header,
                    Some(continue_block),
                    &combined_target_overrides,
                    Some(header),
                )?
                .stmts;
            stmts.extend(self.lower_block_prefix(
                continue_block,
                false,
                &combined_target_overrides,
            )?);
            HirBlock { stmts }
        };
        self.active_loops.pop();
        for phi_id in suppressed {
            self.suppressed_phis.remove(&phi_id);
        }

        self.visited.insert(continue_block);
        self.visited
            .extend(loop_context.break_exits.keys().copied());
        self.install_loop_exit_bindings(candidate, exit, &plan);
        stmts.push(HirStmt::NumericFor(Box::new(HirNumericFor {
            binding,
            start: expr_for_reg_use(self.lowering, block, instr_ref, init.index),
            limit: expr_for_reg_use(self.lowering, block, instr_ref, init.limit),
            step: expr_for_reg_use(self.lowering, block, instr_ref, init.step),
            body,
        })));

        Some(Some(exit))
    }

    pub(super) fn try_lower_generic_for_preheader(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let header = unique_reachable_successor(self.lowering.cfg, block)?;
        let candidate = *self.loop_by_header.get(&header)?;
        if !candidate.reducible
            || candidate.kind_hint != LoopKindHint::GenericForLike
            || candidate.continue_target != Some(header)
            || unique_loop_preheader(self.lowering.cfg, candidate)? != block
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
        self.install_loop_exit_bindings(candidate, exit, &plan);
        stmts.push(HirStmt::GenericFor(Box::new(HirGenericFor {
            bindings,
            iterator: self.lower_generic_for_iterator(header, call_instr_ref, call),
            body,
        })));

        Some(Some(exit))
    }

    fn build_loop_state_plan(
        &self,
        candidate: &LoopCandidate,
        preheader: BlockRef,
        exit: BlockRef,
        excluded_regs: &[Reg],
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<LoopStatePlan> {
        // loop header 的 phi 在 HIR 里需要被“拆 SSA”成稳定的循环状态变量。
        // 这里先把进入循环前的初值、回边写回目标和退出循环后的可见身份一次性整理好，
        // 避免后面再靠局部规则去猜“这个 phi 其实是 while/repeat/for 的状态”。
        let excluded = excluded_regs.iter().copied().collect::<BTreeSet<_>>();
        let mut plan = LoopStatePlan::default();

        for phi in self.header_phis(candidate.header) {
            if excluded.contains(&phi.reg) {
                continue;
            }

            let init = self.loop_entry_expr(preheader, phi)?;
            let temp = *self.lowering.bindings.phi_temps.get(phi.id.index())?;
            let target = self.loop_state_target(candidate, exit, phi.reg, temp, target_overrides);
            plan.backedge_target_overrides.insert(temp, target.clone());
            for incoming in phi
                .incoming
                .iter()
                .filter(|incoming| candidate.blocks.contains(&incoming.pred))
            {
                for def in &incoming.defs {
                    let def_temp = *self.lowering.bindings.fixed_temps.get(def.index())?;
                    plan.backedge_target_overrides
                        .insert(def_temp, target.clone());
                }
            }

            plan.states.push(LoopStateSlot {
                phi_id: phi.id,
                reg: phi.reg,
                temp,
                target,
                init,
            });
        }

        for phi in self
            .lowering
            .dataflow
            .phi_candidates
            .iter()
            .filter(|phi| phi.block == exit)
        {
            if excluded.contains(&phi.reg)
                || plan.states.iter().any(|state| state.reg == phi.reg)
                || !phi_has_inside_and_outside_incoming(phi, &candidate.blocks)
            {
                continue;
            }

            let init = self.loop_exit_entry_expr(phi, &candidate.blocks)?;
            let temp = *self.lowering.bindings.phi_temps.get(phi.id.index())?;
            let target = self.loop_state_target(candidate, exit, phi.reg, temp, target_overrides);
            plan.backedge_target_overrides.insert(temp, target.clone());
            for incoming in phi
                .incoming
                .iter()
                .filter(|incoming| candidate.blocks.contains(&incoming.pred))
            {
                for def in &incoming.defs {
                    let def_temp = *self.lowering.bindings.fixed_temps.get(def.index())?;
                    plan.backedge_target_overrides
                        .insert(def_temp, target.clone());
                }
            }

            plan.states.push(LoopStateSlot {
                phi_id: phi.id,
                reg: phi.reg,
                temp,
                target,
                init,
            });
        }

        Some(plan)
    }

    fn loop_entry_expr(&self, preheader: BlockRef, phi: &PhiCandidate) -> Option<HirExpr> {
        let incoming = phi
            .incoming
            .iter()
            .find(|incoming| incoming.pred == preheader)?;
        self.loop_incoming_expr(preheader, phi.reg, incoming)
    }

    fn loop_exit_entry_expr(
        &self,
        phi: &PhiCandidate,
        loop_blocks: &BTreeSet<BlockRef>,
    ) -> Option<HirExpr> {
        let mut init_expr = None;

        for incoming in phi
            .incoming
            .iter()
            .filter(|incoming| !loop_blocks.contains(&incoming.pred))
        {
            let expr = self.loop_incoming_expr(incoming.pred, phi.reg, incoming)?;
            if init_expr
                .as_ref()
                .is_some_and(|known_expr: &HirExpr| *known_expr != expr)
            {
                return None;
            }
            init_expr = Some(expr);
        }

        init_expr
    }

    fn loop_incoming_expr(
        &self,
        pred: BlockRef,
        reg: Reg,
        incoming: &crate::cfg::PhiIncoming,
    ) -> Option<HirExpr> {
        // 某些 loop 会直接跟在另一个已经结构化的 region 后面。此时 CFG/Dataflow 视角里，
        // predecessor 边上同一寄存器可能仍然带着“多个原始 def 合流”的痕迹；但对 HIR 来说，
        // 前一个结构已经把它稳定成了 entry override。这里只在 predecessor 本身没有再次改写
        // 该寄存器时，沿用这份 override，避免把同一个语义槽位重新打回 unresolved phi。
        if !self.block_redefines_reg(pred, reg)
            && let Some(expr) = self
                .entry_overrides
                .get(&pred)
                .and_then(|overrides| overrides.get(&reg))
        {
            return Some(expr.clone());
        }

        single_fixed_incoming_expr(self.lowering, incoming)
    }

    fn install_loop_exit_bindings(
        &mut self,
        candidate: &LoopCandidate,
        exit: BlockRef,
        plan: &LoopStatePlan,
    ) {
        if plan.states.is_empty() {
            return;
        }

        let entry_overrides = self.entry_overrides.entry(exit).or_default();
        for state in &plan.states {
            let Some(state_expr) = lvalue_as_expr(&state.target) else {
                continue;
            };
            entry_overrides.insert(state.reg, state_expr);
        }
        let inside_exit_blocks = self
            .loop_state_inside_exit_blocks(candidate, exit)
            .unwrap_or_else(|| candidate.blocks.clone());

        for phi in self
            .lowering
            .dataflow
            .phi_candidates
            .iter()
            .filter(|phi| phi.block == exit)
        {
            let Some(state) = plan.states.iter().find(|state| state.reg == phi.reg) else {
                continue;
            };
            let Some(state_expr) = lvalue_as_expr(&state.target) else {
                continue;
            };
            // break 先落在线性 cleanup pad、再跳到 post-loop continuation 时，
            // exit phi 的 incoming 里会混进这些 pad block。它们虽然 CFG 上已不在
            // `candidate.blocks` 内，但语义上仍然是 loop state 的内部出口。
            if phi_incoming_all_within_blocks(phi, &inside_exit_blocks) {
                if state.temp == self.lowering.bindings.phi_temps[phi.id.index()] {
                    self.suppressed_phis.insert(phi.id);
                } else {
                    self.phi_overrides
                        .entry(exit)
                        .or_default()
                        .insert(phi.id, state_expr);
                }
                continue;
            }
            if !phi_has_inside_and_outside_incoming(phi, &inside_exit_blocks) {
                continue;
            }
            let Some(exit_init) = self.loop_exit_entry_expr(phi, &inside_exit_blocks) else {
                continue;
            };
            // 只有当 exit phi 的“循环外初值”与当前 loop state 的初值确实是同一个语义槽位时，
            // 才能直接把 exit merge 认成这条 loop state。否则像外层 if/elseif/else 包着 loop
            // 的 case，exit block 上同寄存器号的 phi 还在和其他分支路径合流，不能被 loop state
            // 直接顶掉。
            if exit_init != state.init {
                continue;
            }
            if state.temp == self.lowering.bindings.phi_temps[phi.id.index()] {
                self.suppressed_phis.insert(phi.id);
                continue;
            }
            self.phi_overrides
                .entry(exit)
                .or_default()
                .insert(phi.id, state_expr);
        }
    }

    fn loop_state_target(
        &self,
        candidate: &LoopCandidate,
        exit: BlockRef,
        reg: Reg,
        temp: TempId,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> HirLValue {
        if let Some(target) = target_overrides
            .get(&temp)
            .filter(|target| lvalue_as_expr(target).is_some())
        {
            return target.clone();
        }

        if let Some(target) =
            self.uniform_loop_header_target_override(candidate, reg, target_overrides)
        {
            return target;
        }

        self.uniform_loop_exit_target_override(candidate, exit, reg, target_overrides)
            .unwrap_or(HirLValue::Temp(temp))
    }

    fn uniform_loop_header_target_override(
        &self,
        candidate: &LoopCandidate,
        reg: Reg,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirLValue> {
        let phi = self
            .header_phis(candidate.header)
            .find(|phi| phi.reg == reg)?;
        self.shared_loop_inside_target(phi, &candidate.blocks, target_overrides)
    }

    fn uniform_loop_exit_target_override(
        &self,
        candidate: &LoopCandidate,
        exit: BlockRef,
        reg: Reg,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirLValue> {
        for phi in self
            .lowering
            .dataflow
            .phi_candidates
            .iter()
            .filter(|phi| phi.block == exit && phi.reg == reg)
        {
            if !phi_has_inside_and_outside_incoming(phi, &candidate.blocks) {
                continue;
            }
            if let Some(target) =
                self.shared_loop_inside_target(phi, &candidate.blocks, target_overrides)
            {
                return Some(target);
            }
        }

        None
    }

    fn shared_loop_inside_target(
        &self,
        phi: &PhiCandidate,
        loop_blocks: &BTreeSet<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirLValue> {
        let mut shared_target = None;

        for incoming in phi
            .incoming
            .iter()
            .filter(|incoming| loop_blocks.contains(&incoming.pred))
        {
            for def in &incoming.defs {
                let def_temp = *self.lowering.bindings.fixed_temps.get(def.index())?;
                let target = target_overrides
                    .get(&def_temp)
                    .filter(|target| lvalue_as_expr(target).is_some())?;
                if shared_target
                    .as_ref()
                    .is_some_and(|known_target: &HirLValue| *known_target != *target)
                {
                    return None;
                }
                shared_target = Some(target.clone());
            }
        }

        shared_target
    }

    fn header_phis(&self, header: BlockRef) -> impl Iterator<Item = &PhiCandidate> {
        self.lowering
            .dataflow
            .phi_candidates
            .iter()
            .filter(move |phi| phi.block == header)
    }

    fn build_active_loop_context(
        &self,
        candidate: &LoopCandidate,
        post_loop: BlockRef,
    ) -> Option<ActiveLoopContext> {
        let downstream_post_loop = self.normalized_post_loop_successor(post_loop);
        let mut break_exits = BTreeMap::new();
        for exit in candidate
            .exits
            .iter()
            .copied()
            .filter(|exit| *exit != post_loop)
        {
            if block_is_terminal_exit(self.lowering, exit) {
                continue;
            }
            // 有些 loop 的“直接退出块”只是一个线性 pad，真正的 post-loop continuation
            // 在这个 pad 后面。对这种形状，pad 的下游不应该再被当成额外的 break exit，
            // 否则 repeat/for 会被误判成“多出口 break loop”，整片结构都会回退。
            if downstream_post_loop == Some(exit) {
                continue;
            }
            break_exits.insert(
                exit,
                self.lower_break_exit_pad(exit, post_loop, downstream_post_loop)?,
            );
        }
        let continue_target = candidate.continue_target;
        let continue_sources = continue_target
            .map(|target| {
                self.lowering
                    .structure
                    .goto_requirements
                    .iter()
                    .filter(|requirement| {
                        requirement.reason == crate::structure::GotoReason::UnstructuredContinueLike
                            && requirement.to == target
                            && candidate.blocks.contains(&requirement.from)
                    })
                    .map(|requirement| requirement.from)
                    .collect::<BTreeSet<_>>()
            })
            .unwrap_or_default();

        Some(ActiveLoopContext {
            header: candidate.header,
            continue_target,
            continue_sources,
            break_exits,
        })
    }

    fn normalized_post_loop_successor(&self, post_loop: BlockRef) -> Option<BlockRef> {
        let (_instr_ref, instr) = self.block_terminator(post_loop)?;
        let LowInstr::Jump(jump) = instr else {
            return None;
        };
        let target = self.lowering.cfg.instr_to_block[jump.target.index()];
        self.lower_block_prefix(post_loop, false, &BTreeMap::new())?;
        Some(target)
    }

    fn loop_state_inside_exit_blocks(
        &self,
        candidate: &LoopCandidate,
        post_loop: BlockRef,
    ) -> Option<BTreeSet<BlockRef>> {
        let downstream_post_loop = self.normalized_post_loop_successor(post_loop);
        let mut inside_blocks = candidate.blocks.clone();
        for exit in candidate
            .exits
            .iter()
            .copied()
            .filter(|exit| *exit != post_loop)
        {
            if block_is_terminal_exit(self.lowering, exit) {
                continue;
            }
            if downstream_post_loop == Some(exit) {
                continue;
            }
            self.lower_break_exit_pad(exit, post_loop, downstream_post_loop)?;
            inside_blocks.insert(exit);
        }
        Some(inside_blocks)
    }

    fn repeat_backedge_pad(
        &self,
        header: BlockRef,
        loop_backedge_target: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        if loop_backedge_target == header {
            return Some(None);
        }
        if unique_reachable_successor(self.lowering.cfg, loop_backedge_target) != Some(header) {
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

    fn lower_break_exit_pad(
        &self,
        block: BlockRef,
        post_loop: BlockRef,
        downstream_post_loop: Option<BlockRef>,
    ) -> Option<HirBlock> {
        // 这里只接受“线性的 break 垫片 block”：它允许先做一些必须保留的 cleanup，
        // 但最终必须无条件跳到循环之后的统一 continuation。更复杂的 exit 形状留给后续轮次，
        // 避免这一步又退化成拼命堆 break 特判。
        let mut stmts = self.lower_block_prefix(block, false, &BTreeMap::new())?;
        let (_instr_ref, instr) = self.block_terminator(block)?;
        let LowInstr::Jump(jump) = instr else {
            return None;
        };
        let target = self.lowering.cfg.instr_to_block[jump.target.index()];
        if target != post_loop && Some(target) != downstream_post_loop {
            return None;
        }

        stmts.push(HirStmt::Break);
        Some(HirBlock { stmts })
    }

    fn generic_for_header_instrs(
        &self,
        header: BlockRef,
    ) -> Option<(
        InstrRef,
        crate::transformer::GenericForCallInstr,
        crate::transformer::GenericForLoopInstr,
    )> {
        let range = self.lowering.cfg.blocks[header.index()].instrs;
        if range.len < 2 {
            return None;
        }

        let call_instr_ref = InstrRef(range.end() - 2);
        let loop_instr_ref = InstrRef(range.end() - 1);
        let LowInstr::GenericForCall(call) =
            self.lowering.proto.instrs.get(call_instr_ref.index())?
        else {
            return None;
        };
        let LowInstr::GenericForLoop(loop_instr) =
            self.lowering.proto.instrs.get(loop_instr_ref.index())?
        else {
            return None;
        };

        Some((call_instr_ref, *call, *loop_instr))
    }

    fn lower_generic_for_iterator(
        &self,
        header: BlockRef,
        call_instr_ref: InstrRef,
        call: crate::transformer::GenericForCallInstr,
    ) -> Vec<HirExpr> {
        (0..call.state.len)
            .map(|offset| {
                expr_for_reg_use(
                    self.lowering,
                    header,
                    call_instr_ref,
                    Reg(call.state.start.index() + offset),
                )
            })
            .collect()
    }
}

fn merge_target_overrides(
    inherited: &BTreeMap<TempId, HirLValue>,
    local: &BTreeMap<TempId, HirLValue>,
) -> BTreeMap<TempId, HirLValue> {
    // 嵌套 loop 里当前轮次新增的 state override 只覆盖“同一个 temp 的新身份”，
    // 但父层已经稳定好的状态变量身份也必须继续向下传。否则子 loop 体里读取外层
    // carried 值时，又会退回成悬空 temp，后面的 closure/capture/cond 都会一起串坏。
    let mut merged = inherited.clone();
    merged.extend(local.iter().map(|(temp, target)| (*temp, target.clone())));
    merged
}

fn loop_state_init_stmts(plan: &LoopStatePlan) -> Vec<HirStmt> {
    plan.states
        .iter()
        .map(|state| assign_stmt(vec![state.target.clone()], vec![state.init.clone()]))
        .collect()
}

fn unique_loop_preheader(cfg: &crate::cfg::Cfg, candidate: &LoopCandidate) -> Option<BlockRef> {
    let mut preds = cfg.preds[candidate.header.index()]
        .iter()
        .map(|edge_ref| cfg.edges[edge_ref.index()].from)
        .filter(|pred| cfg.reachable_blocks.contains(pred))
        .filter(|pred| !candidate.blocks.contains(pred));
    let preheader = preds.next()?;
    if preds.next().is_none() {
        Some(preheader)
    } else {
        None
    }
}

fn unique_reachable_successor(cfg: &crate::cfg::Cfg, block: BlockRef) -> Option<BlockRef> {
    let mut successors = cfg.succs[block.index()]
        .iter()
        .map(|edge_ref| cfg.edges[edge_ref.index()].to)
        .filter(|succ| cfg.reachable_blocks.contains(succ));
    let succ = successors.next()?;
    if successors.next().is_none() {
        Some(succ)
    } else {
        None
    }
}

fn block_is_terminal_exit(lowering: &ProtoLowering<'_>, block: BlockRef) -> bool {
    let Some(instr_ref) = lowering.cfg.blocks[block.index()].instrs.last() else {
        return false;
    };
    matches!(
        lowering.proto.instrs[instr_ref.index()],
        LowInstr::Return(_) | LowInstr::TailCall(_)
    )
}

fn loop_branch_body_and_exit(
    lowering: &ProtoLowering<'_>,
    header: BlockRef,
    loop_blocks: &BTreeSet<BlockRef>,
) -> Option<(BlockRef, BlockRef)> {
    let instr = lowering.cfg.terminator(&lowering.proto.instrs, header)?;
    let LowInstr::Branch(branch) = instr else {
        return None;
    };
    let then_target = lowering.cfg.instr_to_block[branch.then_target.index()];
    let else_target = lowering.cfg.instr_to_block[branch.else_target.index()];

    if loop_blocks.contains(&then_target) && !loop_blocks.contains(&else_target) {
        Some((then_target, else_target))
    } else if !loop_blocks.contains(&then_target) && loop_blocks.contains(&else_target) {
        Some((else_target, then_target))
    } else {
        None
    }
}

fn phi_has_inside_and_outside_incoming(
    phi: &PhiCandidate,
    loop_blocks: &BTreeSet<BlockRef>,
) -> bool {
    let mut saw_inside = false;
    let mut saw_outside = false;

    for incoming in &phi.incoming {
        if loop_blocks.contains(&incoming.pred) {
            saw_inside = true;
        } else {
            saw_outside = true;
        }
    }

    saw_inside && saw_outside
}

fn phi_incoming_all_within_blocks(phi: &PhiCandidate, allowed_blocks: &BTreeSet<BlockRef>) -> bool {
    phi.incoming
        .iter()
        .all(|incoming| allowed_blocks.contains(&incoming.pred))
}

fn single_fixed_incoming_expr(
    lowering: &ProtoLowering<'_>,
    incoming: &crate::cfg::PhiIncoming,
) -> Option<HirExpr> {
    if incoming.defs.len() != 1 {
        return None;
    }

    let def = *incoming
        .defs
        .iter()
        .next()
        .expect("len checked above, exactly one def exists");
    Some(HirExpr::TempRef(lowering.bindings.fixed_temps[def.index()]))
}
