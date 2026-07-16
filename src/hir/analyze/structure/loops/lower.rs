//! 这个子模块负责把已确认的 `LoopCandidate` 真正降成 HIR 循环语句。
//!
//! 它依赖 StructureFacts 已区分好的 while/repeat/numeric-for/generic-for 形态和 override
//! 状态，不会在这里重新识别循环种类；对于仍归为 Unknown 但已经证明可规约、且只有
//! 一个普通 post-loop 的 retry loop，会保守降成 `while true ... break`，其他 terminal
//! exits 仍留在循环体中原样终止。
//! 多条 sibling latch 由 Structure 以 header 作为共同 continue target；这里复用
//! header-retry 路径，不再要求挑出一个并不存在的唯一 latch。
//! 例如：`NumericForLike` 的候选会在这里降成 `HirStmt::NumericFor`。

use super::*;
use crate::hir::expr_safety::expr_observes_eval_order;
use crate::hir::{HirTableField, HirTableKey};

struct PostLoopBreakPrefix {
    instrs: Vec<InstrRef>,
    boundary: InstrRef,
    continuation: BlockRef,
    tbc_regs: Vec<Reg>,
}

impl<'a, 'b> StructuredBodyLowerer<'a, 'b> {
    pub(crate) fn lower_loop(
        &mut self,
        block: BlockRef,
        candidate_id: LoopCandidateId,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let candidate = self.loop_candidate(candidate_id)?;
        if candidate.header != block {
            return None;
        }
        match candidate.kind_hint {
            LoopKindHint::WhileLike => {
                self.lower_while_loop(candidate_id, candidate, stop, stmts, target_overrides)
            }
            LoopKindHint::WhileTrueLike => {
                self.lower_while_true_loop(candidate_id, candidate, stop, stmts, target_overrides)
            }
            LoopKindHint::RepeatLike => {
                self.lower_repeat_loop(candidate_id, candidate, stop, stmts, target_overrides)
            }
            LoopKindHint::NumericForLike => {
                self.try_lower_numeric_for_init(block, stop, stmts, target_overrides)
            }
            LoopKindHint::GenericForLike => {
                self.try_lower_generic_for_preheader(block, stop, stmts, target_overrides)
            }
            LoopKindHint::Unknown => self.lower_unknown_retry_loop(
                candidate_id,
                candidate,
                stop,
                stmts,
                target_overrides,
            ),
        }
    }

    fn lower_unknown_retry_loop(
        &mut self,
        candidate_id: LoopCandidateId,
        candidate: &LoopCandidate,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        if candidate.exits.is_empty() {
            return self.lower_header_retry_while_true_loop(
                candidate_id,
                candidate,
                stop,
                stmts,
                target_overrides,
            );
        }
        if candidate.exits.len() > 1
            && candidate
                .exits
                .iter()
                .all(|exit| self.loop_exit_terminates(candidate, *exit))
        {
            return self.lower_while_true_loop(
                candidate_id,
                candidate,
                stop,
                stmts,
                target_overrides,
            );
        }
        let mut post_loops = candidate
            .exits
            .iter()
            .copied()
            .filter(|exit| !block_is_terminal_exit(self.lowering, *exit));
        let post_loop = match (post_loops.next(), post_loops.next()) {
            (Some(post_loop), None) => post_loop,
            (None, None) if candidate.exits.len() == 1 => candidate.exits.iter().next().copied()?,
            _ => return None,
        };
        if let Some(stop) = stop
            && stop != post_loop
            && candidate.blocks.contains(&stop)
        {
            return None;
        }

        let post_loop_prefix = self.post_loop_break_prefix(candidate, post_loop);
        let preheader = unique_loop_preheader(candidate);
        let plan = self.build_loop_state_plan(
            candidate_id,
            candidate,
            preheader,
            post_loop,
            post_loop_prefix
                .as_ref()
                .map_or(&[], |prefix| prefix.tbc_regs.as_slice()),
            target_overrides,
        )?;
        let combined_target_overrides =
            merge_target_overrides(target_overrides, &plan.backedge_target_overrides);
        let mut loop_context = self.build_active_loop_context(
            candidate_id,
            candidate,
            post_loop,
            &combined_target_overrides,
            &plan.states,
        )?;
        loop_context.loop_blocks = loop_body_blocks(candidate).clone();
        loop_context.continue_target = Some(candidate.header);
        loop_context.continue_sources.clear();
        loop_context.state_slots = plan.states.clone();
        if let Some(prefix) = &post_loop_prefix {
            if prefix.continuation != post_loop {
                loop_context.downstream_post_loop = Some(prefix.continuation);
            }
            loop_context.post_loop_break = Some(self.lower_post_loop_break_prefix(
                post_loop,
                prefix,
                &combined_target_overrides,
            )?);
        }

        for phi_id in &plan.owned_phis {
            self.overrides.suppress_phi(*phi_id);
        }
        self.active_loops.push(loop_context.clone());
        let body = self.lower_region_with_suppressed_loop(
            candidate.header,
            Some(post_loop),
            &combined_target_overrides,
            Some(candidate_id),
        )?;
        self.active_loops.pop();
        for phi_id in &plan.owned_phis {
            self.overrides.unsuppress_phi(*phi_id);
        }
        if let Some(prefix) = &post_loop_prefix {
            self.overrides
                .suppress_instrs(prefix.instrs.iter().copied().chain([prefix.boundary]));
            if prefix.continuation != post_loop {
                self.visited.insert(post_loop);
            }
        }

        stmts.extend(loop_state_init_stmts(&plan));
        self.visited.extend(
            loop_context
                .break_exits
                .values()
                .flat_map(|break_exit| break_exit.blocks.iter().copied()),
        );
        self.install_loop_exit_bindings(
            candidate_id,
            candidate,
            post_loop,
            &plan,
            target_overrides,
        );
        stmts.push(HirStmt::While(Box::new(HirWhile {
            cond: HirExpr::Boolean(true),
            body,
        })));

        Some(Some(
            post_loop_prefix.map_or(post_loop, |prefix| prefix.continuation),
        ))
    }

    fn post_loop_break_prefix(
        &self,
        candidate: &LoopCandidate,
        post_loop: BlockRef,
    ) -> Option<PostLoopBreakPrefix> {
        if self
            .lowering
            .cfg
            .reachable_predecessors(post_loop)
            .iter()
            .any(|pred| !candidate.blocks.contains(pred))
            || self
                .lowering
                .dataflow
                .phi_candidates_in_block(post_loop)
                .iter()
                .any(|phi| !self.lowering.structure.phi_is_dead(phi.id))
        {
            return None;
        }

        let range = self.lowering.cfg.blocks[post_loop.index()].instrs;
        let (instrs, boundary, continuation, close_from) =
            if let Some((boundary, close_from)) = self.first_explicit_tbc_boundary(post_loop) {
                (
                    (range.start.index()..boundary.index())
                        .map(InstrRef)
                        .collect::<Vec<_>>(),
                    boundary,
                    post_loop,
                    close_from,
                )
            } else {
                let (jump_ref, LowInstr::Jump(jump)) = self.block_terminator(post_loop)? else {
                    return None;
                };
                let continuation = self.lowering.cfg.instr_to_block[jump.target.index()];
                if self.lowering.cfg.reachable_predecessors(continuation) != [post_loop]
                    || self
                        .lowering
                        .dataflow
                        .phi_candidates_in_block(continuation)
                        .iter()
                        .any(|phi| !self.lowering.structure.phi_is_dead(phi.id))
                {
                    return None;
                }
                let (boundary, close_from) = self.first_explicit_tbc_boundary(continuation)?;
                if boundary != self.lowering.cfg.blocks[continuation.index()].instrs.start {
                    return None;
                }
                (
                    (range.start.index()..jump_ref.index())
                        .map(InstrRef)
                        .collect::<Vec<_>>(),
                    boundary,
                    continuation,
                    close_from,
                )
            };
        if instrs.is_empty()
            || instrs.iter().any(|instr_ref| {
                matches!(
                    self.lowering.proto.instrs[instr_ref.index()],
                    LowInstr::Close(_) | LowInstr::Tbc(_)
                )
            })
        {
            return None;
        }

        let tbc_regs = candidate
            .blocks
            .iter()
            .flat_map(|block| {
                let range = self.lowering.cfg.blocks[block.index()].instrs;
                range.start.index()..range.end()
            })
            .filter_map(|index| match self.lowering.proto.instrs[index] {
                LowInstr::Tbc(tbc)
                    if tbc.kind == crate::transformer::TbcKind::Explicit
                        && tbc.reg.index() >= close_from.index() =>
                {
                    Some(tbc.reg)
                }
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        if tbc_regs.is_empty()
            || !instrs.iter().any(|instr_ref| {
                self.lowering.dataflow.instr_effects[instr_ref.index()]
                    .fixed_uses
                    .iter()
                    .any(|reg| tbc_regs.contains(reg))
            })
        {
            return None;
        }

        Some(PostLoopBreakPrefix {
            instrs,
            boundary,
            continuation,
            tbc_regs: tbc_regs.into_iter().collect(),
        })
    }

    fn first_explicit_tbc_boundary(&self, block: BlockRef) -> Option<(InstrRef, Reg)> {
        let range = self.lowering.cfg.blocks[block.index()].instrs;
        (range.start.index()..range.end()).find_map(|index| {
            let instr_ref = InstrRef(index);
            let LowInstr::Close(close) = self.lowering.proto.instrs[index] else {
                return None;
            };
            matches!(
                self.lowering.structure.cleanup_disposition(instr_ref),
                CleanupDisposition::ExplicitTbcBoundary
            )
            .then_some((instr_ref, close.from))
        })
    }

    fn lower_post_loop_break_prefix(
        &self,
        post_loop: BlockRef,
        prefix: &PostLoopBreakPrefix,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirBlock> {
        let mut stmts = Vec::new();
        for instr_ref in &prefix.instrs {
            if self.overrides.instr_is_suppressed(*instr_ref) {
                return None;
            }
            stmts.extend(lower_regular_instr(
                self.lowering,
                post_loop,
                *instr_ref,
                &self.lowering.proto.instrs[instr_ref.index()],
            ));
        }
        apply_loop_rewrites(&mut stmts, target_overrides);
        stmts.push(HirStmt::Break);
        Some(HirBlock { stmts })
    }

    fn lower_header_retry_while_true_loop(
        &mut self,
        candidate_id: LoopCandidateId,
        candidate: &LoopCandidate,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        if let Some(stop) = stop
            && candidate.blocks.contains(&stop)
        {
            return None;
        }

        let preheader = unique_loop_preheader(candidate);
        let post_loop = self.lowering.cfg.exit_block;
        let plan = self.build_loop_state_plan(
            candidate_id,
            candidate,
            preheader,
            post_loop,
            &[],
            target_overrides,
        )?;
        let combined_target_overrides =
            merge_target_overrides(target_overrides, &plan.backedge_target_overrides);
        let mut loop_context = self.build_active_loop_context(
            candidate_id,
            candidate,
            post_loop,
            &combined_target_overrides,
            &plan.states,
        )?;
        loop_context.loop_blocks = loop_body_blocks(candidate).clone();
        loop_context.continue_target = Some(candidate.header);
        loop_context.continue_sources.clear();
        loop_context.state_slots = plan.states.clone();

        for phi_id in &plan.owned_phis {
            self.overrides.suppress_phi(*phi_id);
        }
        self.active_loops.push(loop_context.clone());
        let body = self.lower_region_with_suppressed_loop(
            candidate.header,
            None,
            &combined_target_overrides,
            Some(candidate_id),
        )?;
        self.active_loops.pop();
        for phi_id in &plan.owned_phis {
            self.overrides.unsuppress_phi(*phi_id);
        }

        stmts.extend(loop_state_init_stmts(&plan));
        self.visited.extend(
            loop_context
                .break_exits
                .values()
                .flat_map(|break_exit| break_exit.blocks.iter().copied()),
        );
        self.install_loop_exit_bindings(
            candidate_id,
            candidate,
            post_loop,
            &plan,
            target_overrides,
        );
        stmts.push(HirStmt::While(Box::new(HirWhile {
            cond: HirExpr::Boolean(true),
            body,
        })));

        Some(None)
    }

    fn lower_while_loop(
        &mut self,
        candidate_id: LoopCandidateId,
        candidate: &LoopCandidate,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let preheader = unique_loop_preheader(candidate);
        let (body_entry, branch_exit) =
            loop_branch_body_and_exit(self.lowering, candidate.header, &candidate.blocks)?;
        let exit = branch_exit;
        if let Some(stop) = stop
            && stop != exit
            && candidate.blocks.contains(&stop)
        {
            return None;
        }

        let plan = self.build_loop_state_plan(
            candidate_id,
            candidate,
            preheader,
            exit,
            &[],
            target_overrides,
        )?;
        let combined_target_overrides =
            merge_target_overrides(target_overrides, &plan.backedge_target_overrides);
        let mut loop_context = self.build_active_loop_context(
            candidate_id,
            candidate,
            exit,
            &combined_target_overrides,
            &plan.states,
        )?;
        loop_context.loop_blocks = loop_body_blocks(candidate).clone();
        loop_context.state_slots = plan.states.clone();
        stmts.extend(loop_state_init_stmts(&plan));
        self.visited.insert(candidate.header);
        self.install_loop_exit_bindings(candidate_id, candidate, exit, &plan, target_overrides);

        for phi_id in &plan.owned_phis {
            self.overrides.suppress_phi(*phi_id);
        }
        self.active_loops.push(loop_context.clone());
        let body = self.lower_region(
            body_entry,
            Some(candidate.header),
            &combined_target_overrides,
        )?;
        self.active_loops.pop();
        for phi_id in &plan.owned_phis {
            self.overrides.unsuppress_phi(*phi_id);
        }
        self.visited.extend(
            loop_context
                .break_exits
                .values()
                .flat_map(|break_exit| break_exit.blocks.iter().copied()),
        );
        if let Some(continue_target) = loop_context.continue_target {
            self.visited.insert(continue_target);
        }
        let mut cond = self.lower_branch_cond_for_target(candidate.header, body_entry)?;
        let (mut cond_expr_overrides, all_prefix_temps) =
            self.block_prefix_temp_expr_overrides(candidate.header);
        let condition_prefix_temps = self.block_condition_prefix_temps(candidate.header);
        let header_prefix_must_stay_in_body = self
            .header_prefix_has_live_non_condition_defs(candidate.header, &condition_prefix_temps);
        self.remove_reordered_condition_prefix_overrides(
            candidate.header,
            &cond,
            &mut cond_expr_overrides,
        );
        cond_expr_overrides.extend(temp_expr_overrides(&combined_target_overrides));
        rewrite_expr_temps(&mut cond, &cond_expr_overrides);

        // 只有当条件表达式引用了前缀中无法内联的 temp 时才需要回退。
        // 前缀中已成功内联的 temp 经 rewrite_expr_temps 处理后不再以 TempRef 出现；
        // 指向前缀外部（局部变量、upvalue 等）的 TempRef 是合法的，不触发回退。
        let unresolvable_prefix_temps: BTreeSet<TempId> = all_prefix_temps
            .into_iter()
            .filter(|t| !cond_expr_overrides.contains_key(t))
            .collect();

        // 循环头部存在无法内联到条件表达式的指令时（如多返回值调用），
        // 条件中会残留指向前缀内部的 TempRef。此时回退为 `while true do prefix; if-break; body end`，
        // 把原来的头部前缀显式作为循环体开头，条件取反作为 break 守卫。
        // 输入形状：header=[call multi_ret; branch ok] + body_entry=[short-circuit/continue]
        // 输出形状：while true do local ok,val=call(); if not ok then break end; <body> end
        if header_prefix_must_stay_in_body
            || expr_has_temp_ref_in(&cond, &unresolvable_prefix_temps)
        {
            let prefix =
                self.lower_block_prefix(candidate.header, true, &combined_target_overrides)?;
            let break_cond = cond.negate();
            let mut full_body = prefix;
            full_body.push(HirStmt::If(Box::new(HirIf {
                cond: break_cond,
                then_block: HirBlock {
                    stmts: vec![HirStmt::Break],
                },
                else_block: None,
            })));
            full_body.extend(body.stmts);
            stmts.push(HirStmt::While(Box::new(HirWhile {
                cond: HirExpr::Boolean(true),
                body: HirBlock { stmts: full_body },
            })));
        } else {
            stmts.push(HirStmt::While(Box::new(HirWhile { cond, body })));
        }

        Some(Some(exit))
    }

    fn remove_reordered_condition_prefix_overrides(
        &self,
        header: BlockRef,
        cond: &HirExpr,
        expr_overrides: &mut BTreeMap<TempId, HirExpr>,
    ) {
        let def_order = self.block_prefix_temp_def_order(header);
        let mut last_order = None;
        let mut reordered = false;
        for temp in temp_refs_in_eval_order(cond) {
            let Some(expr) = expr_overrides.get(&temp) else {
                continue;
            };
            if !expr_observes_eval_order(expr) {
                continue;
            }
            let Some(order) = def_order.get(&temp).copied() else {
                continue;
            };
            if last_order.is_some_and(|last| order < last) {
                reordered = true;
                break;
            }
            last_order = Some(order);
        }
        if reordered {
            expr_overrides.retain(|_, expr| !expr_observes_eval_order(expr));
        }
    }

    fn lower_while_true_loop(
        &mut self,
        candidate_id: LoopCandidateId,
        candidate: &LoopCandidate,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let continue_target = candidate.continue_target?;
        if continue_target == candidate.header {
            return self.lower_header_retry_while_true_loop(
                candidate_id,
                candidate,
                stop,
                stmts,
                target_overrides,
            );
        }
        if let Some(stop) = stop
            && candidate.blocks.contains(&stop)
            && stop != continue_target
        {
            return None;
        }
        if self
            .lowering
            .cfg
            .unique_reachable_successor(continue_target)
            != Some(candidate.header)
        {
            return None;
        }
        if candidate
            .exits
            .iter()
            .any(|exit| !self.loop_exit_terminates(candidate, *exit))
        {
            return None;
        }

        let preheader = unique_loop_preheader(candidate);
        let post_loop = self.lowering.cfg.exit_block;
        let plan = self.build_loop_state_plan(
            candidate_id,
            candidate,
            preheader,
            post_loop,
            &[],
            target_overrides,
        )?;
        let combined_target_overrides =
            merge_target_overrides(target_overrides, &plan.backedge_target_overrides);
        let mut loop_context = self.build_active_loop_context(
            candidate_id,
            candidate,
            post_loop,
            &combined_target_overrides,
            &plan.states,
        )?;
        loop_context.loop_blocks = loop_body_blocks(candidate).clone();
        loop_context.state_slots = plan.states.clone();

        for phi_id in &plan.owned_phis {
            self.overrides.suppress_phi(*phi_id);
        }
        self.active_loops.push(loop_context.clone());
        let mut body = self
            .lower_region_with_suppressed_loop(
                candidate.header,
                Some(continue_target),
                &combined_target_overrides,
                Some(candidate_id),
            )?
            .stmts;
        body.extend(self.lower_block_prefix(continue_target, false, &combined_target_overrides)?);
        self.active_loops.pop();
        for phi_id in &plan.owned_phis {
            self.overrides.unsuppress_phi(*phi_id);
        }

        stmts.extend(loop_state_init_stmts(&plan));
        self.visited.insert(continue_target);
        self.visited.extend(
            loop_context
                .break_exits
                .values()
                .flat_map(|break_exit| break_exit.blocks.iter().copied()),
        );
        self.install_loop_exit_bindings(
            candidate_id,
            candidate,
            post_loop,
            &plan,
            target_overrides,
        );
        stmts.push(HirStmt::While(Box::new(HirWhile {
            cond: HirExpr::Boolean(true),
            body: HirBlock { stmts: body },
        })));

        Some(None)
    }

    fn header_prefix_has_live_non_condition_defs(
        &self,
        block: BlockRef,
        condition_prefix_temps: &BTreeSet<TempId>,
    ) -> bool {
        let Some((terminator_ref, LowInstr::Branch(_))) = self.block_terminator(block) else {
            return false;
        };
        let range = self.lowering.cfg.blocks[block.index()].instrs;
        let live_out = self.lowering.dataflow.live_out_regs(block);

        for instr_index in range.start.index()..terminator_ref.index() {
            let instr_ref = InstrRef(instr_index);
            if self.overrides.instr_is_suppressed(instr_ref) {
                continue;
            }
            for def in &self.lowering.dataflow.instr_defs[instr_index] {
                let temp = self.lowering.bindings.fixed_temps[def.index()];
                if condition_prefix_temps.contains(&temp) {
                    continue;
                }
                if live_out.contains(&self.lowering.dataflow.def_reg(*def)) {
                    return true;
                }
            }
        }

        false
    }

    fn lower_repeat_loop(
        &mut self,
        candidate_id: LoopCandidateId,
        candidate: &LoopCandidate,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let preheader = unique_loop_preheader(candidate);
        let continue_block = candidate.continue_target?;
        let (loop_backedge_target, exit) =
            loop_branch_body_and_exit(self.lowering, continue_block, &candidate.blocks)?;
        if let Some(stop) = stop
            && stop != exit
            && candidate.blocks.contains(&stop)
        {
            return None;
        }

        let plan = self.build_loop_state_plan(
            candidate_id,
            candidate,
            preheader,
            exit,
            &[],
            target_overrides,
        )?;
        let combined_target_overrides =
            merge_target_overrides(target_overrides, &plan.backedge_target_overrides);
        let repeat_condition = self
            .lowering
            .structure
            .short_circuit_candidates
            .iter()
            .filter(|short| {
                short.reducible
                    && short.blocks.contains(&continue_block)
                    && match candidate.condition_header {
                        Some(condition_header) => short.header == condition_header,
                        None => short.header != candidate.header,
                    }
            })
            .filter_map(|short| {
                let mut plan = build_branch_short_circuit_plan(self.lowering, short.header)?;
                let body_stop = plan.consumed_headers.first().copied()?;
                (plan.consumed_headers.len() > 1
                    && ((plan.truthy == loop_backedge_target && plan.falsy == exit)
                        || (plan.falsy == loop_backedge_target && plan.truthy == exit))
                    && self.rewrite_short_circuit_skipped_header_prefixes(
                        body_stop,
                        &plan.consumed_headers,
                        &mut plan.cond,
                    ))
                .then_some(plan)
            })
            .next();
        let body_stop = repeat_condition
            .as_ref()
            .and_then(|plan| plan.consumed_headers.first().copied())
            .unwrap_or(continue_block);
        let mut loop_context = self.build_active_loop_context(
            candidate_id,
            candidate,
            exit,
            &combined_target_overrides,
            &plan.states,
        )?;
        loop_context.body_stop = Some(body_stop);
        loop_context.loop_blocks = loop_body_blocks(candidate).clone();
        loop_context.state_slots = plan.states.clone();
        let backedge_pad = self.repeat_backedge_pad(
            candidate.header,
            loop_backedge_target,
            &combined_target_overrides,
        )?;
        let mut suppressed = plan
            .states
            .iter()
            .filter_map(|state| state.phi_id)
            .collect::<Vec<_>>();
        suppressed.extend(plan.owned_phis.iter().copied());
        for phi_id in &suppressed {
            self.overrides.suppress_phi(*phi_id);
        }

        self.active_loops.push(loop_context.clone());
        let mut body = self
            .lower_region_with_suppressed_loop(
                candidate.header,
                Some(body_stop),
                &combined_target_overrides,
                Some(candidate_id),
            )?
            .stmts;
        let cond = if let Some(mut condition) = repeat_condition {
            for header in &condition.consumed_headers {
                if let Some(entry_expr_overrides) = self.block_entry_expr_overrides(*header) {
                    rewrite_expr_temps(&mut condition.cond, entry_expr_overrides);
                }
            }
            body.extend(self.lower_block_prefix(body_stop, true, &combined_target_overrides)?);
            self.visited
                .extend(condition.consumed_headers.iter().copied());
            if condition.truthy == exit {
                condition.cond
            } else {
                condition.cond.negate()
            }
        } else {
            body.extend(self.lower_block_prefix(
                continue_block,
                true,
                &combined_target_overrides,
            )?);
            self.visited.insert(continue_block);
            self.lower_branch_cond_for_target(continue_block, exit)?
        };
        self.active_loops.pop();
        for phi_id in suppressed {
            self.overrides.unsuppress_phi(phi_id);
        }

        stmts.extend(loop_state_init_stmts(&plan));
        if let Some(backedge_pad) = backedge_pad {
            self.visited.insert(backedge_pad);
        }
        self.visited.extend(
            loop_context
                .break_exits
                .values()
                .flat_map(|break_exit| break_exit.blocks.iter().copied()),
        );
        self.install_loop_exit_bindings(candidate_id, candidate, exit, &plan, target_overrides);
        stmts.push(HirStmt::Repeat(Box::new(HirRepeat {
            body: HirBlock { stmts: body },
            cond: {
                let mut cond = cond;
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
        let exit = self.lowering.cfg.instr_to_block[init.exit_target.index()];
        let (candidate_id, candidate) =
            self.unique_loop_candidate_matching(header, |candidate| {
                candidate.kind_hint == LoopKindHint::NumericForLike
                    && candidate.preheader == Some(block)
                    && candidate.exits.contains(&exit)
            })?;
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
        let mut plan = self.build_loop_state_plan(
            candidate_id,
            candidate,
            Some(block),
            exit,
            &[init.index],
            target_overrides,
        )?;
        for state in &mut plan.states {
            if state.reg == init.binding {
                // numeric-for 语法本身在每轮初始化 binding；这里只保留
                // state owner 用于嵌套 loop 写回，不在 for 之前再生成赋值。
                state.initialize_target = false;
            }
        }
        self.suppress_unstructured_preheader_state_phis(block, &plan);
        let combined_target_overrides =
            merge_target_overrides(target_overrides, &plan.backedge_target_overrides);
        let mut suppressed = plan
            .states
            .iter()
            .filter_map(|state| state.phi_id)
            .collect::<Vec<_>>();
        suppressed.extend(
            Self::header_values(candidate)
                .filter(|value| value.reg == init.index)
                .map(|value| value.phi_id),
        );
        suppressed.extend(plan.owned_phis.iter().copied());

        self.visited.insert(block);
        stmts.extend(self.lower_block_prefix(block, false, target_overrides)?);
        stmts.extend(loop_state_init_stmts(&plan));

        for phi_id in &suppressed {
            self.overrides.suppress_phi(*phi_id);
        }
        let continue_block = candidate.continue_target.unwrap_or(header);
        let mut loop_context = self.build_active_loop_context(
            candidate_id,
            candidate,
            exit,
            &combined_target_overrides,
            &plan.states,
        )?;
        loop_context.loop_blocks = loop_body_blocks(candidate).clone();
        loop_context.state_slots = plan.states.clone();
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
                    Some(candidate_id),
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
            .extend(candidate.control_blocks.iter().copied());
        self.visited.extend(
            loop_context
                .break_exits
                .values()
                .flat_map(|break_exit| break_exit.blocks.iter().copied()),
        );
        self.install_loop_exit_bindings(candidate_id, candidate, exit, &plan, target_overrides);
        let mut start = expr_for_reg_use(self.lowering, block, instr_ref, init.index);
        let mut limit = expr_for_reg_use(self.lowering, block, instr_ref, init.limit);
        let mut step = expr_for_reg_use(self.lowering, block, instr_ref, init.step);
        if !target_overrides.is_empty() {
            let expr_overrides = temp_expr_overrides(target_overrides);
            rewrite_expr_temps(&mut start, &expr_overrides);
            rewrite_expr_temps(&mut limit, &expr_overrides);
            rewrite_expr_temps(&mut step, &expr_overrides);
        }
        stmts.push(HirStmt::NumericFor(Box::new(HirNumericFor {
            binding,
            start,
            limit,
            step,
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
        let (candidate_id, candidate) =
            self.unique_loop_candidate_matching(header, |candidate| {
                candidate.kind_hint == LoopKindHint::GenericForLike
                    && candidate.continue_target == Some(header)
                    && unique_loop_preheader(candidate) == Some(block)
            })?;
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
        let immediate_break = !candidate.blocks.contains(&body_entry);
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
        let plan = self.build_loop_state_plan(
            candidate_id,
            candidate,
            Some(block),
            exit,
            &excluded_regs,
            target_overrides,
        )?;
        self.suppress_unstructured_preheader_state_phis(block, &plan);
        let combined_target_overrides =
            merge_target_overrides(target_overrides, &plan.backedge_target_overrides);

        self.visited.insert(block);
        stmts.extend(self.lower_block_prefix(block, false, target_overrides)?);
        stmts.extend(loop_state_init_stmts(&plan));
        for phi_id in &plan.owned_phis {
            self.overrides.suppress_phi(*phi_id);
        }

        let mut loop_context = self.build_active_loop_context(
            candidate_id,
            candidate,
            exit,
            &combined_target_overrides,
            &plan.states,
        )?;
        loop_context.loop_blocks = loop_body_blocks(candidate).clone();
        loop_context.state_slots = plan.states.clone();
        self.active_loops.push(loop_context.clone());
        // Structure 不给立即 break 候选分配独立 body block；空循环体或只含
        // `continue` 的 generic-for 则会把 body 编译成 header 自回边。
        let body = if immediate_break {
            // 无独立 body owner 编码的是首轮立即 break；不能降成空 body，否则会继续遍历。
            HirBlock {
                stmts: vec![HirStmt::Break],
            }
        } else if body_entry == header {
            HirBlock { stmts: Vec::new() }
        } else {
            self.lower_region(body_entry, Some(header), &combined_target_overrides)?
        };
        self.active_loops.pop();
        for phi_id in &plan.owned_phis {
            self.overrides.unsuppress_phi(*phi_id);
        }
        self.visited.insert(header);
        self.visited.extend(
            loop_context
                .break_exits
                .values()
                .flat_map(|break_exit| break_exit.blocks.iter().copied()),
        );
        self.install_loop_exit_bindings(candidate_id, candidate, exit, &plan, target_overrides);
        stmts.push(HirStmt::GenericFor(Box::new(HirGenericFor {
            bindings,
            iterator: self
                .lower_generic_for_iterator(header, call_instr_ref, call)
                .into(),
            body,
        })));

        Some(Some(exit))
    }
}

fn temp_refs_in_eval_order(expr: &HirExpr) -> Vec<TempId> {
    let mut refs = Vec::new();
    collect_temp_refs_in_eval_order(expr, &mut refs);
    refs
}

fn collect_temp_refs_in_eval_order(expr: &HirExpr, refs: &mut Vec<TempId>) {
    match expr {
        HirExpr::TempRef(temp) => refs.push(*temp),
        HirExpr::TableAccess(access) => {
            collect_temp_refs_in_eval_order(&access.base, refs);
            collect_temp_refs_in_eval_order(&access.key, refs);
        }
        HirExpr::Unary(unary) => collect_temp_refs_in_eval_order(&unary.expr, refs),
        HirExpr::Binary(binary) => {
            collect_temp_refs_in_eval_order(&binary.lhs, refs);
            collect_temp_refs_in_eval_order(&binary.rhs, refs);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_temp_refs_in_eval_order(&logical.lhs, refs);
            collect_temp_refs_in_eval_order(&logical.rhs, refs);
        }
        HirExpr::Decision(decision) => {
            for node in &decision.nodes {
                collect_temp_refs_in_eval_order(&node.test, refs);
                collect_decision_target_temp_refs(&node.truthy, refs);
                collect_decision_target_temp_refs(&node.falsy, refs);
            }
        }
        HirExpr::Call(call) => {
            collect_temp_refs_in_eval_order(&call.callee, refs);
            for arg in &call.args {
                collect_temp_refs_in_eval_order(arg, refs);
            }
        }
        HirExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    HirTableField::Array(value) => collect_temp_refs_in_eval_order(value, refs),
                    HirTableField::Record(record) => {
                        if let HirTableKey::Expr(key) = &record.key {
                            collect_temp_refs_in_eval_order(key, refs);
                        }
                        collect_temp_refs_in_eval_order(&record.value, refs);
                    }
                }
            }
            if let Some(trailing) = &table.trailing_multivalue {
                collect_temp_refs_in_eval_order(trailing.as_expr(), refs);
            }
        }
        HirExpr::Closure(closure) => {
            for capture in &closure.captures {
                collect_temp_refs_in_eval_order(&capture.value, refs);
            }
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => {}
    }
}

fn collect_decision_target_temp_refs(target: &HirDecisionTarget, refs: &mut Vec<TempId>) {
    if let HirDecisionTarget::Expr(expr) = target {
        collect_temp_refs_in_eval_order(expr, refs);
    }
}
