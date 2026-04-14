//! 这个文件负责 loop state/exit merge 的 HIR 收敛。
//!
//! 它只消费 `StructureFacts` 已经准备好的 loop merge 事实，把这些候选翻成稳定的
//! state temp、entry override 和 exit phi override，不再自己回头拆 `phi.incoming`。
//!
//! 例子：
//! - `while ... do i = i + 1 end` 会把 header merge 翻成一条 loop state，
//!   再把回边 defs 统一改写到同一个 HIR target
//! - `if cond then break end` 形成的 exit merge，会在确认“循环外初值”和当前 state
//!   属于同一个语义槽位后，直接复用已有 loop state，而不是再物化一层假的 phi

use super::*;

impl<'a, 'b> StructuredBodyLowerer<'a, 'b> {
    pub(super) fn build_loop_state_plan(
        &self,
        candidate: &LoopCandidate,
        preheader: Option<BlockRef>,
        exit: BlockRef,
        excluded_regs: &[Reg],
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<LoopStatePlan> {
        // loop header 的 phi 在 HIR 里需要被"拆 SSA"成稳定的循环状态变量。
        // 这里先把进入循环前的初值、回边写回目标和退出循环后的可见身份一次性整理好，
        // 避免后面再靠局部规则去猜"这个 phi 其实是 while/repeat/for 的状态"。
        let excluded = excluded_regs.iter().copied().collect::<BTreeSet<_>>();
        let mut plan = LoopStatePlan::default();

        for value in Self::header_values(candidate) {
            if excluded.contains(&value.reg) {
                continue;
            }

            // outside_arm.defs 为空 → preheader 处该寄存器不存在显式定义。
            // 两种可能：
            //  1) 内层循环控制寄存器的幻影 phi：外层循环不关心这个寄存器，
            //     exit phi 也不引用它 → 安全跳过。
            //  2) nil 初始化的循环携带变量（如 `local last_positive`）：
            //     循环结束后仍需使用（exit phi 引用了该寄存器）→ 用 nil 作为初值。
            let init = match self.loop_entry_expr(preheader?, value, target_overrides) {
                Some(init) => init,
                None => {
                    if value.outside_arm.defs().count() == 0 {
                        if Self::exit_value_for_reg(candidate, exit, value.reg).is_some() {
                            HirExpr::Nil
                        } else {
                            continue;
                        }
                    } else {
                        return None;
                    }
                }
            };
            let temp = *self.lowering.bindings.phi_temps.get(value.phi_id.index())?;
            let target = self.loop_state_target(candidate, exit, value.reg, temp, target_overrides);
            plan.backedge_target_overrides.insert(temp, target.clone());
            // phi_use_count == 0 表示循环体内没有指令直接读取 phi 的 SSA 值——如果该
            // 寄存器同样不出现在 exit phi 中，说明它只是被借用来做临时运算（如内层
            // for-loop 控制变量），可以跳过 inside_arm 重定向，让体内定义保留为独立
            // temp 供 inline pass 折叠。但如果 exit phi 引用了该寄存器，则循环体
            // 内的写入仍需路由到 state target，否则出口处拿不到正确的值。
            if self.lowering.dataflow.phi_use_count(value.phi_id) > 0
                || Self::exit_value_for_reg(candidate, exit, value.reg).is_some()
            {
                for def in value.inside_arm.defs() {
                    let def_temp = *self.lowering.bindings.fixed_temps.get(def.index())?;
                    plan.backedge_target_overrides
                        .insert(def_temp, target.clone());
                }
            }

            plan.states.push(LoopStateSlot {
                phi_id: value.phi_id,
                reg: value.reg,
                temp,
                target,
                init,
            });
        }

        // exit phi 的 incoming 里可能混入 break exit pad 块（形如"先做 cleanup，
        // 再 jump 到 post-loop"的线性垫片）。它们在 CFG 上不属于 candidate.blocks，
        // 但语义上传递的仍是循环体内部的值。这里和 install_loop_exit_bindings 保持一致，
        // 把这些 pad 块也视为"循环内"来计算 outside-arm 的唯一初值。
        let inside_exit_blocks = self
            .loop_state_inside_exit_blocks(candidate, exit)
            .unwrap_or_else(|| candidate.blocks.clone());

        for value in Self::exit_values(candidate, exit) {
            if excluded.contains(&value.reg)
                || plan.states.iter().any(|state| state.reg == value.reg)
                || !loop_value_has_inside_and_outside_incoming(value)
                || self.exit_value_is_owned_by_inherited_state(value, target_overrides)
            {
                continue;
            }

            let Some(init) = self.loop_exit_entry_expr_with_inside_blocks(
                value,
                &inside_exit_blocks,
                target_overrides,
            ) else {
                // exit-only merge 只是“循环结束后也许还能继续复用这条 state”的附加收益，
                // 不是 numeric-for / generic-for 能否结构化的必要前提。
                // 如果循环外 incoming 本身已经是多路语义合流，强行要求这里解出唯一初值，
                // 只会把本来能安全恢复的 loop 整片打回 label/goto。
                continue;
            };
            let temp = *self.lowering.bindings.phi_temps.get(value.phi_id.index())?;
            let target = self.loop_state_target(candidate, exit, value.reg, temp, target_overrides);
            plan.backedge_target_overrides.insert(temp, target.clone());
            if self.lowering.dataflow.phi_use_count(value.phi_id) > 0 {
                for def in value.inside_arm.defs() {
                    let def_temp = *self.lowering.bindings.fixed_temps.get(def.index())?;
                    plan.backedge_target_overrides
                        .insert(def_temp, target.clone());
                }
            }

            plan.states.push(LoopStateSlot {
                phi_id: value.phi_id,
                reg: value.reg,
                temp,
                target,
                init,
            });
        }

        Some(plan)
    }

    fn loop_entry_expr(
        &self,
        preheader: BlockRef,
        value: &LoopValueMerge,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirExpr> {
        let incoming = value.outside_arm.incoming_for_pred(preheader)?;
        self.loop_incoming_expr(
            preheader,
            value.reg,
            incoming.defs.iter().copied(),
            target_overrides,
        )
    }

    fn loop_exit_entry_expr_with_inside_blocks(
        &self,
        value: &LoopValueMerge,
        inside_blocks: &BTreeSet<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirExpr> {
        let mut init_expr = None;

        for incoming in value
            .inside_arm
            .incomings
            .iter()
            .chain(value.outside_arm.incomings.iter())
            .filter(|incoming| !inside_blocks.contains(&incoming.pred))
        {
            let expr = self.loop_incoming_expr(
                incoming.pred,
                value.reg,
                incoming.defs.iter().copied(),
                target_overrides,
            )?;
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
        defs: impl IntoIterator<Item = crate::cfg::DefId>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirExpr> {
        let defs = defs.into_iter().collect::<Vec<_>>();

        // 某些 loop 会直接跟在另一个已经结构化的 region 后面。此时 CFG/Dataflow 视角里，
        // predecessor 边上同一寄存器可能仍然带着“多个原始 def 合流”的痕迹；但对 HIR 来说，
        // 前一个结构已经把它稳定成了 entry override。这里只在 predecessor 本身没有再次改写
        // 该寄存器时，沿用这份 override，避免把同一个语义槽位重新打回 unresolved phi。
        if let Some(expr) = self.overrides.carried_entry_expr(pred, reg) {
            return Some(expr.clone());
        }

        if let Some(expr) =
            shared_expr_for_defs(&self.lowering.bindings.fixed_temps, defs.iter().copied(), target_overrides)
        {
            return Some(expr);
        }

        if let Some(expr) = single_fixed_def_expr(self.lowering, defs.iter().copied()) {
            return Some(expr);
        }

        // 嵌套 loop 的 preheader 上，某个寄存器的 reaching defs 可能包含多个原始定义
        // （初值 + 内层循环回边写入），但在 reaching values 视角里它们早已被外层 loop 的
        // header phi 合并成唯一的 SSA value。如果该 phi 对应的 temp 已经被外层 loop state
        // plan 收录到 target_overrides 里，就可以直接沿用。
        // 典型触发场景：外层 while 的 phi_use_count == 0（没有指令直接读取该 phi，只经由
        // 内层 loop phi 间接消费），此时外层 plan 不把 inside_arm 的原始 def temps 加入
        // override map，导致 shared_expr_for_defs 无法匹配。
        self.reaching_phi_override_expr(pred, reg, target_overrides)
    }

    /// 查找 `pred` 块首条指令的 reaching values 里，`reg` 是否只有一个 phi，
    /// 并且该 phi 的 temp 已在 `target_overrides` 中。
    fn reaching_phi_override_expr(
        &self,
        pred: BlockRef,
        reg: Reg,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirExpr> {
        use crate::cfg::SsaValue;

        let first_instr = self.lowering.cfg.blocks[pred.index()].instrs.start;
        let reaching = self.lowering.dataflow.reaching_values_at(first_instr);
        let values = reaching.get(reg)?;

        let mut phi_ids = values.iter().filter_map(|v| match v {
            SsaValue::Phi(phi_id) => Some(phi_id),
            SsaValue::Def(_) => None,
        });
        let phi_id = phi_ids.next()?;
        if phi_ids.next().is_some() {
            return None;
        }

        let temp = *self.lowering.bindings.phi_temps.get(phi_id.index())?;
        let lvalue = target_overrides.get(&temp)?;
        lvalue_as_expr(lvalue)
    }

    pub(super) fn install_loop_exit_bindings(
        &mut self,
        candidate: &LoopCandidate,
        exit: BlockRef,
        plan: &LoopStatePlan,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) {
        if plan.states.is_empty() {
            return;
        }

        for state in &plan.states {
            let Some(state_expr) = lvalue_as_expr(&state.target) else {
                continue;
            };
            self.install_entry_override(exit, state.reg, state_expr);
        }
        let inside_exit_blocks = self
            .loop_state_inside_exit_blocks(candidate, exit)
            .unwrap_or_else(|| candidate.blocks.clone());

        for value in Self::exit_values(candidate, exit) {
            let Some(state) = plan.states.iter().find(|state| state.reg == value.reg) else {
                continue;
            };
            let Some(state_expr) = lvalue_as_expr(&state.target) else {
                continue;
            };
            // break 先落在线性 cleanup pad、再跳到 post-loop continuation 时，
            // exit phi 的 incoming 里会混进这些 pad block。它们虽然 CFG 上已不在
            // `candidate.blocks` 内，但语义上仍然是 loop state 的内部出口。
            if loop_value_incoming_all_within_blocks(value, &inside_exit_blocks) {
                self.replace_phi_with_target_expr(exit, value.phi_id, state.temp, state_expr);
                continue;
            }
            let Some(exit_init) = self.loop_exit_entry_expr_with_inside_blocks(
                value,
                &inside_exit_blocks,
                target_overrides,
            ) else {
                continue;
            };
            // 只有当 exit phi 的“循环外初值”与当前 loop state 的初值确实是同一个语义槽位时，
            // 才能直接把 exit merge 认成这条 loop state。否则像外层 if/elseif/else 包着 loop
            // 的 case，exit block 上同寄存器号的 phi 还在和其他分支路径合流，不能被 loop state
            // 直接顶掉。
            if exit_init != state.init {
                continue;
            }
            self.replace_phi_with_target_expr(exit, value.phi_id, state.temp, state_expr);
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

        if let Some(target) =
            self.uniform_loop_exit_target_override(candidate, exit, reg, target_overrides)
        {
            return target;
        }

        // 嵌套循环场景：内层 loop 和外层 loop 可能在同一个寄存器上建立各自的 header phi。
        // 外层 loop 的 phi_use_count 可能为 0（因为没有指令直接读取外层 phi，而是通过内层
        // phi 间接消费）。此时外层 plan 不会把 inside_arm defs 加入 target_overrides，
        // 导致前面几个检查都无法匹配到外层的 state target。
        // 这里通过 preheader 上的 reaching values 查找是否存在一个已由外层收纳的 phi，
        // 如果存在就直接沿用外层的 state target，使得内层循环的写入自动传播到外层变量。
        if let Some(preheader) = unique_loop_preheader(candidate)
            && let Some(target) =
                self.reaching_phi_lvalue_override(preheader, reg, target_overrides)
        {
            return target;
        }

        HirLValue::Temp(temp)
    }

    /// 查找 `block` 首条指令的 reaching values 里，`reg` 是否只有一个 phi，
    /// 并且该 phi 的 temp 已在 `target_overrides` 中——返回对应的 `HirLValue`。
    ///
    /// 与 `reaching_phi_override_expr` 平行，这里返回 lvalue 而非 expr，供
    /// `loop_state_target` 直接用作内层 loop 的 state 写入目标。
    fn reaching_phi_lvalue_override(
        &self,
        block: BlockRef,
        reg: Reg,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirLValue> {
        use crate::cfg::SsaValue;

        let first_instr = self.lowering.cfg.blocks[block.index()].instrs.start;
        let reaching = self.lowering.dataflow.reaching_values_at(first_instr);
        let values = reaching.get(reg)?;

        let mut phi_ids = values.iter().filter_map(|v| match v {
            SsaValue::Phi(phi_id) => Some(phi_id),
            SsaValue::Def(_) => None,
        });
        let phi_id = phi_ids.next()?;
        if phi_ids.next().is_some() {
            return None;
        }

        let temp = *self.lowering.bindings.phi_temps.get(phi_id.index())?;
        let lvalue = target_overrides.get(&temp)?;
        lvalue_as_expr(lvalue)?;
        Some(lvalue.clone())
    }

    fn exit_value_is_owned_by_inherited_state(
        &self,
        value: &LoopValueMerge,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> bool {
        let phi_temp = self.lowering.bindings.phi_temps[value.phi_id.index()];
        if target_overrides.contains_key(&phi_temp) {
            return true;
        }

        for def in value.inside_arm.defs() {
            let def_temp = self.lowering.bindings.fixed_temps[def.index()];
            if target_overrides.contains_key(&def_temp) {
                return true;
            }
        }

        false
    }

    fn uniform_loop_header_target_override(
        &self,
        candidate: &LoopCandidate,
        reg: Reg,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirLValue> {
        let value = Self::header_value_for_reg(candidate, reg)?;
        self.shared_loop_inside_target(&value.inside_arm, target_overrides)
    }

    fn uniform_loop_exit_target_override(
        &self,
        candidate: &LoopCandidate,
        exit: BlockRef,
        reg: Reg,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirLValue> {
        if let Some(value) = Self::exit_value_for_reg(candidate, exit, reg) {
            if !loop_value_has_inside_and_outside_incoming(value) {
                return None;
            }
            if let Some(target) =
                self.shared_loop_inside_target(&value.inside_arm, target_overrides)
            {
                return Some(target);
            }
        }

        None
    }

    fn shared_loop_inside_target(
        &self,
        arm: &LoopValueArm,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirLValue> {
        shared_lvalue_for_defs(
            &self.lowering.bindings.fixed_temps,
            arm.defs(),
            target_overrides,
        )
    }

    pub(super) fn header_values(
        candidate: &LoopCandidate,
    ) -> impl Iterator<Item = &LoopValueMerge> {
        candidate.header_value_merges.iter()
    }

    pub(super) fn header_value_for_reg(
        candidate: &LoopCandidate,
        reg: Reg,
    ) -> Option<&LoopValueMerge> {
        Self::header_values(candidate).find(|value| value.reg == reg)
    }

    pub(super) fn exit_values(
        candidate: &LoopCandidate,
        exit: BlockRef,
    ) -> impl Iterator<Item = &LoopValueMerge> {
        candidate
            .exit_value_merges
            .iter()
            .find(|candidate| candidate.exit == exit)
            .into_iter()
            .flat_map(|candidate| candidate.values.iter())
    }

    pub(super) fn exit_value_for_reg(
        candidate: &LoopCandidate,
        exit: BlockRef,
        reg: Reg,
    ) -> Option<&LoopValueMerge> {
        Self::exit_values(candidate, exit).find(|value| value.reg == reg)
    }

    pub(super) fn build_active_loop_context(
        &self,
        candidate: &LoopCandidate,
        post_loop: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
        states: &[LoopStateSlot],
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
                self.lower_break_exit_pad(exit, post_loop, downstream_post_loop, target_overrides, states)?,
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
            loop_blocks: BTreeSet::new(),
            post_loop,
            downstream_post_loop,
            continue_target,
            continue_sources,
            break_exits,
            state_slots: Vec::new(),
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
            self.lower_break_exit_pad(exit, post_loop, downstream_post_loop, &BTreeMap::new(), &[])?;
            inside_blocks.insert(exit);
        }
        Some(inside_blocks)
    }

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

    fn lower_break_exit_pad(
        &self,
        block: BlockRef,
        post_loop: BlockRef,
        downstream_post_loop: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
        states: &[LoopStateSlot],
    ) -> Option<HirBlock> {
        // 这里只接受"线性的 break 垫片 block"：它允许先做一些必须保留的 cleanup，
        // 但最终必须无条件跳到循环之后的统一 continuation。更复杂的 exit 形状留给后续轮次，
        // 避免这一步又退化成拼命堆 break 特判。
        //
        // break pad 里的赋值（如 `found = true; idx = i`）写入的 def temp 与 loop 回边
        // 上的 phi temp 不同，因此仅靠 combined_target_overrides 无法将它们重定向到
        // 循环 state 变量。这里额外扫描 pad 的 def，把匹配 state 寄存器的 def temp
        // 也加入 override map，使 apply_loop_rewrites 能正确替换。
        let mut combined = target_overrides.clone();
        if !states.is_empty() {
            let range = self.lowering.cfg.blocks[block.index()].instrs;
            for instr_index in range.start.index()..range.end() {
                for def_id in &self.lowering.dataflow.instr_defs[instr_index] {
                    let def = &self.lowering.dataflow.defs[def_id.index()];
                    if let Some(state) = states.iter().find(|s| s.reg == def.reg) {
                        let temp = self.lowering.bindings.fixed_temps[def_id.index()];
                        combined.insert(temp, state.target.clone());
                    }
                }
            }
        }
        let mut stmts = self.lower_block_prefix(block, false, &combined)?;
        let target = match self.block_terminator(block) {
            Some((_instr_ref, LowInstr::Jump(jump))) => {
                self.lowering.cfg.instr_to_block[jump.target.index()]
            }
            // Lua 5.4 的 close/capture cleanup pad 很常见的一种形状是“只有 cleanup，
            // 然后直接 fallthrough 到 post-loop continuation”。如果这里仍然硬要求
            // 显式 jump，像 `while ... if ... break end` 这种明明已经结构化的 loop
            // 也会整片回退成 label/goto。
            Some((_instr_ref, instr)) if !is_control_terminator(instr) => {
                self.lowering.cfg.unique_reachable_successor(block)?
            }
            None => self.lowering.cfg.unique_reachable_successor(block)?,
            Some(_) => return None,
        };
        if target != post_loop && Some(target) != downstream_post_loop {
            return None;
        }

        stmts.push(HirStmt::Break);
        Some(HirBlock { stmts })
    }

    pub(super) fn generic_for_header_instrs(
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

    pub(super) fn lower_generic_for_iterator(
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

    pub(super) fn block_prefix_temp_expr_overrides(
        &self,
        block: BlockRef,
    ) -> BTreeMap<TempId, HirExpr> {
        let range = self.lowering.cfg.blocks[block.index()].instrs;
        if range.is_empty() {
            return BTreeMap::new();
        }

        let end = if let Some((_instr_ref, instr)) = self.block_terminator(block) {
            if is_control_terminator(instr) {
                range.end() - 1
            } else {
                range.end()
            }
        } else {
            range.end()
        };

        let mut expr_overrides = BTreeMap::new();
        for instr_index in range.start.index()..end {
            let instr_ref = InstrRef(instr_index);
            if self.overrides.instr_is_suppressed(instr_ref) {
                continue;
            }
            for def in &self.lowering.dataflow.instr_defs[instr_index] {
                let Some(mut expr) = expr_for_fixed_def(self.lowering, *def) else {
                    continue;
                };
                rewrite_expr_temps(&mut expr, &expr_overrides);
                expr_overrides.insert(self.lowering.bindings.fixed_temps[def.index()], expr);
            }
        }

        expr_overrides
    }
}
