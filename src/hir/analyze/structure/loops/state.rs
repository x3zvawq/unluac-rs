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
use crate::structure::SsaValue;

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
        let mut planned_regs = BTreeSet::new();

        for value in Self::header_values(candidate) {
            if excluded.contains(&value.reg) {
                continue;
            }

            // outside_arm.defs 为空 → preheader 处该寄存器不存在显式定义。
            // 两种可能：
            //  1) 内层循环控制寄存器的幻影 phi：外层循环不关心这个寄存器，
            //     exit phi 也不引用它 → 安全跳过。
            //  2) nil 初始化的循环携带变量（如 `local last_positive`）：
            //     循环体或循环结束后仍需使用 → 用 nil 作为初值。
            let init = match self.loop_entry_expr(preheader, value, target_overrides) {
                Some(init) => init,
                None => {
                    if value.outside_arm.defs().count() == 0 {
                        if self.lowering.dataflow.phi_use_count(value.phi_id) > 0
                            || Self::exit_value_for_reg(candidate, exit, value.reg).is_some()
                        {
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
                phi_id: Some(value.phi_id),
                reg: value.reg,
                target,
                init,
            });
            planned_regs.insert(value.reg);
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
                || planned_regs.contains(&value.reg)
                || !loop_value_has_inside_and_outside_incoming(value)
                || self.exit_value_is_owned_by_inherited_state(value, target_overrides)
            {
                continue;
            }

            let Some(init) = self
                .loop_exit_entry_expr_with_inside_blocks(
                    value,
                    &inside_exit_blocks,
                    target_overrides,
                )
                .or_else(|| {
                    self.loop_exit_state_preheader_init(
                        preheader,
                        value,
                        &inside_exit_blocks,
                        target_overrides,
                    )
                })
            else {
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
                phi_id: Some(value.phi_id),
                reg: value.reg,
                target,
                init,
            });
            planned_regs.insert(value.reg);
        }

        self.add_loop_live_out_states(
            candidate,
            preheader,
            exit,
            &excluded,
            target_overrides,
            &mut plan,
        );

        Some(plan)
    }

    fn add_loop_live_out_states(
        &self,
        candidate: &LoopCandidate,
        preheader: Option<BlockRef>,
        exit: BlockRef,
        excluded: &BTreeSet<Reg>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
        plan: &mut LoopStatePlan,
    ) {
        let range = self.lowering.cfg.blocks[exit.index()].instrs;
        if range.is_empty() {
            return;
        }
        let live_in = self.lowering.dataflow.live_in_regs(exit);
        let reaching = self.lowering.dataflow.reaching_values_at(range.start);
        let mut planned_regs = plan
            .states
            .iter()
            .map(|state| state.reg)
            .collect::<BTreeSet<_>>();

        for reg in live_in {
            if excluded.contains(reg) || planned_regs.contains(reg) {
                continue;
            }
            let Some(values) = reaching.get(*reg) else {
                continue;
            };
            let values = values.iter().collect::<Vec<_>>();
            if values.is_empty()
                || !values
                    .iter()
                    .all(|value| self.value_belongs_to_loop(candidate, *value))
            {
                continue;
            }
            let Some(temp) = self.live_out_state_temp(&values) else {
                continue;
            };
            let mut init = preheader
                .map(|preheader| expr_for_reg_at_block_exit(self.lowering, preheader, *reg))
                .or_else(|| {
                    Self::header_values(candidate)
                        .find(|value| value.reg == *reg)
                        .and_then(|value| self.multi_entry_loop_entry_expr(value, target_overrides))
                })
                .unwrap_or_else(|| self.loop_entry_initial_expr(*reg));
            rewrite_expr_temps(&mut init, &temp_expr_overrides(target_overrides));
            let target = target_overrides
                .get(&temp)
                .filter(|target| lvalue_as_expr(target).is_some())
                .cloned()
                .unwrap_or(HirLValue::Temp(temp));

            for value in values {
                match value {
                    SsaValue::Def(def) => {
                        let def_temp = self.lowering.bindings.fixed_temps[def.index()];
                        plan.backedge_target_overrides
                            .insert(def_temp, target.clone());
                    }
                    SsaValue::Phi(phi_id) => {
                        let phi_temp = self.lowering.bindings.phi_temps[phi_id.index()];
                        plan.backedge_target_overrides
                            .insert(phi_temp, target.clone());
                    }
                }
            }
            plan.states.push(LoopStateSlot {
                phi_id: None,
                reg: *reg,
                target,
                init,
            });
            planned_regs.insert(*reg);
        }
    }

    fn value_belongs_to_loop(&self, candidate: &LoopCandidate, value: SsaValue) -> bool {
        match value {
            SsaValue::Def(def) => candidate
                .blocks
                .contains(&self.lowering.dataflow.def_block(def)),
            SsaValue::Phi(phi_id) => candidate
                .blocks
                .contains(&self.lowering.dataflow.phi_candidates[phi_id.index()].block),
        }
    }

    fn live_out_state_temp(&self, values: &[SsaValue]) -> Option<TempId> {
        values.iter().find_map(|value| match *value {
            SsaValue::Def(def) => self.lowering.bindings.fixed_temps.get(def.index()).copied(),
            SsaValue::Phi(phi_id) => self
                .lowering
                .bindings
                .phi_temps
                .get(phi_id.index())
                .copied(),
        })
    }

    fn loop_exit_state_preheader_init(
        &self,
        preheader: Option<BlockRef>,
        value: &LoopValueMerge,
        inside_exit_blocks: &BTreeSet<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirExpr> {
        if !loop_value_incoming_all_within_blocks(value, inside_exit_blocks) {
            return None;
        }
        let preheader = preheader?;

        // 有些 generic/numeric for 会用“循环前默认值 + break pad 写入”的方式
        // 表达循环查找结果：`found = false; for ... do found = true; break end`。
        // exit phi 的 incoming 全部来自 loop body 或 break pad 后，已经没有一个
        // CFG predecessor 能代表“循环外初值”，但源码初值仍然在 preheader 出口。
        // 这时把 preheader 出口值作为 loop state 初值，才能让 break pad 写回同一
        // 个状态槽位，而不是在 post-loop 条件里留下孤立 phi temp。
        let mut expr = expr_for_reg_at_block_exit(self.lowering, preheader, value.reg);
        rewrite_expr_temps(&mut expr, &temp_expr_overrides(target_overrides));
        Some(expr)
    }

    fn loop_entry_expr(
        &self,
        preheader: Option<BlockRef>,
        value: &LoopValueMerge,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirExpr> {
        match preheader {
            Some(preheader) => {
                let incoming = value.outside_arm.incoming_for_pred(preheader)?;
                self.loop_incoming_expr(
                    preheader,
                    value.reg,
                    incoming.defs.iter().copied(),
                    target_overrides,
                )
            }
            None => self.multi_entry_loop_entry_expr(value, target_overrides),
        }
    }

    fn multi_entry_loop_entry_expr(
        &self,
        value: &LoopValueMerge,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirExpr> {
        self.uniform_loop_incoming_expr(
            value.reg,
            value.outside_arm.incomings.iter(),
            target_overrides,
        )
    }

    fn loop_exit_entry_expr_with_inside_blocks(
        &self,
        value: &LoopValueMerge,
        inside_blocks: &BTreeSet<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirExpr> {
        let outside_incomings = value
            .inside_arm
            .incomings
            .iter()
            .chain(value.outside_arm.incomings.iter())
            .filter(|incoming| {
                incoming
                    .pred
                    .is_none_or(|pred| !inside_blocks.contains(&pred))
            });
        self.uniform_loop_incoming_expr(value.reg, outside_incomings, target_overrides)
    }

    fn uniform_loop_incoming_expr<'c>(
        &self,
        reg: Reg,
        incomings: impl IntoIterator<Item = &'c crate::structure::LoopValueIncoming>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirExpr> {
        let raw_target_overrides = BTreeMap::new();

        uniform_mapped_value(incomings, |incoming| match incoming.pred {
            Some(pred) => self
                .loop_incoming_expr_without_carried_override(
                    pred,
                    reg,
                    incoming.defs.iter().copied(),
                    &raw_target_overrides,
                )
                .or_else(|| {
                    self.loop_incoming_expr_without_carried_override(
                        pred,
                        reg,
                        incoming.defs.iter().copied(),
                        target_overrides,
                    )
                })
                .or_else(|| {
                    self.loop_incoming_expr(
                        pred,
                        reg,
                        incoming.defs.iter().copied(),
                        target_overrides,
                    )
                }),
            None => Some(self.loop_entry_initial_expr(reg)),
        })
    }

    fn uniform_loop_incoming_lvalue<'c>(
        &self,
        reg: Reg,
        incomings: impl IntoIterator<Item = &'c crate::structure::LoopValueIncoming>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirLValue> {
        let raw_target_overrides = BTreeMap::new();

        uniform_mapped_value(incomings, |incoming| match incoming.pred {
            Some(pred) => self
                .loop_incoming_lvalue_without_carried_override(
                    pred,
                    reg,
                    incoming.defs.iter().copied(),
                    &raw_target_overrides,
                )
                .or_else(|| {
                    self.loop_incoming_lvalue_without_carried_override(
                        pred,
                        reg,
                        incoming.defs.iter().copied(),
                        target_overrides,
                    )
                })
                .or_else(|| {
                    self.loop_incoming_lvalue(
                        pred,
                        reg,
                        incoming.defs.iter().copied(),
                        target_overrides,
                    )
                }),
            None => expr_as_lvalue(&self.loop_entry_initial_expr(reg)),
        })
    }

    fn loop_entry_initial_expr(&self, reg: Reg) -> HirExpr {
        if reg.index() < self.lowering.bindings.params.len() {
            expr_for_entry_reg(self.lowering, reg)
        } else if let Some(local) = self.lowering.bindings.entry_local_regs.get(&reg) {
            HirExpr::LocalRef(*local)
        } else {
            HirExpr::Nil
        }
    }

    fn loop_incoming_expr(
        &self,
        pred: BlockRef,
        reg: Reg,
        defs: impl IntoIterator<Item = crate::structure::DefId>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirExpr> {
        self.loop_incoming_expr_with_carried_override(pred, reg, defs, target_overrides, true)
    }

    fn loop_incoming_expr_without_carried_override(
        &self,
        pred: BlockRef,
        reg: Reg,
        defs: impl IntoIterator<Item = crate::structure::DefId>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirExpr> {
        self.loop_incoming_expr_with_carried_override(pred, reg, defs, target_overrides, false)
    }

    fn loop_incoming_expr_with_carried_override(
        &self,
        pred: BlockRef,
        reg: Reg,
        defs: impl IntoIterator<Item = crate::structure::DefId>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
        allow_carried_override: bool,
    ) -> Option<HirExpr> {
        let defs = defs.into_iter().collect::<Vec<_>>();

        // 某些 loop 会直接跟在另一个已经结构化的 region 后面。此时 CFG/Dataflow 视角里，
        // predecessor 边上同一寄存器可能仍然带着“多个原始 def 合流”的痕迹；但对 HIR 来说，
        // 前一个结构已经把它稳定成了 entry override。这里只在 predecessor 本身没有再次改写
        // 该寄存器时，沿用这份 override，避免把同一个语义槽位重新打回 unresolved phi。
        if allow_carried_override && let Some(expr) = self.overrides.carried_entry_expr(pred, reg) {
            return Some(expr.clone());
        }

        if let Some(expr) = shared_expr_for_defs(
            &self.lowering.bindings.fixed_temps,
            defs.iter().copied(),
            target_overrides,
        ) {
            return Some(expr);
        }

        if let Some(expr) = single_fixed_def_expr(self.lowering, defs.iter().copied()) {
            return Some(expr);
        }

        if defs.len() > 1 {
            let mut expr = expr_for_reg_at_block_exit(self.lowering, pred, reg);
            rewrite_expr_temps(&mut expr, &temp_expr_overrides(target_overrides));
            return Some(expr);
        }

        // 嵌套 loop 的 preheader 上，某个寄存器的 reaching defs 可能包含多个原始定义
        // （初值 + 内层循环回边写入），但在 reaching values 视角里它们早已被外层 loop 的
        // header phi 合并成唯一的 SSA value。如果该 phi 对应的 temp 已经被外层 loop state
        // plan 收录到 target_overrides 里，就可以直接沿用。
        // 典型触发场景：外层 while 的 phi_use_count == 0（没有指令直接读取该 phi，只经由
        // 内层 loop phi 间接消费），此时外层 plan 不把 inside_arm 的原始 def temps 加入
        // override map，导致 shared_expr_for_defs 无法匹配。
        if let Some(expr) = self.reaching_phi_override_expr(pred, reg, target_overrides) {
            return Some(expr);
        }

        // 空 defs + 该 pred 入口处也没有任何 reaching value → 该寄存器从未写过，
        // 语义等价于未初始化 local，即 Lua 里的 nil。典型触发：函数入口是 loop
        // preheader，携带变量（如 `local found = nil`）并没有显式的 LOADNIL，
        // 编译器依赖栈槽默认 nil。此时 exit phi 的 preheader 分支如果不被识别成
        // nil，外层 loop state 与 exit 值的初值就对不上，phi 只能作为孤立 temp
        // 被生成到 HIR 里。
        if defs.is_empty() && self.pred_has_no_reaching_value(pred, reg) {
            return Some(HirExpr::Nil);
        }

        None
    }

    /// 判断 `pred` 块入口处 `reg` 是否完全没有 reaching value（既无 def 也无 phi）。
    ///
    /// 用于 `loop_incoming_expr` 里的“空 defs → Nil”兜底。只在 pred 本身没有再次
    /// 写该寄存器的情况下成立，否则 pred 内部的写入会在 edge 上提供一个真正的 def。
    fn pred_has_no_reaching_value(&self, pred: BlockRef, reg: Reg) -> bool {
        let range = self.lowering.cfg.blocks[pred.index()].instrs;
        if range.is_empty() {
            return false;
        }
        let values = self.lowering.dataflow.reaching_values_at(range.start);
        let entry_empty = values.get(reg).is_none_or(|set| set.is_empty());
        if !entry_empty {
            return false;
        }
        // pred 内部如果有任何 def 写到该寄存器，edge 上就不再是 undef。
        !(range.start.index()..range.end()).any(|instr_index| {
            let effect = &self.lowering.dataflow.instr_effects[instr_index];
            effect.fixed_must_defs.contains(&reg) || effect.fixed_may_defs.contains(&reg)
        })
    }

    /// 查找 `pred` 块首条指令的 reaching values 里，`reg` 是否只有一个 phi，
    /// 并且该 phi 的 temp 已在 `target_overrides` 中。
    fn reaching_phi_override_expr(
        &self,
        pred: BlockRef,
        reg: Reg,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirExpr> {
        let target = self.reaching_phi_target_override(pred, reg, target_overrides)?;
        lvalue_as_expr(target)
    }

    pub(super) fn install_loop_exit_bindings(
        &mut self,
        candidate: &LoopCandidate,
        exit: BlockRef,
        plan: &LoopStatePlan,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) {
        // 即便当前 loop 自己没有任何 state（比如 numeric-for 的整个携带变量都被
        // 外层 loop 接管，本地 plan 只剩 index 这种被 excluded 的寄存器），exit phi
        // 里仍然可能有需要借助外层 target_overrides 重定向的 phi。这些 phi 如果在
        // 这里被跳过，就会在后续 branch 条件 / post-loop 引用里残留成悬空 temp。

        for state in &plan.states {
            let Some(state_expr) = lvalue_as_expr(&state.target) else {
                continue;
            };
            self.install_entry_override(exit, state.reg, state_expr);
        }
        let inside_exit_blocks = self
            .loop_state_inside_exit_blocks(candidate, exit)
            .unwrap_or_else(|| candidate.blocks.clone());

        let state_by_reg = state_slots_by_reg(&plan.states);
        self.apply_exit_phi_bindings(
            candidate,
            exit,
            &inside_exit_blocks,
            &state_by_reg,
            target_overrides,
        );

        // branch_exit 本身可能只是一条 "cond 不成立 → JMP 到真正 post-loop" 的
        // 线性 pad（典型触发：lua5.4 下 `while cond do ... goto L end` 让
        // normal-exit 和 goto-exit 在同一个 continuation 合流）。结构层已经把
        // 合并点记在 exit_value_merges 里指向下游真正的 continuation，但
        // lower_while_loop 只把 branch_exit 作为 `exit` 传下来，phi 在当前
        // `exit` 上找不到对应 state，也不会在下游物化成赋值。结果 post-loop
        // 里引用 reg 的指令最终只能绑到一批悬空 phi temp，naming 再按悬空
        // temp 直接声明一组未初始化的 local，从而把 print(outer,inner,total)
        // 错写成 print(<uninit>, <uninit>, <uninit>)。
        //
        // 这里沿着 exit 的唯一线性后继再做一次替换：此时 `exit` 本身已经是
        // pad，必须把它加到 inside_exit_blocks，下游 exit phi 的“从 pad 过来”
        // 那条 outside incoming 才能被认成“仍在循环内侧”，从而被顶成同一条
        // loop state。
        if let Some(downstream) = self.normalized_post_loop_successor(exit) {
            let mut inside_with_pad = inside_exit_blocks.clone();
            inside_with_pad.insert(exit);
            self.apply_exit_phi_bindings(
                candidate,
                downstream,
                &inside_with_pad,
                &state_by_reg,
                target_overrides,
            );
        }
    }

    /// 在指定 block 上尝试把 loop exit phi 替换成对应的 loop state 表达式。
    ///
    /// 抽出这段逻辑是为了让 `install_loop_exit_bindings` 可以在 `branch_exit`
    /// 自身以及它下游的线性 continuation 上各跑一遍，而不在两处复制分支判定。
    fn apply_exit_phi_bindings(
        &mut self,
        candidate: &LoopCandidate,
        at_block: BlockRef,
        inside_exit_blocks: &BTreeSet<BlockRef>,
        state_by_reg: &BTreeMap<Reg, &LoopStateSlot>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) {
        for value in Self::exit_values(candidate, at_block) {
            if let Some(state) = state_by_reg.get(&value.reg) {
                let Some(state_expr) = lvalue_as_expr(&state.target) else {
                    continue;
                };
                // break 先落在线性 cleanup pad、再跳到 post-loop continuation 时，
                // exit phi 的 incoming 里会混进这些 pad block。它们虽然 CFG 上已不在
                // `candidate.blocks` 内，但语义上仍然是 loop state 的内部出口。
                if loop_value_incoming_all_within_blocks(value, inside_exit_blocks) {
                    self.replace_phi_with_target_expr(
                        at_block,
                        value.phi_id,
                        &state.target,
                        state_expr,
                    );
                    continue;
                }
                let Some(exit_init) = self.loop_exit_entry_expr_with_inside_blocks(
                    value,
                    inside_exit_blocks,
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
                self.replace_phi_with_target_expr(
                    at_block,
                    value.phi_id,
                    &state.target,
                    state_expr,
                );
                continue;
            }

            // 嵌套循环场景：当前 loop 的某个 exit phi 对应的寄存器不在 plan.states 里
            // （典型是内层循环遇到外层 loop-carried 的变量：因为 build_loop_state_plan
            // 里 `exit_value_is_owned_by_inherited_state` 命中后会跳过），但外层 loop
            // 已经把这个寄存器的所有 def 统一改写到自己的 state target。此时 exit phi
            // 的临时值在 HIR 里不会有任何物化路径，必须在这里显式用外层 state 的
            // lvalue 去替换，否则 branch 条件 / post-loop 引用会保留孤立的 phi temp，
            // 后端看到 `if t28` 这种形状就只好硬着头皮当未初始化变量渲染出来。
            if let Some(target) = self.inherited_exit_target_for_value(value, target_overrides)
                && let Some(expr) = lvalue_as_expr(&target)
            {
                // 直接用 insert_phi_expr 而不是 replace_phi_with_target_expr：
                // 后者在 target_temp == phi_temp 时只会 suppress phi，结果 `if t_phi`
                // 仍然会保留原 phi temp 的引用；这里我们已经知道要把整条 phi 的物化
                // 改成 `t_phi = l2` 形式，必须走 insert_phi_expr 才能在 block 前缀
                // 里真的产出这条赋值。
                self.overrides.insert_phi_expr(at_block, value.phi_id, expr);
            }
        }
    }

    /// 当 exit phi 的 inside/outside arm 所有 defs 都统一指向同一个已继承的
    /// `target_overrides` 目标时，返回该目标。用于把嵌套循环里被外层 loop state
    /// 吸收的 phi 及时替换掉，避免留下没有赋值的 phi temp。
    fn inherited_exit_target_for_value(
        &self,
        value: &LoopValueMerge,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirLValue> {
        let fixed_temps = &self.lowering.bindings.fixed_temps;
        let combined_defs = value
            .inside_arm
            .defs()
            .chain(value.outside_arm.defs())
            .collect::<Vec<_>>();
        if combined_defs.is_empty() {
            return None;
        }
        shared_lvalue_for_defs(fixed_temps, combined_defs, target_overrides)
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

        if candidate.preheader.is_none()
            && let Some(target) =
                self.multi_entry_loop_entry_lvalue(candidate, reg, target_overrides)
        {
            return target;
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

    fn multi_entry_loop_entry_lvalue(
        &self,
        candidate: &LoopCandidate,
        reg: Reg,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirLValue> {
        let value = Self::header_value_for_reg(candidate, reg)?;
        self.uniform_loop_incoming_lvalue(reg, value.outside_arm.incomings.iter(), target_overrides)
    }

    fn loop_incoming_lvalue(
        &self,
        pred: BlockRef,
        reg: Reg,
        defs: impl IntoIterator<Item = crate::structure::DefId>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirLValue> {
        self.loop_incoming_lvalue_with_carried_override(pred, reg, defs, target_overrides, true)
    }

    fn loop_incoming_lvalue_without_carried_override(
        &self,
        pred: BlockRef,
        reg: Reg,
        defs: impl IntoIterator<Item = crate::structure::DefId>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirLValue> {
        self.loop_incoming_lvalue_with_carried_override(pred, reg, defs, target_overrides, false)
    }

    fn loop_incoming_lvalue_with_carried_override(
        &self,
        pred: BlockRef,
        reg: Reg,
        defs: impl IntoIterator<Item = crate::structure::DefId>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
        allow_carried_override: bool,
    ) -> Option<HirLValue> {
        let defs = defs.into_iter().collect::<Vec<_>>();

        if allow_carried_override
            && let Some(target) = self
                .overrides
                .carried_entry_expr(pred, reg)
                .and_then(expr_as_lvalue)
        {
            return Some(target);
        }

        if let Some(target) = shared_lvalue_for_defs(
            &self.lowering.bindings.fixed_temps,
            defs.iter().copied(),
            target_overrides,
        ) {
            return Some(target);
        }

        if let Some(target) = single_fixed_def_lvalue(self.lowering, defs.iter().copied()) {
            return Some(target);
        }

        if let Some(target) = self.reaching_phi_lvalue_override(pred, reg, target_overrides) {
            return Some(target);
        }

        None
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
        self.reaching_phi_target_override(block, reg, target_overrides)
            .cloned()
    }

    fn reaching_phi_target_override<'c>(
        &self,
        block: BlockRef,
        reg: Reg,
        target_overrides: &'c BTreeMap<TempId, HirLValue>,
    ) -> Option<&'c HirLValue> {
        use crate::structure::SsaValue;

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
        Some(lvalue)
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
            if self.loop_exit_region_is_terminal(candidate, exit, post_loop, downstream_post_loop) {
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
                self.lower_break_exit_pad(
                    exit,
                    post_loop,
                    downstream_post_loop,
                    target_overrides,
                    states,
                )?,
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
            if self.loop_exit_region_is_terminal(candidate, exit, post_loop, downstream_post_loop) {
                continue;
            }
            if downstream_post_loop == Some(exit) {
                continue;
            }
            self.lower_break_exit_pad(
                exit,
                post_loop,
                downstream_post_loop,
                &BTreeMap::new(),
                &[],
            )?;
            inside_blocks.insert(exit);
        }
        Some(inside_blocks)
    }

    fn loop_exit_region_is_terminal(
        &self,
        candidate: &LoopCandidate,
        exit: BlockRef,
        post_loop: BlockRef,
        downstream_post_loop: Option<BlockRef>,
    ) -> bool {
        fn visit(
            lowerer: &StructuredBodyLowerer<'_, '_>,
            candidate: &LoopCandidate,
            block: BlockRef,
            post_loop: BlockRef,
            downstream_post_loop: Option<BlockRef>,
            visiting: &mut BTreeSet<BlockRef>,
            memo: &mut BTreeMap<BlockRef, bool>,
        ) -> bool {
            if block == post_loop
                || Some(block) == downstream_post_loop
                || candidate.blocks.contains(&block)
                || !lowerer.lowering.cfg.reachable_blocks.contains(&block)
            {
                return false;
            }
            if block == lowerer.lowering.cfg.exit_block
                || block_is_terminal_exit(lowerer.lowering, block)
            {
                return true;
            }
            if let Some(result) = memo.get(&block).copied() {
                return result;
            }
            if !visiting.insert(block) {
                return false;
            }

            let result = lowerer.lowering.cfg.succs[block.index()]
                .iter()
                .all(|edge_ref| {
                    let successor = lowerer.lowering.cfg.edges[edge_ref.index()].to;
                    visit(
                        lowerer,
                        candidate,
                        successor,
                        post_loop,
                        downstream_post_loop,
                        visiting,
                        memo,
                    )
                });
            visiting.remove(&block);
            memo.insert(block, result);
            result
        }

        // numeric/generic for 的 body 可能只有“命中后 return”的路径；CFG 上这会表现为
        // loop header 的一个非 post-loop exit，但它不是 break pad，不需要合成 break。
        // 只有当 exit region 的所有路径都在回到 post-loop 或 loop blocks 前终结时，
        // 才把它归为 terminal body exit。
        visit(
            self,
            candidate,
            exit,
            post_loop,
            downstream_post_loop,
            &mut BTreeSet::new(),
            &mut BTreeMap::new(),
        )
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
    ) -> Option<BreakExitBlock> {
        // break 垫片允许是线性 cleanup，也允许是一个小型 if cleanup，再统一跳到
        // 循环之后的 continuation。继续限制在单入口、单 merge 的 pad 内，是为了只消费
        // StructureFacts 已能证明属于 break 出口的局部结构，避免退化成任意 exit 拼图。
        //
        // break pad 里的赋值（如 `found = true; idx = i`）写入的 def temp 与 loop 回边
        // 上的 phi temp 不同，因此仅靠 combined_target_overrides 无法将它们重定向到
        // 循环 state 变量。这里额外扫描 pad 的 def，把匹配 state 寄存器的 def temp
        // 也加入 override map，使 apply_loop_rewrites 能正确替换。
        let combined = self.break_pad_target_overrides(block, target_overrides, states);
        if matches!(
            self.block_terminator(block),
            Some((_instr_ref, LowInstr::Branch(_)))
        ) {
            return self.lower_branch_break_exit_pad(
                block,
                post_loop,
                downstream_post_loop,
                &combined,
                states,
            );
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
        Some(BreakExitBlock {
            block: HirBlock { stmts },
            blocks: BTreeSet::from([block]),
        })
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
        let merge = plan.merge?;
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

        let then_pad = self.lower_break_exit_pad_arm(
            plan.then_entry,
            merge,
            post_loop,
            downstream_post_loop,
            target_overrides,
            states,
        )?;
        blocks.extend(then_pad.blocks.iter().copied());
        let else_pad = match plan.else_entry {
            Some(else_entry) => {
                let pad = self.lower_break_exit_pad_arm(
                    else_entry,
                    merge,
                    post_loop,
                    downstream_post_loop,
                    target_overrides,
                    states,
                )?;
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

    fn lower_break_exit_pad_arm(
        &self,
        block: BlockRef,
        merge: BlockRef,
        post_loop: BlockRef,
        downstream_post_loop: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
        states: &[LoopStateSlot],
    ) -> Option<BreakExitBlock> {
        if block == merge || block == post_loop || Some(block) == downstream_post_loop {
            return Some(BreakExitBlock {
                block: HirBlock::default(),
                blocks: BTreeSet::new(),
            });
        }

        let target_overrides = self.break_pad_target_overrides(block, target_overrides, states);
        let stmts = self.lower_block_prefix(block, false, &target_overrides)?;
        let target = match self.block_terminator(block) {
            Some((_instr_ref, LowInstr::Jump(jump))) => {
                self.lowering.cfg.instr_to_block[jump.target.index()]
            }
            Some((_instr_ref, instr)) if !is_control_terminator(instr) => {
                self.lowering.cfg.unique_reachable_successor(block)?
            }
            None => self.lowering.cfg.unique_reachable_successor(block)?,
            Some(_) => return None,
        };
        if target != merge && target != post_loop && Some(target) != downstream_post_loop {
            return None;
        }

        Some(BreakExitBlock {
            block: HirBlock { stmts },
            blocks: BTreeSet::from([block]),
        })
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

    /// 返回 (expr_overrides, all_prefix_temps)，其中：
    /// - `expr_overrides`：前缀指令能成功内联的 temp → 表达式映射
    /// - `all_prefix_temps`：前缀指令定义的所有 temp 集合
    ///
    /// 调用方可通过 `all_prefix_temps - expr_overrides.keys()` 得到"无法内联的前缀 temp"。
    pub(crate) fn block_prefix_temp_expr_overrides(
        &self,
        block: BlockRef,
    ) -> (BTreeMap<TempId, HirExpr>, BTreeSet<TempId>) {
        let Some(prefix_indices) = self.block_prefix_instr_indices(block, false) else {
            return (BTreeMap::new(), BTreeSet::new());
        };

        let mut expr_overrides = BTreeMap::new();
        let mut all_prefix_temps = BTreeSet::new();
        for instr_index in prefix_indices {
            let instr_ref = InstrRef(instr_index);
            if self.overrides.instr_is_suppressed(instr_ref) {
                continue;
            }
            for def in &self.lowering.dataflow.instr_defs[instr_index] {
                let temp = self.lowering.bindings.fixed_temps[def.index()];
                all_prefix_temps.insert(temp);
                let Some(mut expr) = expr_for_fixed_def(self.lowering, *def) else {
                    continue;
                };
                rewrite_expr_temps(&mut expr, &expr_overrides);
                expr_overrides.insert(temp, expr);
            }
        }

        (expr_overrides, all_prefix_temps)
    }

    pub(crate) fn block_prefix_temp_def_order(&self, block: BlockRef) -> BTreeMap<TempId, usize> {
        let Some(prefix_indices) = self.block_prefix_instr_indices(block, false) else {
            return BTreeMap::new();
        };

        let mut def_order = BTreeMap::new();
        for instr_index in prefix_indices {
            for def in &self.lowering.dataflow.instr_defs[instr_index] {
                let temp = self.lowering.bindings.fixed_temps[def.index()];
                def_order.insert(temp, instr_index);
            }
        }
        def_order
    }
}

fn state_slots_by_reg(states: &[LoopStateSlot]) -> BTreeMap<Reg, &LoopStateSlot> {
    states.iter().map(|state| (state.reg, state)).collect()
}
