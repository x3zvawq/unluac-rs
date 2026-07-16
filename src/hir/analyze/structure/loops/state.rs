//! loop state/exit merge 的 HIR plan 组装与 exit override 安装。
//!
//! 它只消费 `StructureFacts` 已经准备好的 loop merge 事实，把这些候选翻成稳定的
//! state temp、entry override 和 exit phi override，不再自己回头拆 `phi.incoming`。
//! 具体的 entry/source/target 解析由 `state_bindings.rs` 负责，这里只决定哪些 slot
//! 进入 plan、哪些 exit phi 可以被替换。
//!
//! 例子：
//! - `while ... do i = i + 1 end` 会把 header merge 翻成一条 loop state，
//!   再把回边 defs 统一改写到同一个 HIR target
//! - `if cond then break end` 形成的 exit merge，会在确认“循环外初值”和当前 state
//!   属于同一个语义槽位后，直接复用已有 loop state，而不是再物化一层假的 phi

use super::*;
use crate::structure::SsaValue;

impl<'a, 'b> StructuredBodyLowerer<'a, 'b> {
    pub(super) fn suppress_unstructured_preheader_state_phis(
        &mut self,
        preheader: BlockRef,
        plan: &LoopStatePlan,
    ) {
        if self
            .lowering
            .structure
            .unstructured_region(preheader)
            .is_none()
        {
            return;
        }

        for phi in self.lowering.dataflow.phi_candidates_in_block(preheader) {
            let temp = self.lowering.bindings.phi_temps[phi.id.index()];
            // island 的显式入边已经按 edge 写入同一状态槽；再次 generic 物化只会
            // 重复定义该槽，且 unresolved source 会把已证明的 loop owner 重新污染。
            if plan
                .states
                .iter()
                .any(|state| state.reg == phi.reg && state.target == HirLValue::Temp(temp))
            {
                self.overrides.suppress_phi(phi.id);
            }
        }
    }

    pub(super) fn build_loop_state_plan(
        &self,
        candidate_id: LoopCandidateId,
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

            // 无观察者的空 outside arm 只是内层循环控制槽留下的幻影 phi，
            // 可以跳过；真正的携带值必须由 entry owner 区分参数、入口 local 与 nil。
            // 若 owner 解析失败，拒绝候选而不猜 nil，避免把缺失事实静默变成错误源码。
            // 相邻结构化 loop 可能共享同一个 CFG header phi：前一个 loop 已在当前
            // header 安装稳定 entry identity，后一个 loop 应直接继承，不能再从混有
            // 前一 loop exit 与自身 backedge 的原始 incoming defs 重新猜初值。
            let inherited_entry = self
                .overrides
                .block_entry_expr(candidate.header, value.reg)
                .cloned();
            let init = match inherited_entry
                .or_else(|| self.loop_entry_expr(preheader, value, target_overrides))
            {
                Some(init) => init,
                None => {
                    if value.outside_arm.values().count() == 0
                        && self.lowering.dataflow.phi_use_count(value.phi_id) == 0
                        && Self::exit_value_for_reg(candidate, exit, value.reg).is_none()
                    {
                        continue;
                    }
                    return None;
                }
            };
            let temp = *self.lowering.bindings.phi_temps.get(value.phi_id.index())?;
            let target = self.loop_state_target(candidate, exit, value.reg, temp, target_overrides);
            plan.backedge_target_overrides.insert(temp, target.clone());
            self.extend_loop_state_input_overrides(
                candidate,
                value.reg,
                value.inside_arm.values(),
                &target,
                true,
                &mut plan,
            );

            plan.states.push(LoopStateSlot {
                phi_id: Some(value.phi_id),
                reg: value.reg,
                target,
                init,
                initialize_target: true,
            });
            planned_regs.insert(value.reg);
        }

        // exit phi 的 incoming 里可能混入 break exit pad 块（形如"先做 cleanup，
        // 再 jump 到 post-loop"的线性垫片）。它们在 CFG 上不属于 candidate.blocks，
        // 但语义上传递的仍是循环体内部的值。这里和 install_loop_exit_bindings 保持一致，
        // 把这些 pad 块也视为"循环内"来计算 outside-arm 的唯一初值。
        let inside_exit_blocks = self
            .loop_state_inside_exit_blocks(candidate_id, candidate, exit)
            .unwrap_or_else(|| candidate.blocks.clone());
        let state_exit = if Self::exit_values(candidate, exit).next().is_some() {
            exit
        } else {
            self.normalized_post_loop_successor(exit)
                .filter(|downstream| Self::exit_values(candidate, *downstream).next().is_some())
                .unwrap_or(exit)
        };

        for value in Self::exit_values(candidate, state_exit) {
            if excluded.contains(&value.reg)
                || planned_regs.contains(&value.reg)
                || self.exit_value_is_owned_by_inherited_state(value, target_overrides)
            {
                continue;
            }

            let Some(init) = self
                .loop_exit_entry_expr(
                    value,
                    |block| inside_exit_blocks.contains(&block),
                    target_overrides,
                )
                .or_else(|| {
                    self.loop_exit_state_preheader_init(
                        preheader,
                        value,
                        |block| inside_exit_blocks.contains(&block),
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
            let target =
                self.loop_state_target(candidate, state_exit, value.reg, temp, target_overrides);
            plan.backedge_target_overrides.insert(temp, target.clone());
            if self.lowering.dataflow.phi_use_count(value.phi_id) > 0 {
                self.extend_loop_state_input_overrides(
                    candidate,
                    value.reg,
                    value.inside_arm.values(),
                    &target,
                    true,
                    &mut plan,
                );
            }

            plan.states.push(LoopStateSlot {
                phi_id: Some(value.phi_id),
                reg: value.reg,
                target,
                init,
                initialize_target: true,
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
        self.extend_generic_for_owned_phi_overrides(candidate, &mut plan);

        Some(plan)
    }

    fn extend_loop_state_input_overrides(
        &self,
        candidate: &LoopCandidate,
        reg: Reg,
        values: impl IntoIterator<Item = SsaValue>,
        target: &HirLValue,
        follow_same_reg_updates: bool,
        plan: &mut LoopStatePlan,
    ) {
        let mut pending = values
            .into_iter()
            .map(|value| (reg, value))
            .collect::<Vec<_>>();
        let mut seen_defs = BTreeSet::new();
        let mut seen_phis = BTreeSet::new();
        while let Some((reg, value)) = pending.pop() {
            match value {
                SsaValue::Def(def) => {
                    if !seen_defs.insert(def) {
                        continue;
                    }
                    let temp = self.lowering.bindings.fixed_temps[def.index()];
                    if target != &HirLValue::Temp(temp) {
                        plan.backedge_target_overrides.insert(temp, target.clone());
                    }
                    if !candidate
                        .blocks
                        .contains(&self.lowering.dataflow.def_block(def))
                    {
                        continue;
                    }
                    let instr = self.lowering.dataflow.def_instr(def);
                    if !follow_same_reg_updates
                        && let LowInstr::Move(move_instr) =
                            &self.lowering.proto.instrs[instr.index()]
                        && move_instr.dst == reg
                        && let source = self.lowering.dataflow.use_value(instr, move_instr.src)
                        && self
                            .lowering
                            .dataflow
                            .value_used_only_by(source, instr, move_instr.src)
                    {
                        pending.push((move_instr.src, source));
                    } else if follow_same_reg_updates {
                        pending.push((reg, self.lowering.dataflow.use_value(instr, reg)));
                    }
                }
                SsaValue::Phi(phi_id) => {
                    let Some(phi) = self.lowering.dataflow.phi_candidate(phi_id) else {
                        continue;
                    };
                    if phi.reg != reg
                        || !candidate.blocks.contains(&phi.block)
                        || !seen_phis.insert(phi_id)
                    {
                        continue;
                    }
                    let temp = self.lowering.bindings.phi_temps[phi_id.index()];
                    plan.owned_phis.insert(phi_id);
                    if target != &HirLValue::Temp(temp) {
                        plan.backedge_target_overrides.insert(temp, target.clone());
                    }
                    pending.extend(
                        phi.incoming
                            .iter()
                            .filter(|incoming| {
                                incoming
                                    .pred
                                    .is_some_and(|pred| candidate.blocks.contains(&pred))
                            })
                            .map(|incoming| (reg, incoming.value)),
                    );
                }
                SsaValue::Entry(_) => {}
            }
        }
    }

    fn extend_generic_for_owned_phi_overrides(
        &self,
        candidate: &LoopCandidate,
        plan: &mut LoopStatePlan,
    ) {
        if candidate.kind_hint != LoopKindHint::GenericForLike {
            return;
        }
        let targets = plan
            .states
            .iter()
            .map(|state| (state.reg, &state.target))
            .collect::<BTreeMap<_, _>>();
        for phi in &self.lowering.dataflow.phi_candidates {
            let Some(target) = targets.get(&phi.reg) else {
                continue;
            };
            if !candidate.blocks.contains(&phi.block) {
                continue;
            }
            let defs = phi
                .incoming
                .iter()
                .flat_map(|incoming| self.lowering.dataflow.leaf_defs(incoming.value))
                .collect::<Vec<_>>();
            if defs.is_empty()
                || shared_lvalue_for_defs(
                    &self.lowering.bindings.fixed_temps,
                    defs,
                    &plan.backedge_target_overrides,
                )
                .as_ref()
                    != Some(*target)
            {
                continue;
            }
            let temp = self.lowering.bindings.phi_temps[phi.id.index()];
            if *target != &HirLValue::Temp(temp) {
                plan.backedge_target_overrides
                    .insert(temp, (*target).clone());
                plan.owned_phis.insert(phi.id);
            }
        }
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
        let live_in = self.lowering.dataflow.live_in_regs(exit);
        let mut planned_regs = plan
            .states
            .iter()
            .map(|state| state.reg)
            .collect::<BTreeSet<_>>();

        for reg in live_in {
            if excluded.contains(reg) || planned_regs.contains(reg) {
                continue;
            }
            let value = self.lowering.dataflow.block_entry_value(exit, *reg);
            if !self.value_belongs_to_loop(candidate, value) {
                continue;
            }
            let Some(temp) = self.live_out_state_temp(value) else {
                continue;
            };
            let inherited_target = self.active_loop_state_target(*reg);
            let target = target_overrides
                .get(&temp)
                .filter(|target| lvalue_as_expr(target).is_some())
                .cloned()
                .or_else(|| inherited_target.clone())
                .unwrap_or(HirLValue::Temp(temp));
            let repeat_defines_before_use = candidate.kind_hint == LoopKindHint::RepeatLike
                && !self
                    .lowering
                    .dataflow
                    .live_in_regs(candidate.header)
                    .contains(reg)
                && target == HirLValue::Temp(temp);
            let mut init = if repeat_defines_before_use {
                // repeat 首轮必经 header；不在 live-in 中的 live-out 寄存器一定先定义再流出。
                // 新建 state 不需要从可能多值合流的 preheader 猜一个不可观察的旧值。
                HirExpr::Nil
            } else {
                preheader
                    .map(|preheader| expr_for_reg_at_block_exit(self.lowering, preheader, *reg))
                    .or_else(|| {
                        Self::header_values(candidate)
                            .find(|value| value.reg == *reg)
                            .and_then(|value| {
                                self.multi_entry_loop_entry_expr(value, target_overrides)
                            })
                    })
                    .or_else(|| inherited_target.as_ref().and_then(lvalue_as_expr))
                    .unwrap_or_else(|| self.loop_entry_initial_expr(*reg))
            };
            rewrite_expr_temps(&mut init, &temp_expr_overrides(target_overrides));

            self.extend_loop_state_input_overrides(candidate, *reg, [value], &target, false, plan);
            plan.states.push(LoopStateSlot {
                phi_id: None,
                reg: *reg,
                target,
                init,
                initialize_target: true,
            });
            planned_regs.insert(*reg);
        }
    }

    fn value_belongs_to_loop(&self, candidate: &LoopCandidate, value: SsaValue) -> bool {
        match value {
            SsaValue::Entry(_) => false,
            SsaValue::Def(def) => candidate
                .blocks
                .contains(&self.lowering.dataflow.def_block(def)),
            SsaValue::Phi(phi_id) => candidate
                .blocks
                .contains(&self.lowering.dataflow.phi_candidates[phi_id.index()].block),
        }
    }

    fn live_out_state_temp(&self, value: SsaValue) -> Option<TempId> {
        match value {
            SsaValue::Entry(_) => None,
            SsaValue::Def(def) => self.lowering.bindings.fixed_temps.get(def.index()).copied(),
            SsaValue::Phi(phi_id) => self
                .lowering
                .bindings
                .phi_temps
                .get(phi_id.index())
                .copied(),
        }
    }

    pub(super) fn install_loop_exit_bindings(
        &mut self,
        candidate_id: LoopCandidateId,
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
            if let Some(phi_id) = state.phi_id {
                let phi_temp = self.lowering.bindings.phi_temps[phi_id.index()];
                if !self.overrides.alias_phi_temp(phi_temp, state_expr.clone()) {
                    self.overrides.unsuppress_phi(phi_id);
                    continue;
                }
            }
            self.install_entry_override(exit, state.reg, state_expr);
        }
        for phi_id in &plan.owned_phis {
            let phi_temp = self.lowering.bindings.phi_temps[phi_id.index()];
            if let Some(expr) = plan
                .backedge_target_overrides
                .get(&phi_temp)
                .and_then(lvalue_as_expr)
                && !self.overrides.alias_phi_temp(phi_temp, expr)
            {
                self.overrides.unsuppress_phi(*phi_id);
            }
        }
        let inside_exit_blocks = self
            .loop_state_inside_exit_blocks(candidate_id, candidate, exit)
            .unwrap_or_else(|| candidate.blocks.clone());

        let state_by_reg = state_slots_by_reg(&plan.states);
        self.apply_exit_phi_bindings(
            candidate,
            exit,
            |block| inside_exit_blocks.contains(&block),
            &state_by_reg,
            target_overrides,
        );
        // 同一 loop state 可能在主 post-loop 之后再次与另一条 body exit 合流；
        // 主出口仍携带当前 state，应和 loop blocks 一起作为该 merge 的内部来源。
        for other_exit in candidate
            .exits
            .iter()
            .copied()
            .filter(|other| *other != exit)
        {
            let region = self
                .branch_regions_by_header
                .get(&exit)
                .copied()
                .filter(|region| region.merge == other_exit);
            let graph_facts = self.lowering.graph_facts;
            self.apply_exit_phi_bindings(
                candidate,
                other_exit,
                |block| {
                    candidate.blocks.contains(&block)
                        || block == exit
                        || region.is_some_and(|region| {
                            region.contains_structured_block(graph_facts, block)
                        })
                },
                &state_by_reg,
                target_overrides,
            );
        }

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
            self.apply_exit_phi_bindings(
                candidate,
                downstream,
                |block| inside_exit_blocks.contains(&block) || block == exit,
                &state_by_reg,
                target_overrides,
            );
        }
    }

    /// 在指定 block 上尝试把 loop exit phi 替换成对应的 loop state 表达式。
    ///
    /// 抽出这段逻辑是为了让 `install_loop_exit_bindings` 可以在 `branch_exit`
    /// 自身以及它下游的线性 continuation 上各跑一遍，而不在两处复制分支判定。
    fn apply_exit_phi_bindings<F>(
        &mut self,
        candidate: &LoopCandidate,
        at_block: BlockRef,
        is_inside: F,
        state_by_reg: &BTreeMap<Reg, &LoopStateSlot>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) where
        F: Fn(BlockRef) -> bool + Copy,
    {
        for value in Self::exit_values(candidate, at_block) {
            if let Some(state) = state_by_reg.get(&value.reg) {
                let Some(state_expr) = lvalue_as_expr(&state.target) else {
                    continue;
                };
                // break 先落在线性 cleanup pad、再跳到 post-loop continuation 时，
                // exit phi 的 incoming 里会混进这些 pad block。它们虽然 CFG 上已不在
                // `candidate.blocks` 内，但语义上仍然是 loop state 的内部出口。
                if loop_value_incoming_all_inside(value, is_inside) {
                    self.replace_phi_with_target_expr(
                        at_block,
                        value.phi_id,
                        &state.target,
                        state_expr,
                    );
                    continue;
                }
                let Some(exit_init) = self.loop_exit_entry_expr(value, is_inside, target_overrides)
                else {
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
                let phi_temp = self.lowering.bindings.phi_temps[value.phi_id.index()];
                if target_overrides.get(&phi_temp) == Some(&target) {
                    self.replace_phi_with_entry_expr(at_block, value.phi_id, value.reg, expr);
                    continue;
                }
                // 直接用 insert_phi_expr 而不是 replace_phi_with_target_expr：
                // 后者在 target_temp == phi_temp 时只会 suppress phi，结果 `if t_phi`
                // 仍然会保留原 phi temp 的引用；这里我们已经知道要把整条 phi 的物化
                // 改成 `t_phi = l2` 形式，必须走 insert_phi_expr 才能在 block 前缀
                // 里真的产出这条赋值。
                self.overrides.insert_phi_expr(at_block, value.phi_id, expr);
            }
        }
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
}
