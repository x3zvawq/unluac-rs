//! loop state 的 entry/source/target 解析工具。
//!
//! `state.rs` 负责把 `StructureFacts` 给出的 loop merge 组装成 HIR plan；这个文件只回答
//! “某个 loop-carried reg 的初值从哪里来、写回到哪个 lvalue”。它依赖 Structure/Dataflow
//! 已经提供的 incoming defs、preheader 和 exit merge 事实，不重新识别 loop 候选，也不安装
//! entry/phi override。
//!
//! 例子：
//! - 输入：多入口 while-like loop 的多个 outside incoming 都指向同一个原始初值
//! - 输出：复用同一个 entry lvalue 作为 loop state target，而不是新建只在分支内可见的 phi temp

use super::*;
use crate::structure::SsaValue;

impl<'a, 'b> StructuredBodyLowerer<'a, 'b> {
    pub(super) fn loop_exit_state_preheader_init(
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

    pub(super) fn loop_entry_expr(
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

    pub(super) fn multi_entry_loop_entry_expr(
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

    pub(super) fn loop_exit_entry_expr_with_inside_blocks(
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

    pub(super) fn loop_entry_initial_expr(&self, reg: Reg) -> HirExpr {
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

    pub(super) fn inherited_exit_target_for_value(
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

    pub(super) fn loop_state_target(
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

    pub(super) fn exit_value_is_owned_by_inherited_state(
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
}
