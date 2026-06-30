//! 这个文件承载 structured body lowering 里的 entry/phi override 安装与传播。
//!
//! loop state、branch value merge、short-circuit value merge 都可能证明某个 phi 不该再
//! 物化为独立 temp，而应改成 block entry 表达式或指定 lvalue 写回。本文件只维护这些
//! override 如何落到 `StructureOverrideState`、如何穿过未重定义寄存器的 block 继续传播；
//! 它不选择 branch/loop 结构，也不降低普通指令。
//!
//! 输入形状：`merge` 上的 phi 已被证明等于 header 入口表达式。
//! 输出形状：suppress 该 phi，并把 entry temp override 传播到可穿透的 successor。

use std::collections::BTreeMap;

use super::*;

impl StructuredBodyLowerer<'_, '_> {
    pub(in crate::hir::analyze::structure) fn block_entry_expr_overrides(
        &self,
        block: BlockRef,
    ) -> Option<&BTreeMap<TempId, HirExpr>> {
        self.overrides.block_entry_temp_exprs(block)
    }

    pub(in crate::hir::analyze::structure) fn block_redefines_reg(
        &self,
        block: BlockRef,
        reg: Reg,
    ) -> bool {
        let range = self.lowering.cfg.blocks[block.index()].instrs;
        (range.start.index()..range.end()).any(|instr_index| {
            let effect = &self.lowering.dataflow.instr_effects[instr_index];
            effect.fixed_must_defs.contains(&reg) || effect.fixed_may_defs.contains(&reg)
        })
    }

    pub(in crate::hir::analyze::structure) fn install_entry_override(
        &mut self,
        block: BlockRef,
        reg: Reg,
        expr: HirExpr,
    ) {
        // 防止循环传播：如果该 block 上这个 reg 已经有完全相同的 override，不再重入。
        if self
            .overrides
            .carried_entry_expr(block, reg)
            .is_some_and(|existing| *existing == expr)
        {
            return;
        }

        let source_temp = self.block_entry_source_temp(block, reg);
        let carries_through_block = !self.block_redefines_reg(block, reg);
        self.overrides.insert_entry_expr(
            block,
            reg,
            expr.clone(),
            source_temp,
            carries_through_block,
        );
        // 当 override 能穿透当前 block（该 register 未被重定义），需要继续向后继传播。
        // 否则后续 block 的 lower_block_prefix 看不到 entry_temp_expr override，
        // 被 suppress 的 phi temp 在 RHS 表达式中就无法被正确替换。
        // 对于分支 block（多后继），所有后继都可能需要该 override，只要后继处没有
        // 该寄存器的 phi 合流（有 phi 说明多来源，不能用单条路径 override 覆盖）。
        if carries_through_block {
            for edge_ref in &self.lowering.cfg.succs[block.index()] {
                let successor = self.lowering.cfg.edges[edge_ref.index()].to;
                if !self.lowering.cfg.reachable_blocks.contains(&successor) {
                    continue;
                }
                if self
                    .lowering
                    .dataflow
                    .phi_candidate_for_reg(successor, reg)
                    .is_none()
                {
                    self.install_entry_override(successor, reg, expr.clone());
                }
            }
        }
    }

    pub(in crate::hir::analyze::structure) fn replace_phi_with_entry_expr(
        &mut self,
        block: BlockRef,
        phi_id: PhiId,
        reg: Reg,
        expr: HirExpr,
    ) {
        self.overrides.suppress_phi(phi_id);
        self.install_entry_override(block, reg, expr);
    }

    pub(in crate::hir::analyze::structure) fn replace_phi_with_entry_expr_if_local_use(
        &mut self,
        block: BlockRef,
        phi_id: PhiId,
        reg: Reg,
        expr: HirExpr,
    ) {
        if self.lowering.dataflow.phi_used_only_in_block(phi_id, block) {
            self.replace_phi_with_entry_expr(block, phi_id, reg, expr);
        } else {
            self.overrides.insert_phi_expr(block, phi_id, expr);
        }
    }

    pub(in crate::hir::analyze::structure) fn replace_phi_with_target_expr(
        &mut self,
        block: BlockRef,
        phi_id: PhiId,
        target: &HirLValue,
        expr: HirExpr,
    ) {
        let phi_temp = self.lowering.bindings.phi_temps[phi_id.index()];
        if lvalue_as_expr(target) == Some(HirExpr::TempRef(phi_temp)) {
            self.overrides.suppress_phi(phi_id);
        } else {
            self.overrides.insert_phi_expr(block, phi_id, expr);
        }
    }

    fn block_entry_source_temp(&self, block: BlockRef, reg: Reg) -> Option<TempId> {
        let range = self.lowering.cfg.blocks[block.index()].instrs;
        if range.is_empty() {
            return None;
        }
        // 即使当前 block 内会重定义该寄存器（如 `SUB r1, r1, 1000` 先读后写），
        // 入口处的 reaching value 仍然是该寄存器在 block 首条指令前的 SSA 值，
        // 对应的 temp 会出现在 RHS 表达式中。移除旧有的 block_redefines_reg 守卫，
        // 让 entry_temp_exprs 能正确建立映射，使 lower_block_prefix 的 rewrite 生效。

        let values = self
            .lowering
            .dataflow
            .reaching_values_at(range.start)
            .get(reg)?;
        if values.len() != 1 {
            return None;
        }

        Some(
            match values
                .iter()
                .next()
                .expect("len checked above, exactly one reaching value exists")
            {
                crate::structure::SsaValue::Def(def) => {
                    self.lowering.bindings.fixed_temps[def.index()]
                }
                crate::structure::SsaValue::Phi(phi) => {
                    self.lowering.bindings.phi_temps[phi.index()]
                }
            },
        )
    }
}
