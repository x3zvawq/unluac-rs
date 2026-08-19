//! 在 HIR 发射前核对 condition/value/SSA binding 合同；依赖最终 payload 与 binding 表，不负责结构发现；例如验证 edge copy 的 canonical SSA 来源。

use super::*;

impl<'a, 'b> PlanBodyLowerer<'a, 'b> {
    pub(super) fn verify_condition_plan(
        &self,
        owner: RegionId,
        condition: &crate::structure::ConditionPlan,
    ) -> Result<(), HirLowerError> {
        if condition.entry.index() >= condition.nodes.len() {
            return self.invalid_region(owner, "condition entry is outside its node arena");
        }
        for (index, node) in condition.nodes.iter().enumerate() {
            if node.id.index() != index
                || !matches!(
                    self.lowering.proto.instrs.get(node.predicate.index()),
                    Some(LowInstr::Branch(_))
                )
            {
                return self
                    .invalid_region(owner, "condition node identity or predicate is invalid");
            }
            for arc in &node.arcs {
                if arc.source != node.id
                    || matches!(
                        arc.target,
                        crate::structure::ConditionTarget::Node(target)
                            if target.index() >= condition.nodes.len()
                    )
                {
                    return self.invalid_region(owner, "condition arc is outside its node arena");
                }
            }
            if let Some(value) = node.materialized_value
                && (value.consumer.index() >= condition.nodes.len()
                    || value.phi.index() >= self.lowering.bindings.phi_temps.len()
                    || value
                        .forwarded_callee
                        .is_some_and(|def| def.index() >= self.lowering.bindings.fixed_temps.len()))
            {
                return self.invalid_region(
                    owner,
                    "condition materialized value references an unbound identity",
                );
            }
        }
        Ok(())
    }

    pub(super) fn verify_value_decision_plan(
        &self,
        owner: RegionId,
        decision: &crate::structure::ValueDecisionPlan,
    ) -> Result<(), HirLowerError> {
        if decision.entry.index() >= decision.nodes.len()
            || decision.result_phi.index() >= self.lowering.bindings.phi_temps.len()
        {
            return self.invalid_region(owner, "value decision root identity is unbound");
        }
        for (index, node) in decision.nodes.iter().enumerate() {
            if node.id.index() != index
                || !matches!(
                    self.lowering.proto.instrs.get(node.predicate.index()),
                    Some(LowInstr::Branch(_))
                )
            {
                return self.invalid_region(
                    owner,
                    "value decision node identity or predicate is invalid",
                );
            }
            for target in [node.truthy.target, node.falsy.target] {
                let valid = match target {
                    crate::structure::ValueDecisionTarget::Node(target) => {
                        target.index() < decision.nodes.len()
                    }
                    crate::structure::ValueDecisionTarget::Leaf(target)
                    | crate::structure::ValueDecisionTarget::CurrentValue(target) => {
                        target.index() < decision.leaves.len()
                    }
                };
                if !valid {
                    return self
                        .invalid_region(owner, "value decision target is outside its arena");
                }
            }
        }
        for (index, leaf) in decision.leaves.iter().enumerate() {
            if leaf.id.index() != index
                || leaf.latest_local_def.is_some_and(|def| {
                    def.index() >= self.lowering.dataflow.defs.len()
                        || def.index() >= self.lowering.bindings.fixed_temps.len()
                })
            {
                return self.invalid_region(owner, "value decision leaf identity is invalid");
            }
            self.ensure_ssa_binding(owner, leaf.value)?;
        }
        Ok(())
    }

    pub(super) fn binding_local_for_reg(
        &self,
        owner: RegionId,
        reg: crate::transformer::Reg,
    ) -> Option<crate::hir::common::LocalId> {
        let loop_id = match self.lowering.structure.plan().region(owner)? {
            RegionPlan::Loop { plan, .. } => *plan,
            _ => return None,
        };
        let payload = self.lowering.structure.plan().loop_(loop_id)?;
        match payload.source_bindings? {
            crate::structure::LoopSourceBindings::Numeric(binding) if reg == binding => self
                .lowering
                .bindings
                .numeric_for_locals
                .get(&payload.header)
                .copied(),
            crate::structure::LoopSourceBindings::Generic(bindings)
                if reg.index() >= bindings.start.index()
                    && reg.index() < bindings.start.index() + bindings.len =>
            {
                self.lowering
                    .bindings
                    .generic_for_locals
                    .get(&payload.header)
                    .and_then(|locals| locals.get(reg.index() - bindings.start.index()))
                    .copied()
            }
            _ => None,
        }
    }

    pub(super) fn ssa_expr(
        &self,
        owner: RegionId,
        value: crate::structure::SsaValue,
    ) -> Result<HirExpr, HirLowerError> {
        self.ensure_ssa_binding(owner, value)?;
        let target = match value {
            SsaValue::Entry(_) => None,
            SsaValue::Def(def) => self.lowering.bindings.fixed_temps.get(def.index()).copied(),
            SsaValue::Phi(phi) => self.lowering.bindings.phi_temps.get(phi.index()).copied(),
        };
        Ok(target.map_or_else(
            || super::super::super::exprs::expr_for_ssa_value(self.lowering, value),
            |temp| self.lowering.bindings.expr_for_temp(temp),
        ))
    }

    pub(super) fn ensure_ssa_binding(
        &self,
        owner: RegionId,
        value: SsaValue,
    ) -> Result<(), HirLowerError> {
        let bound = match value {
            SsaValue::Entry(_) => true,
            SsaValue::Def(def) => def.index() < self.lowering.bindings.fixed_temps.len(),
            SsaValue::Phi(phi) => phi.index() < self.lowering.bindings.phi_temps.len(),
        };
        if bound {
            Ok(())
        } else {
            self.invalid_region(owner, "SSA value has no HIR temp binding")
        }
    }

    /// 条件 region 会吸收内部纯 `Move`，通常必须沿 SSA 恒等链读取真实来源。普通 def
    /// 若已在原指令处物化，则只有 canonical binding 到 source block 出口仍未被另一个
    /// SSA 值复用时才能延后读取；否则必须使用 frozen def binding 保存的快照。
    pub(super) fn edge_copy_expr(
        &self,
        owner: RegionId,
        source_block: BlockRef,
        target: TempId,
        value: SsaValue,
    ) -> Result<HirExpr, HirLowerError> {
        let value = match value {
            SsaValue::Def(def) => {
                let fixed = self
                    .lowering
                    .bindings
                    .fixed_temps
                    .get(def.index())
                    .copied()
                    .ok_or(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "edge copy source has no fixed-temp binding",
                    })?;
                let definition = self.lowering.dataflow.defs.get(def.index()).ok_or(
                    HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "edge copy source references a missing SSA def",
                    },
                )?;
                let absorbed = self
                    .index
                    .absorbed_region_result_moves
                    .get(definition.instr.index())
                    .copied()
                    .ok_or(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "edge copy source has no absorption disposition",
                    })?;
                let writes_fixed_binding = self
                    .lowering
                    .bindings
                    .local_for_reg_in_block(definition.block, definition.reg)
                    .is_none()
                    && !super::super::super::exprs::block_is_absorbed_decision(
                        self.lowering,
                        definition.block,
                    );
                let canonical = self
                    .index
                    .canonical_move_source
                    .get(def.index())
                    .copied()
                    .flatten()
                    .unwrap_or(value);
                let read_exact = !absorbed
                    && writes_fixed_binding
                    && (fixed == target || {
                        let canonical_expr = self.edge_ssa_expr(owner, source_block, canonical)?;
                        match self
                            .lowering
                            .dataflow
                            .block_end_value(source_block, self.ssa_reg(owner, canonical)?)
                        {
                            Some(current) if current != canonical => {
                                self.edge_ssa_expr(owner, source_block, current)? == canonical_expr
                            }
                            Some(_) => false,
                            None => match canonical_expr {
                                HirExpr::LocalRef(_) => true,
                                HirExpr::TempRef(temp) => self
                                    .index
                                    .shared_ssa_temps
                                    .get(temp.index())
                                    .copied()
                                    .unwrap_or(true),
                                _ => false,
                            },
                        }
                    });
                if read_exact { value } else { canonical }
            }
            _ => value,
        };
        self.edge_ssa_expr(owner, source_block, value)
    }

    pub(super) fn edge_ssa_expr(
        &self,
        owner: RegionId,
        source_block: BlockRef,
        value: SsaValue,
    ) -> Result<HirExpr, HirLowerError> {
        let reg = self.ssa_reg(owner, value)?;
        if let Some(local) = self
            .lowering
            .bindings
            .local_for_reg_in_block(source_block, reg)
        {
            return Ok(HirExpr::LocalRef(local));
        }
        self.ssa_expr(owner, value)
    }

    pub(super) fn ssa_reg(&self, owner: RegionId, value: SsaValue) -> Result<Reg, HirLowerError> {
        match value {
            SsaValue::Entry(reg) => Ok(reg),
            SsaValue::Def(def) => self
                .lowering
                .dataflow
                .defs
                .get(def.index())
                .map(|def| def.reg)
                .ok_or(HirLowerError::InvalidPlanRegion {
                    proto: self.proto.index(),
                    region: owner.index(),
                    detail: "SSA value references a missing def",
                }),
            SsaValue::Phi(phi) => self
                .lowering
                .structure
                .plan()
                .phi_plan(phi)
                .map(|phi| phi.reg)
                .ok_or(HirLowerError::InvalidPlanRegion {
                    proto: self.proto.index(),
                    region: owner.index(),
                    detail: "SSA value references a missing final phi plan",
                }),
        }
    }
}
