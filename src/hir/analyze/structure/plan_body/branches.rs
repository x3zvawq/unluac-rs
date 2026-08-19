//! 将分支、短路条件和值判定区域降低为 HIR；依赖冻结的 condition/value payload，不负责选择候选；例如生成带边动作的 if/else。

use super::*;

impl<'a, 'b> PlanBodyLowerer<'a, 'b> {
    pub(super) fn lower_branch(
        &mut self,
        region: RegionId,
        plan: crate::structure::BranchPlanId,
        condition: RegionId,
        mut then_arm: HirBlock,
        else_arm: Option<HirBlock>,
    ) -> Result<HirBlock, HirLowerError> {
        let payload = self.lowering.structure.plan().branch(plan).cloned().ok_or(
            HirLowerError::MissingPlanPayload {
                proto: self.proto.index(),
                kind: "branch",
                id: plan.index(),
            },
        )?;
        let (mut stmts, mut cond) =
            self.lower_short_circuit_condition(region, condition, payload.condition)?;
        if payload.condition_inverted {
            cond = cond.negate();
        }

        let mut then_block = self.lower_edge(region, payload.then_edge)?;
        then_block.stmts.append(&mut then_arm.stmts);
        let mut else_block = self.lower_edge(region, payload.else_edge)?;
        if let Some(mut arm) = else_arm {
            else_block.stmts.append(&mut arm.stmts);
        }
        let else_block = (!else_block.stmts.is_empty()).then_some(else_block);
        stmts.push(branch_stmt(cond, then_block, else_block));
        Ok(HirBlock { stmts })
    }

    pub(super) fn lower_short_circuit_condition(
        &mut self,
        owner: RegionId,
        condition_region: RegionId,
        condition_plan: crate::structure::ConditionPlanId,
    ) -> Result<(Vec<HirStmt>, HirExpr), HirLowerError> {
        let selected = self
            .lowering
            .structure
            .plan()
            .condition(condition_plan)
            .cloned()
            .ok_or(HirLowerError::MissingPlanPayload {
                proto: self.proto.index(),
                kind: "condition",
                id: condition_plan.index(),
            })?;
        self.verify_condition_plan(owner, &selected)?;
        let decision = build_condition_decision_expr(self.lowering, &selected).ok_or(
            HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "frozen short-circuit condition cannot be materialized",
            },
        )?;
        self.verify_condition_region(owner, condition_region, &selected.blocks)?;
        let header = selected.header().ok_or(HirLowerError::InvalidPlanRegion {
            proto: self.proto.index(),
            region: owner.index(),
            detail: "frozen condition has no entry node",
        })?;
        let stmts = self.lower_condition_prefix(owner, header)?;
        #[cfg(debug_assertions)]
        for block in selected.blocks {
            if block != header {
                self.mark_block_emitted(
                    owner,
                    block,
                    "plan emits one condition block more than once",
                )?;
            }
        }
        Ok((stmts, finalize_condition_decision_expr(decision)))
    }

    pub(super) fn lower_value_decision(
        &mut self,
        region: RegionId,
        plan: crate::structure::ValueDecisionPlanId,
    ) -> Result<HirBlock, HirLowerError> {
        let selected = self
            .lowering
            .structure
            .plan()
            .value_decision(plan)
            .cloned()
            .ok_or(HirLowerError::MissingPlanPayload {
                proto: self.proto.index(),
                kind: "value-decision",
                id: plan.index(),
            })?;
        self.verify_value_decision_plan(region, &selected)?;
        if self.lowering.structure.plan().value_decision_region(plan) != Some(region) {
            return self
                .invalid_region(region, "value decision payload is bound to another region");
        }
        let header = selected.header().ok_or(HirLowerError::InvalidPlanRegion {
            proto: self.proto.index(),
            region: region.index(),
            detail: "value decision has no entry node",
        })?;
        let decision = build_value_decision_expr(self.lowering, &selected).ok_or(
            HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "frozen value decision cannot be materialized",
            },
        )?;
        let mut stmts = self.lower_condition_prefix(region, header)?;
        let target = self
            .lowering
            .bindings
            .phi_temps
            .get(selected.result_phi.index())
            .copied()
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "value decision result phi has no HIR binding",
            })?;
        stmts.push(assign_stmt(
            vec![self.lowering.bindings.lvalue_for_temp(target)],
            vec![finalize_value_decision_expr(decision)],
        ));
        stmts.extend(self.lower_edge_effects(region, selected.shared_exit_action)?);
        #[cfg(debug_assertions)]
        for block in selected.blocks().filter(|block| *block != header) {
            self.mark_block_emitted(region, block, "plan emits one value block more than once")?;
        }
        Ok(HirBlock { stmts })
    }

    pub(super) fn verify_condition_region(
        &mut self,
        owner: RegionId,
        region: RegionId,
        blocks: &[BlockRef],
    ) -> Result<(), HirLowerError> {
        let Some(expected_count) = self
            .index
            .plain_block_count
            .get(region.index())
            .copied()
            .flatten()
        else {
            return self.invalid_region(
                region,
                "condition region contains a non-condition control region",
            );
        };
        if blocks.len() != expected_count {
            return self.invalid_region(
                owner,
                "condition materialization did not consume the exact planned region",
            );
        }

        self.condition_epoch = self.condition_epoch.wrapping_add(1);
        if self.condition_epoch == 0 {
            self.condition_block_seen_at.fill(0);
            self.condition_epoch = 1;
        }
        for block in blocks {
            let Some(seen_at) = self.condition_block_seen_at.get_mut(block.index()) else {
                return self.invalid_region(owner, "condition block is outside the CFG arena");
            };
            if std::mem::replace(seen_at, self.condition_epoch) == self.condition_epoch {
                return self.invalid_region(owner, "condition plan contains one block twice");
            }
            let Some(block_region) = self.lowering.structure.plan().region_for_block(*block) else {
                return self.invalid_region(owner, "condition block has no containment owner");
            };
            if !self
                .lowering
                .structure
                .plan()
                .region_contains(region, block_region)
            {
                return self.invalid_region(
                    owner,
                    "condition materialization did not consume the exact planned region",
                );
            }
        }
        Ok(())
    }
}
