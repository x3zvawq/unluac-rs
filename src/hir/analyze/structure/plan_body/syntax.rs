//! 消费循环语法分区、值阶段与并行复制；依赖 loop payload 和块计划，不负责普通区域遍历；例如发射 for preheader 或 latch epilogue。

use super::*;

impl<'a, 'b> PlanBodyLowerer<'a, 'b> {
    pub(super) fn lower_syntax_region_prefix(
        &mut self,
        owner: RegionId,
        region: RegionId,
        skipped: Option<InstrRef>,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let mut stmts = Vec::new();
        let mut pending = vec![region];
        while let Some(region) = pending.pop() {
            match self.lowering.structure.plan().region(region) {
                Some(RegionPlan::Block { block, .. }) => {
                    stmts.extend(self.lower_syntax_block_prefix(owner, *block, skipped)?);
                }
                Some(RegionPlan::Sequence { children, .. }) => {
                    pending.extend(children.iter().rev().copied());
                }
                Some(
                    RegionPlan::Branch { .. }
                    | RegionPlan::ValueDecision { .. }
                    | RegionPlan::Loop { .. }
                    | RegionPlan::Unstructured { .. },
                ) => {
                    return self
                        .invalid_region(owner, "loop syntax partition is not a plain sequence");
                }
                None => {
                    return Err(HirLowerError::MissingPlanRegion {
                        proto: self.proto.index(),
                        region: region.index(),
                    });
                }
            }
        }
        Ok(stmts)
    }

    pub(super) fn consume_syntax_region(
        &mut self,
        owner: RegionId,
        region: RegionId,
    ) -> Result<(), HirLowerError> {
        let mut pending = vec![region];
        while let Some(region) = pending.pop() {
            match self.lowering.structure.plan().region(region) {
                Some(RegionPlan::Block { block, .. }) => {
                    self.consume_syntax_block(owner, *block, None)?;
                }
                Some(RegionPlan::Sequence { children, .. }) => {
                    pending.extend(children.iter().rev().copied());
                }
                Some(
                    RegionPlan::Branch { .. }
                    | RegionPlan::ValueDecision { .. }
                    | RegionPlan::Loop { .. }
                    | RegionPlan::Unstructured { .. },
                ) => {
                    return self
                        .invalid_region(owner, "loop syntax partition is not a plain sequence");
                }
                None => {
                    return Err(HirLowerError::MissingPlanRegion {
                        proto: self.proto.index(),
                        region: region.index(),
                    });
                }
            }
        }
        Ok(())
    }

    pub(super) fn consume_syntax_block(
        &mut self,
        owner: RegionId,
        block: BlockRef,
        _skipped: Option<InstrRef>,
    ) -> Result<(), HirLowerError> {
        if self
            .lowering
            .structure
            .plan()
            .label_for_block(block)
            .is_some()
        {
            return self.invalid_region(owner, "loop syntax block owns a planned label");
        }
        if self
            .lowering
            .structure
            .plan()
            .phis_in_block(block)
            .iter()
            .any(|phi| {
                self.lowering
                    .structure
                    .plan()
                    .phi_plan(*phi)
                    .is_some_and(|phi| phi.has_unresolved())
            })
        {
            return self.invalid_region(owner, "loop syntax block owns unresolved values");
        }
        #[cfg(debug_assertions)]
        self.mark_block_emitted(
            owner,
            block,
            "plan consumes one loop syntax block more than once",
        )?;
        Ok(())
    }

    pub(super) fn lower_syntax_block_prefix(
        &mut self,
        owner: RegionId,
        block: BlockRef,
        skipped: Option<InstrRef>,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        #[cfg(debug_assertions)]
        self.mark_block_emitted(
            owner,
            block,
            "plan emits one loop syntax block more than once",
        )?;
        let mut stmts = Vec::new();
        self.emit_label(block, LabelPlacement::BeforeBlock, &mut stmts)?;
        stmts.extend(self.lower_unresolved_phis(owner, block)?);
        let terminator = self.block_terminator(owner, block)?.clone();
        let end = terminator
            .kind
            .instr()
            .map_or(terminator.instrs.end(), InstrRef::index);
        for index in terminator.instrs.start.index()..end {
            let instr_ref = InstrRef(index);
            if skipped == Some(instr_ref) {
                continue;
            }
            stmts.extend(self.lower_planned_regular(owner, block, instr_ref)?);
        }
        Ok(stmts)
    }

    pub(super) fn lower_loop_value_phase(
        &self,
        owner: RegionId,
        phase: LoopValuePhase,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let mut stmts = Vec::new();
        let plan_id = match self.lowering.structure.plan().region(owner) {
            Some(RegionPlan::Loop { plan, .. }) => *plan,
            _ => return self.invalid_region(owner, "loop value action owner is not a loop"),
        };
        let actions = self
            .lowering
            .structure
            .plan()
            .loop_value_actions(plan_id)
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "loop payload has no finalized value actions",
            })?;
        for batch in actions.batches.iter().filter(|batch| batch.phase == phase) {
            stmts.extend(self.lower_loop_value_batch(owner, batch)?);
        }
        Ok(stmts)
    }

    pub(super) fn lower_loop_value_batch(
        &self,
        owner: RegionId,
        batch: &crate::structure::LoopValueActionBatch,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let assignments = batch
            .writes
            .iter()
            .map(|write| {
                Ok((
                    write.target,
                    self.lower_loop_value_source(owner, write.source)?,
                ))
            })
            .collect::<Result<Vec<_>, HirLowerError>>()?;
        self.copy_assignments(owner, assignments)
    }

    pub(super) fn lower_loop_value_source(
        &self,
        owner: RegionId,
        source: LoopValueSource,
    ) -> Result<HirExpr, HirLowerError> {
        Ok(match source {
            LoopValueSource::Ssa(value) => self.ssa_expr(owner, value)?,
            LoopValueSource::Binding(reg) => self
                .binding_local_for_reg(owner, reg)
                .map(HirExpr::LocalRef)
                .ok_or(HirLowerError::InvalidPlanRegion {
                    proto: self.proto.index(),
                    region: owner.index(),
                    detail: "loop action binding lost its selected local",
                })?,
            LoopValueSource::Carried(phi) => {
                HirExpr::TempRef(*self.lowering.bindings.phi_temps.get(phi.index()).ok_or(
                    HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "loop action carried source has no temp binding",
                    },
                )?)
            }
        })
    }

    pub(super) fn copy_assignments(
        &self,
        owner: RegionId,
        copies: Vec<(PhiId, HirExpr)>,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        if copies.is_empty() {
            return Ok(Vec::new());
        }
        let mut targets = Vec::with_capacity(copies.len());
        let mut values = Vec::with_capacity(copies.len());
        for (phi, value) in copies {
            let target = self
                .lowering
                .bindings
                .phi_temps
                .get(phi.index())
                .copied()
                .ok_or(HirLowerError::InvalidPlanRegion {
                    proto: self.proto.index(),
                    region: owner.index(),
                    detail: "phi copy target has no HIR temp binding",
                })?;
            targets.push(self.lowering.bindings.lvalue_for_temp(target));
            values.push(value);
        }
        Ok(copy_assignment_stmt(targets, values).into_iter().collect())
    }
}
