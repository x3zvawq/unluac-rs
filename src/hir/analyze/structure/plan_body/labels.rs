//! 发射标签并执行 debug-only 的唯一性核对；依赖标签放置和区域入口，不负责决定哪些边需要标签；例如在 Region 前而非 Block 前放置 goto 标签。

use super::*;

impl<'a, 'b> PlanBodyLowerer<'a, 'b> {
    pub(super) fn emit_label(
        &mut self,
        block: BlockRef,
        expected_placement: LabelPlacement,
        stmts: &mut Vec<HirStmt>,
    ) -> Result<(), HirLowerError> {
        let Some(label) = self.lowering.structure.plan().label_for_block(block) else {
            return Ok(());
        };
        let Some(payload) = self.lowering.structure.plan().label(label) else {
            return self.invalid_region(
                self.lowering
                    .structure
                    .plan()
                    .region_for_block(block)
                    .unwrap_or(self.lowering.structure.plan().root()),
                "block label has no frozen payload",
            );
        };
        if matches!(payload.placement, LabelPlacement::BeforeRegion(_))
            && payload.placement != expected_placement
        {
            return Ok(());
        }
        if payload.placement != expected_placement {
            return self.invalid_region(
                self.lowering
                    .structure
                    .plan()
                    .region_for_block(block)
                    .unwrap_or(self.lowering.structure.plan().root()),
                "block label was emitted at the wrong cleanup boundary",
            );
        }
        #[cfg(debug_assertions)]
        {
            let duplicate = self
                .emitted_labels
                .get_mut(label.index())
                .is_none_or(|emitted| std::mem::replace(emitted, true));
            if duplicate {
                return self.invalid_region(
                    self.lowering
                        .structure
                        .plan()
                        .region_for_block(block)
                        .unwrap_or(self.lowering.structure.plan().root()),
                    "plan emits one label more than once",
                );
            }
            self.emitted_label_count += 1;
        }
        stmts.push(HirStmt::Label(Box::new(HirLabel {
            id: HirLabelId(label.index()),
            tbc_barriers: payload.tbc_barriers.clone(),
        })));
        Ok(())
    }

    pub(super) fn emit_region_label(
        &mut self,
        region: RegionId,
        stmts: &mut Vec<HirStmt>,
    ) -> Result<(), HirLowerError> {
        let entry = match self.lowering.structure.plan().region(region) {
            Some(
                RegionPlan::Branch { entry, .. }
                | RegionPlan::ValueDecision { entry, .. }
                | RegionPlan::Loop { entry, .. }
                | RegionPlan::Unstructured { entry, .. },
            ) => *entry,
            Some(RegionPlan::Block { .. } | RegionPlan::Sequence { .. }) => return Ok(()),
            None => {
                return Err(HirLowerError::MissingPlanRegion {
                    proto: self.proto.index(),
                    region: region.index(),
                });
            }
        };
        let Some(label) = self.lowering.structure.plan().label_for_block(entry) else {
            return Ok(());
        };
        if self
            .lowering
            .structure
            .plan()
            .label(label)
            .is_some_and(|label| label.placement == LabelPlacement::BeforeRegion(region))
        {
            self.emit_label(entry, LabelPlacement::BeforeRegion(region), stmts)?;
        }
        Ok(())
    }

    #[cfg(debug_assertions)]
    pub(super) fn mark_block_emitted(
        &mut self,
        owner: RegionId,
        block: BlockRef,
        detail: &'static str,
    ) -> Result<(), HirLowerError> {
        if self
            .emitted_blocks
            .get_mut(block.index())
            .is_none_or(|emitted| std::mem::replace(emitted, true))
        {
            return self.invalid_region(owner, detail);
        }
        Ok(())
    }

    pub(super) fn block_terminator(
        &self,
        owner: RegionId,
        block: BlockRef,
    ) -> Result<&BlockTerminatorPlan, HirLowerError> {
        self.lowering
            .structure
            .plan()
            .block_terminator(block)
            .filter(|terminator| terminator.block == block)
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "block has no dense terminator plan",
            })
    }

    pub(super) fn invalid_region<T>(
        &self,
        region: RegionId,
        detail: &'static str,
    ) -> Result<T, HirLowerError> {
        Err(HirLowerError::InvalidPlanRegion {
            proto: self.proto.index(),
            region: region.index(),
            detail,
        })
    }
}
