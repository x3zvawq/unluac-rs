//! 校验标签放置与跳转需求；依赖 CFG、区域导航和边计划，不负责生成标签；例如确保跨区域 goto 的目标标签唯一。

use super::*;

pub(super) fn validate_labels(cfg: &Cfg, plan: &StructurePlan) -> Result<(), StructureError> {
    if plan.label_by_block.len() != cfg.blocks.len() {
        return Err(StructureError::invalid(
            "block-to-label index length mismatch",
        ));
    }

    let mut actual_targets = vec![false; cfg.blocks.len()];
    for (index, label) in plan.labels.iter().enumerate() {
        let id = super::super::LabelPlanId(index);
        let Some(target) = actual_targets.get_mut(label.block.index()) else {
            return Err(StructureError::invalid(format!(
                "label #{index} references a missing block"
            )));
        };
        if !cfg.reachable_blocks.contains(&label.block)
            || plan.label_for_block(label.block) != Some(id)
            || std::mem::replace(target, true)
        {
            return Err(StructureError::invalid(format!(
                "label #{index} has a stale block reverse index"
            )));
        }
        if label.tbc_barriers.windows(2).any(|pair| pair[0] >= pair[1])
            || label
                .tbc_barriers
                .iter()
                .any(|instr| instr.index() >= cfg.instr_to_block.len())
        {
            return Err(StructureError::invalid(format!(
                "label #{index} has a non-canonical TBC barrier set"
            )));
        }
    }
    for (index, label) in plan.label_by_block.iter().copied().enumerate() {
        let Some(label) = label else {
            continue;
        };
        if plan.label(label).map(|label| label.block) != Some(crate::structure::BlockRef(index)) {
            return Err(StructureError::invalid(format!(
                "block #{index} has a stale label reverse index"
            )));
        }
    }

    let label_region_by_block = label_regions_by_entry(cfg, plan)?;
    let mut expected_placements = vec![None; cfg.blocks.len()];
    for edge_plan in &plan.edge_plans {
        if !matches!(edge_plan.transfer, EdgeTransfer::Goto(_, _)) {
            continue;
        }
        let edge = cfg.edges.get(edge_plan.edge.index()).ok_or_else(|| {
            StructureError::invalid(format!(
                "goto edge {} is outside the CFG arena",
                edge_plan.edge
            ))
        })?;
        record_expected_label_placement(
            &mut expected_placements,
            edge.to,
            expected_label_placement_for_edge(
                cfg,
                &label_region_by_block,
                edge_plan.edge,
                edge.to,
            )?,
        )?;
    }
    let multi_entry_prefix = plan.navigation.multi_entry_island_prefix(&plan.regions);
    for (index, edge) in cfg.edges.iter().enumerate() {
        if plan
            .navigation
            .edge_enters_prefixed_region(EdgeRef(index), &multi_entry_prefix)
        {
            let edge_ref = EdgeRef(index);
            record_expected_label_placement(
                &mut expected_placements,
                edge.to,
                expected_label_placement_for_edge(cfg, &label_region_by_block, edge_ref, edge.to)?,
            )?;
        }
    }
    for (index, expected) in expected_placements.iter().copied().enumerate() {
        let block = BlockRef(index);
        let actual = plan
            .label_for_block(block)
            .and_then(|label| plan.label(label))
            .map(|label| match label.placement {
                LabelPlacement::AfterCleanup(_) => LabelPlacement::BeforeBlock,
                placement => placement,
            });
        if actual != expected {
            return Err(StructureError::invalid(format!(
                "label target {block} has placement {actual:?}; expected {expected:?}"
            )));
        }
    }
    Ok(())
}

pub(super) fn label_regions_by_entry(
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<Vec<Option<RegionId>>, StructureError> {
    let mut by_block = vec![None; cfg.blocks.len()];
    for (index, node) in plan.regions.iter().enumerate() {
        let region = RegionId(index);
        let entry = match node {
            RegionPlan::Branch { entry, .. }
            | RegionPlan::ValueDecision { entry, .. }
            | RegionPlan::Loop { entry, .. } => *entry,
            RegionPlan::Sequence { .. } => {
                let Some((_, fence)) = plan.single_pass_for_region(region) else {
                    continue;
                };
                fence.entry
            }
            RegionPlan::Block { .. } | RegionPlan::Unstructured { .. } => continue,
        };
        let slot = by_block.get_mut(entry.index()).ok_or_else(|| {
            StructureError::invalid("structured label entry is outside the CFG arena")
        })?;
        match *slot {
            None => *slot = Some(region),
            Some(outer) if plan.navigation.contains(outer, region) => {}
            Some(inner) if plan.navigation.contains(region, inner) => *slot = Some(region),
            Some(other) => {
                return Err(StructureError::invalid(format!(
                    "block {entry} is the entry of incomparable structured regions #{} and #{}",
                    other.index(),
                    region.index()
                )));
            }
        }
    }
    Ok(by_block)
}

pub(super) fn record_expected_label_placement(
    placements: &mut [Option<LabelPlacement>],
    block: BlockRef,
    placement: LabelPlacement,
) -> Result<(), StructureError> {
    let slot = placements.get_mut(block.index()).ok_or_else(|| {
        StructureError::invalid(format!("label target {block} is outside the CFG arena"))
    })?;
    if let Some(existing) = slot.replace(placement)
        && existing != placement
    {
        return Err(StructureError::invalid(format!(
            "label target {block} requires conflicting placements {existing:?} and {placement:?}"
        )));
    }
    Ok(())
}

pub(super) fn expected_label_placement_for_edge(
    cfg: &Cfg,
    label_region_by_block: &[Option<RegionId>],
    edge: EdgeRef,
    target: BlockRef,
) -> Result<LabelPlacement, StructureError> {
    if cfg.edges.get(edge.index()).map(|edge| edge.to) != Some(target) {
        return Err(StructureError::invalid(format!(
            "label edge {edge} does not enter target {target}"
        )));
    }
    Ok(label_region_by_block
        .get(target.index())
        .copied()
        .flatten()
        .map_or(LabelPlacement::BeforeBlock, LabelPlacement::BeforeRegion))
}
