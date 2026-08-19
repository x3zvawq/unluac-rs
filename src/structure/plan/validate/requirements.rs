//! 校验后端能力需求及其证据；依赖边与区域计划，不负责能力降级；例如确认 goto 需求引用真实的跨区边。

use super::*;

pub(super) fn validate_requirements(
    cfg: &Cfg,
    plan: &StructurePlan,
    _intervals: &RegionNavigation,
) -> Result<(), StructureError> {
    if plan.requirements.by_edge.len() != cfg.edges.len()
        || plan.requirements.unresolved_by_block.len() != cfg.blocks.len()
    {
        return Err(StructureError::invalid(
            "requirement reverse index length mismatch",
        ));
    }
    let mut required_features = BTreeSet::new();
    let mut expected_by_edge = vec![Vec::new(); cfg.edges.len()];
    let mut expected_unresolved_by_block = vec![false; cfg.blocks.len()];
    let mut multi_entry_requirement = vec![false; plan.regions.len()];
    for (id, requirement) in plan.requirements.iter() {
        match requirement {
            PlanRequirement::Goto { edge, label, .. } => {
                if !matches!(plan.edge_plan(*edge).map(|plan| plan.transfer), Some(EdgeTransfer::Goto(target, _)) if target == *label)
                {
                    return Err(StructureError::invalid(format!(
                        "goto requirement #{} disagrees with edge transfer",
                        id.index()
                    )));
                }
                required_features.insert(ControlFlowFeature::GotoLabel);
                expected_by_edge[edge.index()].push(id);
            }
            PlanRequirement::Continue { edge, loop_region } => {
                if !matches!(plan.edge_plan(*edge).map(|plan| plan.transfer), Some(EdgeTransfer::Continue(region)) if region == *loop_region)
                {
                    return Err(StructureError::invalid(format!(
                        "continue requirement #{} disagrees with edge transfer",
                        id.index()
                    )));
                }
                required_features.insert(ControlFlowFeature::ContinueStatement);
                expected_by_edge[edge.index()].push(id);
            }
            PlanRequirement::MultiEntryIsland {
                region,
                entry_count,
            } => {
                let valid = matches!(
                    plan.region(*region),
                    Some(RegionPlan::Unstructured { entries, .. })
                        if entries.len() == *entry_count && *entry_count > 1
                );
                let Some(seen) = multi_entry_requirement.get_mut(region.index()) else {
                    return Err(StructureError::invalid(
                        "multi-entry requirement references a missing region",
                    ));
                };
                if !valid || std::mem::replace(seen, true) {
                    return Err(StructureError::invalid("multi-entry requirement is stale"));
                }
                required_features.insert(ControlFlowFeature::GotoLabel);
            }
            PlanRequirement::UnresolvedValue { block, .. } => {
                let unresolved = expected_unresolved_by_block
                    .get_mut(block.index())
                    .ok_or_else(|| {
                        StructureError::invalid(
                            "unresolved requirement references a missing CFG block",
                        )
                    })?;
                *unresolved = true;
            }
        }
    }
    for (index, region) in plan.regions.iter().enumerate() {
        let expected = matches!(
            region,
            RegionPlan::Unstructured { entries, .. } if entries.len() > 1
        );
        if multi_entry_requirement[index] != expected {
            return Err(StructureError::invalid(format!(
                "region #{index} multi-entry requirement coverage is stale"
            )));
        }
    }
    if required_features != plan.requirements.required_features {
        return Err(StructureError::invalid(
            "required control-flow feature index is stale",
        ));
    }
    if expected_by_edge != plan.requirements.by_edge {
        return Err(StructureError::invalid(
            "requirement edge reverse index is incomplete or stale",
        ));
    }
    if expected_unresolved_by_block != plan.requirements.unresolved_by_block {
        return Err(StructureError::invalid(
            "unresolved requirement block index is incomplete or stale",
        ));
    }
    let expected_unavailable = required_features
        .iter()
        .copied()
        .filter(|feature| match feature {
            ControlFlowFeature::GotoLabel => !plan.requirements.caps.goto_label,
            ControlFlowFeature::ContinueStatement => !plan.requirements.caps.continue_stmt,
        })
        .collect::<BTreeSet<_>>();
    if expected_unavailable != plan.requirements.unavailable_features {
        return Err(StructureError::invalid(
            "unavailable control-flow feature index is stale",
        ));
    }
    Ok(())
}
