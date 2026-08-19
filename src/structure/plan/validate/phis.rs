//! 校验 SSA φ 输入的结构化处置；依赖数据流事实与边计划，不负责构建 SSA；例如确保每个 incoming 已被转移、保留或消费。

use super::*;

pub(super) fn validate_phis(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    if plan.phis.len() != dataflow.phi_candidates.len()
        || plan.phis_by_block.len() != cfg.blocks.len()
        || plan.phis_by_region.len() != plan.regions.len()
    {
        return Err(StructureError::invalid("phi plan/index length mismatch"));
    }
    let mut expected_by_block = vec![Vec::new(); cfg.blocks.len()];
    let mut expected_by_region = vec![BTreeSet::new(); plan.regions.len()];
    let mut expected_edge_copies = vec![Vec::new(); cfg.edges.len()];
    let mut unresolved_requirements = vec![0usize; dataflow.phi_candidates.len()];
    let canonical_targets = crate::structure::phi_facts::CanonicalEdgeCopyTargets::build(
        plan,
        dataflow.phi_candidates.len(),
    )?;
    for (_, requirement) in plan.requirements.iter() {
        if let PlanRequirement::UnresolvedValue { phi_id, block, reg } = requirement {
            let Some(count) = unresolved_requirements.get_mut(phi_id.index()) else {
                return Err(StructureError::invalid(format!(
                    "unresolved requirement references missing {phi_id}"
                )));
            };
            let candidate = &dataflow.phi_candidates[phi_id.index()];
            if candidate.id != *phi_id || candidate.block != *block || candidate.reg != *reg {
                return Err(StructureError::invalid(format!(
                    "unresolved requirement for {phi_id} has stale location"
                )));
            }
            *count += 1;
        }
    }
    for candidate in &dataflow.phi_candidates {
        let phi = plan.phi_plan(candidate.id).ok_or_else(|| {
            StructureError::invalid(format!("{} has no final value plan", candidate.id))
        })?;
        if phi.phi != candidate.id
            || phi.block != candidate.block
            || phi.reg != candidate.reg
            || phi.incomings.len() != candidate.incoming.len()
        {
            return Err(StructureError::invalid(format!(
                "{} identity/incoming shape is stale",
                candidate.id
            )));
        }
        expected_by_block[candidate.block.index()].push(candidate.id);
        let mut unresolved = false;
        for (incoming, expected) in phi.incomings.iter().zip(&candidate.incoming) {
            if incoming.edge != expected.edge || incoming.value != expected.value {
                return Err(StructureError::invalid(format!(
                    "{} incoming identity is stale",
                    candidate.id
                )));
            }
            if let Some(edge) = incoming.edge
                && cfg.edges.get(edge.index()).map(|edge| edge.to) != Some(candidate.block)
            {
                return Err(StructureError::invalid(format!(
                    "{} incoming edge does not target its phi block",
                    candidate.id
                )));
            }
            let copy_target =
                canonical_targets.for_incoming(plan, candidate, expected, incoming.disposition);
            match incoming.disposition {
                PhiIncomingDisposition::RegionInput(region)
                | PhiIncomingDisposition::RegionResult(region)
                | PhiIncomingDisposition::LoopCarried(region)
                    if region.index() >= plan.regions.len() =>
                {
                    return Err(StructureError::invalid(format!(
                        "{} incoming references missing region",
                        candidate.id
                    )));
                }
                PhiIncomingDisposition::RegionInput(region)
                | PhiIncomingDisposition::RegionResult(region)
                | PhiIncomingDisposition::LoopCarried(region) => {
                    expected_by_region[region.index()].insert(candidate.id);
                    if crate::structure::phi_facts::incoming_requires_edge_copy(
                        plan,
                        candidate.id,
                        incoming.disposition,
                    ) && let Some(edge) = incoming.edge
                    {
                        expected_edge_copies[edge.index()].push(super::super::PhiEdgeCopy {
                            phi_id: copy_target,
                            value: incoming.value,
                        });
                    }
                }
                PhiIncomingDisposition::EdgeCopy => {
                    let edge = incoming.edge.ok_or_else(|| {
                        StructureError::invalid(format!(
                            "{} synthetic incoming cannot be an edge copy",
                            candidate.id
                        ))
                    })?;
                    expected_edge_copies[edge.index()].push(super::super::PhiEdgeCopy {
                        phi_id: copy_target,
                        value: incoming.value,
                    });
                }
                PhiIncomingDisposition::DiagnosticUnresolved => unresolved = true,
                PhiIncomingDisposition::Dead => {}
            }
        }
        let has_requirement = unresolved_requirements[candidate.id.index()] == 1;
        if unresolved != has_requirement || unresolved_requirements[candidate.id.index()] > 1 {
            return Err(StructureError::invalid(format!(
                "{} unresolved disposition/requirement mismatch",
                candidate.id
            )));
        }
    }
    if plan.phis_by_block != expected_by_block {
        return Err(StructureError::invalid("phi block reverse index is stale"));
    }
    for (index, expected) in expected_by_region.iter().enumerate() {
        if plan.phis_by_region[index]
            .iter()
            .copied()
            .collect::<BTreeSet<_>>()
            != *expected
        {
            return Err(StructureError::invalid(format!(
                "region #{index} phi reverse index is stale"
            )));
        }
    }
    if crate::structure::phi_facts::build_forwarded_action_heads(plan)? != plan.forward_action_head
    {
        return Err(StructureError::invalid(
            "forwarded phi action index is stale",
        ));
    }
    for (index, expected) in expected_edge_copies.iter().enumerate() {
        if plan.edge_plans[index].phi_copies != *expected {
            return Err(StructureError::invalid(format!(
                "edge #{index} dense phi actions are stale or conflicting"
            )));
        }
    }
    Ok(())
}
