//! 安装 phi plans、认领 region/condition/branch/loop 输入并标记 disposition；依赖各结构 payload，不负责跨区域 owner 传播；例如将 branch result 认领为 RegionResult。

use super::*;

pub(super) fn install_phi_plans(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &mut StructurePlan,
    dispositions: Vec<Vec<PhiIncomingDisposition>>,
) -> Result<(), StructureError> {
    let mut phis = Vec::with_capacity(dataflow.phi_candidates.len());
    let mut phis_by_block = vec![Vec::new(); cfg.blocks.len()];
    let mut phis_by_region = vec![Vec::new(); plan.regions().len()];
    let mut region_seen_at = vec![usize::MAX; plan.regions().len()];

    for (phi, owners) in dataflow.phi_candidates.iter().zip(dispositions) {
        if phi.incoming.len() != owners.len() {
            return Err(StructureError::invalid(format!(
                "{} has {} owners for {} incomings",
                phi.id,
                owners.len(),
                phi.incoming.len()
            )));
        }
        let Some(block_phis) = phis_by_block.get_mut(phi.block.index()) else {
            return Err(StructureError::invalid(format!(
                "{} target block is outside the CFG arena",
                phi.id
            )));
        };
        block_phis.push(phi.id);

        let incomings = phi
            .incoming
            .iter()
            .zip(owners)
            .map(|(incoming, disposition)| PhiIncomingPlan {
                edge: incoming.edge,
                value: incoming.value,
                disposition,
            })
            .collect::<Vec<_>>();
        for incoming in &incomings {
            let Some(region) = incoming.disposition.region() else {
                continue;
            };
            let Some(seen) = region_seen_at.get_mut(region.index()) else {
                return Err(StructureError::invalid(format!(
                    "{} refers to missing value owner region {}",
                    phi.id,
                    region.index()
                )));
            };
            if *seen == phi.id.index() {
                continue;
            }
            *seen = phi.id.index();
            phis_by_region[region.index()].push(phi.id);
        }
        phis.push(PhiPlan {
            phi: phi.id,
            block: phi.block,
            reg: phi.reg,
            incomings,
        });
    }

    plan.phis = phis;
    plan.phis_by_block = phis_by_block;
    plan.phis_by_region = phis_by_region;
    Ok(())
}

pub(super) fn validate_phi_arena(dataflow: &DataflowFacts) -> Result<(), StructureError> {
    for (index, phi) in dataflow.phi_candidates.iter().enumerate() {
        if phi.id.index() != index {
            return Err(StructureError::invalid(format!(
                "phi arena slot {index} contains {}",
                phi.id
            )));
        }
    }
    Ok(())
}

pub(super) fn regions_owned_by_island_graph(
    plan: &StructurePlan,
) -> Result<Vec<bool>, StructureError> {
    let region_count = plan.regions().len();
    let mut resolved = vec![None; region_count];
    let mut visiting = vec![false; region_count];

    for start in 0..region_count {
        if resolved[start].is_some() {
            continue;
        }
        let mut path = Vec::new();
        let mut current = Some(RegionId(start));
        let inherited = loop {
            let Some(region) = current else {
                break false;
            };
            let Some(region_plan) = plan.region(region) else {
                return Err(StructureError::invalid(format!(
                    "region {} has a missing containment node",
                    region.index()
                )));
            };
            if let Some(flag) = resolved[region.index()] {
                break flag;
            }
            if visiting[region.index()] {
                return Err(StructureError::invalid(format!(
                    "region containment contains a cycle at {}",
                    region.index()
                )));
            }
            visiting[region.index()] = true;
            path.push(region);
            current = region_plan.parent();
        };

        let mut inherited = inherited;
        while let Some(region) = path.pop() {
            inherited = match plan.region(region) {
                Some(RegionPlan::Unstructured { .. }) => true,
                Some(
                    RegionPlan::Branch { .. }
                    | RegionPlan::ValueDecision { .. }
                    | RegionPlan::Loop { .. },
                ) => false,
                Some(RegionPlan::Block { .. } | RegionPlan::Sequence { .. }) => inherited,
                None => {
                    return Err(StructureError::invalid(format!(
                        "missing region {}",
                        region.index()
                    )));
                }
            };
            resolved[region.index()] = Some(inherited);
            visiting[region.index()] = false;
        }
    }

    Ok(resolved
        .into_iter()
        .map(Option::unwrap_or_default)
        .collect())
}

pub(super) fn claim_selected_region_values(
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    owner_index: &RegionOwnerIndex,
    dispositions: &mut [Vec<Option<PhiIncomingDisposition>>],
) -> Result<(), StructureError> {
    let mut loop_incomings = LoopIncomingClassifier::new(dataflow)?;
    for (region_id, region) in plan.regions() {
        match region {
            RegionPlan::Branch {
                plan: branch_id, ..
            } => {
                let branch = plan.branch(*branch_id).ok_or_else(|| {
                    StructureError::invalid(format!(
                        "branch region {} references missing plan {}",
                        region_id.index(),
                        branch_id.index()
                    ))
                })?;
                claim_condition_values(
                    dataflow,
                    plan,
                    owner_index,
                    dispositions,
                    region_id,
                    branch.condition,
                )?;
                if let Some(merge) = &branch.value_plan {
                    for value in &merge.values {
                        claim_branch_result(dataflow, owner_index, dispositions, region_id, value)?;
                    }
                }
            }
            RegionPlan::Loop { plan: loop_id, .. } => {
                let loop_plan = plan.loop_(*loop_id).ok_or_else(|| {
                    StructureError::invalid(format!(
                        "loop region {} references missing plan {}",
                        region_id.index(),
                        loop_id.index()
                    ))
                })?;
                if let Some(condition) = loop_plan.condition {
                    claim_condition_values(
                        dataflow,
                        plan,
                        owner_index,
                        dispositions,
                        region_id,
                        condition,
                    )?;
                }
                for value in &loop_plan.carried_values {
                    claim_loop_header_value(
                        dataflow,
                        owner_index,
                        dispositions,
                        region_id,
                        value,
                        &mut loop_incomings,
                    )?;
                }
                for exit in &loop_plan.exit_values {
                    for value in &exit.values {
                        claim_loop_result(
                            dataflow,
                            owner_index,
                            dispositions,
                            region_id,
                            value,
                            &mut loop_incomings,
                        )?;
                    }
                }
            }
            RegionPlan::ValueDecision { plan: decision, .. } => {
                let decision = plan.value_decision(*decision).ok_or_else(|| {
                    StructureError::invalid(format!(
                        "value decision region {} references a missing payload",
                        region_id.index()
                    ))
                })?;
                for phi_id in std::iter::once(decision.result_phi)
                    .chain(decision.absorbed_phis.iter().copied())
                {
                    let phi = require_phi(dataflow, phi_id)?;
                    for slot in &mut dispositions[phi.id.index()] {
                        claim_owner(
                            owner_index,
                            slot,
                            PhiIncomingDisposition::RegionResult(region_id),
                        );
                    }
                }
            }
            RegionPlan::Block { .. }
            | RegionPlan::Sequence { .. }
            | RegionPlan::Unstructured { .. } => {}
        }
    }
    Ok(())
}

pub(super) fn claim_condition_values(
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    owner_index: &RegionOwnerIndex,
    dispositions: &mut [Vec<Option<PhiIncomingDisposition>>],
    region: RegionId,
    condition: crate::structure::ConditionPlanId,
) -> Result<(), StructureError> {
    let condition = plan.condition(condition).ok_or_else(|| {
        StructureError::invalid("selected region references a missing condition value plan")
    })?;
    for node in &condition.nodes {
        let Some(value) = node.materialized_value else {
            continue;
        };
        let phi = require_phi(dataflow, value.phi)?;
        for slot in &mut dispositions[phi.id.index()] {
            claim_owner(
                owner_index,
                slot,
                PhiIncomingDisposition::RegionResult(region),
            );
        }
    }
    Ok(())
}

pub(in crate::structure) fn incoming_requires_edge_copy(
    plan: &StructurePlan,
    phi: PhiId,
    disposition: PhiIncomingDisposition,
) -> bool {
    !matches!(
        disposition,
        PhiIncomingDisposition::Dead | PhiIncomingDisposition::DiagnosticUnresolved
    ) && !(matches!(disposition, PhiIncomingDisposition::RegionResult(_))
        && (plan.condition_value_owner(phi).is_some() || plan.value_decision_owner(phi).is_some()))
}

pub(super) fn claim_branch_result(
    dataflow: &DataflowFacts,
    owner_index: &RegionOwnerIndex,
    dispositions: &mut [Vec<Option<PhiIncomingDisposition>>],
    region: RegionId,
    value: &BranchValueMergeValue,
) -> Result<(), StructureError> {
    let phi = require_phi(dataflow, value.phi_id)?;
    for (incoming_index, incoming) in phi.incoming.iter().enumerate() {
        if incoming.pred.is_some_and(|pred| {
            value.then_arm.preds.contains(&pred) || value.else_arm.preds.contains(&pred)
        }) {
            claim_owner(
                owner_index,
                &mut dispositions[phi.id.index()][incoming_index],
                PhiIncomingDisposition::RegionResult(region),
            );
        }
    }
    Ok(())
}

pub(super) fn claim_loop_header_value(
    dataflow: &DataflowFacts,
    owner_index: &RegionOwnerIndex,
    dispositions: &mut [Vec<Option<PhiIncomingDisposition>>],
    region: RegionId,
    value: &LoopValueMerge,
    classifier: &mut LoopIncomingClassifier,
) -> Result<(), StructureError> {
    let phi = require_phi(dataflow, value.phi_id)?;
    let classes = classifier.classify(phi, &value.inside_arm, &value.outside_arm)?;
    for (incoming_index, class) in classes.into_iter().enumerate() {
        if class == (LOOP_INSIDE | LOOP_OUTSIDE) {
            return Err(StructureError::invalid(format!(
                "{} incoming #{incoming_index} belongs to both loop arms",
                phi.id
            )));
        }
        let owner = if class == LOOP_INSIDE {
            Some(PhiIncomingDisposition::LoopCarried(region))
        } else if class == LOOP_OUTSIDE {
            Some(PhiIncomingDisposition::RegionInput(region))
        } else {
            None
        };
        if let Some(owner) = owner {
            claim_owner(
                owner_index,
                &mut dispositions[phi.id.index()][incoming_index],
                owner,
            );
        }
    }
    Ok(())
}

pub(super) fn claim_loop_result(
    dataflow: &DataflowFacts,
    owner_index: &RegionOwnerIndex,
    dispositions: &mut [Vec<Option<PhiIncomingDisposition>>],
    region: RegionId,
    value: &LoopValueMerge,
    classifier: &mut LoopIncomingClassifier,
) -> Result<(), StructureError> {
    let phi = require_phi(dataflow, value.phi_id)?;
    let classes = classifier.classify(phi, &value.inside_arm, &value.outside_arm)?;
    for (incoming_index, class) in classes.into_iter().enumerate() {
        if class == (LOOP_INSIDE | LOOP_OUTSIDE) {
            return Err(StructureError::invalid(format!(
                "{} incoming #{incoming_index} belongs to both loop result arms",
                phi.id
            )));
        }
        if class & LOOP_INSIDE != 0 {
            claim_owner(
                owner_index,
                &mut dispositions[phi.id.index()][incoming_index],
                PhiIncomingDisposition::RegionResult(region),
            );
        }
    }
    Ok(())
}
