//! 补充最终发布时的 phi 诊断、控制目标与输入证书校验。
//!
//! 消费已经通过 ownership 验证的 phi 事实，不重建其稳定索引。

use super::*;

pub(super) fn validate_phis(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    let mut unresolved_requirements = vec![0usize; dataflow.phi_candidates.len()];
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
        let phi = &plan.phis[candidate.id.index()];
        if phi.loop_carried_input != super::super::loop_carried_input(plan, &phi.incomings) {
            return Err(StructureError::invalid(format!(
                "{} loop-carried input certificate is stale",
                candidate.id
            )));
        }
        let mut unresolved = false;
        for incoming in &phi.incomings {
            if let Some(edge) = incoming.edge
                && cfg.edges.get(edge.index()).map(|edge| edge.to) != Some(candidate.block)
            {
                return Err(StructureError::invalid(format!(
                    "{} incoming edge does not target its phi block",
                    candidate.id
                )));
            }
            unresolved |= matches!(
                incoming.disposition,
                PhiIncomingDisposition::DiagnosticUnresolved
            );
        }
        let has_requirement = unresolved_requirements[candidate.id.index()] == 1;
        if unresolved != has_requirement || unresolved_requirements[candidate.id.index()] > 1 {
            return Err(StructureError::invalid(format!(
                "{} unresolved disposition/requirement mismatch",
                candidate.id
            )));
        }
    }
    Ok(())
}
