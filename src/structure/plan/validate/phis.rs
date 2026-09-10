//! 补充最终发布时的 phi 诊断、控制目标与输入证书合同。
//!
//! 本入口位于 validate_phi_ownership 成功之后；其已校验的 phi 身份、incoming、
//! 反向索引与 canonical edge copies 在后续 loop protocol/emission 冻结中不再修改。
//! 这里只补最终要求，不再次重建那些索引。例如 unresolved 的唯一诊断必须仍指向
//! 同一 phi 位置，实际 incoming edge 必须进入该 phi 的 block。

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
