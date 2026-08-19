//! 校验结构化分支的条件与 arm 边界；依赖条件边索引和区域统计，不负责条件归约；例如确认 then/else 精确覆盖各自区域。

use super::*;

pub(super) fn forwarded_actions_are_empty(
    plan: &StructurePlan,
    edge: &super::super::EdgePlan,
) -> bool {
    edge.forward_route
        .is_none_or(|route| plan.forward_route_action_edges(route).next().is_none())
}

pub(super) fn validate_branch_plans(
    cfg: &Cfg,
    plan: &StructurePlan,
    intervals: &RegionNavigation,
    block_stats: &RegionBlockStats,
    condition_edges: &ConditionEdgeIndex,
) -> Result<(), StructureError> {
    let mut seen = vec![false; plan.branches.len()];
    for (index, region) in plan.regions.iter().enumerate() {
        let RegionPlan::Branch {
            plan: branch_id,
            entry,
            condition,
            continuation,
            ..
        } = region
        else {
            continue;
        };
        let payload = plan.branch(*branch_id).ok_or_else(|| {
            StructureError::invalid(format!("branch region #{index} has no payload"))
        })?;
        if seen[branch_id.index()] {
            return Err(StructureError::invalid(format!(
                "branch payload #{} has conflicting region ownership",
                branch_id.index()
            )));
        }
        seen[branch_id.index()] = true;
        if payload.header != *entry || payload.continuation != *continuation {
            return Err(StructureError::invalid(format!(
                "branch payload #{} has stale entry or continuation",
                branch_id.index()
            )));
        }
        let condition_id = payload.condition;

        let condition_plan = plan.condition(condition_id).ok_or_else(|| {
            StructureError::invalid(format!(
                "branch payload #{} references a missing condition",
                branch_id.index()
            ))
        })?;
        if condition_plan.header() != Some(payload.header) {
            return Err(StructureError::invalid(format!(
                "branch payload #{} condition has a stale header",
                branch_id.index()
            )));
        }
        let expected_condition_blocks = condition_plan.blocks().collect::<Vec<_>>();
        if !region_matches_exact_blocks(
            plan,
            intervals,
            block_stats,
            *condition,
            expected_condition_blocks.len(),
            expected_condition_blocks.iter().copied(),
        ) {
            return Err(StructureError::invalid(format!(
                "branch payload #{} condition region has stale coverage",
                branch_id.index()
            )));
        }

        let (expected_then, expected_else) = if payload.condition_inverted {
            (condition_plan.falsy, condition_plan.truthy)
        } else {
            (condition_plan.truthy, condition_plan.falsy)
        };
        if (payload.then_edge, payload.else_edge) != (expected_then, expected_else) {
            return Err(StructureError::invalid(format!(
                "branch payload #{} has stale frozen edge polarity",
                branch_id.index()
            )));
        }
        for (edge, expected_arm) in [
            (
                payload.then_edge,
                Some(if payload.condition_inverted {
                    BranchArm::Falsy
                } else {
                    BranchArm::Truthy
                }),
            ),
            (
                payload.else_edge,
                Some(if payload.condition_inverted {
                    BranchArm::Truthy
                } else {
                    BranchArm::Falsy
                }),
            ),
        ] {
            let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "branch payload #{} references a missing edge",
                    branch_id.index()
                ))
            })?;
            plan.edge_plan(edge).ok_or_else(|| {
                StructureError::invalid(format!(
                    "branch payload #{} edge has no plan",
                    branch_id.index()
                ))
            })?;
            if let Some(expected_arm) = expected_arm
                && condition_terminal_arm(condition_edges, payload.condition, edge)
                    != Some(expected_arm)
            {
                return Err(StructureError::invalid(format!(
                    "branch payload #{} edge {edge} contradicts its final condition arm",
                    branch_id.index()
                )));
            }
            if !region_contains_block(plan, intervals, *condition, cfg_edge.from) {
                return Err(StructureError::invalid(format!(
                    "branch payload #{} edge {edge} starts outside its condition region",
                    branch_id.index()
                )));
            }
        }
        if payload
            .value_plan
            .as_ref()
            .is_some_and(|value| Some(value.merge) != *continuation)
        {
            return Err(StructureError::invalid(format!(
                "branch payload #{} value merge has a stale continuation",
                branch_id.index()
            )));
        }
    }
    if seen.iter().any(|seen| !seen) {
        return Err(StructureError::invalid(
            "one or more branch payloads have no owning region",
        ));
    }
    Ok(())
}
