//! 校验单遍分支围栏及逃逸边；依赖区域导航与边计划，不负责普通分支/循环；例如确认
//! fence 的出口动作落在合法位置，并拒绝 synthetic repeat 遮蔽祖先 break/continue。

use super::*;

pub(super) fn validate_single_pass_plans(
    cfg: &Cfg,
    plan: &StructurePlan,
    intervals: &RegionNavigation,
) -> Result<(), StructureError> {
    if plan.single_pass_by_region.len() != plan.regions.len() {
        return Err(StructureError::invalid(
            "single-pass reverse index length mismatch",
        ));
    }
    let mut seen_regions = vec![false; plan.regions.len()];
    for (index, fence) in plan.single_passes.iter().enumerate() {
        if fence.region.index() >= plan.regions.len()
            || std::mem::replace(&mut seen_regions[fence.region.index()], true)
            || plan.single_pass_by_region[fence.region.index()]
                != Some(super::super::SinglePassPlanId(index))
            || !matches!(
                plan.region(fence.region),
                Some(RegionPlan::Sequence {
                    parent: Some(_),
                    ..
                })
            )
        {
            return Err(StructureError::invalid(format!(
                "single-pass payload #{index} has a stale region identity"
            )));
        }
        let entry = plan.region_for_block(fence.entry).ok_or_else(|| {
            StructureError::invalid(format!("single-pass payload #{index} entry is unowned"))
        })?;
        let tail = plan.region_for_block(fence.tail).ok_or_else(|| {
            StructureError::invalid(format!("single-pass payload #{index} tail is unowned"))
        })?;
        if !intervals.contains(fence.region, entry)
            || !intervals.contains(fence.region, tail)
            || fence.escape_edges.is_empty()
        {
            return Err(StructureError::invalid(format!(
                "single-pass payload #{index} is not closed over its entry and tail"
            )));
        }
        let tail_edge = cfg
            .succs
            .get(fence.tail.index())
            .and_then(|edges| match edges.as_slice() {
                [edge] => Some(*edge),
                _ => None,
            })
            .and_then(|edge| cfg.edges.get(edge.index()))
            .ok_or_else(|| {
                StructureError::invalid(format!("single-pass payload #{index} tail is not linear"))
            })?;
        if tail_edge.to != fence.continuation {
            return Err(StructureError::invalid(format!(
                "single-pass payload #{index} tail does not reach its continuation"
            )));
        }
        let mut previous = None;
        for edge_ref in &fence.escape_edges {
            if previous.is_some_and(|previous| previous >= *edge_ref) {
                return Err(StructureError::invalid(format!(
                    "single-pass payload #{index} escape edges are not strictly ordered"
                )));
            }
            previous = Some(*edge_ref);
            let edge = cfg.edges.get(edge_ref.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "single-pass payload #{index} references a missing escape edge"
                ))
            })?;
            let source = plan.region_for_block(edge.from).ok_or_else(|| {
                StructureError::invalid(format!(
                    "single-pass payload #{index} escape source is unowned"
                ))
            })?;
            if edge.from == fence.tail
                || edge.to != fence.continuation
                || !intervals.contains(fence.region, source)
                || !single_pass_escape_plan_matches(
                    plan,
                    intervals,
                    fence.region,
                    source,
                    *edge_ref,
                )
            {
                return Err(StructureError::invalid(format!(
                    "single-pass payload #{index} escape edge {edge_ref} is stale: region={:?} entry={} tail={} continuation={} edge={} -> {} plan={:?}",
                    fence.region,
                    fence.entry,
                    fence.tail,
                    fence.continuation,
                    edge.from,
                    edge.to,
                    plan.edge_plan(*edge_ref),
                )));
            }
        }
    }
    for (region, owner) in plan.single_pass_by_region.iter().copied().enumerate() {
        if owner.is_some() != seen_regions[region] {
            return Err(StructureError::invalid(
                "single-pass reverse index has a stale entry",
            ));
        }
    }
    let mut fence_depth = vec![0usize; plan.regions.len()];
    for region in &intervals.preorder {
        let parent_depth = intervals.parent[region.index()]
            .map(|parent| fence_depth[parent.index()])
            .unwrap_or(0);
        fence_depth[region.index()] =
            parent_depth + usize::from(plan.single_pass_by_region[region.index()].is_some());
    }
    let crosses_fence = |source: RegionId, target: RegionId| -> Result<bool, StructureError> {
        let (Some(source_depth), Some(target_depth)) = (
            fence_depth.get(source.index()),
            fence_depth.get(target.index()),
        ) else {
            return Err(StructureError::invalid(
                "single-pass control target is outside the region arena",
            ));
        };
        Ok(intervals.contains(target, source) && source_depth > target_depth)
    };
    for edge_plan in &plan.edge_plans {
        let target = match edge_plan.transfer {
            EdgeTransfer::Break(target) | EdgeTransfer::Continue(target) => target,
            _ => continue,
        };
        let edge = cfg.edges.get(edge_plan.edge.index()).ok_or_else(|| {
            StructureError::invalid("single-pass control edge is outside the CFG")
        })?;
        let source = plan
            .region_for_block(edge.from)
            .ok_or_else(|| StructureError::invalid("single-pass control edge source is unowned"))?;
        if crosses_fence(source, target)? {
            return Err(StructureError::invalid(format!(
                "edge {} control transfer is shadowed by a single-pass fence",
                edge_plan.edge
            )));
        }
    }
    for (index, payload) in plan.loops.iter().enumerate() {
        let Some(target) = payload.propagated_break else {
            continue;
        };
        let source = plan
            .loop_region(LoopPlanId(index))
            .ok_or_else(|| StructureError::invalid("single-pass loop source is unowned"))?;
        if crosses_fence(source, target)? {
            return Err(StructureError::invalid(format!(
                "loop #{index} propagated break is shadowed by a single-pass fence"
            )));
        }
    }
    Ok(())
}

/// single-pass escape 通常由 fence 自身发射；唯一允许的更深 owner 是同时被
/// numeric/generic-for protocol 吸收的 LoopExit。此时源码顺序是 `for ... end`
/// 后紧跟祖先 `break`，所以 edge 仍归 for，transfer 则指向包含它的 fence。
pub(super) fn single_pass_escape_plan_matches(
    plan: &StructurePlan,
    intervals: &RegionNavigation,
    fence: RegionId,
    source: RegionId,
    edge: EdgeRef,
) -> bool {
    let Some(edge_plan) = plan.edge_plan(edge) else {
        return false;
    };
    if edge_plan.transfer != EdgeTransfer::Break(fence) || edge_plan.forward_route.is_some() {
        return false;
    }
    if edge_plan.owner == fence {
        return true;
    }
    if !intervals.contains(fence, edge_plan.owner) || !intervals.contains(edge_plan.owner, source) {
        return false;
    }
    let Some(RegionPlan::Loop { plan: loop_id, .. }) = plan.region(edge_plan.owner) else {
        return false;
    };
    let Some(loop_) = plan.loop_(*loop_id) else {
        return false;
    };
    matches!(
        loop_.kind,
        crate::structure::LoopKindHint::NumericForLike
            | crate::structure::LoopKindHint::GenericForLike
    ) && (loop_.control_edges.preheader_exit == Some(edge)
        || loop_.control_edges.exit.binary_search(&edge).is_ok())
}
