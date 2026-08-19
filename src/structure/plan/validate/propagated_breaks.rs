//! 校验跨嵌套循环传播的 break；依赖循环边索引与区域导航，不负责普通 break；例如确认传播链逐层指向合法外层循环。

use super::*;

pub(super) fn validate_propagated_breaks(
    cfg: &Cfg,
    plan: &StructurePlan,
    intervals: &RegionNavigation,
    nearest_loop: &[Option<RegionId>],
) -> Result<(), StructureError> {
    let mut target_by_region = vec![None; plan.regions.len()];
    let mut continuation_by_region = vec![None; plan.regions.len()];
    for (loop_index, payload) in plan.loops.iter().enumerate() {
        let Some(target) = payload.propagated_break else {
            continue;
        };
        let source = plan
            .loop_region(super::super::LoopPlanId(loop_index))
            .ok_or_else(|| StructureError::invalid("propagated break source has no loop region"))?;
        let Some(RegionPlan::Loop {
            plan: target_plan, ..
        }) = plan.region(target)
        else {
            return Err(StructureError::invalid(
                "propagated break targets a non-loop region",
            ));
        };
        if target == source || !intervals.contains(target, source) {
            return Err(StructureError::invalid(
                "propagated break target does not contain its source loop",
            ));
        }
        if matches!(
            payload.kind,
            crate::structure::LoopKindHint::NumericForLike
                | crate::structure::LoopKindHint::GenericForLike
        ) {
            for edge in payload
                .control_edges
                .preheader_exit
                .into_iter()
                .chain(payload.control_edges.exit.iter().copied())
            {
                let edge_plan = plan.edge_plan(edge).ok_or_else(|| {
                    StructureError::invalid("VM-for propagated break syntax exit has no edge plan")
                })?;
                if edge_plan.transfer != EdgeTransfer::BranchArm(BranchArm::LoopExit) {
                    return Err(StructureError::invalid(format!(
                        "VM-for propagated break edge {edge} has edge/completion double ownership: {:?}",
                        edge_plan.transfer
                    )));
                }
            }
        }
        target_by_region[source.index()] = Some(target);
        continuation_by_region[source.index()] = plan
            .loop_(*target_plan)
            .and_then(|loop_| loop_.continuation);
    }

    // 只记录每个 region 最近的传播 loop。若一条 edge 没有离开它，就必然也没有
    // 离开更外层的传播 loop；若离开了，transfer 对最近 owner 的证明可沿相同 target
    // 链向祖先复用。这样无需为每个 loop 重扫整张 CFG。
    let mut nearest_propagated = vec![None; plan.regions.len()];
    for region in intervals.preorder.iter().copied() {
        let inherited =
            intervals.parent[region.index()].and_then(|parent| nearest_propagated[parent.index()]);
        nearest_propagated[region.index()] = if target_by_region[region.index()].is_some() {
            Some(region)
        } else {
            inherited
        };
    }

    // 跨过多个源码 loop 的 break 需要每个中间 loop 在完成后继续传播；否则一个
    // Lua `break` 只能退出最内层。该链只沿 loop-parent 检查一次。
    for source in intervals.preorder.iter().copied() {
        let Some(target) = target_by_region[source.index()] else {
            continue;
        };
        let parent_loop = intervals.parent[source.index()]
            .and_then(|parent| nearest_loop[parent.index()])
            .ok_or_else(|| {
                StructureError::invalid("propagated break source has no containing loop")
            })?;
        if parent_loop != target && target_by_region[parent_loop.index()] != Some(target) {
            return Err(StructureError::invalid(
                "propagated break chain changes target before reaching its owner",
            ));
        }
    }

    let mut completing_exit = vec![false; plan.regions.len()];
    for (index, (edge, edge_plan)) in cfg.edges.iter().zip(&plan.edge_plans).enumerate() {
        if matches!(
            edge_plan.transfer,
            EdgeTransfer::Return | EdgeTransfer::TailCall | EdgeTransfer::Unreachable
        ) {
            continue;
        }
        let source_owner = plan.region_for_block(edge.from).ok_or_else(|| {
            StructureError::invalid(format!("propagated break edge #{index} source is unowned"))
        })?;
        let Some(source_loop) = nearest_propagated[source_owner.index()] else {
            continue;
        };
        if plan
            .region_for_block(edge.to)
            .is_some_and(|target_owner| intervals.contains(source_loop, target_owner))
        {
            continue;
        }
        let target = target_by_region[source_loop.index()]
            .ok_or_else(|| StructureError::invalid("propagated break index is sparse"))?;
        let valid = matches!(edge_plan.transfer, EdgeTransfer::Break(owner) if owner == target)
            || edge_plan.transfer == EdgeTransfer::BranchArm(BranchArm::LoopExit)
                && Some(edge.to) == continuation_by_region[source_loop.index()];
        if !valid {
            return Err(StructureError::invalid(format!(
                "loop #{} propagated break has a non-propagating exit edge #{index}",
                source_loop.index()
            )));
        }
        completing_exit[source_loop.index()] = true;
    }

    // 内层完成会执行计划中的下一层 break；逆 preorder 把该完成事实沿同 target
    // 的连续传播链汇总，仍然只访问每个 region 一次。
    for source in intervals.preorder.iter().copied().rev() {
        let Some(target) = target_by_region[source.index()] else {
            continue;
        };
        if !completing_exit[source.index()] {
            return Err(StructureError::invalid(
                "propagated break loop has no completing exit",
            ));
        }
        let parent_loop =
            intervals.parent[source.index()].and_then(|parent| nearest_loop[parent.index()]);
        if let Some(parent) = parent_loop
            && target_by_region[parent.index()] == Some(target)
        {
            completing_exit[parent.index()] = true;
        }
    }
    Ok(())
}
