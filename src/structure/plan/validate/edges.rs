//! 校验最终边计划、条件内部路由与转发路由；依赖各类 payload 索引，不负责构建路由；例如确保每条 CFG 边仅由一种结构语义消费。

use super::*;

pub(super) struct EdgeValidationIndex {
    continue_barriers: Vec<bool>,
    break_barriers: Vec<bool>,
}

impl EdgeValidationIndex {
    fn new(cfg: &Cfg, plan: &StructurePlan) -> Self {
        let mut continue_barriers = vec![false; cfg.blocks.len()];
        let mut break_barriers = vec![false; cfg.blocks.len()];
        for scope in &plan.scopes {
            mark_block(&mut continue_barriers, scope.entry);
            mark_block(&mut break_barriers, scope.entry);
            if let Some(exit) = scope.exit {
                mark_block(&mut continue_barriers, exit);
                mark_block(&mut break_barriers, exit);
            }
            for close in &scope.close_points {
                if let Some(block) = cfg.instr_to_block.get(close.index()).copied() {
                    mark_block(&mut continue_barriers, block);
                }
            }
        }
        for (_, label) in plan.labels() {
            mark_block(&mut continue_barriers, label.block);
            mark_block(&mut break_barriers, label.block);
        }

        Self {
            continue_barriers,
            break_barriers,
        }
    }
}

pub(super) fn mark_block(index: &mut [bool], block: BlockRef) {
    if let Some(slot) = index.get_mut(block.index()) {
        *slot = true;
    }
}

pub(super) fn validate_edges(
    cfg: &Cfg,
    plan: &StructurePlan,
    intervals: &RegionNavigation,
    edge_regions: &RegionNavigation,
    condition_edges: &ConditionEdgeIndex,
    loop_edges: &LoopEdgeIndex,
) -> Result<(), StructureError> {
    if plan.edge_plans.len() != cfg.edges.len() {
        return Err(StructureError::invalid("edge plan length mismatch"));
    }
    let layout_edges =
        super::super::arena::layout_edge_facts(cfg, &plan.regions, &plan.navigation)?;
    let validation_index = EdgeValidationIndex::new(cfg, plan);
    validate_forward_routes(cfg, plan, intervals, condition_edges, &validation_index)?;
    for (index, edge_plan) in plan.edge_plans.iter().enumerate() {
        if edge_plan.edge.index() != index || edge_plan.owner.index() >= plan.regions.len() {
            return Err(StructureError::invalid(format!(
                "edge plan #{index} has invalid identity or owner"
            )));
        }
        let edge = cfg.edges[index];
        match edge_plan.action_placement {
            EdgeActionPlacement::BeforeTransfer => {}
            EdgeActionPlacement::BeforeTrailingCleanup { cleanup } => {
                let block_range = cfg
                    .blocks
                    .get(edge.from.index())
                    .ok_or_else(|| {
                        StructureError::invalid(format!(
                            "edge #{index} action placement source block is missing"
                        ))
                    })?
                    .instrs;
                if !matches!(edge_plan.transfer, EdgeTransfer::LoopBack(_))
                    || edge_plan.forward_route.is_some()
                    || cfg.succs.get(edge.from.index()).map(Vec::as_slice)
                        != Some(&[edge_plan.edge])
                    || cleanup.is_empty()
                    || cleanup.start.index() <= block_range.start.index()
                    || block_range.last().map(|last| last.index()) != Some(cleanup.end())
                {
                    return Err(StructureError::invalid(format!(
                        "edge #{index} has a stale trailing-cleanup action placement"
                    )));
                }
            }
        }
        if !cfg.reachable_blocks.contains(&edge.from)
            && !matches!(edge_plan.transfer, EdgeTransfer::Unreachable)
        {
            return Err(StructureError::invalid(format!(
                "unreachable edge #{index} has executable transfer"
            )));
        }
        if !matches!(
            edge_plan.transfer,
            EdgeTransfer::Break(_) | EdgeTransfer::Continue(_)
        ) && edge_plan.forward_route.is_some()
        {
            return Err(StructureError::invalid(format!(
                "edge #{index} has a forwarding route without loop control transfer"
            )));
        }
        if edge_plan.transfer == EdgeTransfer::Fallthrough {
            let source = plan.region_for_block(edge.from).ok_or_else(|| {
                StructureError::invalid(format!("edge #{index} source has no region"))
            })?;
            let target = plan.region_for_block(edge.to).ok_or_else(|| {
                StructureError::invalid(format!("edge #{index} target has no region"))
            })?;
            edge_regions
                .edge_relation(edge_plan.edge)
                .and_then(|relation| relation.lca)
                .ok_or_else(|| {
                    StructureError::invalid(format!(
                        "edge #{index} has no containment owner while validating fallthrough"
                    ))
                })?;
            if let Some(source_child) = edge_regions
                .edge_relation(edge_plan.edge)
                .and_then(|relation| relation.source_child)
                && matches!(
                    plan.region(source_child),
                    Some(RegionPlan::Unstructured { .. })
                )
                && !intervals.contains(source_child, target)
                && !plan
                    .navigation
                    .region_can_complete_from(source_child, source, edge.from)
            {
                return Err(StructureError::invalid(format!(
                    "edge #{index} falls through from a non-final island layout item"
                )));
            }
        }
        let island_for_syntax_edge = match (edge_plan.transfer, plan.region(edge_plan.owner)) {
            (
                EdgeTransfer::BranchArm(BranchArm::LoopBody),
                Some(RegionPlan::Loop { plan: loop_id, .. }),
            ) => plan.loop_(*loop_id).is_some_and(|payload| {
                matches!(
                    payload.kind,
                    crate::structure::LoopKindHint::NumericForLike
                        | crate::structure::LoopKindHint::GenericForLike
                ) && loop_edges.has_body(*loop_id, edge_plan.edge)
            }),
            (
                EdgeTransfer::BranchArm(BranchArm::LoopExit),
                Some(RegionPlan::Loop { plan: loop_id, .. }),
            ) => plan.loop_(*loop_id).is_some_and(|payload| {
                matches!(
                    payload.kind,
                    crate::structure::LoopKindHint::NumericForLike
                        | crate::structure::LoopKindHint::GenericForLike
                ) && loop_edges.has_exit(*loop_id, edge_plan.edge)
            }),
            _ => false,
        };
        if layout_edges[index].crosses_island_layout
            && !layout_edges[index].natural
            && !island_for_syntax_edge
            && matches!(
                edge_plan.transfer,
                EdgeTransfer::Fallthrough | EdgeTransfer::BranchArm(_)
            )
        {
            return Err(StructureError::invalid(format!(
                "edge #{index} crosses a non-completing island layout item without an explicit transfer"
            )));
        }
        match edge_plan.transfer {
            EdgeTransfer::Return
                if edge.kind != EdgeKind::Return
                    && shared_pure_terminal_kind(cfg, edge.to) != Some(EdgeKind::Return) =>
            {
                return Err(StructureError::invalid("return transfer kind mismatch"));
            }
            EdgeTransfer::TailCall
                if edge.kind != EdgeKind::TailCall
                    && shared_pure_terminal_kind(cfg, edge.to) != Some(EdgeKind::TailCall) =>
            {
                return Err(StructureError::invalid("tail-call transfer kind mismatch"));
            }
            EdgeTransfer::Goto(label, _)
                if plan.label(label).map(|label| label.block) != Some(edge.to) =>
            {
                return Err(StructureError::invalid(
                    "goto label differs from edge target",
                ));
            }
            EdgeTransfer::Break(region)
                if let Some((_, fence)) = plan.single_pass_for_region(region) =>
            {
                let source = plan.region_for_block(edge.from).ok_or_else(|| {
                    StructureError::invalid(format!("edge #{index} source has no region"))
                })?;
                if !intervals.contains(region, source)
                    || edge.to != fence.continuation
                    || fence.escape_edges.binary_search(&edge_plan.edge).is_err()
                    || !single_pass_escape_plan_matches(
                        plan,
                        intervals,
                        region,
                        source,
                        edge_plan.edge,
                    )
                {
                    return Err(StructureError::invalid(format!(
                        "edge #{index} does not match single-pass region #{}",
                        region.index()
                    )));
                }
            }
            EdgeTransfer::LoopBack(region)
            | EdgeTransfer::Break(region)
            | EdgeTransfer::Continue(region) => {
                let Some(RegionPlan::Loop {
                    plan: loop_id,
                    body,
                    ..
                }) = plan.region(region)
                else {
                    return Err(StructureError::invalid(format!(
                        "edge #{index} references a non-loop control owner"
                    )));
                };
                let loop_ = plan.loop_(*loop_id).ok_or_else(|| {
                    StructureError::invalid(format!("edge #{index} loop payload is missing"))
                })?;
                let source = plan.region_for_block(edge.from).ok_or_else(|| {
                    StructureError::invalid(format!("edge #{index} source has no region"))
                })?;
                if !intervals.contains(region, source) {
                    return Err(StructureError::invalid(format!(
                        "edge #{index} {} -> {} {:?} loop region #{} does not contain source owner #{} ({:?})",
                        edge.from,
                        edge.to,
                        edge_plan.transfer,
                        region.index(),
                        source.index(),
                        plan.region(source),
                    )));
                }
                if matches!(edge_plan.transfer, EdgeTransfer::Break(_))
                    && !intervals.contains(*body, source)
                    && !loop_edges.has_exit(*loop_id, edge_plan.edge)
                {
                    return Err(StructureError::invalid(format!(
                        "edge #{index} break source is outside the loop body/control exit"
                    )));
                }
                let semantic_match = match edge_plan.transfer {
                    EdgeTransfer::LoopBack(_) => loop_edges.has_backedge(*loop_id, edge_plan.edge),
                    EdgeTransfer::Continue(_) => {
                        loop_edges.has_continue(*loop_id, edge_plan.edge)
                            && (loop_.continue_target == Some(edge.to)
                                && edge_plan.forward_route.is_none()
                                || validate_continue_forwarding_route(
                                    cfg, plan, edge_plan, region,
                                )?)
                    }
                    EdgeTransfer::Break(_) => {
                        loop_.continuation == Some(edge.to) && edge_plan.forward_route.is_none()
                            || validate_break_forwarding_route(
                                cfg,
                                plan,
                                intervals,
                                edge_plan,
                                region,
                                loop_.continuation,
                                &validation_index,
                            )?
                    }
                    _ => false,
                };
                // 内层源码 loop 的 VM exit 可以同时承担祖先 loop 的 break。例如
                // generic-for 正常耗尽后直接离开包裹它的 while：该 CFG edge 必须由
                // 内层 loop 消费协议/phi，却要在源码 loop 之后发射外层 break。
                // ownership 因而仍属于内层 syntax region，transfer target 才是祖先。
                let nested_syntax_exit = matches!(edge_plan.transfer, EdgeTransfer::Break(_))
                    && edge_plan.owner != region
                    && intervals.contains(region, edge_plan.owner)
                    && matches!(
                        plan.region(edge_plan.owner),
                        Some(RegionPlan::Loop {
                            plan: owner_loop, ..
                        }) if loop_edges.has_exit(*owner_loop, edge_plan.edge)
                    );
                if !semantic_match || edge_plan.owner != region && !nested_syntax_exit {
                    return Err(StructureError::invalid(format!(
                        "edge #{index} {} -> {} {:?} does not match loop #{} payload: backedges={:?}, continues={:?}, forwarded={:?}, continue_target={:?}, continuation={:?}",
                        edge.from,
                        edge.to,
                        edge_plan.transfer,
                        loop_id.index(),
                        loop_.control_edges.backedges,
                        loop_.control_edges.continues,
                        edge_plan.forward_route,
                        loop_.continue_target,
                        loop_.continuation,
                    )));
                }
            }
            EdgeTransfer::BranchArm(arm) => {
                let valid = match plan.region(edge_plan.owner) {
                    Some(RegionPlan::Branch {
                        plan: branch_id, ..
                    }) => plan.branch(*branch_id).is_some_and(|branch| {
                        let condition_target = condition_edges
                            .first_target(branch.condition, edge_plan.edge)
                            .or_else(|| {
                                condition_edges.terminal_target(branch.condition, edge_plan.edge)
                            });
                        matches!(
                            (condition_target, arm),
                            (Some(ConditionTarget::Truthy), BranchArm::Truthy)
                                | (Some(ConditionTarget::Falsy), BranchArm::Falsy)
                                | (
                                    Some(ConditionTarget::Node(_)),
                                    BranchArm::Truthy | BranchArm::Falsy
                                )
                        )
                    }),
                    Some(RegionPlan::Loop { plan: loop_id, .. }) => {
                        plan.loop_(*loop_id).is_some_and(|loop_| {
                            let condition_target = loop_.condition.and_then(|condition| {
                                condition_edges
                                    .first_target(condition, edge_plan.edge)
                                    .or_else(|| {
                                        condition_edges.terminal_target(condition, edge_plan.edge)
                                    })
                            });
                            match arm {
                                BranchArm::LoopBody => {
                                    loop_edges.has_body(*loop_id, edge_plan.edge)
                                        || loop_.control_edges.preheader_body
                                            == Some(edge_plan.edge)
                                }
                                BranchArm::LoopExit => {
                                    loop_edges.has_exit(*loop_id, edge_plan.edge)
                                        || loop_.control_edges.preheader_exit
                                            == Some(edge_plan.edge)
                                }
                                BranchArm::Truthy => {
                                    matches!(
                                        condition_target,
                                        Some(ConditionTarget::Truthy | ConditionTarget::Node(_))
                                    ) || condition_target.is_none()
                                        && loop_.header == edge.from
                                        && edge.kind == EdgeKind::BranchTrue
                                }
                                BranchArm::Falsy => {
                                    matches!(
                                        condition_target,
                                        Some(ConditionTarget::Falsy | ConditionTarget::Node(_))
                                    ) || condition_target.is_none()
                                        && loop_.header == edge.from
                                        && edge.kind == EdgeKind::BranchFalse
                                }
                            }
                        })
                    }
                    _ => false,
                };
                if !valid {
                    return Err(StructureError::invalid(format!(
                        "edge #{index} branch arm {arm:?} lacks a matching structured header: \
                         owner={:?}, cfg={} -> {} {:?}",
                        edge_plan.owner, edge.from, edge.to, edge.kind,
                    )));
                }
            }
            EdgeTransfer::Unreachable
            | EdgeTransfer::Fallthrough
            | EdgeTransfer::Return
            | EdgeTransfer::TailCall
            | EdgeTransfer::Goto(_, _) => {}
        }
    }
    Ok(())
}

pub(super) fn condition_terminal_arm(
    condition_edges: &ConditionEdgeIndex,
    condition: ConditionPlanId,
    edge: EdgeRef,
) -> Option<BranchArm> {
    match condition_edges.terminal_target(condition, edge)? {
        ConditionTarget::Truthy => Some(BranchArm::Truthy),
        ConditionTarget::Falsy => Some(BranchArm::Falsy),
        ConditionTarget::Node(_) => None,
    }
}

pub(super) fn validate_condition_internal_route(
    cfg: &Cfg,
    plan: &StructurePlan,
    condition_index: usize,
    node_index: usize,
    arc: &super::super::ConditionArcPlan,
) -> Result<(), StructureError> {
    let transfer_position = arc
        .route
        .iter()
        .position(|edge| *edge == arc.transfer)
        .ok_or_else(|| {
            StructureError::invalid(format!(
                "condition payload #{condition_index} node {node_index} transfer is outside its route"
            ))
        })?;
    let internal_len = match arc.target {
        ConditionTarget::Node(_) => {
            if transfer_position + 1 != arc.route.len() {
                return Err(StructureError::invalid(format!(
                    "condition payload #{condition_index} node {node_index} has an executable transfer before another condition node"
                )));
            }
            arc.route.len()
        }
        ConditionTarget::Truthy | ConditionTarget::Falsy => transfer_position,
    };
    for (position, edge) in arc.route.iter().copied().take(internal_len).enumerate() {
        let edge_plan = plan.edge_plan(edge).ok_or_else(|| {
            StructureError::invalid(format!(
                "condition payload #{condition_index} route edge has no final plan"
            ))
        })?;
        if !edge_plan.phi_copies.is_empty()
            || edge_plan.actions_before_trailing_cleanup().is_some()
            || !matches!(
                edge_plan.transfer,
                EdgeTransfer::Fallthrough
                    | EdgeTransfer::BranchArm(BranchArm::Truthy | BranchArm::Falsy)
            )
        {
            return Err(StructureError::invalid(format!(
                "condition payload #{condition_index} node {node_index} route edge {edge} at step {position} has unconsumed actions: {edge_plan:?}"
            )));
        }
        let Some(cfg_edge) = cfg.edges.get(edge.index()) else {
            return Err(StructureError::invalid(format!(
                "condition payload #{condition_index} route references a missing CFG edge"
            )));
        };
        if cfg_edge.from == cfg_edge.to {
            return Err(StructureError::invalid(format!(
                "condition payload #{condition_index} node {node_index} route loops in place"
            )));
        }
    }
    if matches!(arc.target, ConditionTarget::Truthy | ConditionTarget::Falsy)
        && transfer_position + 1 < arc.route.len()
    {
        let edge_plan = plan.edge_plan(arc.transfer).ok_or_else(|| {
            StructureError::invalid(format!(
                "condition payload #{condition_index} transfer edge has no final plan"
            ))
        })?;
        let route = edge_plan
            .forward_route
            .ok_or_else(|| {
                StructureError::invalid(format!(
                    "condition payload #{condition_index} transfer does not own its physical route suffix"
                ))
            })
            .map(|route| plan.forward_route_edges(route).collect::<Vec<_>>())?;
        // `forward_route` 绑定在语义 transfer edge 上，但 route 本身从该 edge 的
        // target 开始，因此只覆盖 condition arc 中 transfer 之后的物理后缀。
        if route.as_slice() != &arc.route[transfer_position + 1..] {
            return Err(StructureError::invalid(format!(
                "condition payload #{condition_index} transfer route suffix is stale"
            )));
        }
    }
    Ok(())
}

pub(super) fn validate_forward_routes(
    cfg: &Cfg,
    plan: &StructurePlan,
    intervals: &RegionNavigation,
    _condition_edges: &ConditionEdgeIndex,
    index: &EdgeValidationIndex,
) -> Result<(), StructureError> {
    let edge_count = cfg.edges.len();
    if plan.forward_next.len() != edge_count
        || plan.forward_preorder.len() != edge_count
        || plan.forward_subtree_end.len() != edge_count
        || plan.forward_depth.len() != edge_count
        || plan.forward_owner_by_edge.len() != edge_count
        || plan.forward_kind_by_edge.len() != edge_count
    {
        return Err(StructureError::invalid(
            "forward route dense index length mismatch",
        ));
    }

    let mut entry_count = vec![0usize; plan.forward_routes.len()];
    let mut entry_by_route = vec![None; plan.forward_routes.len()];
    for edge_plan in &plan.edge_plans {
        let Some(route_id) = edge_plan.forward_route else {
            continue;
        };
        let route = plan.forward_route(route_id).ok_or_else(|| {
            StructureError::invalid(format!(
                "{} references missing forward route #{}",
                edge_plan.edge,
                route_id.index()
            ))
        })?;
        if edge_plan.owner != route.loop_region
            || !matches!(
                (edge_plan.transfer, route.kind),
                (EdgeTransfer::Break(owner), ForwardRouteKind::ExclusiveBreak)
                    | (EdgeTransfer::Continue(owner), ForwardRouteKind::ContinueToTarget)
                    | (EdgeTransfer::Continue(owner), ForwardRouteKind::ContinueLatch)
                    | (
                        EdgeTransfer::Continue(owner),
                        ForwardRouteKind::RepeatConditionArc(_)
                    ) if owner == route.loop_region
            )
        {
            return Err(StructureError::invalid(format!(
                "{} has a forwarding route inconsistent with its transfer",
                edge_plan.edge
            )));
        }
        if cfg.edges.get(edge_plan.edge.index()).map(|edge| edge.to) != Some(route.start) {
            return Err(StructureError::invalid(format!(
                "{} does not enter the start of forward route #{}",
                edge_plan.edge,
                route_id.index()
            )));
        }
        entry_count[route_id.index()] = entry_count[route_id.index()]
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("forward route entry count overflow"))?;
        entry_by_route[route_id.index()] = Some(edge_plan.edge);
    }

    let mut first_route = vec![None; edge_count];
    let mut is_route_last = vec![false; edge_count];
    for (route_id, route) in plan.forward_routes() {
        if entry_count[route_id.index()] == 0 {
            return Err(StructureError::invalid(format!(
                "forward route #{} has no bound entry",
                route_id.index()
            )));
        }
        if route.kind == ForwardRouteKind::ExclusiveBreak && entry_count[route_id.index()] != 1 {
            return Err(StructureError::invalid(format!(
                "exclusive break route #{} has multiple entries",
                route_id.index()
            )));
        }
        if route.len == 0
            || route.first.index() >= edge_count
            || route.last.index() >= edge_count
            || cfg.edges[route.first.index()].from != route.start
            || cfg.edges[route.last.index()].to != route.target
            || !plan.forward_route_contains_edge(route_id, route.last)
            || plan.forward_depth[route.first.index()]
                .checked_sub(plan.forward_depth[route.last.index()])
                .and_then(|distance| distance.checked_add(1))
                != Some(route.len)
        {
            return Err(StructureError::invalid(format!(
                "forward route #{} has stale endpoints or length",
                route_id.index()
            )));
        }
        if first_route[route.first.index()]
            .replace(route_id)
            .is_some_and(|old| old != route_id)
        {
            return Err(StructureError::invalid(
                "forward routes with different identities share a first edge",
            ));
        }
        is_route_last[route.last.index()] = true;
        let Some(RegionPlan::Loop {
            plan: loop_id,
            control,
            body,
            ..
        }) = plan.region(route.loop_region)
        else {
            return Err(StructureError::invalid(format!(
                "forward route #{} has a non-loop owner",
                route_id.index()
            )));
        };
        let payload = plan.loop_(*loop_id).ok_or_else(|| {
            StructureError::invalid(format!(
                "forward route #{} loop payload is missing",
                route_id.index()
            ))
        })?;
        let metadata_matches = match route.kind {
            ForwardRouteKind::ExclusiveBreak => payload.continuation == Some(route.target),
            ForwardRouteKind::ContinueToTarget => payload.continue_target == Some(route.target),
            ForwardRouteKind::ContinueLatch => {
                payload.continue_target == Some(route.start) && payload.header == route.target
            }
            ForwardRouteKind::RepeatConditionArc(arc_ref) => {
                let arc = plan
                    .condition(arc_ref.condition)
                    .and_then(|condition| condition.nodes.get(arc_ref.node.index()))
                    .map(|node| node.arc(arc_ref.polarity));
                payload.kind == crate::structure::LoopKindHint::RepeatLike
                    && payload.condition == Some(arc_ref.condition)
                    && payload.header == route.target
                    && arc.is_some_and(|arc| {
                        let Some(first) = arc.route.first().copied() else {
                            return false;
                        };
                        arc.route.last() == Some(&route.last)
                            && cfg.edges.get(first.index()).map(|edge| edge.from)
                                == payload.continue_target
                            && plan.forward_route_contains_edge(route_id, first)
                            && plan.forward_depth[first.index()]
                                .checked_sub(plan.forward_depth[route.last.index()])
                                .and_then(|distance| distance.checked_add(1))
                                == Some(arc.route.len())
                    })
            }
        };
        if !metadata_matches {
            return Err(StructureError::invalid(format!(
                "forward route #{} {:?} #{} -> #{} contradicts loop payload {:?}: condition={:?} header=#{} continue={:?} continuation={:?}",
                route_id.index(),
                route.kind,
                route.start.index(),
                route.target.index(),
                payload.kind,
                payload.condition,
                payload.header.index(),
                payload.continue_target,
                payload.continuation,
            )));
        }
        let entry = entry_by_route[route_id.index()];
        if route.kind == ForwardRouteKind::ExclusiveBreak
            && entry.is_none_or(|entry| {
                plan.region_for_block(cfg.edges[entry.index()].from)
                    .is_none_or(|source| !intervals.contains(route.loop_region, source))
            })
        {
            return Err(StructureError::invalid(format!(
                "exclusive break route #{} starts outside its loop",
                route_id.index()
            )));
        }
        let _ = (control, body);
    }

    let mut route_predecessor = vec![None; edge_count];
    let mut route_predecessor_count = vec![0usize; edge_count];
    for (edge_index, next) in plan.forward_next.iter().copied().enumerate() {
        let edge = EdgeRef(edge_index);
        let assigned = plan.forward_preorder[edge_index] != usize::MAX;
        if assigned
            != (plan.forward_subtree_end[edge_index] != usize::MAX
                && plan.forward_depth[edge_index] != usize::MAX
                && plan.forward_owner_by_edge[edge_index].is_some()
                && plan.forward_kind_by_edge[edge_index].is_some())
        {
            return Err(StructureError::invalid(format!(
                "{edge} has inconsistent forward route indexes"
            )));
        }
        if !assigned {
            if next.is_some() {
                return Err(StructureError::invalid(format!(
                    "unowned {edge} has a forwarding successor"
                )));
            }
            continue;
        }
        if plan.forward_subtree_end[edge_index] <= plan.forward_preorder[edge_index] {
            return Err(StructureError::invalid(format!(
                "{edge} has an invalid forwarding interval"
            )));
        }
        if let Some(next) = next {
            let next_cfg = cfg.edges.get(next.index()).ok_or_else(|| {
                StructureError::invalid(format!("{edge} has a missing forwarding successor"))
            })?;
            if cfg.edges[edge_index].to != next_cfg.from
                || plan.forward_depth[edge_index]
                    != plan.forward_depth[next.index()].saturating_add(1)
                || !(plan.forward_preorder[next.index()] <= plan.forward_preorder[edge_index]
                    && plan.forward_preorder[edge_index] < plan.forward_subtree_end[next.index()])
            {
                return Err(StructureError::invalid(format!(
                    "{edge} has a stale forwarding successor"
                )));
            }
            route_predecessor_count[next.index()] += 1;
            route_predecessor[next.index()] = Some(edge);
        } else if plan.forward_depth[edge_index] != 0 {
            return Err(StructureError::invalid(format!(
                "forward route root {edge} has a non-zero depth"
            )));
        }

        let owner = plan.forward_owner_by_edge[edge_index]
            .ok_or_else(|| StructureError::invalid("forward route edge has no loop owner"))?;
        let kind = plan.forward_kind_by_edge[edge_index]
            .ok_or_else(|| StructureError::invalid("forward route edge has no semantic kind"))?;
        let Some(RegionPlan::Loop { control, body, .. }) = plan.region(owner) else {
            return Err(StructureError::invalid(
                "forward route edge owner is not a loop",
            ));
        };
        let cfg_edge = cfg.edges[edge_index];
        let edge_plan = plan
            .edge_plan(edge)
            .ok_or_else(|| StructureError::invalid("forward route edge has no edge plan"))?;
        let source_owner = plan.region_for_block(cfg_edge.from).ok_or_else(|| {
            StructureError::invalid("forward route source block has no containment owner")
        })?;
        let is_last = is_route_last[edge_index];
        match kind {
            ForwardRouteKind::ExclusiveBreak => {
                let expected_incoming = if let Some(route_id) = first_route[edge_index] {
                    entry_by_route[route_id.index()]
                } else if route_predecessor_count[edge_index] == 1 {
                    route_predecessor[edge_index]
                } else {
                    None
                };
                let ancestor_loopback = matches!(
                    edge_plan.transfer,
                    EdgeTransfer::LoopBack(ancestor)
                        if is_last
                            && ancestor != owner
                            && edge_plan.owner == ancestor
                            && intervals.contains(ancestor, owner)
                            && intervals.contains(ancestor, source_owner)
                            && matches!(
                                plan.region(ancestor),
                                Some(RegionPlan::Loop { plan: loop_id, .. })
                                    if plan.loop_(*loop_id)
                                        .is_some_and(|loop_| loop_.header == cfg_edge.to)
                            )
                );
                if index.break_barriers[cfg_edge.from.index()]
                    || plan.navigation.has_unstructured_ancestor(source_owner)
                    || expected_incoming.is_none()
                    || cfg.preds[cfg_edge.from.index()].as_slice() != expected_incoming.as_slice()
                    || cfg.succs[cfg_edge.from.index()].as_slice() != [edge]
                    || cfg_edge.kind != EdgeKind::Jump
                    || !(edge_plan.transfer == EdgeTransfer::Fallthrough || ancestor_loopback)
                {
                    return Err(StructureError::invalid(format!(
                        "exclusive break forwarding edge {edge} is not a pure pad: block={} preds={:?} expected={expected_incoming:?} succs={:?} kind={:?} transfer={:?} forward-owner={:?} forward-kind={:?} break-barrier={} island={}",
                        cfg_edge.from,
                        cfg.preds[cfg_edge.from.index()],
                        cfg.succs[cfg_edge.from.index()],
                        cfg_edge.kind,
                        edge_plan.transfer,
                        plan.forward_owner_by_edge[edge.index()],
                        plan.forward_kind_by_edge[edge.index()],
                        index.break_barriers[cfg_edge.from.index()],
                        plan.navigation.has_unstructured_ancestor(source_owner),
                    )));
                }
            }
            ForwardRouteKind::ContinueToTarget | ForwardRouteKind::ContinueLatch => {
                let terminal_transfer = matches!(
                    edge_plan.transfer,
                    EdgeTransfer::LoopBack(region) | EdgeTransfer::Continue(region) if region == owner
                );
                let nested_break = matches!(
                    edge_plan.transfer,
                    EdgeTransfer::Break(nested)
                        if !is_last
                            && nested != owner
                            && edge_plan.owner == nested
                            && edge_plan.forward_route.is_none()
                            && edge_plan.iteration.is_empty()
                            && intervals.contains(owner, nested)
                            && intervals.contains(nested, source_owner)
                            && plan.region_for_block(cfg_edge.to).is_some_and(|target_owner| {
                                !intervals.contains(nested, target_owner)
                                    && intervals.contains(*body, target_owner)
                            })
                            && matches!(
                                plan.region(nested),
                                Some(RegionPlan::Loop { plan: loop_id, .. })
                                    if plan.loop_(*loop_id)
                                        .is_some_and(|loop_| loop_.continuation == Some(cfg_edge.to))
                            )
                );
                if index.continue_barriers[cfg_edge.from.index()]
                    || !intervals.contains(*body, source_owner)
                    || plan.navigation.has_unstructured_ancestor(source_owner)
                    || cfg.succs[cfg_edge.from.index()].as_slice() != [edge]
                    || cfg_edge.kind != EdgeKind::Jump
                    || cfg.blocks[cfg_edge.from.index()].instrs.len != 1
                    || if is_last {
                        !terminal_transfer
                    } else {
                        edge_plan.transfer != EdgeTransfer::Fallthrough && !nested_break
                    }
                {
                    return Err(StructureError::invalid(format!(
                        "continue forwarding edge {edge} is not a pure loop pad"
                    )));
                }
            }
            ForwardRouteKind::RepeatConditionArc(_) => {
                let ForwardRouteKind::RepeatConditionArc(arc_ref) = kind else {
                    return Err(StructureError::invalid(
                        "repeat forwarding edge lost its condition arc",
                    ));
                };
                let arc = plan
                    .condition(arc_ref.condition)
                    .and_then(|condition| condition.nodes.get(arc_ref.node.index()))
                    .map(|node| node.arc(arc_ref.polarity))
                    .ok_or_else(|| {
                        StructureError::invalid("repeat forwarding edge has a stale condition arc")
                    })?;
                let arc_first = *arc.route.first().ok_or_else(|| {
                    StructureError::invalid("repeat forwarding condition arc is empty")
                })?;
                let arc_last = *arc.route.last().ok_or_else(|| {
                    StructureError::invalid("repeat forwarding condition arc is empty")
                })?;
                let condition_edge = plan.forward_path_contains_edge(arc_first, arc_last, edge);
                let terminal_transfer = matches!(
                    edge_plan.transfer,
                    EdgeTransfer::LoopBack(region) | EdgeTransfer::Continue(region) if region == owner
                );
                if index.continue_barriers[cfg_edge.from.index()]
                    || plan.navigation.has_unstructured_ancestor(source_owner)
                    || if condition_edge {
                        !intervals.contains(*control, source_owner)
                            || if is_last {
                                !terminal_transfer
                            } else {
                                !matches!(
                                    edge_plan.transfer,
                                    EdgeTransfer::Fallthrough
                                        | EdgeTransfer::BranchArm(
                                            BranchArm::Truthy | BranchArm::Falsy
                                        )
                                )
                            }
                    } else {
                        !intervals.contains(*body, source_owner)
                            || cfg.succs[cfg_edge.from.index()].as_slice() != [edge]
                            || cfg_edge.kind != EdgeKind::Jump
                            || cfg.blocks[cfg_edge.from.index()].instrs.len != 1
                            || edge_plan.transfer != EdgeTransfer::Fallthrough
                    }
                {
                    return Err(StructureError::invalid(format!(
                        "repeat condition forwarding edge {edge} is inconsistent"
                    )));
                }
            }
        }
    }
    Ok(())
}

pub(super) fn validate_continue_forwarding_route(
    cfg: &Cfg,
    plan: &StructurePlan,
    entry: &super::super::EdgePlan,
    loop_region: RegionId,
) -> Result<bool, StructureError> {
    let Some(route_id) = entry.forward_route else {
        return Ok(false);
    };
    let route = plan.forward_route(route_id).ok_or_else(|| {
        StructureError::invalid(format!(
            "continue entry references missing route #{route_id:?}"
        ))
    })?;
    Ok(route.loop_region == loop_region
        && matches!(
            route.kind,
            ForwardRouteKind::ContinueToTarget
                | ForwardRouteKind::ContinueLatch
                | ForwardRouteKind::RepeatConditionArc(_)
        )
        && cfg.edges.get(entry.edge.index()).map(|edge| edge.to) == Some(route.start))
}

pub(super) fn validate_break_forwarding_route(
    cfg: &Cfg,
    plan: &StructurePlan,
    _intervals: &RegionNavigation,
    entry: &super::super::EdgePlan,
    loop_region: RegionId,
    _continuation: Option<crate::structure::BlockRef>,
    _validation_index: &EdgeValidationIndex,
) -> Result<bool, StructureError> {
    let Some(route_id) = entry.forward_route else {
        return Ok(false);
    };
    let route = plan.forward_route(route_id).ok_or_else(|| {
        StructureError::invalid(format!(
            "break entry references missing route #{route_id:?}"
        ))
    })?;
    Ok(route.loop_region == loop_region
        && route.kind == ForwardRouteKind::ExclusiveBreak
        && cfg.edges.get(entry.edge.index()).map(|edge| edge.to) == Some(route.start))
}
