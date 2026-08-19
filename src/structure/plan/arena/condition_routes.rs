//! loop condition route 与构建前 edge 规范化。输入 selected condition、RegionArena 和 CFG，输出对齐后的 condition route、branch-tail continue 与 edge action placement；不负责最终 transfer 分类。例如 repeat 经纯 jump pad 回 header 时会把完整 route 冻结进 condition arc。

use super::*;

pub(super) fn prune_non_iteration_branch_tail_continues(
    proto: &LoweredProto,
    cfg: &Cfg,
    caps: ControlFlowCaps,
    arena: &RegionArena,
    input: &FinalPlanInput,
    partitions: &mut [LoopPartitions],
) -> Result<(), StructureError> {
    if input.loops.len() != partitions.len() {
        return Err(StructureError::invalid(
            "loop evidence and partition arenas have different lengths",
        ));
    }
    let branch_tail_edges = index_branch_tail_edges(cfg, arena)?;
    for (loop_, partition) in input.loops.iter().zip(partitions) {
        let candidate = &loop_.candidate;
        let body = &partition.body;
        partition.continues.retain(|edge| {
            !branch_tail_edges[edge.index()]
                || loop_.semantic_continue_edges.contains(edge)
                || caps.continue_stmt
                    && continue_edge_bypasses_body_parts(cfg, body, *edge)
                    && !(candidate.kind_hint == crate::structure::LoopKindHint::RepeatLike
                        && candidate.continue_target.is_some_and(|target| {
                            branch_conditions_share_subject(
                                proto,
                                cfg,
                                cfg.edges[edge.index()].from,
                                target,
                            )
                        }))
        });
    }
    Ok(())
}

pub(super) fn index_branch_tail_edges(
    cfg: &Cfg,
    arena: &RegionArena,
) -> Result<Vec<bool>, StructureError> {
    #[derive(Clone, Copy)]
    struct ActiveBranch {
        end: usize,
        continuation: BlockRef,
        previous: Option<RegionId>,
    }

    let mut blocks_by_owner = vec![Vec::new(); arena.regions.len()];
    for (index, owner) in arena.region_by_block.iter().copied().enumerate() {
        if let Some(owner) = owner {
            blocks_by_owner[owner.index()].push(BlockRef(index));
        }
    }
    let mut active_by_continuation = vec![None; cfg.blocks.len()];
    let mut active = Vec::<ActiveBranch>::new();
    let mut tail_edges = vec![false; cfg.edges.len()];
    for (position, region) in arena.navigation.preorder.iter().copied().enumerate() {
        while active.last().is_some_and(|frame| frame.end <= position) {
            let frame = active
                .pop()
                .ok_or_else(|| StructureError::invalid("branch tail active stack underflowed"))?;
            active_by_continuation[frame.continuation.index()] = frame.previous;
        }
        if let Some(RegionPlan::Branch {
            continuation: Some(continuation),
            ..
        }) = arena.regions.get(region.index())
        {
            let slot = active_by_continuation
                .get_mut(continuation.index())
                .ok_or_else(|| {
                    StructureError::invalid("branch continuation is outside the block arena")
                })?;
            let previous = slot.replace(region);
            active.push(ActiveBranch {
                end: arena.navigation.subtree_end[region.index()],
                continuation: *continuation,
                previous,
            });
        }
        for block in &blocks_by_owner[region.index()] {
            for edge in &cfg.succs[block.index()] {
                let target = cfg.edges[edge.index()].to;
                if active_by_continuation[target.index()].is_some() {
                    tail_edges[edge.index()] = true;
                }
            }
        }
    }
    Ok(tail_edges)
}

/// 同一个物理 loop condition 可能同时留下 loop 与普通 branch 两份 owner 引用。
/// 在 region 冲突消解前把 branch 引用对齐到 loop 的 closed DAG identity，避免最终
/// plan 为同一对 CFG branch edge 冻结两个 condition owner。
pub(super) fn align_loop_condition_references(
    cfg: &Cfg,
    input: &mut FinalPlanInput,
) -> Result<(), StructureError> {
    let mut by_header = vec![None; cfg.blocks.len()];
    for loop_ in &input.loops {
        let Some(condition_id) = loop_.condition else {
            continue;
        };
        let condition = input.conditions.get(condition_id.index()).ok_or_else(|| {
            StructureError::invalid("loop condition is outside the evidence arena")
        })?;
        let Some(slot) = by_header.get_mut(condition.candidate.header.index()) else {
            return Err(StructureError::invalid(
                "loop condition header is outside the CFG arena",
            ));
        };
        if slot.is_some_and(|existing| existing != condition_id) {
            return Err(StructureError::invalid(
                "one physical condition header belongs to multiple loop DAGs",
            ));
        }
        *slot = Some(condition_id);
    }
    for branch in &mut input.branches {
        let Some(condition_id) = by_header
            .get(branch.branch.header.index())
            .copied()
            .flatten()
        else {
            continue;
        };
        if branch.condition.is_some() {
            branch.condition = Some(condition_id);
        }
    }
    Ok(())
}

/// 把 repeat condition 到 header 之间的纯 jump pad 固化进 condition route。
///
/// Luau 会把 `until` 的回边拆成 `branch -> jump pad -> body header`。若 pad 留在
/// body residual 中，region builder 会把同一可规约 repeat 误判成多入口 island。
/// 这里只吸收无副作用、单后继且完全落在该 loop 词法域内的 jump 链。
pub(super) fn normalize_repeat_condition_routes(
    proto: &LoweredProto,
    cfg: &Cfg,
    input: &mut FinalPlanInput,
) -> Result<(), StructureError> {
    let mut visit = BlockVisitWorkspace::new(cfg.blocks.len());
    let mut condition_owners = vec![0usize; input.conditions.len()];
    for loop_ in &input.loops {
        if let Some(condition) = loop_.condition {
            let Some(slot) = condition_owners.get_mut(condition.index()) else {
                return Err(StructureError::invalid(
                    "loop references a condition outside the evidence arena",
                ));
            };
            *slot = slot
                .checked_add(1)
                .ok_or_else(|| StructureError::invalid("condition owner count overflows"))?;
        }
    }
    for loop_ in &input.loops {
        if loop_.candidate.kind_hint != crate::structure::LoopKindHint::RepeatLike {
            continue;
        }
        let Some(condition_id) = loop_.condition else {
            continue;
        };
        if condition_owners.get(condition_id.index()).copied() != Some(1) {
            continue;
        }
        let condition = input
            .conditions
            .get_mut(condition_id.index())
            .ok_or_else(|| {
                StructureError::invalid("repeat loop condition disappeared during normalization")
            })?;
        let ShortCircuitExit::BranchExit { truthy, falsy } = condition.candidate.exit else {
            continue;
        };
        let mut allowed = loop_.candidate.blocks.clone();
        allowed.extend(loop_.candidate.body_scope_blocks.iter().copied());
        allowed.extend(loop_.candidate.control_blocks.iter().copied());
        let truthy_route = pure_jump_route_to(
            proto,
            cfg,
            truthy,
            loop_.candidate.header,
            &allowed,
            &mut visit,
        );
        let falsy_route = pure_jump_route_to(
            proto,
            cfg,
            falsy,
            loop_.candidate.header,
            &allowed,
            &mut visit,
        );
        let (truthy_backedge, old_target, connectors, route) = match (truthy_route, falsy_route) {
            (Some((connectors, route)), None) => (true, truthy, connectors, route),
            (None, Some((connectors, route))) => (false, falsy, connectors, route),
            (None, None) | (Some(_), Some(_)) => continue,
        };

        let mut extended = false;
        for arc in &mut condition.arcs {
            let targets_backedge = matches!(
                (&arc.target, truthy_backedge),
                (
                    crate::structure::common::ShortCircuitTarget::TruthyExit,
                    true
                ) | (
                    crate::structure::common::ShortCircuitTarget::FalsyExit,
                    false
                )
            );
            if !targets_backedge {
                continue;
            }
            let Some(last) = arc.edges.last().copied() else {
                return Err(StructureError::invalid(
                    "repeat condition contains an empty exit route",
                ));
            };
            if cfg.edges.get(last.index()).map(|edge| edge.to) != Some(old_target) {
                return Err(StructureError::invalid(
                    "repeat condition exit route changed before normalization",
                ));
            }
            arc.connector_blocks.extend(connectors.iter().copied());
            arc.edges.extend(route.iter().copied());
            extended = true;
        }
        if !extended {
            return Err(StructureError::invalid(
                "repeat condition has no semantic arc for its backedge exit",
            ));
        }
        condition.candidate.blocks.extend(connectors);
        condition.candidate.exit = if truthy_backedge {
            ShortCircuitExit::BranchExit {
                truthy: loop_.candidate.header,
                falsy,
            }
        } else {
            ShortCircuitExit::BranchExit {
                truthy,
                falsy: loop_.candidate.header,
            }
        };
    }
    Ok(())
}

pub(super) fn pure_jump_route_to(
    proto: &LoweredProto,
    cfg: &Cfg,
    start: BlockRef,
    target: BlockRef,
    allowed: &BTreeSet<BlockRef>,
    visit: &mut BlockVisitWorkspace,
) -> Option<(Vec<BlockRef>, Vec<EdgeRef>)> {
    if start == target {
        return None;
    }
    let mut connectors = Vec::new();
    let mut route = Vec::new();
    visit.begin();
    let mut block = start;
    while block != target {
        if !visit.mark(block) || !allowed.contains(&block) {
            return None;
        }
        let range = cfg.blocks.get(block.index())?.instrs;
        let [edge] = cfg.succs.get(block.index())?.as_slice() else {
            return None;
        };
        if range.len != 1
            || !matches!(
                proto.instrs.get(range.start.index()),
                Some(LowInstr::Jump(_))
            )
            || cfg.edges.get(edge.index())?.kind != EdgeKind::Jump
        {
            return None;
        }
        connectors.push(block);
        route.push(*edge);
        block = cfg.edges[edge.index()].to;
    }
    Some((connectors, route))
}

pub(super) struct BlockVisitWorkspace {
    seen_at: Vec<u32>,
    epoch: u32,
}

impl BlockVisitWorkspace {
    fn new(block_count: usize) -> Self {
        Self {
            seen_at: vec![0; block_count],
            epoch: 0,
        }
    }

    fn begin(&mut self) {
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.seen_at.fill(0);
            self.epoch = 1;
        }
    }

    fn mark(&mut self, block: BlockRef) -> bool {
        let Some(seen_at) = self.seen_at.get_mut(block.index()) else {
            return false;
        };
        std::mem::replace(seen_at, self.epoch) != self.epoch
    }
}

pub(super) fn repeat_condition_route_kind(
    cfg: &Cfg,
    input: &FinalPlanInput,
    condition_id: Option<super::super::ConditionPlanId>,
    route: &[EdgeRef],
) -> Result<Option<ForwardRouteKind>, StructureError> {
    let condition_id = condition_id.ok_or_else(|| {
        StructureError::invalid("repeat continue route has no frozen condition owner")
    })?;
    let condition = input.conditions.get(condition_id.index()).ok_or_else(|| {
        StructureError::invalid("repeat continue route references a missing condition")
    })?;
    let mut matching = condition.arcs.iter().filter(|arc| arc.edges == route);
    let Some(arc) = matching.next() else {
        return Ok(None);
    };
    if matching.next().is_some() {
        return Err(StructureError::invalid(
            "repeat continue route matches multiple condition arcs",
        ));
    }
    let first = route
        .first()
        .and_then(|edge| cfg.edges.get(edge.index()))
        .ok_or_else(|| StructureError::invalid("repeat continue route is empty or stale"))?;
    let polarity = match first.kind {
        EdgeKind::BranchTrue => super::super::ConditionArcPolarity::BranchTrue,
        EdgeKind::BranchFalse => super::super::ConditionArcPolarity::BranchFalse,
        _ => {
            return Err(StructureError::invalid(
                "repeat continue route does not start with a branch edge",
            ));
        }
    };
    Ok(Some(ForwardRouteKind::RepeatConditionArc(
        super::super::ConditionArcRef {
            condition: condition_id,
            node: super::super::ConditionNodeId(arc.source.index()),
            polarity,
        },
    )))
}

pub(super) fn freeze_edge_action_placement(
    proto: &LoweredProto,
    cfg: &Cfg,
    arena: &RegionArena,
    input: &FinalPlanInput,
    edge_ref: EdgeRef,
    transfer: EdgeTransfer,
) -> EdgeActionPlacement {
    let EdgeTransfer::LoopBack(loop_region) = transfer else {
        return EdgeActionPlacement::BeforeTransfer;
    };
    let Some(edge) = cfg.edges.get(edge_ref.index()) else {
        return EdgeActionPlacement::BeforeTransfer;
    };
    if edge.kind != EdgeKind::Jump
        || cfg.succs.get(edge.from.index()).map(Vec::as_slice) != Some(&[edge_ref])
    {
        return EdgeActionPlacement::BeforeTransfer;
    }
    let Some(RegionPlan::Loop { plan: loop_id, .. }) = arena.regions.get(loop_region.index())
    else {
        return EdgeActionPlacement::BeforeTransfer;
    };
    let has_carried_action = input.loops.get(loop_id.index()).is_some_and(|loop_| {
        loop_
            .carried_values
            .iter()
            .any(|value| value.inside_arm.contains_pred(edge.from))
    });
    if !has_carried_action {
        return EdgeActionPlacement::BeforeTransfer;
    }

    let Some(block_range) = cfg.blocks.get(edge.from.index()).map(|block| block.instrs) else {
        return EdgeActionPlacement::BeforeTransfer;
    };
    let Some(terminator) = block_range.last() else {
        return EdgeActionPlacement::BeforeTransfer;
    };
    if !matches!(
        proto.instrs.get(terminator.index()),
        Some(LowInstr::Jump(_))
    ) {
        return EdgeActionPlacement::BeforeTransfer;
    }

    let cleanup_end = terminator.index();
    let mut cleanup_start = cleanup_end;
    while cleanup_start > block_range.start.index()
        && matches!(
            proto.instrs.get(cleanup_start - 1),
            Some(LowInstr::Close(_) | LowInstr::Tbc(_))
        )
    {
        cleanup_start -= 1;
    }
    if cleanup_start == cleanup_end || cleanup_start == block_range.start.index() {
        return EdgeActionPlacement::BeforeTransfer;
    }

    EdgeActionPlacement::BeforeTrailingCleanup {
        cleanup: crate::structure::InstrRange::new(
            InstrRef(cleanup_start),
            cleanup_end - cleanup_start,
        ),
    }
}
