//! 校验循环 payload、分区与 break/continue 边；依赖循环区域及 CFG，不负责发现循环候选；例如核对 normal-tail 与 continuation 的边界。

use super::*;

pub(super) struct LoopEdgeIndex {
    body: Vec<Option<LoopPlanId>>,
    exit: Vec<Option<LoopPlanId>>,
    backedge: Vec<Option<LoopPlanId>>,
    continue_: Vec<Option<LoopPlanId>>,
}

impl LoopEdgeIndex {
    fn new(plan: &StructurePlan, edge_count: usize) -> Result<Self, StructureError> {
        let mut index = Self {
            body: vec![None; edge_count],
            exit: vec![None; edge_count],
            backedge: vec![None; edge_count],
            continue_: vec![None; edge_count],
        };
        for (loop_index, payload) in plan.loops.iter().enumerate() {
            let loop_id = LoopPlanId(loop_index);
            for edge in payload
                .control_edges
                .preheader_body
                .iter()
                .chain(&payload.control_edges.body)
            {
                record_loop_edge(&mut index.body, *edge, loop_id, "body")?;
            }
            for edge in payload
                .control_edges
                .preheader_exit
                .iter()
                .chain(&payload.control_edges.exit)
            {
                record_loop_edge(&mut index.exit, *edge, loop_id, "exit")?;
            }
            for edge in &payload.control_edges.backedges {
                record_loop_edge(&mut index.backedge, *edge, loop_id, "backedge")?;
            }
            for edge in &payload.control_edges.continues {
                record_loop_edge(&mut index.continue_, *edge, loop_id, "continue")?;
            }
        }
        Ok(index)
    }

    pub(super) fn has_body(&self, loop_id: LoopPlanId, edge: EdgeRef) -> bool {
        loop_edge_matches(&self.body, loop_id, edge)
    }

    pub(super) fn has_exit(&self, loop_id: LoopPlanId, edge: EdgeRef) -> bool {
        loop_edge_matches(&self.exit, loop_id, edge)
    }

    pub(super) fn has_backedge(&self, loop_id: LoopPlanId, edge: EdgeRef) -> bool {
        loop_edge_matches(&self.backedge, loop_id, edge)
    }

    pub(super) fn has_continue(&self, loop_id: LoopPlanId, edge: EdgeRef) -> bool {
        loop_edge_matches(&self.continue_, loop_id, edge)
    }
}

pub(super) fn record_loop_edge(
    index: &mut [Option<LoopPlanId>],
    edge: EdgeRef,
    loop_id: LoopPlanId,
    role: &str,
) -> Result<(), StructureError> {
    let Some(slot) = index.get_mut(edge.index()) else {
        return Err(StructureError::invalid(format!(
            "loop payload #{} {role} edge is outside the CFG arena",
            loop_id.index()
        )));
    };
    if slot.is_some_and(|owner| owner != loop_id) {
        return Err(StructureError::invalid(format!(
            "edge {edge} has multiple loop {role} owners"
        )));
    }
    *slot = Some(loop_id);
    Ok(())
}

pub(super) fn loop_edge_matches(
    index: &[Option<LoopPlanId>],
    loop_id: LoopPlanId,
    edge: EdgeRef,
) -> bool {
    index.get(edge.index()).copied().flatten() == Some(loop_id)
}

pub(super) fn validate_loop_plans(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &StructurePlan,
    intervals: &RegionNavigation,
    block_stats: &RegionBlockStats,
) -> Result<LoopEdgeIndex, StructureError> {
    if plan.loop_region_by_plan.len() != plan.loops.len() {
        return Err(StructureError::invalid("loop region index length mismatch"));
    }
    if plan.loop_exit_tail_by_block.len() != cfg.blocks.len()
        || plan.loop_exit_tail_by_edge.len() != cfg.edges.len()
        || plan.loop_exit_tail_by_cleanup_instr.len() != cfg.instr_to_block.len()
    {
        return Err(StructureError::invalid(
            "loop exit tail reverse index length mismatch",
        ));
    }
    let loop_edges = LoopEdgeIndex::new(plan, cfg.edges.len())?;
    let mut break_edges_by_region = vec![Vec::new(); plan.regions.len()];
    for (edge_index, edge_plan) in plan.edge_plans.iter().enumerate() {
        if edge_plan.edge.index() != edge_index {
            return Err(StructureError::invalid(format!(
                "edge plan #{edge_index} has a stale identity while indexing loop exits"
            )));
        }
        if let EdgeTransfer::Break(region) = edge_plan.transfer {
            let Some(edges) = break_edges_by_region.get_mut(region.index()) else {
                return Err(StructureError::invalid(format!(
                    "edge plan #{edge_index} references a missing break region"
                )));
            };
            edges.push(edge_plan.edge);
        }
    }
    // 独立从最终 containment 与 transfer 重建 normal-tail guard 集合，不能信任
    // freeze 阶段保存的候选边。只有最内层当前 loop 的真实 Break 才会写 guard；
    // forwarding route 取最终 target，pad outgoing 自身不拥有动作。
    let mut nearest_loop = vec![None; plan.regions.len()];
    for region in intervals.preorder.iter().copied() {
        let inherited =
            intervals.parent[region.index()].and_then(|parent| nearest_loop[parent.index()]);
        nearest_loop[region.index()] =
            if matches!(plan.region(region), Some(RegionPlan::Loop { .. })) {
                Some(region)
            } else {
                inherited
            };
    }
    let mut expected_normal_tail_guards = vec![Vec::new(); plan.loops.len()];
    for edge_plan in &plan.edge_plans {
        let EdgeTransfer::Break(loop_region) = edge_plan.transfer else {
            continue;
        };
        let Some(RegionPlan::Loop { plan: loop_id, .. }) = plan.region(loop_region) else {
            continue;
        };
        let Some(tail) = plan
            .loop_(*loop_id)
            .and_then(|payload| payload.normal_tail.as_ref())
        else {
            continue;
        };
        if tail.normal_exits.binary_search(&edge_plan.edge).is_ok() {
            continue;
        }
        let cfg_edge = cfg.edges.get(edge_plan.edge.index()).ok_or_else(|| {
            StructureError::invalid("normal-tail guard entry references a missing CFG edge")
        })?;
        let source = plan
            .region_for_block(cfg_edge.from)
            .ok_or_else(|| StructureError::invalid("normal-tail guard entry source is unowned"))?;
        if nearest_loop[source.index()] != Some(loop_region) {
            continue;
        }
        let target = edge_plan
            .forward_route
            .map(|route| {
                plan.forward_route(route)
                    .map(|route| route.target)
                    .ok_or_else(|| {
                        StructureError::invalid(
                            "normal-tail guard entry references a missing forwarding route",
                        )
                    })
            })
            .transpose()?
            .unwrap_or(cfg_edge.to);
        if target == tail.continuation {
            expected_normal_tail_guards[loop_id.index()].push(edge_plan.edge);
        }
    }
    for entries in &mut expected_normal_tail_guards {
        entries.sort_by_key(|edge| edge.index());
        entries.dedup();
    }
    let mut seen = vec![false; plan.loops.len()];
    let mut syntax_edge_epoch = vec![0usize; cfg.edges.len()];
    let mut normal_exit_epoch = vec![0usize; cfg.edges.len()];
    let mut expected_tail_by_block = vec![None; cfg.blocks.len()];
    let mut expected_tail_by_edge = vec![None; cfg.edges.len()];
    let mut expected_tail_by_cleanup_instr = vec![None; cfg.instr_to_block.len()];
    for (index, region) in plan.regions.iter().enumerate() {
        let RegionPlan::Loop {
            plan: loop_id,
            entry,
            preheader,
            control,
            body,
            normal_tail,
            ..
        } = region
        else {
            continue;
        };
        let region_id = RegionId(index);
        let payload = plan.loop_(*loop_id).ok_or_else(|| {
            StructureError::invalid(format!("loop region #{index} has no payload"))
        })?;
        if seen[loop_id.index()] || plan.loop_region(*loop_id) != Some(region_id) {
            return Err(StructureError::invalid(format!(
                "loop payload #{} has conflicting region ownership",
                loop_id.index()
            )));
        }
        seen[loop_id.index()] = true;

        for child in preheader
            .iter()
            .copied()
            .chain([*control, *body])
            .chain(normal_tail.iter().copied())
        {
            if !matches!(plan.region(child), Some(RegionPlan::Sequence { parent: Some(parent), .. }) if *parent == region_id)
            {
                return Err(StructureError::invalid(format!(
                    "loop region #{index} partition is not an owned sequence"
                )));
            }
        }
        let partitions = preheader
            .iter()
            .copied()
            .chain([*control, *body])
            .chain(normal_tail.iter().copied())
            .collect::<BTreeSet<_>>();
        if partitions.len()
            != 2 + usize::from(preheader.is_some()) + usize::from(normal_tail.is_some())
        {
            return Err(StructureError::invalid(format!(
                "loop region #{index} reuses a partition region"
            )));
        }
        let expected_preheader_len = usize::from(payload.preheader_block.is_some());
        if preheader.is_some_and(|partition| {
            !region_matches_exact_blocks(
                plan,
                intervals,
                block_stats,
                partition,
                expected_preheader_len,
                payload.preheader_block,
            )
        }) || (preheader.is_none() && expected_preheader_len != 0)
        {
            return Err(StructureError::invalid(format!(
                "loop payload #{} preheader partition is stale",
                loop_id.index()
            )));
        }
        let preheader_count = preheader
            .map(|partition| block_stats.subtree_count(partition))
            .unwrap_or(0);
        let control_count = block_stats.subtree_count(*control);
        let normal_tail_count = normal_tail
            .map(|partition| block_stats.subtree_count(partition))
            .unwrap_or(0);
        let owned_count = block_stats.subtree_count(region_id);
        let body_count = block_stats.subtree_count(*body);
        let expected_body_count = owned_count
            .saturating_sub(control_count)
            .saturating_sub(preheader_count)
            .saturating_sub(normal_tail_count);
        if body_count != expected_body_count {
            return Err(StructureError::invalid(format!(
                "loop payload #{} body is not the remainder of its owned blocks",
                loop_id.index()
            )));
        }
        match (&payload.normal_tail, normal_tail) {
            (None, None) => {}
            (Some(tail), Some(tail_region)) => {
                if !matches!(
                    payload.kind,
                    crate::structure::LoopKindHint::WhileLike
                        | crate::structure::LoopKindHint::NumericForLike
                        | crate::structure::LoopKindHint::GenericForLike
                ) || payload.continuation != Some(tail.continuation)
                    || normal_tail_count == 0
                    || !region_contains_block(plan, intervals, *tail_region, tail.entry)
                {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} has an invalid normal-tail partition",
                        loop_id.index()
                    )));
                }
                let entry_owner = plan.region_for_block(tail.entry).ok_or_else(|| {
                    StructureError::invalid(format!(
                        "loop payload #{} normal-tail entry is unowned",
                        loop_id.index()
                    ))
                })?;
                if !intervals.contains(*tail_region, entry_owner) {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} normal-tail entry is outside its partition",
                        loop_id.index()
                    )));
                }
                let boundary = intervals.boundary(*tail_region).ok_or_else(|| {
                    StructureError::invalid("normal-tail region has no boundary summary")
                })?;
                if tail.normal_exits.is_empty()
                    || tail
                        .normal_exits
                        .windows(2)
                        .any(|pair| pair[0].index() >= pair[1].index())
                    || tail
                        .early_exits
                        .iter()
                        .any(|edge| tail.normal_exits.binary_search(edge).is_ok())
                    || boundary.entry_count != tail.normal_exits.len()
                    || boundary.exit_count != tail.completion_exits.len()
                {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} has stale normal-tail boundary ports",
                        loop_id.index()
                    )));
                }
                for edge in &tail.normal_exits {
                    let edge_plan = plan.edge_plan(*edge).ok_or_else(|| {
                        StructureError::invalid("normal-tail exit has no edge plan")
                    })?;
                    let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                        StructureError::invalid("normal-tail exit references a missing edge")
                    })?;
                    let syntax_exit_kind =
                        if payload.kind == crate::structure::LoopKindHint::WhileLike {
                            !matches!(cfg_edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                        } else {
                            cfg_edge.kind == EdgeKind::LoopExit
                        };
                    let syntax_exit_transfer = match edge_plan.transfer {
                        EdgeTransfer::BranchArm(super::super::BranchArm::LoopExit) => true,
                        EdgeTransfer::Break(target) => target == region_id,
                        _ => false,
                    };
                    if !syntax_exit_kind
                        || cfg_edge.to != tail.entry
                        || region_contains_block(plan, intervals, *tail_region, cfg_edge.from)
                        || !loop_edges.has_exit(*loop_id, *edge)
                        || !syntax_exit_transfer
                    {
                        return Err(StructureError::invalid(format!(
                            "loop payload #{} normal-tail exit is stale",
                            loop_id.index()
                        )));
                    }
                }
                if tail.completion_exits.is_empty()
                    || tail
                        .completion_exits
                        .windows(2)
                        .any(|pair| pair[0].index() >= pair[1].index())
                {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} has invalid normal-tail completion exits",
                        loop_id.index()
                    )));
                }
                for edge in &tail.completion_exits {
                    let edge_plan = plan.edge_plan(*edge).ok_or_else(|| {
                        StructureError::invalid("normal-tail completion has no edge plan")
                    })?;
                    let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                        StructureError::invalid("normal-tail completion references a missing edge")
                    })?;
                    if edge_plan.edge != *edge
                        || cfg_edge.to != tail.continuation
                        || !region_contains_block(plan, intervals, *tail_region, cfg_edge.from)
                    {
                        return Err(StructureError::invalid(format!(
                            "loop payload #{} normal-tail completion is stale",
                            loop_id.index()
                        )));
                    }
                }
                if tail.early_exits != expected_normal_tail_guards[loop_id.index()] {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} normal-tail guard entries are stale: frozen={:?}, expected={:?}",
                        loop_id.index(),
                        tail.early_exits,
                        expected_normal_tail_guards[loop_id.index()],
                    )));
                }
            }
            _ => {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} normal-tail slot disagrees with its payload",
                    loop_id.index()
                )));
            }
        }
        if payload.normal_tail.is_some() && payload.exit_tail.is_some() {
            return Err(StructureError::invalid(format!(
                "loop payload #{} owns two normal-exit tail forms",
                loop_id.index()
            )));
        }
        if let Some(tail) = &payload.exit_tail {
            let Some(block_slot) = expected_tail_by_block.get_mut(tail.block.index()) else {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} exit tail block is outside the CFG arena",
                    loop_id.index()
                )));
            };
            if block_slot.replace(*loop_id).is_some() {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} shares an exit-tail block",
                    loop_id.index()
                )));
            }
            let Some(edge_slot) = expected_tail_by_edge.get_mut(tail.normal_exit.index()) else {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} exit-tail edge is outside the CFG arena",
                    loop_id.index()
                )));
            };
            if edge_slot.replace(*loop_id).is_some() {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} shares an exit-tail edge",
                    loop_id.index()
                )));
            }
            for instr in &tail.cleanup {
                let Some(cleanup_slot) = expected_tail_by_cleanup_instr.get_mut(instr.index())
                else {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} exit-tail cleanup is outside the instruction arena",
                        loop_id.index()
                    )));
                };
                if cleanup_slot.replace(*loop_id).is_some() {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} shares an exit-tail cleanup instruction",
                        loop_id.index()
                    )));
                }
            }
            let cfg_edge = cfg.edges.get(tail.normal_exit.index()).ok_or_else(|| {
                StructureError::invalid("loop exit tail references a missing normal edge")
            })?;
            let edge_plan = plan
                .edge_plan(tail.normal_exit)
                .ok_or_else(|| StructureError::invalid("loop exit tail normal edge has no plan"))?;
            let block_range = cfg
                .blocks
                .get(tail.block.index())
                .ok_or_else(|| {
                    StructureError::invalid("loop exit tail references a missing block")
                })?
                .instrs;
            let expected_early = break_edges_by_region[region_id.index()]
                .iter()
                .copied()
                .filter(|edge| *edge != tail.normal_exit)
                .collect::<Vec<_>>();
            let reachable_predecessors = cfg.preds[tail.block.index()]
                .iter()
                .copied()
                .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
                .collect::<Vec<_>>();
            let cleanup_block_range = cfg
                .blocks
                .get(tail.cleanup_block.index())
                .map(|block| block.instrs);
            let cleanup_instrs_are_dense =
                tail.cleanup.iter().enumerate().all(|(offset, instr)| {
                    Some(tail.cleanup_block) == cfg.instr_to_block.get(instr.index()).copied()
                        && tail.cleanup.first().map(|first| first.index() + offset)
                            == Some(instr.index())
                });
            let cleanup_location_is_valid = if tail.cleanup_block == tail.block {
                tail.cleanup_route.is_empty()
                    && tail.cleanup.iter().all(|instr| {
                        instr.index() >= tail.range.start.index()
                            && instr.index() < tail.range.end()
                    })
            } else {
                let [route] = tail.cleanup_route.as_slice() else {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} cleanup route is not direct",
                        loop_id.index()
                    )));
                };
                let route_cfg = cfg.edges.get(route.index());
                let route_plan = plan.edge_plan(*route);
                let mut cleanup_predecessors = cfg.preds[tail.cleanup_block.index()]
                    .iter()
                    .copied()
                    .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
                    .collect::<Vec<_>>();
                cleanup_predecessors.sort_by_key(|edge| edge.index());
                cfg.succs[tail.block.index()].as_slice() == [*route]
                    && route_cfg.is_some_and(|edge| {
                        edge.from == tail.block && edge.to == tail.cleanup_block
                    })
                    && route_plan.is_some_and(|edge| {
                        edge.transfer == EdgeTransfer::Fallthrough && edge.forward_route.is_none()
                    })
                    && cleanup_predecessors.as_slice() == [*route]
                    && cleanup_block_range
                        .is_some_and(|range| tail.cleanup.first() == Some(&range.start))
                    && block_range.last().map(|last| last.index()) == Some(tail.range.end())
                    && plan.label_for_block(tail.cleanup_block).is_none()
            };
            if payload.continuation != Some(tail.continuation)
                || tail.block != tail.continuation
                || cfg_edge.to != tail.block
                || edge_plan.owner != region_id
                || edge_plan.transfer != EdgeTransfer::Break(region_id)
                || edge_plan.forward_route.is_some()
                || !payload.control_edges.exit.contains(&tail.normal_exit)
                || tail.range.start != block_range.start
                || tail.range.is_empty()
                || tail.range.end() >= block_range.end()
                || reachable_predecessors.as_slice() != [tail.normal_exit]
                || tail.early_exits != expected_early
                || tail.early_exits.iter().any(|edge| {
                    cfg.edges
                        .get(edge.index())
                        .is_some_and(|edge| edge.to == tail.block)
                })
                || plan.label_for_block(tail.block).is_some()
                || tail.cleanup.is_empty()
                || tail.cleanup.windows(2).any(|pair| pair[0] >= pair[1])
                || !cleanup_instrs_are_dense
                || !cleanup_location_is_valid
            {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} has a stale instruction exit tail",
                    loop_id.index()
                )));
            }
            let tail_owner = plan
                .region_for_block(tail.block)
                .ok_or_else(|| StructureError::invalid("loop exit tail block is unowned"))?;
            if intervals.contains(region_id, tail_owner) {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} instruction exit tail is still contained by the loop",
                    loop_id.index()
                )));
            }
        }
        let header_owner = plan.region_for_block(payload.header).ok_or_else(|| {
            StructureError::invalid(format!(
                "loop payload #{} header is unowned",
                loop_id.index()
            ))
        })?;
        let header_partition = if intervals.contains(*control, header_owner) {
            *control
        } else {
            *body
        };
        if !intervals.contains(header_partition, header_owner) {
            return Err(StructureError::invalid(format!(
                "loop payload #{} header is outside its frozen partition",
                loop_id.index()
            )));
        }
        if matches!(
            payload.kind,
            crate::structure::LoopKindHint::NumericForLike
                | crate::structure::LoopKindHint::GenericForLike
        ) && let Some(latch) = payload.continue_target
        {
            let latch_owner = plan.region_for_block(latch).ok_or_else(|| {
                StructureError::invalid(format!(
                    "loop payload #{} VM latch is unowned",
                    loop_id.index()
                ))
            })?;
            if !intervals.contains(*control, latch_owner) {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} VM latch is outside control",
                    loop_id.index()
                )));
            }
        }
        let entry_owner = plan.region_for_block(*entry).ok_or_else(|| {
            StructureError::invalid(format!("loop region #{index} entry is unowned"))
        })?;
        let expected_entry = payload.preheader_block.unwrap_or(payload.header);
        if *entry != expected_entry || preheader.is_some() != payload.preheader_block.is_some() {
            return Err(StructureError::invalid(format!(
                "loop region #{index} entry/preheader contract is stale"
            )));
        }
        let expected_entry_partition = preheader.unwrap_or(header_partition);
        if !intervals.contains(expected_entry_partition, entry_owner) {
            return Err(StructureError::invalid(format!(
                "loop region #{index} entry is outside its entry partition"
            )));
        }
        let requires_condition = matches!(
            payload.kind,
            crate::structure::LoopKindHint::WhileLike | crate::structure::LoopKindHint::RepeatLike
        ) || (payload.kind == crate::structure::LoopKindHint::Unknown
            && control_count != 0);
        if requires_condition && payload.condition.is_none() {
            return Err(StructureError::invalid(format!(
                "loop payload #{} is missing its frozen condition plan",
                loop_id.index()
            )));
        }
        if let Some(condition_id) = payload.condition {
            let condition = plan.condition(condition_id).ok_or_else(|| {
                StructureError::invalid(format!(
                    "loop payload #{} references a missing condition",
                    loop_id.index()
                ))
            })?;
            for block in condition.blocks() {
                let owner = plan.region_for_block(block).ok_or_else(|| {
                    StructureError::invalid(format!(
                        "loop payload #{} condition block {block} is unowned",
                        loop_id.index()
                    ))
                })?;
                if !intervals.contains(*control, owner) {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} condition block {block} is outside control",
                        loop_id.index()
                    )));
                }
            }
            let expected_condition_blocks = condition.blocks().collect::<Vec<_>>();
            if !region_matches_exact_blocks(
                plan,
                intervals,
                block_stats,
                *control,
                expected_condition_blocks.len(),
                expected_condition_blocks.iter().copied(),
            ) {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} condition region has stale coverage",
                    loop_id.index()
                )));
            }
        }
        let condition_entry = payload
            .condition
            .and_then(|id| plan.condition(id))
            .and_then(ConditionPlan::header)
            .or(payload.condition_header)
            .or_else(|| {
                (payload.kind == crate::structure::LoopKindHint::RepeatLike)
                    .then_some(payload.continue_target)
                    .flatten()
            })
            .unwrap_or(payload.header);
        let expected_prefix_placement = (control_count != 0
            && matches!(
                payload.kind,
                crate::structure::LoopKindHint::WhileLike
                    | crate::structure::LoopKindHint::RepeatLike
                    | crate::structure::LoopKindHint::Unknown
            ))
        .then_some(
            if payload.kind == crate::structure::LoopKindHint::RepeatLike
                && condition_entry != payload.header
                && payload.control_edges.continues.is_empty()
            {
                crate::structure::LoopConditionPrefixPlacement::AfterBody
            } else {
                crate::structure::LoopConditionPrefixPlacement::BeforeBody
            },
        );
        if payload.condition_prefix_placement != expected_prefix_placement {
            return Err(StructureError::invalid(format!(
                "loop payload #{} condition prefix placement is stale",
                loop_id.index()
            )));
        }

        if payload
            .normalized_exit_aliases
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
        {
            return Err(StructureError::invalid(format!(
                "loop payload #{} normalized exits are not unique and sorted",
                loop_id.index()
            )));
        }
        for alias in &payload.normalized_exit_aliases {
            let alias_owner = plan.region_for_block(alias.block).ok_or_else(|| {
                StructureError::invalid("normalized loop exit alias block is unowned")
            })?;
            let continuation_owner =
                plan.region_for_block(alias.continuation).ok_or_else(|| {
                    StructureError::invalid("normalized loop exit continuation is unowned")
                })?;
            let alias_instr = cfg
                .blocks
                .get(alias.block.index())
                .map(|block| block.instrs.start)
                .ok_or_else(|| {
                    StructureError::invalid("normalized loop exit alias is outside the CFG")
                })?;
            let continuation_instr = cfg
                .blocks
                .get(alias.continuation.index())
                .map(|block| block.instrs.start)
                .ok_or_else(|| {
                    StructureError::invalid("normalized loop exit continuation is outside the CFG")
                })?;
            let alias_in_control = intervals.contains(*control, alias_owner);
            let continuation_in_loop = intervals.contains(region_id, continuation_owner);
            let has_exit_edge = payload.control_edges.exit.iter().any(|edge| {
                cfg.edges
                    .get(edge.index())
                    .is_some_and(|edge| edge.to == alias.block)
            });
            let equivalent = super::super::super::helpers::equivalent_single_return_targets(
                proto,
                cfg,
                alias_instr,
                continuation_instr,
            );
            if !alias_in_control || continuation_in_loop || !has_exit_edge || !equivalent {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} has an invalid normalized exit alias {} -> {}: in-control={alias_in_control} continuation-in-loop={continuation_in_loop} exit-edge={has_exit_edge} equivalent={equivalent}",
                    loop_id.index(),
                    alias.block,
                    alias.continuation,
                )));
            }
        }

        let syntax_epoch = loop_id.index().checked_add(1).ok_or_else(|| {
            StructureError::invalid("loop count exceeds validation epoch capacity")
        })?;
        if let Some(tail) = &payload.normal_tail {
            for edge in &tail.normal_exits {
                let slot = normal_exit_epoch.get_mut(edge.index()).ok_or_else(|| {
                    StructureError::invalid("normal-tail exit is outside the CFG arena")
                })?;
                if std::mem::replace(slot, syntax_epoch) == syntax_epoch {
                    return Err(StructureError::invalid(
                        "normal-tail exit is listed more than once",
                    ));
                }
            }
        }
        for (edge, role) in payload
            .control_edges
            .preheader_body
            .map(|edge| (edge, "preheader body"))
            .into_iter()
            .chain(
                payload
                    .control_edges
                    .preheader_exit
                    .map(|edge| (edge, "preheader exit")),
            )
            .chain(
                payload
                    .control_edges
                    .body
                    .iter()
                    .copied()
                    .map(|edge| (edge, "control body")),
            )
            .chain(
                payload
                    .control_edges
                    .exit
                    .iter()
                    .copied()
                    .map(|edge| (edge, "control exit")),
            )
        {
            let Some(edge_epoch) = syntax_edge_epoch.get_mut(edge.index()) else {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} {role} edge is outside the CFG arena",
                    loop_id.index()
                )));
            };
            if std::mem::replace(edge_epoch, syntax_epoch) == syntax_epoch {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} assigns edge {edge} multiple syntax roles",
                    loop_id.index()
                )));
            }
            let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "loop payload #{} {role} edge is missing",
                    loop_id.index()
                ))
            })?;
            let source = plan.region_for_block(cfg_edge.from).ok_or_else(|| {
                StructureError::invalid(format!(
                    "loop payload #{} {role} source is unowned",
                    loop_id.index()
                ))
            })?;
            let source_partition = if role.starts_with("preheader") {
                preheader.ok_or_else(|| {
                    StructureError::invalid(format!(
                        "loop payload #{} has a preheader edge without a preheader region",
                        loop_id.index()
                    ))
                })?
            } else {
                *control
            };
            if !intervals.contains(source_partition, source) {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} {:?} header {} {role} edge {edge} source {} owner {:?} ({:?}) is outside partition {:?}",
                    loop_id.index(),
                    payload.kind,
                    payload.header,
                    cfg_edge.from,
                    source,
                    plan.region(source),
                    source_partition,
                )));
            }
            let target_inside = plan
                .region_for_block(cfg_edge.to)
                .is_some_and(|target| intervals.contains(region_id, target));
            let immediate_break_body = role == "control body"
                && payload.kind == crate::structure::LoopKindHint::GenericForLike
                && matches!(
                    cfg.terminator(&proto.instrs, payload.header),
                    Some(LowInstr::GenericForLoop(instr))
                        if super::super::super::loops::generic_for_immediate_break(proto, cfg, instr)
                );
            let expects_inside = role.ends_with("body") && !immediate_break_body
                || normal_exit_epoch[edge.index()] == syntax_epoch;
            let normalized_exit = role == "control exit"
                && payload
                    .normalized_exit_aliases
                    .iter()
                    .any(|alias| alias.block == cfg_edge.to);
            if (target_inside && !normalized_exit) != expects_inside {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} {role} edge crosses the wrong boundary",
                    loop_id.index()
                )));
            }
        }
    }
    validate_propagated_breaks(cfg, plan, intervals, &nearest_loop)?;
    if seen.into_iter().any(|seen| !seen) {
        return Err(StructureError::invalid(
            "selected loop payload has no owning region",
        ));
    }
    if expected_tail_by_block != plan.loop_exit_tail_by_block {
        return Err(StructureError::invalid(
            "loop exit tail block reverse index is stale",
        ));
    }
    if expected_tail_by_edge != plan.loop_exit_tail_by_edge {
        return Err(StructureError::invalid(
            "loop exit tail edge reverse index is stale",
        ));
    }
    if expected_tail_by_cleanup_instr != plan.loop_exit_tail_by_cleanup_instr {
        return Err(StructureError::invalid(
            "loop exit tail cleanup reverse index is stale",
        ));
    }
    Ok(loop_edges)
}
