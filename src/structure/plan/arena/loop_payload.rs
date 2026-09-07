//! loop payload 与 VM control edge 的最终冻结。输入 loop partition、edge plans、TBC flow 和 loop evidence，证明资源退出边界并输出 LoopPlanData、传播 break 与 syntax edge roles；不负责发现循环候选。例如 numeric-for 的 body/exit/backedge 会被一次写入控制合同；正常出口还需跨分叉保持本轮资源时，则不能签发 break owner。

use super::*;

/// 正常出口不能把资源边界后的事件吸入仍持有该资源的条件 arm。
/// 例如 backward goto 的自然循环在 `assert(inner_closed and not outer_closed)`
/// 前结束，但 outer 的真实 Close 在断言后；或 inner Close 与 outer Close 间还有
/// observable。单 block exit-tail 只可消费终末清理，不能拥有这些交错的词法范围。
pub(super) fn loop_exit_crosses_resource_boundary(
    proto: &LoweredProto,
    cfg: &Cfg,
    candidate: &crate::structure::LoopCandidate,
    partition: &LoopPartitions,
    scopes: &[crate::structure::ScopePlan],
    flow: &crate::structure::scope::TbcFlowFacts,
) -> Result<bool, StructureError> {
    if partition.normal_tail.is_some() {
        return Ok(false);
    }
    let Some(continuation) = partition.continuation else {
        return Ok(false);
    };
    if partition.owned.contains(&continuation) {
        return Ok(false);
    }
    let before = flow
        .active_at_entry(continuation)
        .ok_or_else(|| StructureError::invalid("loop normal exit has no TBC entry facts"))?;
    let mut required = before
        .iter()
        .copied()
        .filter(|origin| {
            cfg.instr_to_block
                .get(origin.index())
                .is_some_and(|block| loop_body_owns_block(partition, *block))
        })
        .collect::<BTreeSet<_>>();
    if required.is_empty() {
        return Ok(false);
    }
    // Lua 5.4 的 goto pad 可只有 Jump，5.5 可把 Close 放在同一个 pad 内。
    // 沿已有 cleanup connector 保留关闭状态，不能跳过 Close 后再重置生命周期。
    let mut target = continuation;
    let mut connectors = BTreeSet::new();
    let mut closed_resource = false;
    let crosses = 'tail: loop {
        if partition.owned.contains(&target) || !connectors.insert(target) {
            break false;
        }
        let after = flow
            .active_after_block(target)
            .ok_or_else(|| StructureError::invalid("loop normal exit has no TBC exit facts"))?;
        if cfg.succs[target.index()].len() >= 2 && !required.is_disjoint(after) {
            break true;
        }
        // ScopePlan 已按 block 发布全部 Close 位置；相邻位置间的空隙就是执行事件，
        // 无须再扫描 opcode，也不按槽位重建每次 Close 的关闭集合。
        let range = cfg.blocks[target.index()].instrs;
        let mut event_start = range.start.index();
        if let Ok(index) = scopes.binary_search_by_key(&target, |scope| scope.entry) {
            for &close in &scopes[index].close_points {
                if closed_resource && event_start < close.index() {
                    break 'tail true;
                }
                if let Some(closed) = flow.close_origins(close) {
                    closed_resource |= !required.is_disjoint(closed);
                    required.retain(|origin| !closed.contains(origin));
                }
                if required.is_empty() {
                    break 'tail false;
                }
                event_start = close.index() + 1;
            }
        }
        let event_end = cfg.non_control_instr_range(&proto.instrs, target).end;
        if closed_resource && event_start < event_end {
            break true;
        }
        let Some(next) = crate::structure::loops::transparent_loop_exit_target(proto, cfg, target)
        else {
            break false;
        };
        target = next;
    };
    if !crosses {
        return Ok(false);
    }
    // 仅有交错资源边界时才冻结控制边；正常出口不依赖内部 terminal 细分。
    let control = freeze_loop_control_edges(cfg, candidate, partition, None)?;
    Ok(control
        .exit
        .into_iter()
        .chain(control.preheader_exit)
        .any(|edge| cfg.edges[edge.index()].to == continuation))
}

fn loop_body_owns_block(partition: &LoopPartitions, block: BlockRef) -> bool {
    // for 的 preheader prefix 在循环前求值；其中的资源不属于本轮词法 body。
    Some(block) != partition.preheader && partition.owned.contains(&block)
}

pub(super) struct LoopPayloadFreezeInput<'a> {
    pub(super) proto: &'a LoweredProto,
    pub(super) cfg: &'a Cfg,
    pub(super) edge_plans: &'a [EdgePlan],
    pub(super) evidence: &'a super::super::LoopPlanInput,
    pub(super) partition: &'a LoopPartitions,
    pub(super) loop_region: RegionId,
    pub(super) planned_propagated_break: Option<RegionId>,
    pub(super) break_edges: &'a [EdgeRef],
    pub(super) continue_edges: &'a [EdgeRef],
    pub(super) tbc_flow: &'a crate::structure::scope::TbcFlowFacts,
    pub(super) condition: Option<super::super::ConditionPlanId>,
    pub(super) condition_entry: Option<BlockRef>,
    pub(super) condition_terminals: Option<[EdgeRef; 2]>,
}

pub(super) fn freeze_loop_payload(
    input: LoopPayloadFreezeInput<'_>,
) -> Result<super::super::LoopPlanData, StructureError> {
    let LoopPayloadFreezeInput {
        proto,
        cfg,
        edge_plans,
        evidence,
        partition,
        loop_region,
        planned_propagated_break,
        break_edges,
        continue_edges,
        tbc_flow,
        condition,
        condition_entry,
        condition_terminals,
    } = input;
    let candidate = &evidence.candidate;
    let mut control_edges =
        freeze_loop_control_edges(cfg, candidate, partition, condition_terminals)?;
    control_edges.continues.extend_from_slice(continue_edges);
    control_edges.continues.sort_by_key(|edge| edge.index());
    control_edges.continues.dedup();
    let exit_tail = detect_loop_exit_tail(
        proto,
        cfg,
        edge_plans,
        partition,
        loop_region,
        &control_edges,
        break_edges,
        tbc_flow,
    )?;
    let propagated_break =
        freeze_propagated_break(cfg, edge_plans, partition, planned_propagated_break);
    let condition_prefix_placement = (!partition.control.is_empty()
        && matches!(
            candidate.kind_hint,
            crate::structure::LoopKindHint::WhileLike
                | crate::structure::LoopKindHint::RepeatLike
                | crate::structure::LoopKindHint::Unknown
        ))
    .then_some(
        if candidate.kind_hint == crate::structure::LoopKindHint::RepeatLike
            && condition_entry
                .or(candidate.condition_header)
                .or(candidate.continue_target)
                .unwrap_or(candidate.header)
                != candidate.header
            && control_edges.continues.is_empty()
        {
            super::super::LoopConditionPrefixPlacement::AfterBody
        } else {
            super::super::LoopConditionPrefixPlacement::BeforeBody
        },
    );
    let continue_target = if matches!(
        candidate.kind_hint,
        crate::structure::LoopKindHint::NumericForLike
            | crate::structure::LoopKindHint::GenericForLike
    ) {
        candidate
            .continue_target
            .filter(|target| partition.control.contains(target))
    } else {
        candidate.continue_target
    };

    Ok(super::super::LoopPlanData {
        kind: candidate.kind_hint,
        header: candidate.header,
        preheader_block: partition.preheader,
        condition_header: candidate.condition_header,
        condition,
        condition_prefix_placement,
        continuation: partition.continuation,
        continue_target,
        source_bindings: candidate.source_bindings,
        control_edges,
        break_edges: break_edges.to_vec(),
        normalized_exit_aliases: candidate.normalized_exit_aliases.clone(),
        normal_tail: partition
            .normal_tail
            .as_ref()
            .map(|tail| tail.contract.clone()),
        exit_tail,
        propagated_break,
        header_values: candidate.header_value_merges.clone(),
        exit_values: candidate.exit_value_merges.clone(),
        carried_values: evidence.carried_values.clone(),
        protocol: None,
        value_actions: None,
    })
}

pub(super) fn freeze_propagated_break(
    cfg: &Cfg,
    edge_plans: &[EdgePlan],
    partition: &LoopPartitions,
    planned_target: Option<RegionId>,
) -> Option<RegionId> {
    let target = planned_target?;
    let mut exits = Vec::new();
    for block in &partition.owned {
        for edge in &cfg.succs[block.index()] {
            let cfg_edge = cfg.edges.get(edge.index())?;
            if partition.owned.contains(&cfg_edge.to)
                || matches!(cfg_edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                || shared_pure_terminal_kind(cfg, cfg_edge.to).is_some()
            {
                continue;
            }
            let edge_plan = edge_plans.get(edge.index())?;
            exits.push((cfg_edge, edge_plan));
        }
    }
    (!exits.is_empty()
        && exits.into_iter().all(|(edge, plan)| {
            matches!(plan.transfer, EdgeTransfer::Break(owner) if owner == target)
                || matches!(
                    plan.transfer,
                    EdgeTransfer::BranchArm(super::super::BranchArm::LoopExit)
                ) && Some(edge.to) == partition.continuation
        }))
    .then_some(target)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn detect_loop_exit_tail(
    proto: &LoweredProto,
    cfg: &Cfg,
    edge_plans: &[EdgePlan],
    partition: &LoopPartitions,
    loop_region: RegionId,
    control_edges: &super::super::LoopControlEdges,
    break_edges: &[EdgeRef],
    tbc_flow: &crate::structure::scope::TbcFlowFacts,
) -> Result<Option<super::super::LoopExitTailPlan>, StructureError> {
    if partition.normal_tail.is_some() {
        return Ok(None);
    }
    let [normal_exit] = control_edges.exit.as_slice() else {
        return Ok(None);
    };
    let normal_exit = *normal_exit;
    let Some(edge_plan) = edge_plans.get(normal_exit.index()) else {
        return Err(StructureError::invalid(
            "loop normal exit references a missing edge plan",
        ));
    };
    if edge_plan.owner != loop_region
        || edge_plan.transfer != EdgeTransfer::Break(loop_region)
        || edge_plan.forward_route.is_some()
    {
        return Ok(None);
    }
    let cfg_edge = cfg
        .edges
        .get(normal_exit.index())
        .ok_or_else(|| StructureError::invalid("loop normal exit references a missing CFG edge"))?;
    let Some(continuation) = partition.continuation else {
        return Ok(None);
    };
    if cfg_edge.to != continuation || continuation == cfg.exit_block {
        return Ok(None);
    }
    let mut predecessors = cfg.preds[continuation.index()]
        .iter()
        .copied()
        .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
        .collect::<Vec<_>>();
    predecessors.sort_by_key(|edge| edge.index());
    if predecessors.as_slice() != [normal_exit] {
        return Ok(None);
    }

    let active = tbc_flow
        .active_at_entry(continuation)
        .ok_or_else(|| StructureError::invalid("loop exit tail block has no TBC entry facts"))?;
    let mut required = BTreeSet::<InstrRef>::new();
    for origin in active {
        let Some(origin_block) = cfg.instr_to_block.get(origin.index()) else {
            return Err(StructureError::invalid(
                "loop exit tail TBC origin has no CFG block",
            ));
        };
        if !loop_body_owns_block(partition, *origin_block) {
            continue;
        }
        let Some(LowInstr::Tbc(_)) = proto.instrs.get(origin.index()) else {
            return Err(StructureError::invalid(
                "loop exit tail active origin is not a TBC instruction",
            ));
        };
        required.insert(*origin);
    }
    if required.is_empty() {
        return Ok(None);
    }

    let block_range = cfg.blocks[continuation.index()].instrs;
    let mut cleanup = Vec::new();
    let mut has_observable_prefix = false;
    let mut tail_end = None;
    let mut cleanup_block = continuation;
    let mut cleanup_route = Vec::new();
    let mut trailing_jump = None;
    for index in block_range.start.index()..block_range.end() {
        let instr_ref = InstrRef(index);
        match proto.instrs.get(index) {
            Some(LowInstr::Tbc(_)) => {
                // 注册仍是可抛错的执行事件，不属于 break 可吸收的清理后缀。
                cleanup.clear();
                has_observable_prefix = true;
                required.insert(instr_ref);
            }
            Some(LowInstr::Close(_)) => {
                cleanup.push(instr_ref);
                // 稀疏索引不记录仅关闭 open upvalue 的 Close；absence 即空 TBC kill。
                if let Some(closed) = tbc_flow.close_origins(instr_ref) {
                    required.retain(|origin| !closed.contains(origin));
                }
                if required.is_empty() {
                    tail_end = Some(index + 1);
                    break;
                }
            }
            Some(LowInstr::Jump(_)) if index + 1 == block_range.end() => {
                trailing_jump = Some(instr_ref);
                break;
            }
            Some(instr) if instr.is_control_terminator() => return Ok(None),
            Some(_) => {
                // 例如 Close(inner); observe(); Close(outer)：只消费末端 outer Close，
                // inner Close 必须在 observe 前经原始位置或已冻结的入边事件执行。
                cleanup.clear();
                has_observable_prefix = true;
            }
            None => {
                return Err(StructureError::invalid(
                    "loop exit tail range exceeds the instruction arena",
                ));
            }
        }
    }
    if tail_end.is_none() {
        let Some(jump) = trailing_jump else {
            return Ok(None);
        };
        // 先前的独立 Close 留在执行范围；唯一后继的连续 Close 才是终末后缀。
        cleanup.clear();
        let [route_edge] = cfg.succs[continuation.index()].as_slice() else {
            return Ok(None);
        };
        let Some(route_cfg) = cfg.edges.get(route_edge.index()) else {
            return Err(StructureError::invalid(
                "loop exit tail cleanup route references a missing edge",
            ));
        };
        let Some(route_plan) = edge_plans.get(route_edge.index()) else {
            return Err(StructureError::invalid(
                "loop exit tail cleanup route has no edge plan",
            ));
        };
        if route_cfg.from != continuation
            || route_cfg.kind != EdgeKind::Jump
            || route_plan.transfer != EdgeTransfer::Fallthrough
            || route_plan.forward_route.is_some()
            || route_cfg.to == cfg.exit_block
        {
            return Ok(None);
        }
        let mut cleanup_predecessors = cfg.preds[route_cfg.to.index()]
            .iter()
            .copied()
            .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
            .collect::<Vec<_>>();
        cleanup_predecessors.sort_by_key(|edge| edge.index());
        if cleanup_predecessors.as_slice() != [*route_edge] {
            return Ok(None);
        }

        cleanup_block = route_cfg.to;
        cleanup_route.push(*route_edge);
        let cleanup_range = cfg.blocks[cleanup_block.index()].instrs;
        for index in cleanup_range.start.index()..cleanup_range.end() {
            let instr_ref = InstrRef(index);
            let Some(LowInstr::Close(_)) = proto.instrs.get(index) else {
                return Ok(None);
            };
            cleanup.push(instr_ref);
            if let Some(closed) = tbc_flow.close_origins(instr_ref) {
                required.retain(|origin| !closed.contains(origin));
            }
            if required.is_empty() {
                break;
            }
        }
        if required.is_empty() {
            tail_end = Some(jump.index());
        }
    }
    let Some(end) = tail_end else {
        return Ok(None);
    };
    if !has_observable_prefix || end >= block_range.end() || cleanup.is_empty() {
        return Ok(None);
    }

    let mut early_exits = break_edges
        .iter()
        .copied()
        .filter(|edge| *edge != normal_exit)
        .collect::<Vec<_>>();
    early_exits.sort_by_key(|edge| edge.index());
    early_exits.dedup();
    if early_exits.iter().any(|edge| {
        cfg.edges
            .get(edge.index())
            .is_some_and(|edge| edge.to == continuation)
    }) {
        return Ok(None);
    }

    Ok(Some(super::super::LoopExitTailPlan {
        normal_exit,
        block: continuation,
        range: crate::structure::InstrRange::new(
            block_range.start,
            end - block_range.start.index(),
        ),
        continuation,
        early_exits,
        cleanup_block,
        cleanup_route,
        cleanup,
    }))
}

pub(super) fn freeze_loop_control_edges(
    cfg: &Cfg,
    candidate: &crate::structure::LoopCandidate,
    partition: &LoopPartitions,
    condition_terminals: Option<[EdgeRef; 2]>,
) -> Result<super::super::LoopControlEdges, StructureError> {
    let is_vm_for = matches!(
        candidate.kind_hint,
        crate::structure::LoopKindHint::NumericForLike
            | crate::structure::LoopKindHint::GenericForLike
    );
    let mut control_edges = super::super::LoopControlEdges {
        backedges: candidate.backedges.clone(),
        ..super::super::LoopControlEdges::default()
    };
    let repeat_condition_has_unique_backedge = candidate.kind_hint
        == crate::structure::LoopKindHint::RepeatLike
        && condition_terminals.is_some_and(|terminals| {
            terminals
                .iter()
                .filter(|edge| candidate.backedges.contains(edge))
                .count()
                == 1
        });
    if let Some(preheader) = partition.preheader {
        for edge in cfg.succs.get(preheader.index()).into_iter().flatten() {
            let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                StructureError::invalid("loop preheader references a missing edge")
            })?;
            let body_role = match (is_vm_for, cfg_edge.kind) {
                (true, EdgeKind::LoopBody) => true,
                (true, EdgeKind::LoopExit) => false,
                _ => partition.owned.contains(&cfg_edge.to) && cfg_edge.to != preheader,
            };
            let slot = if body_role {
                &mut control_edges.preheader_body
            } else {
                &mut control_edges.preheader_exit
            };
            if slot.replace(*edge).is_some() {
                return Err(StructureError::invalid(
                    "for preheader has multiple edges with the same syntax role",
                ));
            }
        }
    }

    for block in &partition.control {
        if candidate
            .normalized_exit_aliases
            .iter()
            .any(|alias| alias.block == *block)
        {
            continue;
        }
        for edge in cfg.succs.get(block.index()).into_iter().flatten() {
            let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                StructureError::invalid("loop condition references a missing edge")
            })?;
            let condition_terminal =
                condition_terminals.is_some_and(|terminals| terminals.contains(edge));
            // Numeric/generic-for 的 syntax body edge 可以是 header 自环，同时也是
            // backedge。它仍必须出现在 body role 中，不能因为目标留在 control
            // partition 就被丢弃。
            let vm_for_body_backedge = is_vm_for && candidate.backedges.contains(edge);
            let normalized_exit = candidate
                .normalized_exit_aliases
                .iter()
                .any(|alias| alias.block == cfg_edge.to);
            if partition.control.contains(&cfg_edge.to)
                && !condition_terminal
                && !vm_for_body_backedge
                && !normalized_exit
            {
                continue;
            }
            let body_role = match (is_vm_for, cfg_edge.kind) {
                (true, EdgeKind::LoopBody) => true,
                (true, EdgeKind::LoopExit) => false,
                (false, _) if repeat_condition_has_unique_backedge && condition_terminal => {
                    candidate.backedges.contains(edge)
                }
                _ => {
                    partition.owned.contains(&cfg_edge.to)
                        && Some(cfg_edge.to) != partition.preheader
                }
            };
            if body_role {
                control_edges.body.push(*edge);
            } else {
                control_edges.exit.push(*edge);
            }
        }
    }
    control_edges.body.sort_by_key(|edge| edge.index());
    control_edges.body.dedup();
    control_edges.exit.sort_by_key(|edge| edge.index());
    control_edges.exit.dedup();
    control_edges.backedges.sort_by_key(|edge| edge.index());
    control_edges.backedges.dedup();

    Ok(control_edges)
}
