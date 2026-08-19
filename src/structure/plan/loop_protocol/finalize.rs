//! 编排循环协议与值动作的冻结并校验最终 arena；依赖各专题构造器，不负责识别循环候选；例如逐个 loop 写入 protocol/value_actions。

use super::*;

pub(in crate::structure::plan) fn finalize(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &mut StructurePlan,
) -> Result<(), StructureError> {
    let analysis = LoopValueAnalysis::build(proto, cfg, graph_facts, dataflow, plan)?;
    let body_completion = freeze_vm_for_body_completion(cfg, plan)?;
    let frozen = plan
        .loops
        .iter()
        .enumerate()
        .map(|(index, payload)| {
            let region = plan
                .loop_region_by_plan
                .get(index)
                .copied()
                .ok_or_else(|| StructureError::invalid("loop region reverse index is stale"))?;
            let protocol = freeze_protocol(&LoopProtocolContext {
                proto,
                cfg,
                dataflow,
                plan,
                analysis: &analysis,
                region,
                payload,
                body_completes_normally: body_completion[index],
            })?;
            let value_actions =
                freeze_value_actions(proto, cfg, dataflow, plan, &analysis, region, payload)?;
            Ok((protocol, value_actions))
        })
        .collect::<Result<Vec<_>, StructureError>>()?;
    for (payload, (protocol, actions)) in plan.loops.iter_mut().zip(frozen) {
        payload.protocol = Some(protocol);
        payload.value_actions = Some(actions);
    }
    freeze_iteration_edge_dispositions(proto, cfg, graph_facts, dataflow, plan, &analysis)?;
    Ok(())
}

/// 证明最终 loop protocol/value-action arena 与被语法吸收的 CFG edge 完全一致。
///
/// 每个 origin 只遍历一次；随后按 edge 用 phi-id epoch 对照 canonical copy，因此不会
/// 为 `(edge, phi)` 建稀疏全对索引，也不会重新执行 SSA 来源分析。
pub(in crate::structure::plan) fn validate(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    let analysis = LoopValueAnalysis::build(proto, cfg, graph_facts, dataflow, plan)?;
    let body_completion = freeze_vm_for_body_completion(cfg, plan)?;
    if plan
        .loops
        .iter()
        .any(|payload| payload.protocol.is_none() || payload.value_actions.is_none())
    {
        return Err(StructureError::invalid(
            "loop payload is missing its frozen protocol/value actions",
        ));
    }

    let absorbed_owner = analysis.absorbed_owner_by_edge.clone();
    let mut origins_by_edge = vec![Vec::<PhiId>::new(); cfg.edges.len()];
    let mut partial_elided_by_edge = vec![Vec::<PhiId>::new(); cfg.edges.len()];
    for (index, payload) in plan.loops.iter().enumerate() {
        let loop_id = super::super::LoopPlanId(index);
        let region = plan
            .loop_region(loop_id)
            .ok_or_else(|| StructureError::invalid("loop protocol has no owning region"))?;
        let protocol = plan
            .loop_protocol(loop_id)
            .ok_or_else(|| StructureError::invalid("loop protocol arena is sparse"))?;
        let expected = freeze_protocol(&LoopProtocolContext {
            proto,
            cfg,
            dataflow,
            plan,
            analysis: &analysis,
            region,
            payload,
            body_completes_normally: body_completion[index],
        })?;
        if *protocol != expected {
            return Err(StructureError::invalid(format!(
                "loop protocol #{} changed after freezing",
                loop_id.index()
            )));
        }
        if let LoopVmProtocol::Repeat(repeat) = protocol {
            validate_repeat_outer_loop_owned_exit_copies(
                proto, cfg, dataflow, plan, &analysis, region, repeat,
            )?;
        }

        let actions = plan
            .loop_value_actions(loop_id)
            .ok_or_else(|| StructureError::invalid("loop value-action arena is sparse"))?;
        let expected_actions =
            freeze_value_actions(proto, cfg, dataflow, plan, &analysis, region, payload)?;
        if *actions != expected_actions {
            return Err(StructureError::invalid(format!(
                "loop value actions #{} changed after freezing",
                loop_id.index()
            )));
        }
        let is_vm_for = matches!(
            protocol,
            LoopVmProtocol::NumericFor(_) | LoopVmProtocol::GenericFor(_)
        );
        if !is_vm_for && (!actions.batches.is_empty() || !actions.elided.is_empty()) {
            return Err(StructureError::invalid(format!(
                "non-for loop #{} owns VM value actions",
                loop_id.index()
            )));
        }

        for batch in &actions.batches {
            for write in &batch.writes {
                if write.origins.is_empty()
                    || dataflow.phi_candidate(write.target).is_none()
                    || !loop_value_source_is_valid(dataflow, payload, write.source)
                {
                    return Err(StructureError::invalid(format!(
                        "loop value action #{} has an invalid target, source, or empty origin set",
                        loop_id.index()
                    )));
                }
                for origin in &write.origins {
                    if origin.target != write.target {
                        return Err(StructureError::invalid(format!(
                            "loop value action #{} origin changes phi target",
                            loop_id.index()
                        )));
                    }
                    record_origin(cfg, &absorbed_owner, &mut origins_by_edge, loop_id, *origin)?;
                }
            }
        }
        for origin in &actions.elided {
            match absorbed_owner.get(origin.edge.index()).copied().flatten() {
                Some(owner) if owner == loop_id => {
                    record_origin(cfg, &absorbed_owner, &mut origins_by_edge, loop_id, *origin)?;
                }
                None if cfg.edges.get(origin.edge.index()).is_some()
                    && payload
                        .control_edges
                        .backedges
                        .binary_search(&origin.edge)
                        .is_ok()
                    && plan.edge_plan(origin.edge).is_some_and(|edge| {
                        edge.owner == region || plan.region_contains(region, edge.owner)
                    }) =>
                {
                    partial_elided_by_edge[origin.edge.index()].push(origin.target);
                }
                _ => {
                    return Err(StructureError::invalid(format!(
                        "loop value action #{} cites an invalid edge origin",
                        loop_id.index()
                    )));
                }
            }
        }
    }

    let mut seen_phi = vec![0usize; dataflow.phi_candidates.len()];
    let mut epoch = 0usize;
    for (edge_index, owner) in absorbed_owner.into_iter().enumerate() {
        let Some(loop_id) = owner else {
            if !origins_by_edge[edge_index].is_empty() {
                return Err(StructureError::invalid(
                    "loop value action escaped its absorbed edge set",
                ));
            }
            continue;
        };
        epoch = epoch.checked_add(1).ok_or_else(|| {
            StructureError::invalid("loop value-action validation epoch overflow")
        })?;
        let edge = EdgeRef(edge_index);
        let region = plan
            .loop_region(loop_id)
            .ok_or_else(|| StructureError::invalid("loop value action lost its owner"))?;
        let edge_plan = plan
            .edge_plan(edge)
            .ok_or_else(|| StructureError::invalid("absorbed loop edge has no final plan"))?;
        // 一条 VM-for syntax edge 仍只有一个最终 transfer owner，但它也可能在
        // containment 上结束一个内层 for 并自然落入祖先结构。例如 Luau 会把空
        // generic-for 的 exit 直接折叠成外层 for 的 LoopBack。只有无需额外语句的
        // 祖先 transfer 能被语法吸收；Break/Continue/Goto 必须由 HIR 显式发射。
        let ancestor_implicit_transfer = edge_plan.owner != region
            && plan.region_contains(edge_plan.owner, region)
            && matches!(
                edge_plan.transfer,
                EdgeTransfer::Fallthrough | EdgeTransfer::BranchArm(_) | EdgeTransfer::LoopBack(_)
            );
        if edge_plan.owner != region && !ancestor_implicit_transfer {
            return Err(StructureError::invalid(format!(
                "absorbed loop edge {edge} {} -> {} ({:?}) is owned by region #{} instead of loop region #{}",
                cfg.edges[edge.index()].from,
                cfg.edges[edge.index()].to,
                edge_plan.transfer,
                edge_plan.owner.index(),
                region.index(),
            )));
        }
        for target in &origins_by_edge[edge_index] {
            let slot = seen_phi.get_mut(target.index()).ok_or_else(|| {
                StructureError::invalid("loop value action references a missing phi")
            })?;
            if *slot == epoch {
                return Err(StructureError::invalid(format!(
                    "edge {edge} phi {target} has multiple loop value dispositions"
                )));
            }
            *slot = epoch;
        }
        let matching_copies = edge_plan
            .phi_copies
            .iter()
            .filter(|copy| {
                seen_phi
                    .get(copy.phi_id.index())
                    .is_some_and(|seen| *seen == epoch)
            })
            .count();
        let missing_origin = matching_copies != origins_by_edge[edge_index].len();
        let undispositioned_owned_copy = edge_plan.owner == region
            && edge_plan.phi_copies.len() != origins_by_edge[edge_index].len();
        if missing_origin || undispositioned_owned_copy {
            return Err(StructureError::invalid(format!(
                "absorbed loop edge {edge} does not disposition every canonical phi copy exactly once"
            )));
        }
    }
    for (edge_index, targets) in partial_elided_by_edge.into_iter().enumerate() {
        if targets.is_empty() {
            continue;
        }
        epoch = epoch.checked_add(1).ok_or_else(|| {
            StructureError::invalid("loop value-action validation epoch overflow")
        })?;
        for target in &targets {
            let slot = seen_phi.get_mut(target.index()).ok_or_else(|| {
                StructureError::invalid("loop value action references a missing phi")
            })?;
            if std::mem::replace(slot, epoch) == epoch {
                return Err(StructureError::invalid(
                    "one backedge phi copy has multiple loop value dispositions",
                ));
            }
        }
        let edge = EdgeRef(edge_index);
        let matching = plan
            .edge_plan(edge)
            .ok_or_else(|| StructureError::invalid("elided loop backedge has no final plan"))?
            .phi_copies
            .iter()
            .filter(|copy| {
                seen_phi
                    .get(copy.phi_id.index())
                    .is_some_and(|seen| *seen == epoch)
            })
            .count();
        if matching != targets.len() {
            return Err(StructureError::invalid(format!(
                "loop backedge {edge} does not contain every elided phi copy exactly once"
            )));
        }
    }
    validate_iteration_edge_dispositions(proto, cfg, graph_facts, dataflow, plan, &analysis)?;
    Ok(())
}
