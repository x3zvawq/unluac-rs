//! 冻结和校验迭代边处置及其值可用性；依赖 CFG、SSA 和最终边计划，不负责 loop 语法形态；例如区分 latch、backedge 和绕过 tail 的 continue。

use super::*;

pub(super) fn freeze_iteration_edge_dispositions(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &mut StructurePlan,
    analysis: &LoopValueAnalysis,
) -> Result<(), StructureError> {
    let frozen =
        build_iteration_edge_dispositions(proto, cfg, graph_facts, dataflow, plan, analysis)?;
    for (edge, dispositions) in plan.edge_plans.iter_mut().zip(frozen) {
        if !edge.iteration.is_empty() {
            return Err(StructureError::invalid(
                "iteration edge dispositions were finalized more than once",
            ));
        }
        edge.iteration = dispositions;
    }
    Ok(())
}

pub(super) fn validate_iteration_edge_dispositions(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    analysis: &LoopValueAnalysis,
) -> Result<(), StructureError> {
    let expected =
        build_iteration_edge_dispositions(proto, cfg, graph_facts, dataflow, plan, analysis)?;
    let mut seen_target_at = vec![usize::MAX; dataflow.phi_candidates.len()];
    for (edge_index, (edge, expected)) in plan.edge_plans.iter().zip(expected).enumerate() {
        if edge.iteration != expected {
            return Err(StructureError::invalid(format!(
                "edge {} iteration dispositions changed after freezing",
                edge.edge
            )));
        }
        for disposition in &edge.iteration {
            let slot = seen_target_at
                .get_mut(disposition.target.index())
                .ok_or_else(|| {
                    StructureError::invalid("iteration edge action targets a missing phi")
                })?;
            if std::mem::replace(slot, edge_index) == edge_index {
                return Err(StructureError::invalid(format!(
                    "edge {} writes one iteration result more than once",
                    edge.edge
                )));
            }
        }
    }
    Ok(())
}

pub(super) fn build_iteration_edge_dispositions(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    analysis: &LoopValueAnalysis,
) -> Result<Vec<Vec<LoopIterationDisposition>>, StructureError> {
    let mut canonical_moves = crate::structure::phi_facts::CanonicalMoveIndex::new(proto, dataflow);
    let mut by_edge = vec![Vec::new(); cfg.edges.len()];
    for (index, payload) in plan.loops.iter().enumerate() {
        let loop_id = super::super::LoopPlanId(index);
        let region = plan
            .loop_region(loop_id)
            .ok_or_else(|| StructureError::invalid("loop iteration action has no owner"))?;
        let control = loop_control_region(plan, region)?;
        let context = LoopValueContext {
            proto,
            cfg,
            dataflow,
            plan,
            analysis,
            owner: region,
            control,
            payload,
        };
        let actions = plan.loop_value_actions(loop_id).ok_or_else(|| {
            StructureError::invalid("loop iteration action has no finalized value protocol")
        })?;
        let writes = actions
            .batches
            .iter()
            .filter(|batch| batch.phase == LoopValuePhase::IterationEpilogue)
            .flat_map(|batch| batch.writes.iter())
            .collect::<Vec<_>>();
        if writes.is_empty() {
            continue;
        }
        for edge in payload
            .control_edges
            .continues
            .iter()
            .copied()
            .filter(|edge| {
                plan.edge_plan(*edge)
                    .is_some_and(|edge_plan| iteration_edge_bypasses_tail(edge_plan, region))
            })
        {
            let edge_plan = plan.edge_plan(edge).ok_or_else(|| {
                StructureError::invalid("loop iteration action references a missing edge plan")
            })?;
            let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                StructureError::invalid("loop iteration action references a missing CFG edge")
            })?;
            let value_block = edge_plan
                .forward_route
                .and_then(|route| plan.forward_route(route))
                .and_then(|route| cfg.edges.get(route.last.index()))
                .map_or(cfg_edge.from, |edge| edge.from);
            for write in &writes {
                let reg = dataflow
                    .phi_candidate(write.target)
                    .ok_or_else(|| {
                        StructureError::invalid("loop iteration action targets a missing phi")
                    })?
                    .reg;
                let incoming =
                    canonical_moves.resolve(dataflow.block_exit_value(value_block, reg))?;
                if !value_is_available_at_edge_action(
                    cfg,
                    graph_facts,
                    dataflow,
                    edge_plan,
                    incoming,
                ) {
                    return Err(StructureError::invalid(format!(
                        "loop iteration result {} is unavailable before edge {edge}",
                        write.target
                    )));
                }
                let source =
                    classify_value_source(&context, incoming, write.target)?.ok_or_else(|| {
                        StructureError::invalid(
                            "loop iteration result resolves to an implicit VM-for control value",
                        )
                    })?;
                by_edge[edge.index()].push(LoopIterationDisposition {
                    loop_region: region,
                    target: write.target,
                    incoming,
                    source,
                });
            }
        }
    }
    let mut seen_target_at = vec![usize::MAX; dataflow.phi_candidates.len()];
    for (edge_index, dispositions) in by_edge.iter().enumerate() {
        for disposition in dispositions {
            let slot = seen_target_at
                .get_mut(disposition.target.index())
                .ok_or_else(|| {
                    StructureError::invalid("iteration edge action targets a missing phi")
                })?;
            if std::mem::replace(slot, edge_index) == edge_index {
                return Err(StructureError::invalid(
                    "one edge has conflicting loop iteration result owners",
                ));
            }
        }
    }
    Ok(by_edge)
}

pub(super) fn iteration_edge_bypasses_tail(edge: &super::super::EdgePlan, owner: RegionId) -> bool {
    matches!(edge.transfer, EdgeTransfer::Continue(region) if region == owner)
        || matches!(
            edge.transfer,
            EdgeTransfer::Goto(
                _,
                GotoReason::UnstructuredContinueLike | GotoReason::CrossLoopContinueLike
            )
        )
}

pub(super) fn value_is_available_at_edge_action(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    edge_plan: &super::super::EdgePlan,
    value: SsaValue,
) -> bool {
    let Some(edge) = cfg.edges.get(edge_plan.edge.index()) else {
        return false;
    };
    match value {
        SsaValue::Entry(_) => true,
        SsaValue::Phi(phi) => dataflow
            .phi_candidate(phi)
            .is_some_and(|phi| graph_facts.dominates(phi.block, edge.from)),
        SsaValue::Def(def) => dataflow.defs.get(def.index()).is_some_and(|definition| {
            if definition.block != edge.from {
                return graph_facts.dominates(definition.block, edge.from);
            }
            let action_limit = edge_plan
                .actions_before_trailing_cleanup()
                .map_or(cfg.blocks[edge.from.index()].instrs.end(), |range| {
                    range.start.index()
                });
            definition.instr.index() < action_limit
        }),
    }
}

pub(super) fn absorbed_value_edges(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    owner: RegionId,
    payload: &LoopPlanData,
) -> Result<Vec<EdgeRef>, StructureError> {
    let control = loop_control_region(plan, owner)?;
    let mut edges = payload
        .control_edges
        .preheader_body
        .into_iter()
        .chain(payload.control_edges.preheader_exit)
        .chain(payload.control_edges.body.iter().copied())
        .chain(payload.control_edges.exit.iter().copied())
        .chain(
            payload
                .control_edges
                .backedges
                .iter()
                .copied()
                .filter(|edge| {
                    cfg.edges
                        .get(edge.index())
                        .is_some_and(|cfg_edge| block_is_in_region(plan, control, cfg_edge.from))
                }),
        )
        .collect::<Vec<_>>();
    if normal_tail_completion_copies(plan, owner, payload)?.is_some_and(|copies| {
        copies.iter().all(|(copy, _)| {
            value_is_available_before_loop(graph_facts, dataflow, payload, copy.value)
        })
    }) && let Some(tail) = &payload.normal_tail
    {
        edges.extend(tail.completion_exits.iter().copied());
    }
    edges.sort_by_key(|edge| edge.index());
    edges.dedup();
    Ok(edges)
}

pub(super) fn value_is_available_before_loop(
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    payload: &LoopPlanData,
    value: SsaValue,
) -> bool {
    match value {
        SsaValue::Entry(_) => true,
        SsaValue::Def(def) => dataflow.defs.get(def.index()).is_some_and(|definition| {
            Some(definition.block) == payload.preheader_block
                || (definition.block != payload.header
                    && graph_facts.dominates(definition.block, payload.header))
        }),
        SsaValue::Phi(phi) => dataflow.phi_candidate(phi).is_some_and(|candidate| {
            candidate.block == payload.header
                || graph_facts.dominates(candidate.block, payload.header)
        }),
    }
}

pub(super) fn record_origin(
    cfg: &Cfg,
    absorbed_owner: &[Option<super::super::LoopPlanId>],
    origins_by_edge: &mut [Vec<PhiId>],
    loop_id: super::super::LoopPlanId,
    origin: EdgeCopyOrigin,
) -> Result<(), StructureError> {
    if cfg.edges.get(origin.edge.index()).is_none()
        || absorbed_owner.get(origin.edge.index()).copied().flatten() != Some(loop_id)
    {
        return Err(StructureError::invalid(format!(
            "loop value action #{} cites a non-absorbed edge origin",
            loop_id.index()
        )));
    }
    origins_by_edge[origin.edge.index()].push(origin.target);
    Ok(())
}

pub(super) fn loop_value_source_is_valid(
    dataflow: &DataflowFacts,
    payload: &LoopPlanData,
    source: LoopValueSource,
) -> bool {
    match source {
        LoopValueSource::Ssa(SsaValue::Entry(_)) => true,
        LoopValueSource::Ssa(SsaValue::Def(def)) => dataflow.defs.get(def.index()).is_some(),
        LoopValueSource::Ssa(SsaValue::Phi(phi)) => dataflow.phi_candidate(phi).is_some(),
        LoopValueSource::Binding(reg) => match payload.source_bindings {
            Some(LoopSourceBindings::Numeric(binding)) => reg == binding,
            Some(LoopSourceBindings::Generic(bindings)) => {
                reg.index() >= bindings.start.index()
                    && reg.index() < bindings.start.index() + bindings.len
            }
            None => false,
        },
        LoopValueSource::Carried(phi) => payload
            .header_values
            .iter()
            .any(|value| value.phi_id == phi),
    }
}

pub(super) fn loop_control_region(
    plan: &StructurePlan,
    owner: RegionId,
) -> Result<RegionId, StructureError> {
    match plan.region(owner) {
        Some(RegionPlan::Loop { control, .. }) => Ok(*control),
        _ => Err(StructureError::invalid(format!(
            "loop payload owner #{} is not a loop region",
            owner.index()
        ))),
    }
}

pub(super) fn block_is_in_region(plan: &StructurePlan, region: RegionId, block: BlockRef) -> bool {
    plan.region_for_block(block)
        .is_some_and(|owner| plan.region_contains(region, owner))
}
