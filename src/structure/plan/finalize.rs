//! 冻结最终 StructurePlan、loop 合同与 block emission，并调用严格校验；依赖 arena/validator/loop protocol，不负责候选分析；例如在 phi ownership 完成后生成稠密块发射计划。

use super::*;

pub(crate) fn build_final_structure_plan(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    caps: ControlFlowCaps,
    input: FinalPlanInput,
) -> Result<StructurePlan, StructureError> {
    let mut plan = arena::build(proto, cfg, graph_facts, dataflow, caps, input)?;
    finalize_normal_tail_guards(cfg, &mut plan)?;
    validate::validate(proto, cfg, &plan)?;
    Ok(plan)
}

/// value/cleanup ownership 安装完成后的全量 plan 校验入口。
pub(crate) fn validate_final_structure_plan(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &super::super::DataflowFacts,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    validate::validate_final(proto, cfg, graph_facts, dataflow, plan)
}

pub(crate) fn finalize_loop_contracts(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &mut StructurePlan,
) -> Result<(), StructureError> {
    loop_protocol::finalize(proto, cfg, graph_facts, dataflow, plan)
}

/// 将 normal-tail 的候选边收窄为 HIR 真正发射 `break` 的入口边。
/// forwarding pad 的 outgoing 只承载物理路径，不能持有 guard 动作。
pub(super) fn finalize_normal_tail_guards(
    cfg: &Cfg,
    plan: &mut StructurePlan,
) -> Result<(), StructureError> {
    let mut nearest_loop = vec![None; plan.regions.len()];
    for region in &plan.navigation.preorder {
        let inherited =
            plan.navigation.parent[region.index()].and_then(|parent| nearest_loop[parent.index()]);
        nearest_loop[region.index()] =
            if matches!(plan.region(*region), Some(RegionPlan::Loop { .. })) {
                Some(*region)
            } else {
                inherited
            };
    }

    let mut guard_entries = vec![Vec::new(); plan.loops.len()];
    for edge_plan in &plan.edge_plans {
        let EdgeTransfer::Break(loop_region) = edge_plan.transfer else {
            continue;
        };
        let Some(RegionPlan::Loop { plan: loop_id, .. }) = plan.region(loop_region) else {
            if plan.single_pass_for_region(loop_region).is_some() {
                continue;
            }
            return Err(StructureError::invalid(
                "break transfer targets an unsupported region while freezing normal-tail guards",
            ));
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
            StructureError::invalid("normal-tail guard references a missing CFG edge")
        })?;
        let source_owner = plan.region_for_block(cfg_edge.from).ok_or_else(|| {
            StructureError::invalid("normal-tail guard source has no containment owner")
        })?;
        if nearest_loop[source_owner.index()] != Some(loop_region) {
            // 指向祖先 loop 的 break 由外围 loop lowering 继续物化，不是当前
            // normal-tail 的直接 break，也不能在这里写祖先 guard。
            continue;
        }
        let target = if let Some(route) = edge_plan.forward_route {
            plan.forward_route(route)
                .ok_or_else(|| {
                    StructureError::invalid(
                        "normal-tail break entry references a missing forwarding route",
                    )
                })?
                .target
        } else {
            cfg_edge.to
        };
        if target == tail.continuation {
            guard_entries[loop_id.index()].push(edge_plan.edge);
        }
    }
    for (payload, mut entries) in plan.loops.iter_mut().zip(guard_entries) {
        let Some(tail) = &mut payload.normal_tail else {
            continue;
        };
        entries.sort_by_key(|edge| edge.index());
        entries.dedup();
        tail.early_exits = entries;
    }
    Ok(())
}

pub(crate) fn finalize_block_emissions(
    cfg: &Cfg,
    plan: &mut StructurePlan,
) -> Result<(), StructureError> {
    plan.block_emissions = (0..cfg.blocks.len())
        .map(|index| expected_block_emission(cfg, plan, BlockRef(index)))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(())
}

pub(in crate::structure) fn expected_block_emission(
    cfg: &Cfg,
    plan: &StructurePlan,
    block: BlockRef,
) -> Result<BlockEmissionPlan, StructureError> {
    let emit = || Ok(BlockEmissionPlan::Emit);
    if block == cfg.entry_block
        || block == cfg.exit_block
        || !cfg.reachable_blocks.contains(&block)
        || plan.label_for_block(block).is_some()
    {
        return emit();
    }
    let Some(terminator) = plan.block_terminator(block) else {
        return Err(StructureError::invalid(format!(
            "block {block} has no terminator while freezing emission"
        )));
    };
    let BlockTerminatorKind::Jump {
        instr,
        edge: outgoing,
    } = terminator.kind
    else {
        return emit();
    };
    if terminator.instrs.len != 1 || terminator.instrs.start != instr {
        return emit();
    }
    let Some(owner) = plan.region_for_block(block) else {
        return Err(StructureError::invalid(format!(
            "reachable block {block} has no owner while freezing emission"
        )));
    };
    if !plan.phis_for_region(owner).is_empty() || plan.requirements().has_unresolved_at(block) {
        return emit();
    }
    let incoming = cfg
        .preds
        .get(block.index())
        .ok_or_else(|| StructureError::invalid("forwarded block has no predecessor index"))?
        .iter()
        .copied()
        .filter(|edge| {
            cfg.edges
                .get(edge.index())
                .is_some_and(|edge| cfg.reachable_blocks.contains(&edge.from))
        })
        .collect::<Vec<_>>();
    if incoming.is_empty()
        || incoming.iter().any(|edge| {
            plan.edge_plan(*edge).is_none_or(|entry| {
                !matches!(
                    entry.transfer,
                    EdgeTransfer::Break(_) | EdgeTransfer::Continue(_)
                ) || entry
                    .forward_route
                    .and_then(|route| plan.forward_route(route))
                    .map(|route| route.first)
                    != Some(outgoing)
            })
        })
    {
        return emit();
    }
    Ok(BlockEmissionPlan::ForwardedControl { outgoing })
}
