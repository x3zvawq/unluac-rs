//! 已选结构 payload 的压缩与 condition 冻结。输入 region arena、edge plans 和候选 evidence，输出紧凑的 branch/loop/condition arenas 及旧到新 ID 映射；不负责值决策 arc。例如被 containment 选中的 condition 会在这里获得稳定节点与值索引。

use super::*;

pub(super) struct PayloadSelectionContext<'a> {
    pub(super) proto: &'a LoweredProto,
    pub(super) cfg: &'a Cfg,
    pub(super) dataflow: &'a DataflowFacts,
    pub(super) input: &'a FinalPlanInput,
    pub(super) partitions: &'a [LoopPartitions],
    pub(super) propagated_break_by_region: &'a [Option<RegionId>],
    pub(super) edge_plans: &'a [EdgePlan],
    pub(super) tbc_flow: &'a crate::structure::scope::TbcFlowFacts,
}

pub(super) fn compact_selected_payloads(
    arena: &mut RegionArena,
    context: PayloadSelectionContext<'_>,
) -> Result<SelectedPayloads, StructureError> {
    let PayloadSelectionContext {
        proto,
        cfg,
        dataflow,
        input,
        partitions,
        propagated_break_by_region,
        edge_plans,
        tbc_flow,
    } = context;
    let selected_branches = arena
        .specs
        .iter()
        .filter_map(|spec| match spec.kind {
            ContainerKind::Branch(id) => Some(id),
            ContainerKind::SinglePass(_)
            | ContainerKind::ValueDecision(_)
            | ContainerKind::Loop(_)
            | ContainerKind::Island(_)
            | ContainerKind::Residual(_) => None,
        })
        .collect::<BTreeSet<_>>();
    let selected_loops = arena
        .specs
        .iter()
        .filter_map(|spec| match spec.kind {
            ContainerKind::Loop(id) => Some(id),
            ContainerKind::SinglePass(_)
            | ContainerKind::Branch(_)
            | ContainerKind::ValueDecision(_)
            | ContainerKind::Island(_)
            | ContainerKind::Residual(_) => None,
        })
        .collect::<BTreeSet<_>>();
    let selected_value_decisions = arena
        .specs
        .iter()
        .filter_map(|spec| match spec.kind {
            ContainerKind::ValueDecision(id) => Some(id),
            ContainerKind::SinglePass(_)
            | ContainerKind::Branch(_)
            | ContainerKind::Loop(_)
            | ContainerKind::Island(_)
            | ContainerKind::Residual(_) => None,
        })
        .collect::<BTreeSet<_>>();
    let selected_conditions = selected_branches
        .iter()
        .filter_map(|id| input.branches[id.index()].condition)
        .chain(selected_loops.iter().filter_map(|id| {
            input.loops[id.index()].condition.filter(|condition| {
                input.conditions[condition.index()]
                    .candidate
                    .blocks
                    .iter()
                    .all(|block| partitions[id.index()].control.contains(block))
            })
        }))
        .collect::<BTreeSet<_>>();

    let mut condition_map = vec![None; input.conditions.len()];
    let mut conditions = Vec::with_capacity(selected_conditions.len());
    for old in selected_conditions {
        let new = super::super::ConditionPlanId(conditions.len());
        condition_map[old.index()] = Some(new);
        conditions.push(freeze_condition(
            proto,
            cfg,
            dataflow,
            &input.conditions[old.index()],
            Some(edge_plans),
        )?);
    }

    let mut branch_map = vec![None; input.branches.len()];
    let mut branches = Vec::with_capacity(selected_branches.len());
    let mut single_pass_exit_by_header = vec![None; cfg.blocks.len()];
    for fence in &arena.single_passes {
        single_pass_exit_by_header[fence.entry.index()] = Some(fence.continuation);
    }
    for old in selected_branches {
        let new = super::super::BranchPlanId(branches.len());
        branch_map[old.index()] = Some(new);
        let evidence = &input.branches[old.index()];
        let condition = evidence
            .condition
            .ok_or_else(|| StructureError::invalid("selected branch is missing its condition"))?;
        let condition = condition_map[condition.index()].ok_or_else(|| {
            StructureError::invalid("selected branch condition was not compacted")
        })?;
        branches.push(freeze_branch_payload(
            cfg,
            edge_plans,
            evidence,
            condition,
            conditions.get(condition.index()),
            single_pass_exit_by_header[evidence.branch.header.index()],
        )?);
    }

    let mut value_decision_map = vec![None; input.value_decisions.len()];
    let mut value_decisions = Vec::with_capacity(selected_value_decisions.len());
    let mut value_decision_regions = Vec::with_capacity(selected_value_decisions.len());
    for old in selected_value_decisions {
        let new = super::super::ValueDecisionPlanId(value_decisions.len());
        value_decision_map[old.index()] = Some(new);
        value_decisions.push(freeze_value_decision(
            proto,
            cfg,
            dataflow,
            &input.value_decisions[old.index()],
        )?);
        value_decision_regions.push(arena.value_decision_region_by_plan[old.index()]);
    }
    assign_absorbed_value_phis(cfg, dataflow, &mut value_decisions)?;

    let mut loop_map = vec![None; input.loops.len()];
    let mut loops = Vec::with_capacity(selected_loops.len());
    let mut loop_regions = Vec::with_capacity(selected_loops.len());
    let mut break_edges_by_region = vec![Vec::new(); arena.regions.len()];
    let mut continue_edges_by_region = vec![Vec::new(); arena.regions.len()];
    for edge_plan in edge_plans {
        match edge_plan.transfer {
            EdgeTransfer::Break(region) => {
                break_edges_by_region[region.index()].push(edge_plan.edge);
            }
            EdgeTransfer::Continue(region) => {
                continue_edges_by_region[region.index()].push(edge_plan.edge);
            }
            _ => {}
        }
    }
    for old in selected_loops {
        let new = super::super::LoopPlanId(loops.len());
        loop_map[old.index()] = Some(new);
        let evidence = &input.loops[old.index()];
        let condition = evidence
            .condition
            .filter(|condition| {
                input.conditions[condition.index()]
                    .candidate
                    .blocks
                    .iter()
                    .all(|block| partitions[old.index()].control.contains(block))
            })
            .map(|id| {
                condition_map[id.index()].ok_or_else(|| {
                    StructureError::invalid("selected loop condition was not compacted")
                })
            })
            .transpose()?;
        let partition = partitions
            .get(old.index())
            .ok_or_else(|| StructureError::invalid("selected loop has no frozen partitions"))?;
        let loop_region = arena.loop_region_by_plan[old.index()];
        loops.push(freeze_loop_payload(LoopPayloadFreezeInput {
            proto,
            cfg,
            edge_plans,
            evidence,
            partition,
            loop_region,
            planned_propagated_break: propagated_break_by_region
                .get(loop_region.index())
                .copied()
                .flatten(),
            break_edges: &break_edges_by_region[loop_region.index()],
            continue_edges: &continue_edges_by_region[loop_region.index()],
            tbc_flow,
            condition,
            condition_entry: condition
                .and_then(|id| conditions.get(id.index()))
                .and_then(super::super::ConditionPlan::header),
            condition_terminals: condition
                .and_then(|id| conditions.get(id.index()))
                .map(|condition| [condition.truthy, condition.falsy]),
        })?);
        loop_regions.push(loop_region);
    }

    for region in &mut arena.regions {
        match region {
            RegionPlan::Branch { plan, .. } => {
                *plan = branch_map[plan.index()].ok_or_else(|| {
                    StructureError::invalid("branch region references unselected payload")
                })?;
            }
            RegionPlan::Loop { plan, .. } => {
                *plan = loop_map[plan.index()].ok_or_else(|| {
                    StructureError::invalid("loop region references unselected payload")
                })?;
            }
            RegionPlan::ValueDecision { plan, .. } => {
                *plan = value_decision_map[plan.index()].ok_or_else(|| {
                    StructureError::invalid("value decision region references unselected payload")
                })?;
            }
            RegionPlan::Block { .. }
            | RegionPlan::Sequence { .. }
            | RegionPlan::Unstructured { .. } => {}
        }
    }

    Ok(SelectedPayloads {
        branches,
        loops,
        loop_regions,
        conditions,
        condition_map,
        value_decisions,
        value_decision_regions,
    })
}

pub(super) fn freeze_condition(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    evidence: &super::super::ConditionPlanInput,
    edge_plans: Option<&[EdgePlan]>,
) -> Result<super::super::ConditionPlan, StructureError> {
    let condition = &evidence.candidate;
    let ShortCircuitExit::BranchExit { truthy, falsy } = condition.exit else {
        return Err(StructureError::invalid(
            "selected control condition does not have branch exits",
        ));
    };
    let mut arc_slots = vec![[None, None]; condition.nodes.len()];
    for arc in &evidence.arcs {
        let slots = arc_slots.get_mut(arc.source.index()).ok_or_else(|| {
            StructureError::invalid("condition route references a missing source node")
        })?;
        // slots 的稳定顺序是 [semantic truthy, semantic falsy]；bool 到 usize 的原生
        // 映射恰好相反（false=0, true=1），不能直接拿来索引。
        let slot = &mut slots[usize::from(!arc.truthy)];
        if slot.replace(arc).is_some() {
            return Err(StructureError::invalid(
                "condition node has duplicate semantic branch evidence",
            ));
        }
    }
    let mut truthy_edges = Vec::new();
    let mut falsy_edges = Vec::new();
    let nodes = condition
        .nodes
        .iter()
        .enumerate()
        .map(|(index, node)| {
            let predicate = cfg.blocks[node.header.index()]
                .instrs
                .last()
                .ok_or_else(|| {
                    StructureError::invalid("condition node has an empty predicate block")
                })?;
            let [truthy_arc, falsy_arc] = arc_slots.get(index).copied().ok_or_else(|| {
                StructureError::invalid("condition node is missing its arc slots")
            })?;
            let truthy_arc = truthy_arc.ok_or_else(|| {
                StructureError::invalid("condition node is missing its truthy arc")
            })?;
            let falsy_arc = falsy_arc.ok_or_else(|| {
                StructureError::invalid("condition node is missing its falsy arc")
            })?;
            let truthy_arc = freeze_condition_arc(
                cfg,
                condition,
                truthy_arc,
                truthy,
                falsy,
                &mut truthy_edges,
                &mut falsy_edges,
                edge_plans,
            )?;
            let falsy_arc = freeze_condition_arc(
                cfg,
                condition,
                falsy_arc,
                truthy,
                falsy,
                &mut truthy_edges,
                &mut falsy_edges,
                edge_plans,
            )?;
            let predicate_negated =
                truthy_arc.polarity == super::super::ConditionArcPolarity::BranchFalse;
            let mut arcs = [None, None];
            for arc in [truthy_arc, falsy_arc] {
                let slot = &mut arcs[arc.polarity.index()];
                if slot.replace(arc).is_some() {
                    return Err(StructureError::invalid(
                        "condition node has duplicate physical branch polarity",
                    ));
                }
            }
            let [Some(branch_true_arc), Some(branch_false_arc)] = arcs else {
                return Err(StructureError::invalid(
                    "condition node is missing one physical branch route",
                ));
            };
            Ok(super::super::ConditionNodePlan {
                id: super::super::ConditionNodeId(index),
                block: node.header,
                predicate,
                predicate_negated,
                arcs: [branch_true_arc, branch_false_arc],
                materialized_value: None,
            })
        })
        .collect::<Result<Vec<_>, StructureError>>()?;
    let mut nodes = nodes;
    for index in 0..nodes.len() {
        nodes[index].materialized_value = freeze_condition_value(
            proto,
            cfg,
            dataflow,
            &nodes,
            super::super::ConditionNodeId(condition.entry.index()),
            super::super::ConditionNodeId(index),
        );
    }
    let mut blocks = BTreeSet::new();
    let mut frozen_blocks = Vec::new();
    for node in &nodes {
        if blocks.insert(node.block) {
            frozen_blocks.push(node.block);
        }
        for arc in &node.arcs {
            let transfer_position = arc
                .route
                .iter()
                .position(|edge| *edge == arc.transfer)
                .ok_or_else(|| {
                    StructureError::invalid("condition transfer is outside its physical route")
                })?;
            // transfer 之后的 connector 已由 forward route 物理覆盖，不属于会被
            // condition 表达式吸收的控制分区。
            for block in arc.connector_blocks.iter().copied().take(transfer_position) {
                if blocks.insert(block) {
                    frozen_blocks.push(block);
                }
            }
        }
    }
    let truthy = truthy_edges
        .into_iter()
        .min_by_key(|edge| edge.index())
        .ok_or_else(|| StructureError::invalid("selected condition has no truthy terminal edge"))?;
    let falsy = falsy_edges
        .into_iter()
        .min_by_key(|edge| edge.index())
        .ok_or_else(|| StructureError::invalid("selected condition has no falsy terminal edge"))?;
    Ok(super::super::ConditionPlan {
        entry: super::super::ConditionNodeId(condition.entry.index()),
        nodes,
        blocks: frozen_blocks,
        truthy,
        falsy,
    })
}

pub(super) fn freeze_condition_value(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    nodes: &[super::super::ConditionNodePlan],
    entry: super::super::ConditionNodeId,
    node_id: super::super::ConditionNodeId,
) -> Option<super::super::ConditionValuePlan> {
    let node = nodes.get(node_id.index())?;
    let LowInstr::Branch(branch) = proto.instrs.get(node.predicate.index())? else {
        return None;
    };
    // Truthiness 会把任意 Lua 值压成 bool；这里只吸收本身已经返回 bool 的比较，
    // 避免把 `not not value` 错还原成原值。
    if !matches!(branch.cond.subject, BranchSubject::Compare { .. }) {
        return None;
    }
    let [raw_truthy, raw_falsy] = [true, false].map(|truthy| {
        let polarity = match truthy ^ node.predicate_negated {
            true => super::super::ConditionArcPolarity::BranchTrue,
            false => super::super::ConditionArcPolarity::BranchFalse,
        };
        node.arc(polarity)
    });
    let (
        super::super::ConditionTarget::Node(truthy_consumer),
        super::super::ConditionTarget::Node(falsy_consumer),
    ) = (raw_truthy.target, raw_falsy.target)
    else {
        return None;
    };
    if truthy_consumer != falsy_consumer || truthy_consumer == node_id {
        return None;
    }
    let consumer = nodes.get(truthy_consumer.index())?;
    let incoming_edges = [
        raw_truthy.route.last().copied()?,
        raw_falsy.route.last().copied()?,
    ];
    let mut matched = None;
    for phi in dataflow.phi_candidates_in_block(consumer.block) {
        if phi.incoming.len() != 2
            || dataflow.phi_use_count(phi.id) != 1
            || !dataflow.phi_used_only_in_block(phi.id, consumer.block)
            || !dataflow.phi_consumer_ids(phi.id).is_empty()
        {
            continue;
        }
        let values = incoming_edges.map(|edge| {
            let incoming = phi
                .incoming
                .iter()
                .find(|incoming| incoming.edge == Some(edge))?;
            let SsaValue::Def(def) = incoming.value else {
                return None;
            };
            let instr = dataflow.def_instr(def);
            let LowInstr::LoadBool(load) = proto.instrs.get(instr.index())? else {
                return None;
            };
            let block = dataflow.def_block(def);
            node.arcs
                .iter()
                .find(|arc| arc.route.last().copied() == Some(edge))?
                .connector_blocks
                .contains(&block)
                .then_some(load.value)
        });
        let [Some(raw_truthy_value), Some(raw_falsy_value)] = values else {
            continue;
        };
        if raw_truthy_value == raw_falsy_value {
            continue;
        }
        let uses = dataflow.phi_uses.get(phi.id.index())?;
        let [use_site] = uses.as_slice() else {
            continue;
        };
        if cfg.instr_to_block.get(use_site.instr.index()).copied() != Some(consumer.block) {
            continue;
        }
        let Some(forwarded_callee) = super::super::condition_forwarded_callee(
            proto,
            cfg,
            dataflow,
            node,
            phi.id,
            use_site.instr,
            node_id == entry,
        ) else {
            continue;
        };
        let plan = super::super::ConditionValuePlan {
            phi: phi.id,
            consumer: truthy_consumer,
            use_instr: use_site.instr,
            negated: !raw_truthy_value,
            forwarded_callee,
        };
        if matched.replace(plan).is_some() {
            return None;
        }
    }
    matched
}

pub(super) fn index_condition_values(
    phi_count: usize,
    conditions: &[super::super::ConditionPlan],
) -> Result<
    Vec<Option<(super::super::ConditionPlanId, super::super::ConditionNodeId)>>,
    StructureError,
> {
    let mut by_phi = vec![None; phi_count];
    for (condition_index, condition) in conditions.iter().enumerate() {
        let condition_id = super::super::ConditionPlanId(condition_index);
        for node in &condition.nodes {
            let Some(value) = node.materialized_value else {
                continue;
            };
            let slot = by_phi.get_mut(value.phi.index()).ok_or_else(|| {
                StructureError::invalid("condition value references a missing phi")
            })?;
            if slot.replace((condition_id, node.id)).is_some() {
                return Err(StructureError::invalid(
                    "condition value phi has multiple frozen owners",
                ));
            }
        }
    }
    Ok(by_phi)
}

pub(super) fn index_absorbed_condition_blocks(
    block_count: usize,
    conditions: &[super::super::ConditionPlan],
) -> Result<Vec<Option<super::super::ConditionPlanId>>, StructureError> {
    let mut by_block = vec![None; block_count];
    for (condition_index, condition) in conditions.iter().enumerate() {
        let condition_id = super::super::ConditionPlanId(condition_index);
        let entry = condition.header().ok_or_else(|| {
            StructureError::invalid("condition plan has no entry block while building its index")
        })?;
        for block in condition.blocks().filter(|block| *block != entry) {
            let slot = by_block.get_mut(block.index()).ok_or_else(|| {
                StructureError::invalid("condition plan references a block outside the arena")
            })?;
            if slot.replace(condition_id).is_some() {
                return Err(StructureError::invalid(
                    "one block is absorbed by multiple condition plans",
                ));
            }
        }
    }
    Ok(by_block)
}
