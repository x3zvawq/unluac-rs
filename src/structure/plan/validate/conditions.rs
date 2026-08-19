//! 校验条件谓词、值、前缀位置与条件边索引；依赖 CFG/SSA/区域计划，不负责分支或循环 payload；例如核对短路条件终端的极性。

use super::*;

pub(super) fn validate_condition_predicates(
    proto: &LoweredProto,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    for (condition_index, condition) in plan.conditions.iter().enumerate() {
        for (node_index, node) in condition.nodes.iter().enumerate() {
            let Some(LowInstr::Branch(branch)) = proto.instrs.get(node.predicate.index()) else {
                return Err(StructureError::invalid(format!(
                    "condition payload #{condition_index} node {node_index} predicate is not a branch"
                )));
            };
            if node.predicate_negated != branch.cond.negated {
                return Err(StructureError::invalid(format!(
                    "condition payload #{condition_index} node {node_index} has stale predicate polarity"
                )));
            }
        }
    }
    Ok(())
}

pub(super) fn validate_condition_values(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    let mut owner_by_condition = vec![None; plan.conditions.len()];
    for (region, region_plan) in plan.regions() {
        let condition = match region_plan {
            RegionPlan::Branch { plan: branch, .. } => Some(
                plan.branch(*branch)
                    .ok_or_else(|| {
                        StructureError::invalid(
                            "condition value owner has a missing branch payload",
                        )
                    })?
                    .condition,
            ),
            RegionPlan::Loop { plan: loop_, .. } => {
                plan.loop_(*loop_)
                    .ok_or_else(|| {
                        StructureError::invalid("condition value owner has a missing loop payload")
                    })?
                    .condition
            }
            RegionPlan::Block { .. }
            | RegionPlan::Sequence { .. }
            | RegionPlan::ValueDecision { .. }
            | RegionPlan::Unstructured { .. } => None,
        };
        let Some(condition) = condition else {
            continue;
        };
        let slot = owner_by_condition
            .get_mut(condition.index())
            .ok_or_else(|| {
                StructureError::invalid("region references a missing condition value payload")
            })?;
        if slot
            .replace(region)
            .is_some_and(|existing| existing != region)
        {
            return Err(StructureError::invalid(
                "condition value payload has multiple region owners",
            ));
        }
    }

    for (condition_index, condition) in plan.conditions.iter().enumerate() {
        let condition_id = super::super::ConditionPlanId(condition_index);
        for node in &condition.nodes {
            let Some(value) = node.materialized_value else {
                continue;
            };
            let owner = owner_by_condition[condition_index].ok_or_else(|| {
                StructureError::invalid("condition value payload has no owning region")
            })?;
            if plan.condition_value_owner(value.phi) != Some((condition_id, node.id)) {
                return Err(StructureError::invalid(
                    "condition value has a stale reverse owner",
                ));
            }
            let Some(LowInstr::Branch(branch)) = proto.instrs.get(node.predicate.index()) else {
                return Err(StructureError::invalid(
                    "condition value predicate is not a branch",
                ));
            };
            if !matches!(branch.cond.subject, BranchSubject::Compare { .. }) {
                return Err(StructureError::invalid(
                    "condition value predicate does not produce a boolean",
                ));
            }
            let consumer = condition.nodes.get(value.consumer.index()).ok_or_else(|| {
                StructureError::invalid("condition value references a missing consumer")
            })?;
            let phi = dataflow.phi_candidate(value.phi).ok_or_else(|| {
                StructureError::invalid("condition value references a missing phi")
            })?;
            let uses = dataflow.phi_uses.get(value.phi.index()).map(Vec::as_slice);
            if phi.block != consumer.block
                || phi.incoming.len() != 2
                || uses
                    != Some(&[crate::structure::UseSite {
                        instr: value.use_instr,
                        reg: phi.reg,
                    }])
                || cfg.instr_to_block.get(value.use_instr.index()).copied() != Some(consumer.block)
            {
                return Err(StructureError::invalid(
                    "condition value phi has stale use ownership",
                ));
            }
            if phi.incoming.iter().enumerate().any(|(index, incoming)| {
                !matches!(
                    plan.phi_plan(phi.id)
                        .and_then(|plan| plan.incomings.get(index))
                        .map(|incoming| incoming.disposition),
                    Some(PhiIncomingDisposition::RegionResult(region)) if region == owner
                ) || incoming.edge.is_none()
            }) {
                return Err(StructureError::invalid(
                    "condition value phi is not owned by its region",
                ));
            }

            let bool_for_arc = |truthy: bool| -> Option<bool> {
                let polarity = match truthy ^ node.predicate_negated {
                    true => ConditionArcPolarity::BranchTrue,
                    false => ConditionArcPolarity::BranchFalse,
                };
                let arc = node.arc(polarity);
                let edge = arc.route.last().copied()?;
                let incoming = phi
                    .incoming
                    .iter()
                    .find(|incoming| incoming.edge == Some(edge))?;
                let crate::structure::SsaValue::Def(def) = incoming.value else {
                    return None;
                };
                let instr = dataflow.def_instr(def);
                let LowInstr::LoadBool(load) = proto.instrs.get(instr.index())? else {
                    return None;
                };
                arc.connector_blocks
                    .contains(&dataflow.def_block(def))
                    .then_some(load.value)
            };
            let (Some(raw_truthy), Some(raw_falsy)) = (bool_for_arc(true), bool_for_arc(false))
            else {
                return Err(StructureError::invalid(
                    "condition value routes do not materialize booleans",
                ));
            };
            if raw_truthy == raw_falsy || value.negated == raw_truthy {
                return Err(StructureError::invalid(
                    "condition value boolean polarity is stale",
                ));
            }
            if super::super::condition_forwarded_callee(
                proto,
                cfg,
                dataflow,
                node,
                value.phi,
                value.use_instr,
                node.id == condition.entry,
            ) != Some(value.forwarded_callee)
            {
                return Err(StructureError::invalid(
                    "condition value forwarded callee is stale",
                ));
            }
        }
    }
    Ok(())
}

pub(super) fn validate_condition_prefix_placements(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    for (index, payload) in plan.loops.iter().enumerate() {
        if payload.kind != crate::structure::LoopKindHint::RepeatLike
            || payload.condition_prefix_placement
                != Some(crate::structure::LoopConditionPrefixPlacement::BeforeBody)
            || payload.control_edges.continues.is_empty()
        {
            continue;
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
        if condition_entry == payload.header {
            continue;
        }
        let range = cfg.blocks[condition_entry.index()].instrs;
        let end = range.last().map_or(range.end(), |last| {
            if proto.instrs[last.index()].is_control_terminator() {
                range.end() - 1
            } else {
                range.end()
            }
        });
        if !(range.start.index()..end).all(|instr| {
            matches!(
                proto.instrs[instr],
                LowInstr::LoadNil(_)
                    | LowInstr::LoadBool(_)
                    | LowInstr::LoadConst(_)
                    | LowInstr::LoadInteger(_)
                    | LowInstr::LoadNumber(_)
            )
        }) {
            return Err(StructureError::invalid(format!(
                "loop payload #{index} moves an effectful condition prefix before the body"
            )));
        }
    }
    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ConditionEdgeBinding {
    condition: ConditionPlanId,
    node: BlockRef,
    target: ConditionTarget,
}

pub(super) struct ConditionEdgeIndex {
    first: Vec<Option<ConditionEdgeBinding>>,
    terminal: Vec<Option<ConditionEdgeBinding>>,
    terminal_endpoint: Vec<Option<BlockRef>>,
}

impl ConditionEdgeIndex {
    fn new(edge_count: usize) -> Self {
        Self {
            first: vec![None; edge_count],
            terminal: vec![None; edge_count],
            terminal_endpoint: vec![None; edge_count],
        }
    }

    fn record_first(
        &mut self,
        edge: EdgeRef,
        binding: ConditionEdgeBinding,
    ) -> Result<(), StructureError> {
        record_condition_edge(&mut self.first, edge, binding, "first")
    }

    fn record_terminal(
        &mut self,
        edge: EdgeRef,
        binding: ConditionEdgeBinding,
        endpoint: BlockRef,
    ) -> Result<(), StructureError> {
        record_condition_edge(&mut self.terminal, edge, binding, "terminal")?;
        let slot = self
            .terminal_endpoint
            .get_mut(edge.index())
            .ok_or_else(|| StructureError::invalid("condition terminal edge is outside the CFG"))?;
        if slot.replace(endpoint).is_some_and(|old| old != endpoint) {
            return Err(StructureError::invalid(format!(
                "condition terminal edge {edge} has conflicting physical endpoints"
            )));
        }
        Ok(())
    }

    pub(super) fn first_target(
        &self,
        condition: ConditionPlanId,
        edge: EdgeRef,
    ) -> Option<ConditionTarget> {
        self.first
            .get(edge.index())
            .copied()
            .flatten()
            .filter(|binding| binding.condition == condition)
            .map(|binding| binding.target)
    }

    pub(super) fn terminal_target(
        &self,
        condition: ConditionPlanId,
        edge: EdgeRef,
    ) -> Option<ConditionTarget> {
        self.terminal
            .get(edge.index())
            .copied()
            .flatten()
            .filter(|binding| binding.condition == condition)
            .map(|binding| binding.target)
    }

    fn terminal_endpoint(&self, condition: ConditionPlanId, edge: EdgeRef) -> Option<BlockRef> {
        self.terminal
            .get(edge.index())
            .copied()
            .flatten()
            .filter(|binding| binding.condition == condition)?;
        self.terminal_endpoint.get(edge.index()).copied().flatten()
    }
}

pub(super) fn record_condition_edge(
    index: &mut [Option<ConditionEdgeBinding>],
    edge: EdgeRef,
    binding: ConditionEdgeBinding,
    position: &str,
) -> Result<(), StructureError> {
    let Some(slot) = index.get_mut(edge.index()) else {
        return Err(StructureError::invalid(format!(
            "condition {} edge {edge} is outside the CFG arena",
            position
        )));
    };
    if let Some(existing) = *slot
        && existing != binding
    {
        return Err(StructureError::invalid(format!(
            "condition {position} edge {edge} has conflicting frozen owners: {existing:?} vs {binding:?}"
        )));
    }
    *slot = Some(binding);
    Ok(())
}

pub(super) fn validate_condition_plans(
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<ConditionEdgeIndex, StructureError> {
    let mut edge_index = ConditionEdgeIndex::new(cfg.edges.len());
    for (phi_index, owner) in plan.condition_value_by_phi.iter().copied().enumerate() {
        let Some((condition_id, node_id)) = owner else {
            continue;
        };
        let value = plan
            .condition(condition_id)
            .and_then(|condition| condition.nodes.get(node_id.index()))
            .and_then(|node| node.materialized_value)
            .ok_or_else(|| {
                StructureError::invalid("condition value reverse index references a missing node")
            })?;
        if value.phi.index() != phi_index {
            return Err(StructureError::invalid(
                "condition value reverse index has a stale phi",
            ));
        }
    }
    let mut referenced = vec![false; plan.conditions.len()];
    for branch in &plan.branches {
        let Some(slot) = referenced.get_mut(branch.condition.index()) else {
            return Err(StructureError::invalid(
                "branch references a missing condition payload",
            ));
        };
        *slot = true;
    }
    for loop_ in &plan.loops {
        if let Some(condition) = loop_.condition {
            let Some(slot) = referenced.get_mut(condition.index()) else {
                return Err(StructureError::invalid(
                    "loop references a missing condition payload",
                ));
            };
            *slot = true;
        }
    }

    let mut seen_block_epoch = vec![0usize; cfg.blocks.len()];
    for (index, condition) in plan.conditions.iter().enumerate() {
        if !referenced[index]
            || condition.nodes.is_empty()
            || condition.entry.index() >= condition.nodes.len()
        {
            return Err(StructureError::invalid(format!(
                "condition payload #{index} is unreferenced or has no valid entry"
            )));
        }

        let mut blocks = Vec::new();
        let epoch = index.checked_add(1).ok_or_else(|| {
            StructureError::invalid("condition count exceeds validation epoch capacity")
        })?;
        let mut reachable = vec![false; condition.nodes.len()];
        let mut indegree = vec![0usize; condition.nodes.len()];
        let mut terminal_edges = [Vec::new(), Vec::new()];
        for (node_index, node) in condition.nodes.iter().enumerate() {
            if node.id.index() != node_index || node.block.index() >= cfg.blocks.len() {
                return Err(StructureError::invalid(format!(
                    "condition payload #{index} has non-dense nodes or duplicate blocks"
                )));
            }
            let Some(seen_epoch) = seen_block_epoch.get_mut(node.block.index()) else {
                return Err(StructureError::invalid(format!(
                    "condition payload #{index} references a missing block"
                )));
            };
            if std::mem::replace(seen_epoch, epoch) == epoch {
                return Err(StructureError::invalid(format!(
                    "condition payload #{index} has duplicate node blocks"
                )));
            }
            blocks.push(node.block);
            let range = cfg.blocks[node.block.index()].instrs;
            let predicate = range.last().ok_or_else(|| {
                StructureError::invalid(format!(
                    "condition payload #{index} node {node_index} has an empty predicate block"
                ))
            })?;
            if predicate != node.predicate {
                return Err(StructureError::invalid(format!(
                    "condition payload #{index} node {node_index} has a stale predicate binding"
                )));
            }
            let (branch_true, branch_false) = cfg.branch_edges(node.block).ok_or_else(|| {
                StructureError::invalid(format!(
                    "condition payload #{index} node {node_index} is not a CFG branch"
                ))
            })?;
            for (polarity, expected_first) in [
                (ConditionArcPolarity::BranchTrue, branch_true),
                (ConditionArcPolarity::BranchFalse, branch_false),
            ] {
                let arc = node.arc(polarity);
                if arc.source != node.id {
                    return Err(StructureError::invalid(format!(
                        "condition payload #{index} node {node_index} arc owner is stale"
                    )));
                }
                let Some(first_edge) = arc.route.first().copied() else {
                    return Err(StructureError::invalid(format!(
                        "condition payload #{index} node {node_index} has an empty route"
                    )));
                };
                if first_edge != expected_first || arc.polarity != polarity {
                    return Err(StructureError::invalid(format!(
                        "condition payload #{index} node {node_index} has a stale physical route"
                    )));
                }
                edge_index.record_first(
                    first_edge,
                    ConditionEdgeBinding {
                        condition: ConditionPlanId(index),
                        node: node.block,
                        target: arc.target,
                    },
                )?;
                let mut connector_blocks = Vec::new();
                for pair in arc.route.windows(2) {
                    let current = cfg.edges.get(pair[0].index()).ok_or_else(|| {
                        StructureError::invalid(format!(
                            "condition payload #{index} route references a missing CFG edge"
                        ))
                    })?;
                    let next = cfg.edges.get(pair[1].index()).ok_or_else(|| {
                        StructureError::invalid(format!(
                            "condition payload #{index} route references a missing CFG edge"
                        ))
                    })?;
                    if current.to != next.from {
                        return Err(StructureError::invalid(format!(
                            "condition payload #{index} node {node_index} route is not contiguous"
                        )));
                    }
                    connector_blocks.push(current.to);
                }
                if connector_blocks != arc.connector_blocks {
                    return Err(StructureError::invalid(format!(
                        "condition payload #{index} node {node_index} route connector blocks are stale"
                    )));
                }
                if !arc.route.contains(&arc.transfer) {
                    return Err(StructureError::invalid(format!(
                        "condition payload #{index} node {node_index} transfer is outside its route"
                    )));
                }
                let transfer_position = arc
                    .route
                    .iter()
                    .position(|edge| *edge == arc.transfer)
                    .ok_or_else(|| {
                        StructureError::invalid(format!(
                            "condition payload #{index} node {node_index} transfer is outside its route"
                        ))
                    })?;
                for block in arc.connector_blocks.iter().take(transfer_position) {
                    let Some(seen_epoch) = seen_block_epoch.get_mut(block.index()) else {
                        return Err(StructureError::invalid(format!(
                            "condition payload #{index} connector references a missing block"
                        )));
                    };
                    if std::mem::replace(seen_epoch, epoch) == epoch {
                        return Err(StructureError::invalid(format!(
                            "condition payload #{index} reuses a condition block across nodes"
                        )));
                    }
                    blocks.push(*block);
                }
                validate_condition_internal_route(cfg, plan, index, node_index, arc)?;
                let last_edge = *arc.route.last().ok_or_else(|| {
                    StructureError::invalid(format!(
                        "condition payload #{index} node {node_index} route is empty"
                    ))
                })?;
                match arc.target {
                    ConditionTarget::Node(target) => {
                        let target_node = condition.nodes.get(target.index()).ok_or_else(|| {
                            StructureError::invalid(format!(
                                "condition payload #{index} references a missing node"
                            ))
                        })?;
                        if cfg.edges[last_edge.index()].to != target_node.block {
                            return Err(StructureError::invalid(format!(
                                "condition payload #{index} node edge contradicts the CFG"
                            )));
                        }
                        indegree[target.index()] += 1;
                    }
                    ConditionTarget::Truthy => {
                        terminal_edges[0].push(arc.transfer);
                        edge_index.record_terminal(
                            arc.transfer,
                            ConditionEdgeBinding {
                                condition: ConditionPlanId(index),
                                node: node.block,
                                target: ConditionTarget::Truthy,
                            },
                            cfg.edges[last_edge.index()].to,
                        )?;
                    }
                    ConditionTarget::Falsy => {
                        terminal_edges[1].push(arc.transfer);
                        edge_index.record_terminal(
                            arc.transfer,
                            ConditionEdgeBinding {
                                condition: ConditionPlanId(index),
                                node: node.block,
                                target: ConditionTarget::Falsy,
                            },
                            cfg.edges[last_edge.index()].to,
                        )?;
                    }
                }
            }
            if let Some(value) = node.materialized_value {
                let (ConditionTarget::Node(truthy), ConditionTarget::Node(falsy)) =
                    (node.semantic_target(true), node.semantic_target(false))
                else {
                    return Err(StructureError::invalid(format!(
                        "condition payload #{index} value node {node_index} has a terminal route"
                    )));
                };
                if truthy != falsy
                    || truthy == node.id
                    || condition.nodes.get(truthy.index()).is_none()
                    || plan.condition_value_owner(value.phi)
                        != Some((super::super::ConditionPlanId(index), node.id))
                    || cfg.instr_to_block.get(value.use_instr.index()).copied()
                        != Some(condition.nodes[truthy.index()].block)
                {
                    return Err(StructureError::invalid(format!(
                        "condition payload #{index} value node {node_index} has stale ownership or consumer"
                    )));
                }
            }
        }
        if blocks != condition.blocks {
            return Err(StructureError::invalid(format!(
                "condition payload #{index} has stale frozen block coverage"
            )));
        }

        let expected_exits = [condition.truthy, condition.falsy];
        for terminal_index in 0..2 {
            let exits = &terminal_edges[terminal_index];
            let representative = expected_exits[terminal_index];
            if exits.is_empty() || !exits.contains(&representative) {
                return Err(StructureError::invalid(format!(
                    "condition payload #{index} is missing a frozen terminal edge"
                )));
            }
            let terminal_target = if terminal_index == 0 {
                ConditionTarget::Truthy
            } else {
                ConditionTarget::Falsy
            };
            let condition_id = ConditionPlanId(index);
            let representative_target = edge_index
                .terminal_endpoint(condition_id, representative)
                .filter(|_| {
                    edge_index.terminal_target(condition_id, representative)
                        == Some(terminal_target)
                })
                .ok_or_else(|| {
                    StructureError::invalid(format!(
                        "condition payload #{index} terminal transfer has no physical endpoint"
                    ))
                })?;
            let representative_plan = plan.edge_plan(representative).ok_or_else(|| {
                StructureError::invalid(format!(
                    "condition payload #{index} terminal edge has no plan"
                ))
            })?;
            for edge in exits {
                let edge_plan = plan.edge_plan(*edge).ok_or_else(|| {
                    StructureError::invalid(format!(
                        "condition payload #{index} terminal edge has no plan"
                    ))
                })?;
                if edge_index.terminal_endpoint(condition_id, *edge) != Some(representative_target)
                    || edge_plan.owner != representative_plan.owner
                    || edge_plan.transfer != representative_plan.transfer
                    || edge_plan.action_placement != representative_plan.action_placement
                    || edge_plan.phi_copies != representative_plan.phi_copies
                    || edge_plan.iteration != representative_plan.iteration
                    || plan.edge_action_is_forwarded_only(*edge)
                        != plan.edge_action_is_forwarded_only(representative)
                    || edge_plan.forward_route != representative_plan.forward_route
                        && (!forwarded_actions_are_empty(plan, edge_plan)
                            || !forwarded_actions_are_empty(plan, representative_plan))
                {
                    return Err(StructureError::invalid(format!(
                        "condition payload #{index} has inconsistent terminal edge actions: \
                         representative={representative:?}/{representative_plan:?}, \
                         edge={edge:?}/{edge_plan:?}"
                    )));
                }
            }
        }

        let mut stack = vec![condition.entry];
        while let Some(node) = stack.pop() {
            if std::mem::replace(&mut reachable[node.index()], true) {
                continue;
            }
            let node = &condition.nodes[node.index()];
            for target in [node.semantic_target(true), node.semantic_target(false)] {
                if let ConditionTarget::Node(target) = target {
                    stack.push(target);
                }
            }
        }
        if reachable.iter().any(|reachable| !reachable) {
            return Err(StructureError::invalid(format!(
                "condition payload #{index} has unreachable DAG nodes"
            )));
        }

        let mut ready = indegree
            .iter()
            .enumerate()
            .filter_map(|(index, degree)| (*degree == 0).then_some(index))
            .collect::<Vec<_>>();
        let mut visited = 0usize;
        while let Some(node_index) = ready.pop() {
            visited += 1;
            let node = &condition.nodes[node_index];
            for target in [node.semantic_target(true), node.semantic_target(false)] {
                let ConditionTarget::Node(target) = target else {
                    continue;
                };
                indegree[target.index()] -= 1;
                if indegree[target.index()] == 0 {
                    ready.push(target.index());
                }
            }
        }
        if visited != condition.nodes.len() {
            return Err(StructureError::invalid(format!(
                "condition payload #{index} contains a cycle"
            )));
        }
        let header = condition.header().ok_or_else(|| {
            StructureError::invalid(format!("condition payload #{index} has no entry node"))
        })?;
        if condition
            .blocks()
            .any(|block| block != header && plan.label_for_block(block).is_some())
        {
            return Err(StructureError::invalid(format!(
                "condition payload #{index} absorbs a labeled non-entry block"
            )));
        }
    }
    Ok(edge_index)
}
