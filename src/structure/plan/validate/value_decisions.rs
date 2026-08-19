//! 校验值判定计划及路径值传播；依赖 CFG、SSA 与条件计划，不负责选择判定候选；例如确认每条决策弧产生预期结果值。

use super::*;

pub(super) fn validate_value_decision_plans(
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    let decision_count = plan.value_decisions.len();
    let mut reachable_blocks = vec![false; cfg.blocks.len()];
    for block in &cfg.reachable_blocks {
        if let Some(reachable) = reachable_blocks.get_mut(block.index()) {
            *reachable = true;
        }
    }
    if plan.value_decision_region_by_plan.len() != decision_count {
        return Err(StructureError::invalid(
            "value decision region reverse index length mismatch",
        ));
    }

    let mut region_by_decision = vec![None; decision_count];
    let mut decision_by_region = vec![None; plan.regions.len()];
    for (region_index, region_plan) in plan.regions.iter().enumerate() {
        let RegionPlan::ValueDecision {
            plan: decision_id,
            entry,
            continuation,
            ..
        } = region_plan
        else {
            continue;
        };
        let region = RegionId(region_index);
        let decision = plan.value_decision(*decision_id).ok_or_else(|| {
            StructureError::invalid(format!(
                "value decision region #{region_index} references a missing payload"
            ))
        })?;
        let slot = region_by_decision
            .get_mut(decision_id.index())
            .ok_or_else(|| StructureError::invalid("value decision payload id is not dense"))?;
        if slot.replace(region).is_some() {
            return Err(StructureError::invalid(format!(
                "value decision payload #{} has multiple region owners",
                decision_id.index()
            )));
        }
        decision_by_region[region_index] = Some(*decision_id);
        if plan.value_decision_region(*decision_id) != Some(region)
            || decision.header() != Some(*entry)
            || decision.merge != *continuation
        {
            return Err(StructureError::invalid(format!(
                "value decision payload #{} has a stale region, entry, or continuation",
                decision_id.index()
            )));
        }
    }
    for (index, region) in region_by_decision.iter().copied().enumerate() {
        let region = region.ok_or_else(|| {
            StructureError::invalid(format!(
                "value decision payload #{index} has no owning region"
            ))
        })?;
        if plan.value_decision_region_by_plan[index] != region {
            return Err(StructureError::invalid(format!(
                "value decision payload #{index} has a stale region reverse index"
            )));
        }
    }

    let mut expected_decision_by_phi = vec![None; plan.value_decision_by_phi.len()];
    for index in 0..decision_count {
        let decision_id = ValueDecisionPlanId(index);
        let decision = &plan.value_decisions[index];
        for phi in
            std::iter::once(decision.result_phi).chain(decision.absorbed_phis.iter().copied())
        {
            let slot = expected_decision_by_phi
                .get_mut(phi.index())
                .ok_or_else(|| {
                    StructureError::invalid(
                        "value decision phi reverse index exceeds the phi arena",
                    )
                })?;
            if slot.replace(decision_id).is_some() {
                return Err(StructureError::invalid(
                    "one phi is absorbed by multiple value decisions",
                ));
            }
        }
        if plan.value_decision_owner(decision.result_phi) != Some(decision_id) {
            return Err(StructureError::invalid(format!(
                "value decision payload #{index} has no unique phi reverse index"
            )));
        }
    }
    if plan.value_decision_by_phi != expected_decision_by_phi {
        return Err(StructureError::invalid(
            "value decision phi reverse index is stale",
        ));
    }

    let mut decision_for_block = vec![None; cfg.blocks.len()];
    let mut node_for_block = vec![None; cfg.blocks.len()];
    let mut leaf_for_block = vec![None; cfg.blocks.len()];
    for (decision_index, decision) in plan.value_decisions.iter().enumerate() {
        let decision_id = ValueDecisionPlanId(decision_index);
        let region = region_by_decision[decision_index].ok_or_else(|| {
            StructureError::invalid("value decision payload lost its region owner")
        })?;
        if decision.blocks.is_empty()
            || decision.merge.index() >= cfg.blocks.len()
            || !reachable_blocks[decision.merge.index()]
        {
            return Err(StructureError::invalid(format!(
                "value decision payload #{decision_index} has empty coverage or a missing merge"
            )));
        }
        for block in &decision.blocks {
            let slot = decision_for_block.get_mut(block.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "value decision payload #{decision_index} references missing block {block}"
                ))
            })?;
            let prior_owner = *slot;
            let label = plan.label_for_block(*block);
            if !reachable_blocks
                .get(block.index())
                .copied()
                .unwrap_or(false)
                || plan.region_for_block(*block) != Some(region)
                || prior_owner.is_some()
                || label.is_some() && decision.header() != Some(*block)
            {
                let goto_edges = label.map_or_else(Vec::new, |label| {
                    plan.edge_plans
                        .iter()
                        .filter(|edge| {
                            matches!(
                                edge.transfer,
                                EdgeTransfer::Goto(target, _) if target == label
                            )
                        })
                        .map(|edge| {
                            let cfg_edge = cfg.edges[edge.edge.index()];
                            format!(
                                "{} {} -> {} owner={:?} transfer={:?}",
                                edge.edge, cfg_edge.from, cfg_edge.to, edge.owner, edge.transfer
                            )
                        })
                        .collect::<Vec<_>>()
                });
                return Err(StructureError::invalid(format!(
                    "value decision payload #{decision_index} has stale, duplicate, or labeled block {block}: reachable={} expected-region={region:?} actual-region={:?} prior-owner={prior_owner:?} label={label:?} goto-edges={goto_edges:?}",
                    reachable_blocks
                        .get(block.index())
                        .copied()
                        .unwrap_or(false),
                    plan.region_for_block(*block),
                )));
            }
            *slot = Some(decision_id);
        }
        for (node_index, node) in decision.nodes.iter().enumerate() {
            let Some(slot) = node_for_block.get_mut(node.block.index()) else {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{decision_index} node {node_index} references a missing block"
                )));
            };
            if node.id.index() != node_index
                || decision_for_block[node.block.index()] != Some(decision_id)
                || slot.replace((decision_id, node.id)).is_some()
                || cfg.blocks[node.block.index()].instrs.last() != Some(node.predicate)
                || cfg.branch_edges(node.block).is_none()
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{decision_index} has a stale or non-dense node {node_index}"
                )));
            }
        }
        for (leaf_index, leaf) in decision.leaves.iter().enumerate() {
            let Some(slot) = leaf_for_block.get_mut(leaf.block.index()) else {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{decision_index} leaf {leaf_index} references a missing block"
                )));
            };
            if leaf.id.index() != leaf_index
                || decision_for_block[leaf.block.index()] != Some(decision_id)
                || slot.replace((decision_id, leaf.id)).is_some()
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{decision_index} has a stale or non-dense leaf {leaf_index}"
                )));
            }
        }
    }

    for (block_index, owner) in plan.region_by_block.iter().copied().enumerate() {
        let Some(owner) = owner else {
            continue;
        };
        if let Some(decision_id) = decision_by_region[owner.index()]
            && decision_for_block[block_index] != Some(decision_id)
        {
            return Err(StructureError::invalid(format!(
                "value decision region {owner:?} has block #{block_index} outside its frozen payload"
            )));
        }
    }
    for (decision_index, decision) in plan.value_decisions.iter().enumerate() {
        if decision_for_block[decision.merge.index()] == Some(ValueDecisionPlanId(decision_index)) {
            return Err(StructureError::invalid(format!(
                "value decision payload #{decision_index} absorbs its merge block"
            )));
        }
    }

    let mut expected_route_owner = vec![None; cfg.edges.len()];
    for (decision_index, decision) in plan.value_decisions.iter().enumerate() {
        let decision_id = ValueDecisionPlanId(decision_index);
        for block in &decision.blocks {
            for edge in cfg.succs.get(block.index()).into_iter().flatten() {
                let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                    StructureError::invalid("value decision successor index left the CFG arena")
                })?;
                if !reachable_blocks
                    .get(cfg_edge.to.index())
                    .copied()
                    .unwrap_or(false)
                {
                    continue;
                }
                let slot = &mut expected_route_owner[edge.index()];
                if slot.replace(decision_id).is_some() {
                    return Err(StructureError::invalid(
                        "one absorbed CFG edge belongs to multiple value decisions",
                    ));
                }
            }
        }
    }
    let mut requirement_on_edge = vec![false; cfg.edges.len()];
    for (_, requirement) in plan.requirements.iter() {
        let Some(edge) = requirement.edge() else {
            continue;
        };
        let Some(slot) = requirement_on_edge.get_mut(edge.index()) else {
            return Err(StructureError::invalid(
                "value decision saw a requirement outside the CFG arena",
            ));
        };
        *slot = true;
    }
    let unique_reachable_outgoing = cfg
        .succs
        .iter()
        .map(|outgoing| {
            let mut reachable = outgoing
                .iter()
                .copied()
                .filter(|edge| reachable_blocks[cfg.edges[edge.index()].to.index()]);
            match (reachable.next(), reachable.next()) {
                (Some(edge), None) => Some(edge),
                _ => None,
            }
        })
        .collect::<Vec<_>>();

    let mut covered_route_owner = vec![None; cfg.edges.len()];
    let mut route_visit_stamp = vec![0usize; cfg.blocks.len()];
    let mut route_state = ValueDecisionRouteState {
        covered_route_owner: &mut covered_route_owner,
        route_visit_stamp: &mut route_visit_stamp,
        next_route_stamp: 0,
    };
    for (decision_index, decision) in plan.value_decisions.iter().enumerate() {
        let decision_id = ValueDecisionPlanId(decision_index);
        let region = region_by_decision[decision_index].ok_or_else(|| {
            StructureError::invalid("value decision payload lost its region owner")
        })?;
        if decision.nodes.is_empty() || decision.entry.index() >= decision.nodes.len() {
            return Err(StructureError::invalid(format!(
                "value decision payload #{decision_index} has no valid entry"
            )));
        }
        if !decision
            .leaves
            .iter()
            .any(|leaf| leaf.terminal_edge == decision.shared_exit_action)
        {
            return Err(StructureError::invalid(format!(
                "value decision payload #{decision_index} has no valid shared exit action"
            )));
        }

        let mut indegree = vec![0usize; decision.nodes.len()];
        for (node_index, node) in decision.nodes.iter().enumerate() {
            let context = ValueDecisionRouteContext {
                cfg,
                plan,
                decision_id,
                region,
                decision,
                decision_for_block: &decision_for_block,
                node_for_block: &node_for_block,
                expected_route_owner: &expected_route_owner,
                requirement_on_edge: &requirement_on_edge,
                unique_reachable_outgoing: &unique_reachable_outgoing,
            };
            for (semantic_truthy, arc) in [(true, &node.truthy), (false, &node.falsy)] {
                context.validate_arc(node_index, node, semantic_truthy, arc, &mut route_state)?;
                match arc.target {
                    ValueDecisionTarget::Node(target) => {
                        let Some(degree) = indegree.get_mut(target.index()) else {
                            return Err(StructureError::invalid(format!(
                                "value decision payload #{decision_index} references a missing node"
                            )));
                        };
                        *degree += 1;
                    }
                    ValueDecisionTarget::Leaf(leaf) | ValueDecisionTarget::CurrentValue(leaf)
                        if leaf.index() >= decision.leaves.len() =>
                    {
                        return Err(StructureError::invalid(format!(
                            "value decision payload #{decision_index} references a missing leaf"
                        )));
                    }
                    ValueDecisionTarget::Leaf(_) | ValueDecisionTarget::CurrentValue(_) => {}
                }
            }
        }

        let mut reachable_nodes = vec![false; decision.nodes.len()];
        let mut reachable_leaves = vec![false; decision.leaves.len()];
        let mut pending = vec![decision.entry];
        while let Some(node_id) = pending.pop() {
            let Some(node) = decision.nodes.get(node_id.index()) else {
                return Err(StructureError::invalid(
                    "value decision reachability left the node arena",
                ));
            };
            if std::mem::replace(&mut reachable_nodes[node_id.index()], true) {
                continue;
            }
            for target in [node.truthy.target, node.falsy.target] {
                match target {
                    ValueDecisionTarget::Node(target) => pending.push(target),
                    ValueDecisionTarget::Leaf(leaf) | ValueDecisionTarget::CurrentValue(leaf) => {
                        let Some(reachable) = reachable_leaves.get_mut(leaf.index()) else {
                            return Err(StructureError::invalid(
                                "value decision reachability left the leaf arena",
                            ));
                        };
                        *reachable = true;
                    }
                }
            }
        }
        if reachable_nodes.iter().any(|reachable| !reachable)
            || reachable_leaves.iter().any(|reachable| !reachable)
        {
            return Err(StructureError::invalid(format!(
                "value decision payload #{decision_index} has unreachable nodes or leaves"
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
            let node = &decision.nodes[node_index];
            for target in [node.truthy.target, node.falsy.target] {
                let ValueDecisionTarget::Node(target) = target else {
                    continue;
                };
                indegree[target.index()] -= 1;
                if indegree[target.index()] == 0 {
                    ready.push(target.index());
                }
            }
        }
        if visited != decision.nodes.len() {
            return Err(StructureError::invalid(format!(
                "value decision payload #{decision_index} contains a cycle"
            )));
        }
    }
    if route_state.covered_route_owner != expected_route_owner {
        return Err(StructureError::invalid(
            "value decision routes do not exactly cover their absorbed CFG edges",
        ));
    }
    Ok(())
}

pub(super) struct ValueDecisionRouteContext<'a> {
    cfg: &'a Cfg,
    plan: &'a StructurePlan,
    decision_id: ValueDecisionPlanId,
    region: RegionId,
    decision: &'a ValueDecisionPlan,
    decision_for_block: &'a [Option<ValueDecisionPlanId>],
    node_for_block: &'a [Option<(ValueDecisionPlanId, super::super::ValueDecisionNodeId)>],
    expected_route_owner: &'a [Option<ValueDecisionPlanId>],
    requirement_on_edge: &'a [bool],
    unique_reachable_outgoing: &'a [Option<crate::structure::EdgeRef>],
}

pub(super) struct ValueDecisionRouteState<'a> {
    covered_route_owner: &'a mut [Option<ValueDecisionPlanId>],
    route_visit_stamp: &'a mut [usize],
    next_route_stamp: usize,
}

impl ValueDecisionRouteContext<'_> {
    fn validate_arc(
        &self,
        node_index: usize,
        node: &super::super::ValueDecisionNodePlan,
        semantic_truthy: bool,
        arc: &ValueDecisionArcPlan,
        state: &mut ValueDecisionRouteState<'_>,
    ) -> Result<(), StructureError> {
        let expected_polarity = match semantic_truthy ^ node.predicate_negated {
            true => ConditionArcPolarity::BranchTrue,
            false => ConditionArcPolarity::BranchFalse,
        };
        let (branch_true, branch_false) = self.cfg.branch_edges(node.block).ok_or_else(|| {
            StructureError::invalid("value decision node lost its physical branch edges")
        })?;
        let expected_first = match expected_polarity {
            ConditionArcPolarity::BranchTrue => branch_true,
            ConditionArcPolarity::BranchFalse => branch_false,
        };
        let first = arc.route.first().copied().ok_or_else(|| {
            StructureError::invalid(format!(
                "value decision payload #{} node {node_index} has an empty route",
                self.decision_id.index()
            ))
        })?;
        if arc.polarity != expected_polarity || first != expected_first {
            return Err(StructureError::invalid(format!(
                "value decision payload #{} node {node_index} has stale semantic polarity",
                self.decision_id.index()
            )));
        }

        if state.next_route_stamp == usize::MAX {
            state.route_visit_stamp.fill(0);
            state.next_route_stamp = 1;
        } else {
            state.next_route_stamp += 1;
        }
        let stamp = state.next_route_stamp;
        state.route_visit_stamp[node.block.index()] = stamp;
        let logical_leaf = match arc.target {
            ValueDecisionTarget::Node(_) => None,
            ValueDecisionTarget::Leaf(leaf) | ValueDecisionTarget::CurrentValue(leaf) => self
                .decision
                .leaves
                .get(leaf.index())
                .map(|leaf| leaf.block),
        };
        let mut passes_logical_leaf = logical_leaf == Some(node.block);
        let mut previous_target = None;
        for (position, edge_ref) in arc.route.iter().copied().enumerate() {
            let edge = self.cfg.edges.get(edge_ref.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "value decision payload #{} route references a missing CFG edge",
                    self.decision_id.index()
                ))
            })?;
            if (position == 0 && edge.from != node.block)
                || previous_target.is_some_and(|target| target != edge.from)
                || self
                    .decision_for_block
                    .get(edge.from.index())
                    .copied()
                    .flatten()
                    != Some(self.decision_id)
                || self
                    .expected_route_owner
                    .get(edge_ref.index())
                    .copied()
                    .flatten()
                    != Some(self.decision_id)
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} node {node_index} has a non-contiguous or foreign route",
                    self.decision_id.index()
                )));
            }
            if position == 0
                && !matches!(
                    (arc.polarity, edge.kind),
                    (ConditionArcPolarity::BranchTrue, EdgeKind::BranchTrue)
                        | (ConditionArcPolarity::BranchFalse, EdgeKind::BranchFalse)
                )
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} node {node_index} route starts on the wrong CFG arm",
                    self.decision_id.index()
                )));
            }
            if position > 0
                && self
                    .unique_reachable_outgoing
                    .get(edge.from.index())
                    .copied()
                    .flatten()
                    != Some(edge_ref)
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} route crosses a non-linear connector",
                    self.decision_id.index()
                )));
            }
            let is_last = position + 1 == arc.route.len();
            if !is_last
                && (edge.to == self.decision.merge
                    || self
                        .node_for_block
                        .get(edge.to.index())
                        .copied()
                        .flatten()
                        .is_some()
                    || self
                        .decision_for_block
                        .get(edge.to.index())
                        .copied()
                        .flatten()
                        != Some(self.decision_id))
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} route crosses an undeclared node or boundary",
                    self.decision_id.index()
                )));
            }
            let Some(visit) = state.route_visit_stamp.get_mut(edge.to.index()) else {
                return Err(StructureError::invalid(
                    "value decision route reaches a missing block",
                ));
            };
            if *visit == stamp {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} contains a cyclic physical route",
                    self.decision_id.index()
                )));
            }
            *visit = stamp;
            passes_logical_leaf |= logical_leaf == Some(edge.to);

            let edge_plan = self.plan.edge_plan(edge_ref).ok_or_else(|| {
                StructureError::invalid("value decision route has no frozen edge plan")
            })?;
            let shared_action = self
                .plan
                .edge_plan(self.decision.shared_exit_action)
                .ok_or_else(|| {
                    StructureError::invalid(
                        "value decision shared exit action has no frozen edge plan",
                    )
                })?;
            let terminal_action_matches = if is_last && logical_leaf.is_some() {
                edge_plan.phi_copies == shared_action.phi_copies && edge_plan.iteration.is_empty()
            } else {
                edge_plan.phi_copies.is_empty() && edge_plan.iteration.is_empty()
            };
            if edge_plan.owner != self.region
                || edge_plan.transfer != EdgeTransfer::Fallthrough
                || edge_plan.action_placement != EdgeActionPlacement::BeforeTransfer
                || edge_plan.forward_route.is_some()
                || !terminal_action_matches
                || self.requirement_on_edge[edge_ref.index()]
                || !self.plan.requirements.for_edge(edge_ref).is_empty()
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} has incompatible absorbed edge {edge_ref}: owner={:?} transfer={:?} copies={} iteration={} terminal-action={terminal_action_matches}",
                    self.decision_id.index(),
                    edge_plan.owner,
                    edge_plan.transfer,
                    edge_plan.phi_copies.len(),
                    edge_plan.iteration.len(),
                )));
            }
            match state.covered_route_owner[edge_ref.index()] {
                Some(existing) if existing != self.decision_id => {
                    return Err(StructureError::invalid(
                        "one physical route edge belongs to multiple value decisions",
                    ));
                }
                Some(_) => {}
                None => state.covered_route_owner[edge_ref.index()] = Some(self.decision_id),
            }
            previous_target = Some(edge.to);
        }

        let terminal = previous_target
            .ok_or_else(|| StructureError::invalid("value decision route has no terminal block"))?;
        match arc.target {
            ValueDecisionTarget::Node(target) => {
                if self
                    .decision
                    .nodes
                    .get(target.index())
                    .map(|node| node.block)
                    != Some(terminal)
                {
                    return Err(StructureError::invalid(format!(
                        "value decision payload #{} node {node_index} route misses its target node",
                        self.decision_id.index()
                    )));
                }
            }
            ValueDecisionTarget::Leaf(leaf) | ValueDecisionTarget::CurrentValue(leaf) => {
                let leaf = self.decision.leaves.get(leaf.index()).ok_or_else(|| {
                    StructureError::invalid("value decision route references a missing leaf")
                })?;
                if terminal != self.decision.merge
                    || !passes_logical_leaf
                    || arc.route.last().copied() != Some(leaf.terminal_edge)
                {
                    return Err(StructureError::invalid(format!(
                        "value decision payload #{} node {node_index} route misses its logical leaf or merge",
                        self.decision_id.index()
                    )));
                }
            }
        }
        Ok(())
    }
}

pub(super) fn validate_value_decision_values(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    if plan.value_decision_by_phi.len() != dataflow.phi_candidates.len() {
        return Err(StructureError::invalid(
            "value decision phi reverse index length mismatch",
        ));
    }
    let mut unresolved_result_phi = vec![false; dataflow.phi_candidates.len()];
    for (_, requirement) in plan.requirements.iter() {
        let PlanRequirement::UnresolvedValue { phi_id, .. } = requirement else {
            continue;
        };
        let Some(slot) = unresolved_result_phi.get_mut(phi_id.index()) else {
            return Err(StructureError::invalid(
                "unresolved value requirement references a missing phi",
            ));
        };
        *slot = true;
    }
    let mut incoming_by_edge = vec![None; cfg.edges.len()];
    let mut terminal_edge_owner = vec![None; cfg.edges.len()];
    for (decision_id, decision) in plan.value_decisions() {
        let region = plan
            .value_decision_region(decision_id)
            .ok_or_else(|| StructureError::invalid("value decision has no final region owner"))?;
        let result_phi = dataflow.phi_candidate(decision.result_phi).ok_or_else(|| {
            StructureError::invalid(format!(
                "value decision payload #{} references a missing result phi",
                decision_id.index()
            ))
        })?;
        if result_phi.id != decision.result_phi
            || result_phi.block != decision.merge
            || result_phi.reg != decision.result_reg
        {
            return Err(StructureError::invalid(format!(
                "value decision payload #{} has a stale result identity",
                decision_id.index()
            )));
        }
        let phi_plan = plan.phi_plan(decision.result_phi).ok_or_else(|| {
            StructureError::invalid("value decision result phi has no final value plan")
        })?;
        if phi_plan.incomings.len() != result_phi.incoming.len()
            || !plan.phis_for_region(region).contains(&decision.result_phi)
        {
            return Err(StructureError::invalid(format!(
                "value decision payload #{} result phi has stale shape or no region owner",
                decision_id.index()
            )));
        }
        for (incoming, incoming_plan) in result_phi.incoming.iter().zip(&phi_plan.incomings) {
            let valid = match incoming_plan.disposition {
                PhiIncomingDisposition::RegionResult(owner) => owner == region,
                PhiIncomingDisposition::LoopCarried(owner)
                    if incoming.value == SsaValue::Phi(result_phi.id) =>
                {
                    matches!(
                        plan.region(owner),
                        Some(RegionPlan::Loop { plan: loop_id, .. })
                            if plan.loop_(*loop_id).is_some_and(|loop_| loop_.header == decision.merge)
                    )
                }
                _ => false,
            };
            if !valid {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} result phi has a foreign incoming owner",
                    decision_id.index()
                )));
            }
        }
        if unresolved_result_phi[decision.result_phi.index()] {
            return Err(StructureError::invalid(format!(
                "value decision payload #{} retains an unresolved result requirement",
                decision_id.index()
            )));
        }

        for (node_index, node) in decision.nodes.iter().enumerate() {
            let Some(LowInstr::Branch(branch)) = proto.instrs.get(node.predicate.index()) else {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} node {node_index} predicate is not a branch",
                    decision_id.index()
                )));
            };
            if cfg.instr_to_block.get(node.predicate.index()).copied() != Some(node.block)
                || branch.cond.negated != node.predicate_negated
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} node {node_index} has a stale predicate binding",
                    decision_id.index()
                )));
            }
            for arc in [&node.truthy, &node.falsy] {
                let ValueDecisionTarget::CurrentValue(leaf) = arc.target else {
                    continue;
                };
                let leaf = decision.leaves.get(leaf.index()).ok_or_else(|| {
                    StructureError::invalid(
                        "value decision current-value target references a missing leaf",
                    )
                })?;
                if !super::super::value_leaf_is_current(
                    proto,
                    dataflow,
                    node.predicate,
                    branch,
                    decision.result_reg,
                    leaf.value,
                    leaf.latest_local_def,
                ) {
                    return Err(StructureError::invalid(format!(
                        "value decision payload #{} node {node_index} current-value target contradicts its SSA identity",
                        decision_id.index()
                    )));
                }
            }
        }

        for (incoming_index, (incoming, incoming_plan)) in result_phi
            .incoming
            .iter()
            .zip(&phi_plan.incomings)
            .enumerate()
        {
            if incoming_plan.disposition != PhiIncomingDisposition::RegionResult(region) {
                continue;
            }
            let edge = incoming.edge.ok_or_else(|| {
                StructureError::invalid("value decision result phi has a synthetic incoming")
            })?;
            let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                StructureError::invalid("value decision result incoming left the CFG arena")
            })?;
            let slot = &mut incoming_by_edge[edge.index()];
            if cfg_edge.to != decision.merge
                || incoming.pred != Some(cfg_edge.from)
                || slot.replace((decision_id, incoming_index)).is_some()
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} has a stale or duplicate result incoming",
                    decision_id.index()
                )));
            }
        }
        for (leaf_index, leaf) in decision.leaves.iter().enumerate() {
            if dataflow.block_exit_value(leaf.block, decision.result_reg) != leaf.value {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} leaf {leaf_index} has a stale logical SSA value",
                    decision_id.index()
                )));
            }
            let expected_local_def = match leaf.value {
                SsaValue::Def(def) => dataflow
                    .defs
                    .get(def.index())
                    .filter(|record| {
                        record.id == def
                            && record.block == leaf.block
                            && record.reg == decision.result_reg
                    })
                    .map(|_| def),
                SsaValue::Entry(_) | SsaValue::Phi(_) => None,
            };
            if leaf.latest_local_def != expected_local_def {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} leaf {leaf_index} has a stale local definition",
                    decision_id.index()
                )));
            }

            let edge = cfg.edges.get(leaf.terminal_edge.index()).ok_or_else(|| {
                StructureError::invalid("value decision leaf terminal edge is outside the CFG")
            })?;
            let incoming_index = incoming_by_edge
                .get(leaf.terminal_edge.index())
                .copied()
                .flatten()
                .filter(|(owner, _)| *owner == decision_id)
                .map(|(_, incoming)| incoming)
                .ok_or_else(|| {
                    StructureError::invalid(
                        "value decision leaf terminal edge has no result incoming",
                    )
                })?;
            let incoming = &result_phi.incoming[incoming_index];
            if edge.from != leaf.physical_pred
                || edge.to != decision.merge
                || incoming.pred != Some(leaf.physical_pred)
                || incoming.value != leaf.physical_value
                || !dataflow.value_contains(leaf.physical_value, leaf.value)
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} leaf {leaf_index} has stale physical provenance",
                    decision_id.index()
                )));
            }
            let slot = &mut terminal_edge_owner[leaf.terminal_edge.index()];
            if slot.is_some_and(|owner| owner != decision_id) {
                return Err(StructureError::invalid(
                    "one terminal edge belongs to multiple value decisions",
                ));
            }
            *slot = Some(decision_id);
        }
        if result_phi
            .incoming
            .iter()
            .zip(&phi_plan.incomings)
            .any(|(incoming, incoming_plan)| {
                incoming_plan.disposition == PhiIncomingDisposition::RegionResult(region)
                    && incoming
                        .edge
                        .is_none_or(|edge| terminal_edge_owner[edge.index()] != Some(decision_id))
            })
        {
            return Err(StructureError::invalid(format!(
                "value decision payload #{} leaves a result incoming uncovered",
                decision_id.index()
            )));
        }
    }
    Ok(())
}
