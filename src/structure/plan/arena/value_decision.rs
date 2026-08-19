//! value-decision payload 与 arc 的最终冻结。输入 canonical SSA、condition DAG 和 edge plans，输出值决策节点、arc 与 phi ownership 索引；不负责普通 branch lowering。例如短路值合流会把每条叶子路径冻结成唯一 arc transfer。

use super::*;

pub(super) fn freeze_value_decision(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    evidence: &super::super::ValueDecisionPlanInput,
) -> Result<super::super::ValueDecisionPlan, StructureError> {
    use crate::structure::ShortCircuitNodeRef;

    let candidate = &evidence.candidate;
    let ShortCircuitExit::ValueMerge(merge) = candidate.exit else {
        return Err(StructureError::invalid(
            "selected value decision does not have a merge exit",
        ));
    };
    let result_phi = candidate
        .result_phi_id
        .ok_or_else(|| StructureError::invalid("value decision is missing its result phi"))?;
    let result_reg = candidate
        .result_reg
        .ok_or_else(|| StructureError::invalid("value decision is missing its result register"))?;
    let phi = dataflow
        .phi_candidate(result_phi)
        .ok_or_else(|| StructureError::invalid("value decision references a missing result phi"))?;
    if phi.block != merge || phi.reg != result_reg {
        return Err(StructureError::invalid(
            "value decision result identity contradicts its merge phi",
        ));
    }
    if candidate.entry.index() >= candidate.nodes.len() {
        return Err(StructureError::invalid(
            "value decision entry references a missing node",
        ));
    }

    let mut leaf_by_block = BTreeMap::new();
    let mut leaf_evidence = Vec::with_capacity(candidate.value_incomings.len());
    for incoming in &candidate.value_incomings {
        if !candidate.blocks.contains(&incoming.pred)
            || dataflow.block_exit_value(incoming.pred, result_reg) != incoming.value
        {
            return Err(StructureError::invalid(
                "value decision leaf contradicts frozen SSA facts",
            ));
        }
        if incoming.latest_local_def.is_some_and(|def| {
            dataflow.def_block(def) != incoming.pred
                || dataflow.def_reg(def) != result_reg
                || SsaValue::Def(def) != incoming.value
        }) {
            return Err(StructureError::invalid(
                "value decision leaf local definition is stale",
            ));
        }
        let id = super::super::ValueDecisionLeafId(leaf_evidence.len());
        if leaf_by_block.insert(incoming.pred, id).is_some() {
            return Err(StructureError::invalid(
                "value decision has duplicate leaf identities",
            ));
        }
        leaf_evidence.push(incoming);
    }
    let mut leaf_bindings = vec![None; leaf_evidence.len()];
    let mut route_edges = BTreeSet::new();
    let mut nodes = Vec::with_capacity(candidate.nodes.len());
    for (index, node) in candidate.nodes.iter().enumerate() {
        if node.id != ShortCircuitNodeRef(index) || !candidate.blocks.contains(&node.header) {
            return Err(StructureError::invalid(
                "value decision node identity is not dense",
            ));
        }
        let predicate_ref = cfg
            .blocks
            .get(node.header.index())
            .and_then(|block| block.instrs.last())
            .ok_or_else(|| StructureError::invalid("value decision node is empty"))?;
        let Some(LowInstr::Branch(predicate)) = proto.instrs.get(predicate_ref.index()) else {
            return Err(StructureError::invalid(
                "value decision node has no branch predicate",
            ));
        };
        let truthy = freeze_value_decision_arc(
            proto,
            cfg,
            dataflow,
            candidate,
            phi,
            node,
            predicate_ref,
            predicate,
            true,
            &node.truthy,
            &leaf_by_block,
            &leaf_evidence,
            &mut leaf_bindings,
        )?;
        let falsy = freeze_value_decision_arc(
            proto,
            cfg,
            dataflow,
            candidate,
            phi,
            node,
            predicate_ref,
            predicate,
            false,
            &node.falsy,
            &leaf_by_block,
            &leaf_evidence,
            &mut leaf_bindings,
        )?;
        route_edges.extend(truthy.route.iter().copied());
        route_edges.extend(falsy.route.iter().copied());
        nodes.push(super::super::ValueDecisionNodePlan {
            id: super::super::ValueDecisionNodeId(index),
            block: node.header,
            predicate: predicate_ref,
            predicate_negated: predicate.cond.negated,
            truthy,
            falsy,
        });
    }

    let mut leaves = Vec::with_capacity(leaf_evidence.len());
    let mut terminal_edges = BTreeSet::new();
    for (index, (evidence, binding)) in leaf_evidence.into_iter().zip(leaf_bindings).enumerate() {
        let (terminal_edge, physical_pred, physical_value) = binding.ok_or_else(|| {
            StructureError::invalid("value decision has an unreachable frozen leaf")
        })?;
        terminal_edges.insert(terminal_edge);
        leaves.push(super::super::ValueDecisionLeafPlan {
            id: super::super::ValueDecisionLeafId(index),
            block: evidence.pred,
            value: evidence.value,
            latest_local_def: evidence.latest_local_def,
            terminal_edge,
            physical_pred,
            physical_value,
        });
    }

    let phi_edges = phi
        .incoming
        .iter()
        .filter(|incoming| incoming.value != SsaValue::Phi(phi.id))
        .map(|incoming| {
            incoming.edge.ok_or_else(|| {
                StructureError::invalid("value decision result phi has a synthetic incoming")
            })
        })
        .collect::<Result<BTreeSet<_>, StructureError>>()?;
    if terminal_edges != phi_edges {
        return Err(StructureError::invalid(
            "value decision leaves do not cover every physical result incoming",
        ));
    }
    let expected_edges = candidate
        .blocks
        .iter()
        .flat_map(|block| cfg.succs[block.index()].iter().copied())
        .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].to))
        .collect::<BTreeSet<_>>();
    if route_edges != expected_edges {
        return Err(StructureError::invalid(
            "value decision routes do not cover its closed CFG subgraph",
        ));
    }
    let shared_exit_action = leaves
        .first()
        .map(|leaf| leaf.terminal_edge)
        .ok_or_else(|| StructureError::invalid("value decision has no result leaf"))?;
    Ok(super::super::ValueDecisionPlan {
        entry: super::super::ValueDecisionNodeId(candidate.entry.index()),
        nodes,
        leaves,
        blocks: candidate.blocks.iter().copied().collect(),
        merge,
        shared_exit_action,
        result_phi,
        absorbed_phis: Vec::new(),
        result_reg,
    })
}

pub(super) fn assign_absorbed_value_phis(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    decisions: &mut [super::super::ValueDecisionPlan],
) -> Result<(), StructureError> {
    let mut owner_by_edge = vec![None; cfg.edges.len()];
    for (index, decision) in decisions.iter().enumerate() {
        let owner = super::super::ValueDecisionPlanId(index);
        for block in &decision.blocks {
            for &edge in &cfg.succs[block.index()] {
                if !cfg.reachable_blocks.contains(&cfg.edges[edge.index()].to) {
                    continue;
                }
                let slot = owner_by_edge.get_mut(edge.index()).ok_or_else(|| {
                    StructureError::invalid(
                        "value decision references an edge outside the CFG arena",
                    )
                })?;
                if slot
                    .replace(owner)
                    .is_some_and(|existing| existing != owner)
                {
                    return Err(StructureError::invalid(
                        "one CFG edge is absorbed by multiple value decisions",
                    ));
                }
            }
        }
    }

    for phi in &dataflow.phi_candidates {
        let Some(first_edge) = phi.incoming.first().and_then(|incoming| incoming.edge) else {
            continue;
        };
        let Some(owner) = owner_by_edge[first_edge.index()] else {
            continue;
        };
        if phi.id == decisions[owner.index()].result_phi
            || !phi.incoming.iter().all(|incoming| {
                incoming
                    .edge
                    .is_some_and(|edge| owner_by_edge[edge.index()] == Some(owner))
            })
        {
            continue;
        }
        decisions[owner.index()].absorbed_phis.push(phi.id);
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn freeze_value_decision_arc(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    candidate: &crate::structure::ShortCircuitCandidate,
    phi: &crate::structure::PhiCandidate,
    node: &crate::structure::ShortCircuitNode,
    predicate_ref: InstrRef,
    predicate: &crate::transformer::BranchInstr,
    semantic_truthy: bool,
    raw_target: &crate::structure::ShortCircuitTarget,
    leaf_by_block: &BTreeMap<BlockRef, super::super::ValueDecisionLeafId>,
    leaf_evidence: &[&crate::structure::ShortCircuitValueIncoming],
    leaf_bindings: &mut [Option<(EdgeRef, BlockRef, SsaValue)>],
) -> Result<super::super::ValueDecisionArcPlan, StructureError> {
    use crate::structure::ShortCircuitTarget;

    let result_reg = candidate
        .result_reg
        .ok_or_else(|| StructureError::invalid("value decision has no result register"))?;
    let target = match raw_target {
        ShortCircuitTarget::Node(next) => {
            if next.index() >= candidate.nodes.len() {
                return Err(StructureError::invalid(
                    "value decision edge references a missing node",
                ));
            }
            super::super::ValueDecisionTarget::Node(super::super::ValueDecisionNodeId(next.index()))
        }
        ShortCircuitTarget::Value(block) => {
            let leaf = leaf_by_block.get(block).copied().ok_or_else(|| {
                StructureError::invalid("value decision target has no frozen value leaf")
            })?;
            let evidence = leaf_evidence.get(leaf.index()).ok_or_else(|| {
                StructureError::invalid("value decision target has no leaf evidence")
            })?;
            if super::super::value_leaf_is_current(
                proto,
                dataflow,
                predicate_ref,
                predicate,
                result_reg,
                evidence.value,
                evidence.latest_local_def,
            ) {
                super::super::ValueDecisionTarget::CurrentValue(leaf)
            } else {
                super::super::ValueDecisionTarget::Leaf(leaf)
            }
        }
        ShortCircuitTarget::TruthyExit | ShortCircuitTarget::FalsyExit => {
            return Err(StructureError::invalid(
                "control exit reached a value decision",
            ));
        }
    };

    let (branch_true, branch_false) = cfg
        .branch_edges(node.header)
        .ok_or_else(|| StructureError::invalid("value decision node is not a CFG branch"))?;
    let physical_truthy = if predicate.cond.negated {
        branch_false
    } else {
        branch_true
    };
    let first = if semantic_truthy {
        physical_truthy
    } else if physical_truthy == branch_true {
        branch_false
    } else {
        branch_true
    };
    let polarity = match cfg.edges[first.index()].kind {
        EdgeKind::BranchTrue => super::super::ConditionArcPolarity::BranchTrue,
        EdgeKind::BranchFalse => super::super::ConditionArcPolarity::BranchFalse,
        _ => {
            return Err(StructureError::invalid(
                "value decision route does not start with a branch edge",
            ));
        }
    };
    let endpoint = match target {
        super::super::ValueDecisionTarget::Node(next) => candidate.nodes[next.index()].header,
        super::super::ValueDecisionTarget::Leaf(_)
        | super::super::ValueDecisionTarget::CurrentValue(_) => phi.block,
    };
    let mut route = vec![first];
    let mut visited = BTreeSet::from([node.header]);
    loop {
        let last = route
            .last()
            .copied()
            .ok_or_else(|| StructureError::invalid("value decision route is empty"))?;
        let current = cfg
            .edges
            .get(last.index())
            .ok_or_else(|| StructureError::invalid("value decision route left the edge arena"))?
            .to;
        if current == endpoint {
            break;
        }
        if !candidate.blocks.contains(&current) || !visited.insert(current) {
            return Err(StructureError::invalid(
                "value decision route leaves or cycles inside its frozen subgraph",
            ));
        }
        let mut outgoing = cfg.succs[current.index()]
            .iter()
            .copied()
            .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].to));
        let next = outgoing.next().ok_or_else(|| {
            StructureError::invalid("value decision route ends before its declared target")
        })?;
        if outgoing.next().is_some() {
            return Err(StructureError::invalid(
                "value decision connector has multiple reachable successors",
            ));
        }
        route.push(next);
    }

    if let super::super::ValueDecisionTarget::Leaf(leaf)
    | super::super::ValueDecisionTarget::CurrentValue(leaf) = target
    {
        let evidence = leaf_evidence.get(leaf.index()).ok_or_else(|| {
            StructureError::invalid("value decision target references a missing leaf")
        })?;
        if evidence.pred != node.header
            && !route
                .iter()
                .any(|edge| cfg.edges[edge.index()].to == evidence.pred)
        {
            return Err(StructureError::invalid(
                "value decision route does not pass through its logical value leaf",
            ));
        }
        let terminal_edge = *route
            .last()
            .ok_or_else(|| StructureError::invalid("value decision route is empty"))?;
        let physical_pred = cfg.edges[terminal_edge.index()].from;
        let incoming = phi
            .incoming
            .iter()
            .find(|incoming| incoming.edge == Some(terminal_edge))
            .ok_or_else(|| {
                StructureError::invalid(
                    "value decision terminal edge has no physical result incoming",
                )
            })?;
        if incoming.pred != Some(physical_pred)
            || !dataflow.value_contains(incoming.value, evidence.value)
        {
            return Err(StructureError::invalid(
                "value decision physical incoming does not contain its logical leaf value",
            ));
        }
        let binding = (terminal_edge, physical_pred, incoming.value);
        let slot = leaf_bindings.get_mut(leaf.index()).ok_or_else(|| {
            StructureError::invalid("value decision leaf binding is outside the arena")
        })?;
        if slot.is_some_and(|existing| existing != binding) {
            return Err(StructureError::invalid(
                "value decision leaf reaches multiple physical result incomings",
            ));
        }
        *slot = Some(binding);
    }

    Ok(super::super::ValueDecisionArcPlan {
        polarity,
        route,
        target,
    })
}

pub(super) fn index_value_decisions(
    phi_count: usize,
    decisions: &[super::super::ValueDecisionPlan],
) -> Result<Vec<Option<super::super::ValueDecisionPlanId>>, StructureError> {
    let mut by_phi = vec![None; phi_count];
    for (index, decision) in decisions.iter().enumerate() {
        let id = super::super::ValueDecisionPlanId(index);
        for phi in
            std::iter::once(decision.result_phi).chain(decision.absorbed_phis.iter().copied())
        {
            let slot = by_phi.get_mut(phi.index()).ok_or_else(|| {
                StructureError::invalid("value decision references a phi outside the arena")
            })?;
            if slot.replace(id).is_some() {
                return Err(StructureError::invalid(
                    "one phi has multiple value decision owners",
                ));
            }
        }
    }
    Ok(by_phi)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn freeze_condition_arc(
    cfg: &Cfg,
    condition: &crate::structure::common::ShortCircuitCandidate,
    arc: &crate::structure::short_circuit::ConditionArcEvidence,
    truthy_block: BlockRef,
    falsy_block: BlockRef,
    truthy_edges: &mut Vec<EdgeRef>,
    falsy_edges: &mut Vec<EdgeRef>,
    edge_plans: Option<&[EdgePlan]>,
) -> Result<super::super::ConditionArcPlan, StructureError> {
    let source = condition.nodes.get(arc.source.index()).ok_or_else(|| {
        StructureError::invalid("condition route references a missing source node")
    })?;
    let first = arc
        .edges
        .first()
        .copied()
        .ok_or_else(|| StructureError::invalid("condition route is empty"))?;
    let first_edge = cfg
        .edges
        .get(first.index())
        .ok_or_else(|| StructureError::invalid("condition route references a missing CFG edge"))?;
    if first_edge.from != source.header {
        return Err(StructureError::invalid(
            "condition route does not start at its source node",
        ));
    }
    let polarity = match first_edge.kind {
        EdgeKind::BranchTrue => super::super::ConditionArcPolarity::BranchTrue,
        EdgeKind::BranchFalse => super::super::ConditionArcPolarity::BranchFalse,
        _ => {
            return Err(StructureError::invalid(
                "condition route does not start with a physical branch edge",
            ));
        }
    };
    let mut connector_blocks = Vec::with_capacity(arc.edges.len().saturating_sub(1));
    for pair in arc.edges.windows(2) {
        let current = cfg.edges.get(pair[0].index()).ok_or_else(|| {
            StructureError::invalid("condition route references a missing CFG edge")
        })?;
        let next = cfg.edges.get(pair[1].index()).ok_or_else(|| {
            StructureError::invalid("condition route references a missing CFG edge")
        })?;
        if current.to != next.from {
            return Err(StructureError::invalid(
                "condition route contains non-contiguous CFG edges",
            ));
        }
        connector_blocks.push(current.to);
    }
    if connector_blocks != arc.connector_blocks {
        return Err(StructureError::invalid(
            "condition route connector blocks contradict the CFG path",
        ));
    }
    let last =
        arc.edges.last().copied().ok_or_else(|| {
            StructureError::invalid("condition route is missing its terminal edge")
        })?;
    let transfer = condition_arc_transfer_edge(&arc.edges, edge_plans)?;
    let edge_target = cfg.edges[last.index()].to;
    let target = match &arc.target {
        crate::structure::common::ShortCircuitTarget::Node(node) => {
            let expected = condition.nodes.get(node.index()).ok_or_else(|| {
                StructureError::invalid("condition DAG references a missing node")
            })?;
            if edge_target != expected.header {
                return Err(StructureError::invalid(format!(
                    "condition DAG node edge contradicts the CFG: source=#{} target={:?} last={} cfg-to=#{} expected=#{}",
                    source.header.index(),
                    arc.target,
                    last,
                    edge_target.index(),
                    expected.header.index(),
                )));
            }
            super::super::ConditionTarget::Node(super::super::ConditionNodeId(node.index()))
        }
        crate::structure::common::ShortCircuitTarget::TruthyExit => {
            if edge_target != truthy_block {
                return Err(StructureError::invalid(format!(
                    "condition truthy edge {last} from {} reaches {} instead of frozen exit {}",
                    first_edge.from, edge_target, truthy_block,
                )));
            }
            truthy_edges.push(transfer);
            super::super::ConditionTarget::Truthy
        }
        crate::structure::common::ShortCircuitTarget::FalsyExit => {
            if edge_target != falsy_block {
                return Err(StructureError::invalid(format!(
                    "condition falsy edge {last} from {} reaches {} instead of frozen exit {}",
                    first_edge.from, edge_target, falsy_block,
                )));
            }
            falsy_edges.push(transfer);
            super::super::ConditionTarget::Falsy
        }
        crate::structure::common::ShortCircuitTarget::Value(_) => Err(StructureError::invalid(
            "value-merge leaf reached a control condition",
        ))?,
    };
    Ok(super::super::ConditionArcPlan {
        source: super::super::ConditionNodeId(arc.source.index()),
        polarity,
        route: arc.edges.clone(),
        transfer,
        connector_blocks,
        target,
    })
}

pub(super) fn condition_arc_transfer_edge(
    route: &[EdgeRef],
    edge_plans: Option<&[EdgePlan]>,
) -> Result<EdgeRef, StructureError> {
    let last = route
        .last()
        .copied()
        .ok_or_else(|| StructureError::invalid("condition route is empty"))?;
    let Some(edge_plans) = edge_plans else {
        return Ok(last);
    };
    let mut transfer = None;
    for edge in route {
        let edge_plan = edge_plans.get(edge.index()).ok_or_else(|| {
            StructureError::invalid("condition route references a missing final edge plan")
        })?;
        let inert = edge_plan.action_placement == EdgeActionPlacement::BeforeTransfer
            && edge_plan.forward_route.is_none()
            && matches!(
                edge_plan.transfer,
                EdgeTransfer::Fallthrough
                    | EdgeTransfer::BranchArm(
                        super::super::BranchArm::Truthy | super::super::BranchArm::Falsy
                    )
            );
        if !inert && transfer.replace(*edge).is_some() {
            return Err(StructureError::invalid(
                "condition route contains multiple executable edge transfers",
            ));
        }
    }
    Ok(transfer.unwrap_or(last))
}
