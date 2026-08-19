//! 构建、跟随并冻结闭合控制 DAG 及 condition arc；依赖稠密 workspace 与 SSA 逃逸检查，不负责候选枚举；例如证明 connector 只服务当前 DAG。

use super::*;

pub(super) fn build_closed_branch_control_dag(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    root: BlockRef,
    truthy_exit: BlockRef,
    falsy_exit: BlockRef,
    claimed: &[bool],
) -> Option<ClosedControlDagEvidence> {
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    let mut raw_arcs = Vec::new();
    while let Some(header) = pending.pop() {
        if !seen.insert(header) {
            continue;
        }
        if header != root && claimed.get(header.index()).copied().unwrap_or(true) {
            return None;
        }
        let (truthy_edge, falsy_edge) = truthy_falsy_edges(proto, cfg, header)?;
        for (truthy, edge) in [(true, truthy_edge), (false, falsy_edge)] {
            let arc = follow_closed_branch_arc(
                proto,
                cfg,
                dataflow,
                header,
                truthy,
                edge,
                truthy_exit,
                falsy_exit,
            )?;
            if let RawConditionTarget::Node(target) = arc.target {
                pending.push(target);
            }
            raw_arcs.push(arc);
        }
    }
    finalize_closed_control_dag(cfg, dataflow, root, seen, raw_arcs, truthy_exit, falsy_exit)
}

pub(super) fn finalize_closed_control_dag(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    root: BlockRef,
    headers: BTreeSet<BlockRef>,
    raw_arcs: Vec<RawConditionArc>,
    truthy_exit: BlockRef,
    falsy_exit: BlockRef,
) -> Option<ClosedControlDagEvidence> {
    if headers.len() < 2 {
        return None;
    }
    let mut blocks = headers.clone();
    for arc in &raw_arcs {
        blocks.extend(arc.connector_blocks.iter().copied());
    }
    let exits = raw_arcs
        .iter()
        .filter_map(|arc| match arc.target {
            RawConditionTarget::Exit(exit) => Some(exit),
            RawConditionTarget::Node(_) => None,
        })
        .collect::<BTreeSet<_>>();
    if exits != BTreeSet::from([truthy_exit, falsy_exit])
        || headers
            .iter()
            .copied()
            .filter(|header| *header != root)
            .any(|header| block_defs_escape(cfg, dataflow, header, &blocks))
        || !connector_defs_stay_inside(cfg, dataflow, &raw_arcs, &blocks)
        || !is_reducible_candidate(cfg, root, &blocks)
    {
        return None;
    }

    let mut headers = headers.into_iter().collect::<Vec<_>>();
    headers.retain(|header| *header != root);
    headers.insert(0, root);
    let refs = headers
        .iter()
        .copied()
        .enumerate()
        .map(|(index, header)| (header, ShortCircuitNodeRef(index)))
        .collect::<BTreeMap<_, _>>();
    let mut nodes = headers
        .iter()
        .copied()
        .enumerate()
        .map(|(index, header)| ShortCircuitNode {
            id: ShortCircuitNodeRef(index),
            header,
            truthy: ShortCircuitTarget::TruthyExit,
            falsy: ShortCircuitTarget::FalsyExit,
        })
        .collect::<Vec<_>>();
    let mut arcs = Vec::with_capacity(raw_arcs.len());
    for raw in raw_arcs {
        let source = refs[&raw.source];
        let target = match raw.target {
            RawConditionTarget::Node(header) => ShortCircuitTarget::Node(refs[&header]),
            RawConditionTarget::Exit(exit) if exit == truthy_exit => ShortCircuitTarget::TruthyExit,
            RawConditionTarget::Exit(exit) if exit == falsy_exit => ShortCircuitTarget::FalsyExit,
            RawConditionTarget::Exit(_) => return None,
        };
        let node = nodes.get_mut(source.index())?;
        if raw.truthy {
            node.truthy = target.clone();
        } else {
            node.falsy = target.clone();
        }
        arcs.push(ConditionArcEvidence {
            source,
            truthy: raw.truthy,
            edges: raw.edges,
            connector_blocks: raw.connector_blocks,
            target,
        });
    }
    let entry = ShortCircuitNodeRef(0);
    if !short_circuit_nodes_are_acyclic(&nodes, entry) {
        return None;
    }
    Some(ClosedControlDagEvidence {
        candidate: ShortCircuitCandidate {
            header: root,
            blocks,
            entry,
            nodes,
            exit: ShortCircuitExit::BranchExit {
                truthy: truthy_exit,
                falsy: falsy_exit,
            },
            result_reg: None,
            result_phi_id: None,
            entry_value: None,
            value_incomings: Vec::new(),
            reducible: true,
        },
        arcs,
    })
}

#[allow(clippy::too_many_arguments)]
pub(super) fn follow_closed_branch_arc(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    source: BlockRef,
    truthy: bool,
    first_edge: EdgeRef,
    truthy_exit: BlockRef,
    falsy_exit: BlockRef,
) -> Option<RawConditionArc> {
    let mut edges = vec![first_edge];
    let mut connector_blocks = Vec::new();
    let mut target = cfg.edges.get(first_edge.index())?.to;
    loop {
        if target == truthy_exit || target == falsy_exit {
            break;
        }
        if cfg.branch_edges(target).is_some() {
            return Some(RawConditionArc {
                source,
                truthy,
                edges,
                connector_blocks,
                target: RawConditionTarget::Node(target),
            });
        }
        if reachable_predecessor_count(cfg, target) != 1
            || !connector_block_is_safe(proto, cfg, dataflow, target)
        {
            return None;
        }
        let [next] = cfg.succs[target.index()].as_slice() else {
            return None;
        };
        connector_blocks.push(target);
        edges.push(*next);
        target = cfg.edges[next.index()].to;
    }
    Some(RawConditionArc {
        source,
        truthy,
        edges,
        connector_blocks,
        target: RawConditionTarget::Exit(target),
    })
}

pub(super) fn build_raw_condition_index(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    irreducible_regions: &[IrreducibleRegion],
    loops: &[LoopCandidate],
) -> RawConditionIndex {
    let mut selected_by_header = vec![None::<usize>; cfg.blocks.len()];
    for (index, candidate) in loops.iter().enumerate() {
        let header = closed_control_root(cfg, graph_facts, candidate);
        if header.index() >= cfg.blocks.len()
            || !cfg.reachable_blocks.contains(&header)
            || cfg.branch_edges(header).is_none()
        {
            continue;
        }
        let slot = &mut selected_by_header[header.index()];
        let replace = slot.is_none_or(|current| {
            (candidate.blocks.len(), index) < (loops[current].blocks.len(), current)
        });
        if replace {
            *slot = Some(index);
        }
    }
    let mut selected = selected_by_header.into_iter().flatten().collect::<Vec<_>>();
    selected.sort_by_key(|index| {
        let candidate = &loops[*index];
        (
            candidate.blocks.len(),
            closed_control_root(cfg, graph_facts, candidate),
        )
    });

    let mut roots = Vec::with_capacity(selected.len());
    let mut loop_headers = Vec::with_capacity(selected.len());
    let mut owner_by_block = vec![None; cfg.blocks.len()];
    let mut owner_conflicts = Vec::with_capacity(selected.len());
    for index in selected {
        let candidate = &loops[index];
        let header = closed_control_root(cfg, graph_facts, candidate);
        let owner = roots.len();
        for block in candidate.blocks.iter().copied() {
            if let Some(slot) = owner_by_block.get_mut(block.index())
                && slot.is_none()
            {
                *slot = Some(owner);
            }
        }
        if owner_by_block[header.index()].is_none() {
            owner_by_block[header.index()] = Some(owner);
        }
        owner_conflicts.push(owner_by_block[header.index()] != Some(owner));
        roots.push(RawConditionRoot { owner, header });
        loop_headers.push(candidate.header);
    }

    let mut irreducible = vec![false; cfg.blocks.len()];
    for block in irreducible_regions
        .iter()
        .flat_map(|region| region.blocks.iter().copied())
    {
        irreducible[block.index()] = true;
    }
    let mut decision = vec![false; cfg.blocks.len()];
    for header in cfg.block_order.iter().copied() {
        decision[header.index()] = cfg.reachable_blocks.contains(&header)
            && !irreducible[header.index()]
            && owner_by_block[header.index()].is_some()
            && cfg.branch_edges(header).is_some();
    }

    let root_by_owner = roots.iter().map(|root| root.header).collect::<Vec<_>>();
    let mut connector_claims = vec![None::<ConnectorClaim>; cfg.blocks.len()];
    let mut arcs_by_header = vec![None; cfg.blocks.len()];
    for header in cfg.block_order.iter().copied() {
        if !decision[header.index()] {
            continue;
        }
        let Some(owner) = owner_by_block[header.index()] else {
            continue;
        };
        let Some((truthy_edge, falsy_edge)) = truthy_falsy_edges(proto, cfg, header) else {
            owner_conflicts[owner] = true;
            continue;
        };
        let truthy = follow_indexed_condition_arc(
            proto,
            cfg,
            dataflow,
            &owner_by_block,
            &decision,
            &root_by_owner,
            &loop_headers,
            &mut connector_claims,
            &mut owner_conflicts,
            owner,
            header,
            true,
            truthy_edge,
        );
        let falsy = follow_indexed_condition_arc(
            proto,
            cfg,
            dataflow,
            &owner_by_block,
            &decision,
            &root_by_owner,
            &loop_headers,
            &mut connector_claims,
            &mut owner_conflicts,
            owner,
            header,
            false,
            falsy_edge,
        );
        if let (Some(truthy), Some(falsy)) = (truthy, falsy) {
            arcs_by_header[header.index()] = Some([truthy, falsy]);
        } else {
            owner_conflicts[owner] = true;
        }
    }

    RawConditionIndex {
        roots,
        owner_by_block,
        arcs_by_header,
        owner_conflicts,
    }
}

pub(super) fn closed_control_root(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    candidate: &LoopCandidate,
) -> BlockRef {
    let declared = candidate.condition_header.unwrap_or(candidate.header);
    if declared != candidate.header || candidate.backedges.len() < 2 {
        return declared;
    }
    let mut sources = candidate
        .backedges
        .iter()
        .filter_map(|edge| cfg.edges.get(edge.index()).map(|edge| edge.from));
    let Some(first) = sources.next() else {
        return declared;
    };
    let Some(common) = sources.try_fold(first, |common, source| {
        graph_facts
            .dominator_tree
            .nearest_common_ancestor(common, source)
    }) else {
        return declared;
    };
    if common != candidate.header && cfg.branch_edges(common).is_some() {
        common
    } else {
        declared
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn follow_indexed_condition_arc(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    owner_by_block: &[Option<usize>],
    decision: &[bool],
    root_by_owner: &[BlockRef],
    loop_header_by_owner: &[BlockRef],
    connector_claims: &mut [Option<ConnectorClaim>],
    owner_conflicts: &mut [bool],
    owner: usize,
    source: BlockRef,
    truthy: bool,
    first_edge: EdgeRef,
) -> Option<RawConditionArc> {
    let mut edges = vec![first_edge];
    let mut connector_blocks = Vec::new();
    let mut target = cfg.edges.get(first_edge.index())?.to;

    loop {
        if target == cfg.exit_block
            || owner_by_block.get(target.index()).copied().flatten() != Some(owner)
        {
            break;
        }
        if decision[target.index()] {
            let target = if target == root_by_owner[owner] || target == loop_header_by_owner[owner]
            {
                RawConditionTarget::Exit(target)
            } else {
                RawConditionTarget::Node(target)
            };
            return Some(RawConditionArc {
                source,
                truthy,
                edges,
                connector_blocks,
                target,
            });
        }
        if reachable_predecessor_count(cfg, target) != 1
            || !connector_block_is_safe(proto, cfg, dataflow, target)
        {
            break;
        }
        if let Some(claim) = connector_claims[target.index()] {
            owner_conflicts[owner] = true;
            owner_conflicts[claim.owner] = true;
            return None;
        }
        connector_claims[target.index()] = Some(ConnectorClaim { owner });
        let [next_edge] = cfg.succs[target.index()].as_slice() else {
            break;
        };
        connector_blocks.push(target);
        edges.push(*next_edge);
        target = cfg.edges[next_edge.index()].to;
    }

    Some(RawConditionArc {
        source,
        truthy,
        edges,
        connector_blocks,
        target: RawConditionTarget::Exit(target),
    })
}

pub(super) fn build_closed_control_dag(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    index: &RawConditionIndex,
    root: RawConditionRoot,
    workspace: &mut DenseConditionWorkspace,
) -> Option<ClosedControlDagEvidence> {
    if index.owner_by_block[root.header.index()] != Some(root.owner) {
        return None;
    }
    let raw_epoch = workspace.raw.begin();
    let mut pending = vec![root.header];
    let mut raw_nodes = Vec::new();
    let mut raw_blocks = BTreeSet::new();

    while let Some(header) = pending.pop() {
        if !workspace.raw.insert(header, raw_epoch) {
            continue;
        }
        if index.owner_by_block[header.index()] != Some(root.owner) {
            return None;
        }
        raw_nodes.push(header);
        raw_blocks.insert(header);
        let arcs = index.arcs_by_header[header.index()].as_ref()?;
        for arc in arcs {
            raw_blocks.extend(arc.connector_blocks.iter().copied());
            if let RawConditionTarget::Node(next) = arc.target {
                pending.push(next);
            }
        }
    }

    // decision prefix 若把定义带到候选外，它已经属于 body/continuation，而不是条件。
    // 把该 decision 当作边界，再从 root 重建可达子图，避免吸收 loop body 的首个判断。
    let blocked_epoch = workspace.blocked.begin();
    for header in raw_nodes
        .iter()
        .copied()
        .filter(|header| *header != root.header)
    {
        if block_defs_escape(cfg, dataflow, header, &raw_blocks) {
            workspace.blocked.insert(header, blocked_epoch);
        }
    }
    let retained_epoch = workspace.retained.begin();
    let mut pending = vec![root.header];
    let mut node_headers = Vec::new();
    let mut raw_arcs = Vec::new();
    while let Some(header) = pending.pop() {
        if !workspace.retained.insert(header, retained_epoch) {
            continue;
        }
        node_headers.push(header);
        for raw in index.arcs_by_header[header.index()].as_ref()? {
            let mut arc = raw.clone();
            if let RawConditionTarget::Node(target) = arc.target {
                if workspace.blocked.contains(target, blocked_epoch) {
                    arc.target = RawConditionTarget::Exit(target);
                } else {
                    pending.push(target);
                }
            }
            raw_arcs.push(arc);
        }
    }
    if node_headers.len() < 2 {
        return None;
    }

    let mut blocks = node_headers.iter().copied().collect::<BTreeSet<_>>();
    for arc in &raw_arcs {
        blocks.extend(arc.connector_blocks.iter().copied());
    }
    if !connector_defs_stay_inside(cfg, dataflow, &raw_arcs, &blocks)
        || !is_reducible_candidate(cfg, root.header, &blocks)
    {
        return None;
    }

    let mut exits = raw_arcs.iter().filter_map(|arc| match arc.target {
        RawConditionTarget::Exit(exit) => Some(exit),
        RawConditionTarget::Node(_) => None,
    });
    let first_exit = exits.next()?;
    let second_exit = exits.find(|exit| *exit != first_exit)?;
    if exits.any(|exit| exit != first_exit && exit != second_exit) {
        return None;
    }
    let (truthy_exit, falsy_exit) = classify_guard_branch_exits(
        cfg,
        &graph_facts.post_dominator_tree,
        first_exit,
        second_exit,
    )?;

    node_headers.sort();
    node_headers.retain(|header| *header != root.header);
    node_headers.insert(0, root.header);
    for (position, header) in node_headers.iter().copied().enumerate() {
        workspace.node_refs[header.index()] = Some(ShortCircuitNodeRef(position));
    }
    let entry = ShortCircuitNodeRef(0);
    let mut nodes = node_headers
        .iter()
        .copied()
        .enumerate()
        .map(|(index, header)| ShortCircuitNode {
            id: ShortCircuitNodeRef(index),
            header,
            truthy: ShortCircuitTarget::TruthyExit,
            falsy: ShortCircuitTarget::FalsyExit,
        })
        .collect::<Vec<_>>();
    let mut arcs = Vec::with_capacity(raw_arcs.len());
    for raw in raw_arcs {
        let source = workspace.node_refs[raw.source.index()]?;
        let target = match raw.target {
            RawConditionTarget::Node(header) => {
                ShortCircuitTarget::Node(workspace.node_refs[header.index()]?)
            }
            RawConditionTarget::Exit(exit) if exit == truthy_exit => ShortCircuitTarget::TruthyExit,
            RawConditionTarget::Exit(exit) if exit == falsy_exit => ShortCircuitTarget::FalsyExit,
            RawConditionTarget::Exit(_) => return None,
        };
        let node = nodes.get_mut(source.index())?;
        if raw.truthy {
            node.truthy = target.clone();
        } else {
            node.falsy = target.clone();
        }
        arcs.push(ConditionArcEvidence {
            source,
            truthy: raw.truthy,
            edges: raw.edges,
            connector_blocks: raw.connector_blocks,
            target,
        });
    }
    if !short_circuit_nodes_are_acyclic(&nodes, entry) {
        return None;
    }

    Some(ClosedControlDagEvidence {
        candidate: ShortCircuitCandidate {
            header: root.header,
            blocks,
            entry,
            nodes,
            exit: ShortCircuitExit::BranchExit {
                truthy: truthy_exit,
                falsy: falsy_exit,
            },
            result_reg: None,
            result_phi_id: None,
            entry_value: None,
            value_incomings: Vec::new(),
            reducible: true,
        },
        arcs,
    })
}

pub(super) fn truthy_falsy_edges(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: BlockRef,
) -> Option<(EdgeRef, EdgeRef)> {
    let (then_edge, else_edge) = cfg.branch_edges(header)?;
    match cfg.terminator(&proto.instrs, header) {
        Some(LowInstr::Branch(branch)) if branch.cond.negated => Some((else_edge, then_edge)),
        Some(LowInstr::Branch(_)) => Some((then_edge, else_edge)),
        _ => None,
    }
}

pub(super) fn connector_block_is_safe(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    block: BlockRef,
) -> bool {
    let [edge] = cfg.succs[block.index()].as_slice() else {
        return false;
    };
    let range = cfg.blocks[block.index()].instrs;
    if cfg.edges[edge.index()].to == block {
        return false;
    }
    (range.start.index()..range.end()).all(|index| {
        let Some(instr) = proto.instrs.get(index) else {
            return false;
        };
        if instr.is_control_terminator() && index + 1 != range.end() {
            return false;
        }
        dataflow
            .effect_summaries
            .get(index)
            .is_some_and(|summary| summary.tags.is_empty())
    })
}

pub(super) fn block_defs_escape(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    block: BlockRef,
    allowed_blocks: &BTreeSet<BlockRef>,
) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    (range.start.index()..range.end()).any(|instr| {
        dataflow.instr_defs[instr]
            .iter()
            .copied()
            .any(|def| dataflow.def_has_use_outside(cfg, def, allowed_blocks))
    })
}

pub(super) fn connector_defs_stay_inside(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    arcs: &[RawConditionArc],
    allowed_blocks: &BTreeSet<BlockRef>,
) -> bool {
    arcs.iter()
        .flat_map(|arc| arc.connector_blocks.iter().copied())
        .all(|block| !block_defs_escape(cfg, dataflow, block, allowed_blocks))
}

pub(super) fn reachable_predecessor_count(cfg: &Cfg, block: BlockRef) -> usize {
    cfg.preds[block.index()]
        .iter()
        .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
        .take(2)
        .count()
}
