//! 选择、组合并评分结构化条件候选；依赖分支/循环边界和预备边动作，不负责直接 CFG 弧合成；例如合并相邻纯条件 guard。

use super::*;

pub(super) fn unique_branch_regions(
    regions: &[BranchRegionFact],
) -> Result<BTreeMap<super::super::BlockRef, &BranchRegionFact>, StructureError> {
    let mut by_header = BTreeMap::new();
    for region in regions {
        if by_header.insert(region.header, region).is_some() {
            return Err(StructureError::invalid(format!(
                "branch {} has multiple region facts",
                region.header
            )));
        }
    }
    Ok(by_header)
}

pub(super) fn unique_branch_value_merges(
    candidates: &[BranchValueMergeCandidate],
) -> Result<
    BTreeMap<(super::super::BlockRef, super::super::BlockRef), &BranchValueMergeCandidate>,
    StructureError,
> {
    let mut by_region = BTreeMap::new();
    for candidate in candidates {
        let key = (candidate.header, candidate.merge);
        if by_region.insert(key, candidate).is_some() {
            return Err(StructureError::invalid(format!(
                "branch {} -> {} has multiple value plans",
                candidate.header, candidate.merge
            )));
        }
    }
    Ok(by_region)
}

pub(super) struct ConditionSelectionInput<'a> {
    pub(super) proto: &'a LoweredProto,
    pub(super) cfg: &'a Cfg,
    pub(super) dataflow: &'a DataflowFacts,
    pub(super) loops: &'a [LoopCandidate],
    pub(super) caps: ControlFlowCaps,
    pub(super) branches: &'a [BranchCandidate],
    pub(super) candidates: &'a [ShortCircuitCandidate],
    pub(super) closed_control_dags: &'a [ClosedControlDagEvidence],
    pub(super) residual_transfers: &'a [ResidualTransferEvidence],
}

pub(super) fn selected_conditions(
    input: ConditionSelectionInput<'_>,
) -> Result<
    (
        Vec<ConditionPlanInput>,
        BTreeMap<super::super::BlockRef, ConditionPlanId>,
    ),
    StructureError,
> {
    let ConditionSelectionInput {
        proto,
        cfg,
        dataflow,
        loops,
        caps,
        branches,
        candidates,
        closed_control_dags,
        residual_transfers,
    } = input;
    let edge_actions = preliminary_edge_actions(cfg, dataflow, loops, residual_transfers, caps);
    let mut loops_by_condition_header = vec![Vec::new(); cfg.blocks.len()];
    for (index, loop_) in loops.iter().enumerate() {
        if let Some(header) = required_loop_condition_header(cfg, loop_) {
            loops_by_condition_header[header.index()].push(index);
        }
    }
    let mut condition_arc_workspace = ConditionArcWorkspace::new(cfg.blocks.len());
    let mut condition_safety_workspace = ConditionSafetyWorkspace::new(dataflow);
    let mut selected = BTreeMap::<super::super::BlockRef, (usize, ConditionPlanInput)>::new();
    for (index, candidate) in candidates.iter().enumerate() {
        if !candidate.reducible || !matches!(candidate.exit, ShortCircuitExit::BranchExit { .. }) {
            continue;
        }
        if condition_crosses_foreign_loop_header(candidate, loops, &loops_by_condition_header) {
            continue;
        }
        let Some(candidate) =
            safe_condition_candidate(cfg, dataflow, candidate, &mut condition_safety_workspace)
        else {
            continue;
        };
        let arcs =
            synthesize_direct_condition_arcs(proto, cfg, &candidate, &mut condition_arc_workspace)?
                .unwrap_or_default();
        let input = normalized_condition_input(candidate, arcs);
        if input.arcs.is_empty() || !condition_terminal_actions_are_uniform(&input, &edge_actions) {
            continue;
        }
        let score = score_condition(&input, index);
        let replace = selected
            .get(&input.candidate.header)
            .is_none_or(|(current, old)| score > score_condition(old, *current));
        if replace {
            selected.insert(input.candidate.header, (index, input));
        }
    }
    for (index, evidence) in closed_control_dags.iter().enumerate() {
        if !evidence.candidate.reducible
            || !matches!(evidence.candidate.exit, ShortCircuitExit::BranchExit { .. })
        {
            continue;
        }
        if condition_crosses_foreign_loop_header(
            &evidence.candidate,
            loops,
            &loops_by_condition_header,
        ) {
            continue;
        }
        let Some(candidate) = safe_condition_candidate(
            cfg,
            dataflow,
            &evidence.candidate,
            &mut condition_safety_workspace,
        ) else {
            continue;
        };
        let arcs = if candidate == evidence.candidate {
            evidence.arcs.clone()
        } else {
            synthesize_direct_condition_arcs(proto, cfg, &candidate, &mut condition_arc_workspace)?
                .unwrap_or_default()
        };
        let input = normalized_condition_input(candidate, arcs);
        if input.arcs.is_empty() || !condition_terminal_actions_are_uniform(&input, &edge_actions) {
            continue;
        }
        let score = score_condition(&input, candidates.len() + index);
        let replace = selected
            .get(&input.candidate.header)
            .is_none_or(|(current, old)| score > score_condition(old, *current));
        if replace {
            selected.insert(input.candidate.header, (candidates.len() + index, input));
        }
    }
    for branch in branches {
        if selected.contains_key(&branch.header) {
            continue;
        }
        if let Some(input) = simple_condition_input(proto, cfg, branch.header) {
            selected.insert(
                branch.header,
                (usize::MAX / 2 + branch.header.index(), input),
            );
        }
    }
    for loop_ in loops {
        let Some(header) = required_loop_condition_header(cfg, loop_) else {
            continue;
        };
        if selected.contains_key(&header) {
            continue;
        }
        if let Some(input) = simple_condition_input(proto, cfg, header) {
            selected.insert(
                header,
                (usize::MAX / 2 + cfg.blocks.len() + header.index(), input),
            );
        }
    }
    selected = compose_adjacent_condition_guards(cfg, dataflow, loops, selected, &edge_actions);
    let mut conditions = Vec::with_capacity(selected.len());
    let mut by_header = BTreeMap::new();
    for (header, (_, condition)) in selected {
        let id = ConditionPlanId(conditions.len());
        conditions.push(condition);
        by_header.insert(header, id);
    }
    Ok((conditions, by_header))
}

/// Keep the logical condition candidate and its physical CFG evidence in sync.
///
/// A short-circuit arc may cross a side-effect-free jump block before reaching its
/// semantic target. That connector is part of the condition's owned region even
/// though it is not a decision node, so every condition producer must include it
/// before branch ranges and region ownership are materialized.
fn normalized_condition_input(
    mut candidate: ShortCircuitCandidate,
    arcs: Vec<ConditionArcEvidence>,
) -> ConditionPlanInput {
    candidate.blocks.extend(
        arcs.iter()
            .flat_map(|arc| arc.connector_blocks.iter().copied()),
    );
    ConditionPlanInput { candidate, arcs }
}

pub(super) fn compose_adjacent_condition_guards(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    loops: &[LoopCandidate],
    selected: BTreeMap<super::super::BlockRef, (usize, ConditionPlanInput)>,
    edge_actions: &[PreliminaryEdgeAction],
) -> BTreeMap<super::super::BlockRef, (usize, ConditionPlanInput)> {
    let mut entries = selected
        .into_iter()
        .map(|(header, (score, input))| (header, score, Some(input)))
        .collect::<Vec<_>>();
    let mut by_header = vec![None; cfg.blocks.len()];
    for (index, (header, _, _)) in entries.iter().enumerate() {
        by_header[header.index()] = Some(index);
    }
    let mut absorbed_header = vec![false; cfg.blocks.len()];
    for (header, _, input) in &entries {
        let Some(input) = input else { continue };
        for block in &input.candidate.blocks {
            if block != header {
                absorbed_header[block.index()] = true;
            }
        }
    }
    let mut child_by_parent = vec![None; entries.len()];
    for (index, (header, _, input)) in entries.iter().enumerate() {
        if absorbed_header[header.index()] {
            continue;
        }
        let Some(input) = input else { continue };
        let Some(child) = adjacent_condition_guard(
            cfg,
            dataflow,
            loops,
            input,
            &entries,
            &by_header,
            edge_actions,
        ) else {
            continue;
        };
        child_by_parent[index] = Some(child);
    }
    for parent in 0..entries.len() {
        let Some(child) = child_by_parent[parent] else {
            continue;
        };
        let Some(mut downstream) = entries[child].2.clone() else {
            continue;
        };
        let Some(mut root) = entries[parent].2.take() else {
            continue;
        };
        let _ = compose_condition_guard(&mut root, &mut downstream);
        entries[parent].2 = Some(root);
    }
    entries
        .into_iter()
        .filter_map(|(header, score, input)| input.map(|input| (header, (score, input))))
        .collect()
}

pub(super) fn adjacent_condition_guard(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    loops: &[LoopCandidate],
    root: &ConditionPlanInput,
    entries: &[(super::super::BlockRef, usize, Option<ConditionPlanInput>)],
    by_header: &[Option<usize>],
    edge_actions: &[PreliminaryEdgeAction],
) -> Option<usize> {
    let ShortCircuitExit::BranchExit { truthy, falsy } = &root.candidate.exit else {
        return None;
    };
    let mut selected = None;
    for (continuation, other, other_truthy) in [(*truthy, *falsy, false), (*falsy, *truthy, true)] {
        let Some(child) = by_header.get(continuation.index()).copied().flatten() else {
            continue;
        };
        let Some(downstream) = entries.get(child).and_then(|entry| entry.2.as_ref()) else {
            continue;
        };
        let ShortCircuitExit::BranchExit {
            truthy: downstream_truthy,
            falsy: downstream_falsy,
        } = &downstream.candidate.exit
        else {
            continue;
        };
        let downstream_other_truthy = other == *downstream_truthy;
        let actions_match = condition_exit_action(root, other_truthy, edge_actions)
            .zip(condition_exit_action(
                downstream,
                downstream_other_truthy,
                edge_actions,
            ))
            .is_some_and(|(root, downstream)| {
                root.has_continue_evidence == downstream.has_continue_evidence
                    && root.iteration == downstream.iteration
                    && root.phi_inputs == downstream.phi_inputs
            });
        if downstream.candidate.nodes.len() != 1
            || !downstream
                .candidate
                .blocks
                .is_disjoint(&root.candidate.blocks)
            || (!downstream_other_truthy && other != *downstream_falsy)
            || !repeated_loop_break_guard(cfg, dataflow, loops, downstream.candidate.header, other)
            || !actions_match
        {
            continue;
        }
        if selected.replace(child).is_some() {
            return None;
        }
    }
    selected
}

pub(super) fn repeated_loop_break_guard(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    loops: &[LoopCandidate],
    condition: super::super::BlockRef,
    repeated: super::super::BlockRef,
) -> bool {
    let condition_uses = block_condition_uses(cfg, dataflow, condition);
    if condition_uses.is_none() || condition_uses != block_condition_uses(cfg, dataflow, repeated) {
        return false;
    }
    loops.iter().any(|loop_| {
        loop_.body_scope_blocks.contains(&condition)
            && loop_.body_scope_blocks.contains(&repeated)
            && cfg.succs[repeated.index()].iter().any(|edge| {
                let target = cfg.edges[edge.index()].to;
                loop_.exits.contains(&target)
                    || cfg
                        .unique_reachable_successor(target)
                        .is_some_and(|target| loop_.exits.contains(&target))
            })
    })
}

pub(super) fn block_condition_uses<'a>(
    cfg: &Cfg,
    dataflow: &'a DataflowFacts,
    block: super::super::BlockRef,
) -> Option<&'a super::super::SsaRegMap> {
    cfg.branch_edges(block)?;
    let range = cfg.blocks.get(block.index())?.instrs;
    let offset = range.len.checked_sub(1)?;
    dataflow
        .use_values
        .get(range.start.index() + offset)
        .map(|uses| &uses.fixed)
}

pub(super) fn compose_condition_guard(
    root: &mut ConditionPlanInput,
    downstream: &mut ConditionPlanInput,
) -> bool {
    let (
        ShortCircuitExit::BranchExit {
            truthy: root_truthy,
            falsy: root_falsy,
        },
        ShortCircuitExit::BranchExit {
            truthy: downstream_truthy,
            falsy: downstream_falsy,
        },
    ) = (&root.candidate.exit, &downstream.candidate.exit)
    else {
        return false;
    };
    let (continued_target, other_target, other_block) =
        if *root_truthy == downstream.candidate.header {
            (
                ShortCircuitTarget::TruthyExit,
                ShortCircuitTarget::FalsyExit,
                *root_falsy,
            )
        } else if *root_falsy == downstream.candidate.header {
            (
                ShortCircuitTarget::FalsyExit,
                ShortCircuitTarget::TruthyExit,
                *root_truthy,
            )
        } else {
            return false;
        };
    let final_other = if other_block == *downstream_truthy {
        ShortCircuitTarget::TruthyExit
    } else if other_block == *downstream_falsy {
        ShortCircuitTarget::FalsyExit
    } else {
        return false;
    };
    let offset = root.candidate.nodes.len();
    let downstream_entry = ShortCircuitTarget::Node(ShortCircuitNodeRef(
        offset + downstream.candidate.entry.index(),
    ));
    let rewrite_root_target = |target: &mut ShortCircuitTarget| {
        if *target == continued_target {
            *target = downstream_entry.clone();
        } else if *target == other_target {
            *target = final_other.clone();
        }
    };
    for node in &mut root.candidate.nodes {
        rewrite_root_target(&mut node.truthy);
        rewrite_root_target(&mut node.falsy);
    }
    for arc in &mut root.arcs {
        rewrite_root_target(&mut arc.target);
    }
    for node in &mut downstream.candidate.nodes {
        node.id = ShortCircuitNodeRef(offset + node.id.index());
        offset_condition_target(&mut node.truthy, offset);
        offset_condition_target(&mut node.falsy, offset);
    }
    for arc in &mut downstream.arcs {
        arc.source = ShortCircuitNodeRef(offset + arc.source.index());
        offset_condition_target(&mut arc.target, offset);
    }
    root.candidate
        .blocks
        .append(&mut downstream.candidate.blocks);
    root.candidate.nodes.append(&mut downstream.candidate.nodes);
    root.arcs.append(&mut downstream.arcs);
    root.candidate.exit = downstream.candidate.exit.clone();
    true
}

pub(super) fn condition_exit_action<'a>(
    condition: &ConditionPlanInput,
    truthy: bool,
    edge_actions: &'a [PreliminaryEdgeAction],
) -> Option<&'a PreliminaryEdgeAction> {
    condition
        .arcs
        .iter()
        .find(|arc| {
            matches!(
                (&arc.target, truthy),
                (ShortCircuitTarget::TruthyExit, true) | (ShortCircuitTarget::FalsyExit, false)
            )
        })
        .and_then(|arc| arc.edges.last())
        .and_then(|edge| edge_actions.get(edge.index()))
}

pub(super) fn offset_condition_target(target: &mut ShortCircuitTarget, offset: usize) {
    if let ShortCircuitTarget::Node(node) = target {
        *node = ShortCircuitNodeRef(offset + node.index());
    }
}

pub(super) fn condition_crosses_foreign_loop_header(
    candidate: &ShortCircuitCandidate,
    loops: &[LoopCandidate],
    loops_by_condition_header: &[Vec<usize>],
) -> bool {
    let owner_headers = loops_by_condition_header
        .get(candidate.header.index())
        .into_iter()
        .flatten()
        .filter_map(|index| loops.get(*index))
        .filter(|loop_| {
            candidate.blocks.iter().all(|block| {
                loop_.blocks.contains(block)
                    || loop_.body_scope_blocks.contains(block)
                    || loop_.control_blocks.contains(block)
            })
        })
        .map(|loop_| loop_.header)
        .collect::<BTreeSet<_>>();
    candidate
        .blocks
        .iter()
        .filter(|block| **block != candidate.header)
        .any(|block| {
            loops_by_condition_header
                .get(block.index())
                .into_iter()
                .flatten()
                .filter_map(|index| loops.get(*index))
                .any(|loop_| !owner_headers.contains(&loop_.header))
        })
}

pub(super) fn score_condition(
    condition: &ConditionPlanInput,
    index: usize,
) -> (usize, usize, Reverse<usize>) {
    (
        condition.candidate.nodes.len(),
        condition.candidate.blocks.len(),
        Reverse(index),
    )
}

pub(super) fn condition_terminal_actions_are_uniform(
    condition: &ConditionPlanInput,
    edge_actions: &[PreliminaryEdgeAction],
) -> bool {
    let mut truthy = None::<super::super::EdgeRef>;
    let mut falsy = None::<super::super::EdgeRef>;
    for arc in &condition.arcs {
        let Some(edge) = arc.edges.last().copied() else {
            return false;
        };
        let slot = match arc.target {
            ShortCircuitTarget::TruthyExit => &mut truthy,
            ShortCircuitTarget::FalsyExit => &mut falsy,
            ShortCircuitTarget::Node(_) => continue,
            ShortCircuitTarget::Value(_) => return false,
        };
        let Some(action) = edge_actions.get(edge.index()) else {
            return false;
        };
        match slot {
            Some(expected) => {
                let Some(expected) = edge_actions.get(expected.index()) else {
                    return false;
                };
                if expected != action || action.goto.is_some() || action.has_continue_evidence {
                    return false;
                }
            }
            None => *slot = Some(edge),
        }
    }
    truthy.is_some() && falsy.is_some()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct PreliminaryEdgeAction {
    goto: Option<super::super::GotoReason>,
    has_continue_evidence: bool,
    iteration: Option<PreliminaryIteration>,
    phi_inputs: Vec<(super::super::PhiId, super::super::SsaValue)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum PreliminaryIteration {
    LoopBack(super::super::BlockRef),
    Continue(super::super::BlockRef),
    Conflicting,
}

pub(super) fn preliminary_edge_actions(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    loops: &[LoopCandidate],
    residual_transfers: &[ResidualTransferEvidence],
    caps: ControlFlowCaps,
) -> Vec<PreliminaryEdgeAction> {
    // terminal 一致性会被多个 condition evidence 查询；先按 EdgeRef 稠密登记，避免
    // 每个叶子都重新扫描全部 loop 与 phi incoming。
    let mut actions = cfg
        .edges
        .iter()
        .map(|_| PreliminaryEdgeAction {
            goto: None,
            has_continue_evidence: false,
            iteration: None,
            phi_inputs: Vec::new(),
        })
        .collect::<Vec<_>>();
    for residual in residual_transfers {
        if let Some(action) = actions.get_mut(residual.edge.index()) {
            action.goto = Some(residual.reason);
        }
    }
    for loop_ in loops {
        for edge in &loop_.backedges {
            if let Some(action) = actions.get_mut(edge.index()) {
                record_preliminary_iteration(action, PreliminaryIteration::LoopBack(loop_.header));
            }
        }
    }
    if caps.continue_stmt {
        for loop_ in loops {
            for edge in &loop_.continue_edges {
                if let Some(action) = actions.get_mut(edge.index()) {
                    action.has_continue_evidence = true;
                    record_preliminary_iteration(
                        action,
                        PreliminaryIteration::Continue(loop_.header),
                    );
                }
            }
            let Some(target) = loop_.continue_target else {
                continue;
            };
            for edge in &cfg.preds[target.index()] {
                let cfg_edge = cfg.edges[edge.index()];
                let source_in_body = loop_.blocks.contains(&cfg_edge.from)
                    || loop_.body_scope_blocks.contains(&cfg_edge.from);
                let conditional_escape = cfg.succs[cfg_edge.from.index()].len() > 1
                    && cfg.succs[cfg_edge.from.index()].iter().any(|sibling| {
                        *sibling != *edge && {
                            let target = cfg.edges[sibling.index()].to;
                            loop_.blocks.contains(&target)
                                || loop_.body_scope_blocks.contains(&target)
                        }
                    });
                if source_in_body
                    && conditional_escape
                    && loop_.backedges.binary_search(edge).is_err()
                    && let Some(action) = actions.get_mut(edge.index())
                {
                    action.has_continue_evidence = true;
                    record_preliminary_iteration(
                        action,
                        PreliminaryIteration::Continue(loop_.header),
                    );
                }
            }
        }
    }
    for phi in &dataflow.phi_candidates {
        for incoming in &phi.incoming {
            if let Some(edge) = incoming.edge
                && let Some(action) = actions.get_mut(edge.index())
            {
                action.phi_inputs.push((phi.id, incoming.value));
            }
        }
    }
    actions
}

pub(super) fn record_preliminary_iteration(
    action: &mut PreliminaryEdgeAction,
    iteration: PreliminaryIteration,
) {
    action.iteration = match action.iteration {
        None => Some(iteration),
        Some(current) if current == iteration => Some(current),
        Some(_) => Some(PreliminaryIteration::Conflicting),
    };
}

pub(super) fn simple_condition_input(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: super::super::BlockRef,
) -> Option<ConditionPlanInput> {
    let (truthy_edge, falsy_edge) = semantic_branch_edges(proto, cfg, header)?;
    let truthy = cfg.edges.get(truthy_edge.index())?.to;
    let falsy = cfg.edges.get(falsy_edge.index())?.to;
    let candidate = ShortCircuitCandidate {
        header,
        blocks: BTreeSet::from([header]),
        entry: ShortCircuitNodeRef(0),
        nodes: vec![super::super::ShortCircuitNode {
            id: ShortCircuitNodeRef(0),
            header,
            truthy: ShortCircuitTarget::TruthyExit,
            falsy: ShortCircuitTarget::FalsyExit,
        }],
        exit: ShortCircuitExit::BranchExit { truthy, falsy },
        result_reg: None,
        result_phi_id: None,
        entry_value: None,
        value_incomings: Vec::new(),
        reducible: true,
    };
    Some(normalized_condition_input(
        candidate,
        vec![
            ConditionArcEvidence {
                source: ShortCircuitNodeRef(0),
                truthy: true,
                edges: vec![truthy_edge],
                connector_blocks: Vec::new(),
                target: ShortCircuitTarget::TruthyExit,
            },
            ConditionArcEvidence {
                source: ShortCircuitNodeRef(0),
                truthy: false,
                edges: vec![falsy_edge],
                connector_blocks: Vec::new(),
                target: ShortCircuitTarget::FalsyExit,
            },
        ],
    ))
}

pub(super) fn required_loop_condition_header(
    cfg: &Cfg,
    loop_: &LoopCandidate,
) -> Option<super::super::BlockRef> {
    use super::super::LoopKindHint;

    match loop_.kind_hint {
        LoopKindHint::NumericForLike
        | LoopKindHint::GenericForLike
        | LoopKindHint::WhileTrueLike => None,
        LoopKindHint::RepeatLike => loop_
            .condition_header
            .or(loop_.continue_target)
            .filter(|block| cfg.branch_edges(*block).is_some()),
        LoopKindHint::WhileLike => loop_
            .condition_header
            .or(Some(loop_.header))
            .filter(|block| cfg.branch_edges(*block).is_some()),
        LoopKindHint::Unknown => loop_
            .condition_header
            .or(Some(loop_.header))
            .filter(|block| cfg.branch_edges(*block).is_some()),
    }
}
