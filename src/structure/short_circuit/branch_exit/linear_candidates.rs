//! 枚举 guard、线性与 if/else branch-exit 条件候选；依赖 branch 表和闭合 interior 过滤，不负责临时 DAG 节点构造；例如选择最长的无副作用线性条件链。

use super::*;

pub(in crate::structure::short_circuit) fn analyze_guard_branch_exit_dag_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    branch_candidates: &[BranchCandidate],
    closed_linear_interiors: &BTreeSet<BlockRef>,
    value_decision_headers: &BTreeSet<BlockRef>,
) -> Vec<ShortCircuitCandidate> {
    let mut best_by_header = BTreeMap::<BlockRef, ShortCircuitCandidate>::new();
    let mut node_refs = DenseNodeRefs::new(cfg.blocks.len());
    let context = GuardBranchExitDagContext {
        proto,
        cfg,
        graph_facts,
        branch_by_header,
        value_decision_headers,
    };

    for root in branch_candidates {
        if closed_linear_interiors.contains(&root.header) {
            continue;
        }
        let candidate =
            GuardBranchExitDagBuilder::new(&context, root.header, true, &mut node_refs).build();
        let candidate = match candidate {
            Some(candidate) => Some(candidate),
            None => {
                GuardBranchExitDagBuilder::new(&context, root.header, false, &mut node_refs).build()
            }
        };
        let Some(candidate) = candidate else {
            continue;
        };

        match best_by_header.get(&root.header) {
            Some(existing) if !prefer_short_circuit_candidate(proto, cfg, &candidate, existing) => {
            }
            _ => {
                best_by_header.insert(root.header, candidate);
            }
        }
    }

    best_by_header.into_values().collect()
}

pub(in crate::structure::short_circuit) fn analyze_linear_branch_exit_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    branch_candidates: &[BranchCandidate],
) -> Vec<ShortCircuitCandidate> {
    let chains =
        LinearChainIndex::branch_then(cfg.blocks.len(), branch_by_header, branch_candidates);
    analyze_linear_branch_exit_candidates_with(
        proto,
        cfg,
        branch_by_header,
        branch_candidates,
        &chains,
    )
}

pub(in crate::structure::short_circuit) fn analyze_cfg_linear_branch_exit_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    branch_candidates: &[BranchCandidate],
) -> Vec<ShortCircuitCandidate> {
    let chains = LinearChainIndex::cfg(proto, cfg, branch_by_header, branch_candidates);
    analyze_linear_branch_exit_candidates_with(
        proto,
        cfg,
        branch_by_header,
        branch_candidates,
        &chains,
    )
}

pub(super) fn analyze_linear_branch_exit_candidates_with(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    branch_candidates: &[BranchCandidate],
    chains: &LinearChainIndex,
) -> Vec<ShortCircuitCandidate> {
    let mut candidates = Vec::new();
    let mut closed_linear_interiors = BTreeSet::new();
    let mut visited = DenseMarks::new(cfg.blocks.len());
    for candidate in branch_candidates {
        if candidate.kind != BranchKind::IfThen
            || closed_linear_interiors.contains(&candidate.header)
        {
            continue;
        }

        let visited_epoch = visited.begin();
        let mut headers = Vec::new();
        let mut current = candidate.header;

        loop {
            if !visited.insert(current, visited_epoch) {
                break;
            }
            headers.push(current);

            let Some(next) = chains.next(current, &visited, visited_epoch) else {
                break;
            };
            current = next;
        }

        // If the full chain fails at `infer_linear_branch_exit`, the last block
        // might be a body block mistakenly included because it is also a branch
        // candidate. Detect this by checking whether every preceding header has
        // the last header as one of its truthy/falsy targets (i.e. it is the
        // common short-circuit exit). Only trim in that case to avoid producing
        // spurious candidates elsewhere.
        let mut exit = infer_linear_branch_exit(proto, cfg, &headers);
        if exit.is_none() && headers.len() >= 3 {
            let Some(last) = headers.last().copied() else {
                continue;
            };
            let is_common_exit = headers[..headers.len() - 1].iter().all(|h| {
                truthy_falsy_targets(proto, cfg, *h).is_some_and(|(t, f)| t == last || f == last)
            });
            if is_common_exit {
                headers.pop();
                exit = infer_linear_branch_exit(proto, cfg, &headers);
            }
        }
        // `a or b` 沿 falsy 边进入下一判断；其 truthy body 若也以 branch 开头，
        // 线性跟随会越过条件链。AND 链可由嵌套 if 自然表达，不在证据不足时扩候选。
        if exit.is_none()
            && headers
                .first()
                .zip(headers.get(1))
                .is_some_and(|(header, next)| {
                    truthy_falsy_targets(proto, cfg, *header)
                        .is_some_and(|(_, falsy)| falsy == *next)
                })
            && let Some((prefix_len, prefix_exit)) =
                infer_longest_linear_branch_exit(proto, cfg, &headers)
        {
            headers.truncate(prefix_len);
            exit = Some(prefix_exit);
        }
        let Some(exit) = exit else {
            continue;
        };
        let Some(nodes) = build_linear_branch_exit_nodes(proto, cfg, &headers, &exit) else {
            continue;
        };

        let blocks = headers.iter().copied().collect::<BTreeSet<_>>();
        let reducible = is_reducible_candidate(cfg, candidate.header, &blocks);
        let candidate = ShortCircuitCandidate {
            header: candidate.header,
            blocks,
            entry: ShortCircuitNodeRef(0),
            nodes,
            exit,
            result_reg: None,
            result_phi_id: None,
            entry_value: None,
            value_incomings: Vec::new(),
            reducible,
        };
        if candidate.reducible
            && let Some(interiors) =
                closed_single_entry_linear_interiors(cfg, branch_by_header, &candidate)
        {
            closed_linear_interiors.extend(interiors);
        }
        candidates.push(candidate);
    }

    candidates.sort_by_key(|candidate| candidate.header);
    candidates.dedup_by(|left, right| {
        left.header == right.header
            && left.exit == right.exit
            && left.blocks == right.blocks
            && left.nodes == right.nodes
    });
    candidates
}

pub(in crate::structure::short_circuit) fn closed_linear_interior_headers(
    cfg: &Cfg,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    candidates: &[ShortCircuitCandidate],
) -> BTreeSet<BlockRef> {
    candidates
        .iter()
        .filter(|candidate| candidate.reducible)
        .filter_map(|candidate| {
            closed_single_entry_linear_interiors(cfg, branch_by_header, candidate)
        })
        .flatten()
        .collect()
}

pub(super) fn closed_single_entry_linear_interiors(
    cfg: &Cfg,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    candidate: &ShortCircuitCandidate,
) -> Option<Vec<BlockRef>> {
    let ShortCircuitExit::BranchExit { truthy, falsy } = candidate.exit else {
        return None;
    };
    if branch_by_header.contains_key(&truthy) || branch_by_header.contains_key(&falsy) {
        return None;
    }

    let interiors = candidate
        .blocks
        .iter()
        .copied()
        .filter(|block| *block != candidate.header)
        .collect::<Vec<_>>();
    interiors
        .iter()
        .all(|block| cfg.reachable_predecessors(*block).len() == 1)
        .then_some(interiors)
}

pub(in crate::structure::short_circuit) fn analyze_if_else_branch_exit_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    branch_candidates: &[BranchCandidate],
) -> Vec<ShortCircuitCandidate> {
    let mut candidates = Vec::new();
    let mut visited = DenseMarks::new(cfg.blocks.len());
    let chains = LinearChainIndex::cfg(proto, cfg, branch_by_header, branch_candidates);

    for candidate in branch_candidates {
        if candidate.kind != BranchKind::IfElse {
            continue;
        }

        let headers = collect_if_else_branch_exit_chain(candidate, &chains, &mut visited);
        if headers.len() < 2 {
            continue;
        }

        let Some((prefix_len, exit)) = infer_longest_if_else_branch_exit(proto, cfg, &headers)
        else {
            continue;
        };
        let prefix = &headers[..prefix_len];
        let Some(nodes) = build_linear_branch_exit_nodes(proto, cfg, prefix, &exit) else {
            continue;
        };
        let blocks = prefix.iter().copied().collect::<BTreeSet<_>>();
        let reducible = is_reducible_candidate(cfg, candidate.header, &blocks);
        candidates.push(ShortCircuitCandidate {
            header: candidate.header,
            blocks,
            entry: ShortCircuitNodeRef(0),
            nodes,
            exit,
            result_reg: None,
            result_phi_id: None,
            entry_value: None,
            value_incomings: Vec::new(),
            reducible,
        });
    }

    candidates.sort_by_key(|candidate| candidate.header);
    candidates.dedup_by(|left, right| {
        left.header == right.header
            && left.exit == right.exit
            && left.blocks == right.blocks
            && left.nodes == right.nodes
    });
    candidates
}
