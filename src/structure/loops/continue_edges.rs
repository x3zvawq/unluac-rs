//! 识别并分配结构化 continue 边所有权；依赖 loop/branch 候选与图事实，不负责循环形态推导；例如识别经共享 backedge pad 的提前下一轮。

use super::*;

pub(in crate::structure) fn assign_continue_edge_ownership(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    branches: &[BranchCandidate],
    candidates: &mut [LoopCandidate],
) {
    let mut owners_by_entry = vec![Vec::new(); cfg.blocks.len()];
    let mut owners_by_block = vec![Vec::new(); cfg.blocks.len()];
    for (index, candidate) in candidates.iter().enumerate() {
        for block in &candidate.blocks {
            owners_by_block[block.index()].push(index);
        }
        if numeric_continue_target_carries_body_tail(proto, cfg, candidate) {
            continue;
        }
        let Some(target) = candidate.continue_target else {
            continue;
        };
        owners_by_entry[target.index()].push(index);
        for source in candidate
            .backedges
            .iter()
            .map(|edge| cfg.edges[edge.index()].from)
            .filter(|source| *source != target && jump_only_to(proto, cfg, *source, target))
        {
            owners_by_entry[source.index()].push(index);
        }
    }
    for owners in &mut owners_by_entry {
        owners.sort_unstable();
        owners.dedup();
    }

    for branch in branches {
        let Some((then_edge, else_edge)) = cfg.branch_edges(branch.header) else {
            continue;
        };
        if cfg.edges[then_edge.index()].to == cfg.edges[else_edge.index()].to {
            continue;
        }
        for edge_ref in [then_edge, else_edge] {
            let edge = cfg.edges[edge_ref.index()];
            let owners = &owners_by_entry[edge.to.index()];
            if owners.is_empty() {
                continue;
            }
            let eligible = || {
                owners.iter().copied().filter(|index| {
                    let candidate = &candidates[*index];
                    // repeat 的 backedge pad 还承载条件求值，不能仅凭 jump 形状认作 continue。
                    candidate.kind_hint != LoopKindHint::RepeatLike
                        && candidate.continue_target != Some(branch.header)
                        && candidate.blocks.contains(&branch.header)
                        && (candidate.backedges.binary_search(&edge_ref).is_err()
                            || branch.kind == BranchKind::Guard
                                && branch.then_entry == edge.to
                                && branch.merge != Some(edge.to))
                })
            };
            let Some(owner) = eligible().min_by_key(|index| {
                let candidate = &candidates[*index];
                (candidate.body_scope_blocks.len(), candidate.blocks.len())
            }) else {
                continue;
            };
            let owner_scope = (
                candidates[owner].body_scope_blocks.len(),
                candidates[owner].blocks.len(),
            );
            if eligible().filter(|index| *index != owner).any(|index| {
                let candidate = &candidates[index];
                (candidate.body_scope_blocks.len(), candidate.blocks.len()) == owner_scope
            }) {
                continue;
            }
            candidates[owner].continue_edges.insert(edge_ref);
        }

        if branch.else_entry.is_some() {
            continue;
        }
        let guard_merge = (branch.kind == BranchKind::Guard)
            .then_some(branch.merge)
            .flatten()
            .filter(|merge| {
                *merge != branch.then_entry
                    && !graph_facts.dominance_frontier[branch.then_entry.index()].contains(merge)
            })
            .map(|entry| (entry, None, true));
        for (entry, merge, from_guard_merge) in
            std::iter::once((branch.then_entry, branch.merge, false)).chain(guard_merge)
        {
            for index in owners_by_block[branch.header.index()].iter().copied() {
                let candidate = &mut candidates[index];
                if candidate.kind_hint == LoopKindHint::RepeatLike
                    || numeric_continue_target_carries_body_tail(proto, cfg, candidate)
                    || !candidate.blocks.contains(&entry)
                    || from_guard_merge
                        && (candidate.backedges.len() < 2
                            || !candidate.blocks.contains(&branch.then_entry))
                {
                    continue;
                }
                let Some(target) = candidate.continue_target else {
                    continue;
                };
                let Some(edge_ref) =
                    linear_arm_continue_edge(cfg, &candidate.blocks, entry, merge, target)
                else {
                    continue;
                };
                candidate.continue_edges.insert(edge_ref);
            }
        }
    }
}

pub(super) fn numeric_continue_target_carries_body_tail(
    proto: &LoweredProto,
    cfg: &Cfg,
    candidate: &LoopCandidate,
) -> bool {
    candidate.kind_hint == LoopKindHint::NumericForLike
        && candidate
            .continue_target
            .is_some_and(|target| block_has_non_control_prefix(proto, cfg, target))
}

pub(super) fn linear_arm_continue_edge(
    cfg: &Cfg,
    loop_blocks: &BTreeSet<BlockRef>,
    start: BlockRef,
    merge: Option<BlockRef>,
    target: BlockRef,
) -> Option<EdgeRef> {
    // 单臂 branch 的 continuation 本身就是 VM latch 时，then arm 自然落回 merge；
    // 这条边没有跳过任何源码 tail，不能因为目标恰好等于 continue target 就升级为
    // continue（Lua 5.1 会因此被迫生成非法 goto）。真正的 continue 会在到达 branch
    // continuation 之前先跳到 target。
    if merge == Some(target) {
        return None;
    }
    let mut current = start;
    let mut visited = BTreeSet::new();
    while current != target && Some(current) != merge && visited.insert(current) {
        if !loop_blocks.contains(&current) {
            return None;
        }
        let [edge_ref] = cfg.succs[current.index()].as_slice() else {
            return None;
        };
        let edge = cfg.edges[edge_ref.index()];
        if edge.to == target {
            return Some(*edge_ref);
        }
        current = edge.to;
    }
    None
}

pub(super) fn jump_only_to(
    proto: &LoweredProto,
    cfg: &Cfg,
    block: BlockRef,
    target: BlockRef,
) -> bool {
    cfg.blocks[block.index()].instrs.len == 1
        && matches!(
            cfg.terminator(&proto.instrs, block),
            Some(LowInstr::Jump(jump))
                if cfg.instr_to_block[jump.target.index()] == target
        )
}
