//! 分类 postdom/reachable/terminal/loop-bounded 的 one-arm 分支；依赖 BranchIndex 与 loop 出口，不负责普通 if/else；例如识别 for 退出边界内的条件 guard。

use super::*;

pub(super) fn one_arm_candidate(
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
    then_reaches_else: bool,
    else_reaches_then: bool,
) -> Option<BranchCandidate> {
    match (then_reaches_else, else_reaches_then) {
        (true, false) => Some(BranchCandidate {
            header,
            then_entry,
            else_entry: None,
            merge: Some(else_entry),
            kind: BranchKind::IfThen,
            invert_hint: false,
        }),
        (false, true) => Some(BranchCandidate {
            header,
            then_entry: else_entry,
            else_entry: None,
            merge: Some(then_entry),
            kind: BranchKind::IfThen,
            invert_hint: true,
        }),
        _ => None,
    }
}

pub(super) fn classify_postdom_one_arm_branch(
    graph_facts: &GraphFacts,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let then_reaches_else = graph_facts.post_dominates(else_entry, then_entry);
    let else_reaches_then = graph_facts.post_dominates(then_entry, else_entry);

    one_arm_candidate(
        header,
        then_entry,
        else_entry,
        then_reaches_else,
        else_reaches_then,
    )
}

pub(super) fn classify_reachable_one_arm_branch(
    branch_index: &BranchIndex<'_>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    // 唯一非 exit dominance-frontier 已经证明该臂真实汇入 continuation；再做一遍
    // 任意 CFG reachability 只会为每个 terminal branch 重扫全图。
    let then_reaches_else = branch_index.has_single_local_join(then_entry, else_entry);
    let else_reaches_then = branch_index.has_single_local_join(else_entry, then_entry);
    one_arm_candidate(
        header,
        then_entry,
        else_entry,
        then_reaches_else,
        else_reaches_then,
    )
}

pub(super) fn refine_terminal_one_arm_branches(
    cfg: &Cfg,
    branch_index: &BranchIndex<'_>,
    irreducible_blocks: &[bool],
    candidates: &mut [BranchCandidate],
) {
    for candidate in candidates {
        if candidate.kind != BranchKind::IfElse
            || candidate.merge.is_some()
            || irreducible_blocks[candidate.header.index()]
        {
            continue;
        }
        let Some((truthy, falsy)) = cfg.branch_edges(candidate.header) else {
            continue;
        };
        let then_entry = cfg.edges[truthy.index()].to;
        let else_entry = cfg.edges[falsy.index()].to;
        if let Some(refined) = classify_reachable_one_arm_branch(
            branch_index,
            candidate.header,
            then_entry,
            else_entry,
        ) {
            *candidate = refined;
        }
    }
}

pub(super) fn classify_infinite_loop_bounded_branch(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    branch_index: &BranchIndex<'_>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let loop_candidate = branch_index
        .endpoint_loops(header)
        .filter(|candidate| {
            candidate.exits.is_empty()
                && candidate.blocks.contains(&header)
                && candidate.blocks.contains(&then_entry)
                && candidate.blocks.contains(&else_entry)
        })
        .min_by_key(|candidate| candidate.blocks.len())?;

    let reaches_local_tail = |from, to| {
        graph_facts.post_dominates(to, from)
            || branch_index.has_single_local_join(from, to)
                && !branch_index.joins_at(from, loop_candidate.header)
    };
    let then_reaches_else = reaches_local_tail(then_entry, else_entry);
    let else_reaches_then = reaches_local_tail(else_entry, then_entry);
    let local_merge = find_soft_merge(cfg, graph_facts, header, then_entry, else_entry)
        .filter(|merge| *merge != header && *merge != loop_candidate.header)
        .filter(|merge| loop_candidate.blocks.contains(merge));

    match (then_reaches_else, else_reaches_then) {
        (true, false) => Some(BranchCandidate {
            header,
            then_entry,
            else_entry: None,
            merge: Some(else_entry),
            kind: BranchKind::IfThen,
            invert_hint: false,
        }),
        (false, true) => Some(BranchCandidate {
            header,
            then_entry: else_entry,
            else_entry: None,
            merge: Some(then_entry),
            kind: BranchKind::IfThen,
            invert_hint: true,
        }),
        (false, false) if local_merge.is_some() => Some(BranchCandidate {
            header,
            then_entry,
            else_entry: Some(else_entry),
            merge: local_merge,
            kind: BranchKind::IfElse,
            invert_hint: false,
        }),
        (false, false)
            if branch_index.joins_at(then_entry, loop_candidate.header)
                && branch_index.joins_at(else_entry, loop_candidate.header) =>
        {
            // 无出口循环没有严格后支配点，但两臂都在本轮结束后回到同一 header，
            // 该 header 就是源码层 if/else 的循环内合流边界。
            Some(BranchCandidate {
                header,
                then_entry,
                else_entry: Some(else_entry),
                merge: Some(loop_candidate.header),
                kind: BranchKind::IfElse,
                invert_hint: false,
            })
        }
        _ => None,
    }
}

pub(super) fn classify_loop_exit_bounded_one_arm_branch(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    branch_index: &BranchIndex<'_>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let strict_merge = graph_facts.nearest_common_postdom(then_entry, else_entry)?;
    // 局部 break 会把严格后支配点推到外层 loop exit；但若一臂进入单跳回边 pad，
    // 它表达的是下一轮 continue，不能把 loop-header frontier 当成普通 continuation。
    let enters_continue_pad = branch_index.endpoint_loops(header).any(|candidate| {
        candidate.blocks.contains(&header)
            && [then_entry, else_entry].into_iter().any(|entry| {
                transparent_jump_target(cfg, entry).is_some()
                    && candidate
                        .backedges
                        .iter()
                        .any(|edge| cfg.edges[edge.index()].from == entry)
            })
    });
    let owner = branch_index.endpoint_loops(header).find(|candidate| {
        candidate.blocks.contains(&header)
            && [then_entry, else_entry].into_iter().all(|entry| {
                candidate.body_scope_blocks.contains(&entry)
                    || candidate.blocks.contains(&entry)
                    || candidate.exits.contains(&entry)
            })
            && (loop_exits_at(cfg, candidate, strict_merge) || strict_merge == cfg.exit_block)
    })?;
    let then_continues =
        then_entry == owner.header || branch_index.joins_at(then_entry, owner.header);
    let else_continues =
        else_entry == owner.header || branch_index.joins_at(else_entry, owner.header);
    match (then_continues, else_continues) {
        (true, false) => Some(BranchCandidate {
            header,
            then_entry: else_entry,
            else_entry: None,
            merge: Some(then_entry),
            kind: BranchKind::Guard,
            invert_hint: true,
        }),
        (false, true) => Some(BranchCandidate {
            header,
            then_entry,
            else_entry: None,
            merge: Some(else_entry),
            kind: BranchKind::Guard,
            invert_hint: false,
        }),
        _ if enters_continue_pad => None,
        _ => classify_loop_bounded_one_arm_branch(branch_index, header, then_entry, else_entry),
    }
}

pub(super) fn classify_for_loop_exit_branch(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    branch_index: &BranchIndex<'_>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let strict_merge = graph_facts.nearest_common_postdom(then_entry, else_entry)?;
    let owner = find_for_loop_exit_owner(
        cfg,
        branch_index.endpoint_loops(header),
        header,
        then_entry,
        else_entry,
        strict_merge,
    )?;

    let body_entry = for_loop_body_entry(cfg, owner)?;
    match (
        cfg.unique_reachable_successor(then_entry) == Some(strict_merge),
        cfg.unique_reachable_successor(else_entry) == Some(strict_merge),
    ) {
        (true, false) => Some(BranchCandidate {
            header,
            then_entry,
            else_entry: None,
            merge: Some(else_entry),
            kind: BranchKind::Guard,
            invert_hint: false,
        }),
        (false, true) => Some(BranchCandidate {
            header,
            then_entry: else_entry,
            else_entry: None,
            merge: Some(then_entry),
            kind: BranchKind::Guard,
            invert_hint: true,
        }),
        _ if body_entry == header
            && owner.blocks.contains(&then_entry)
            && owner.blocks.contains(&else_entry) =>
        {
            let merge = find_soft_merge(cfg, graph_facts, header, then_entry, else_entry)?;
            owner
                .body_scope_blocks
                .contains(&merge)
                .then_some(BranchCandidate {
                    header,
                    then_entry,
                    else_entry: Some(else_entry),
                    merge: Some(merge),
                    kind: BranchKind::IfElse,
                    invert_hint: false,
                })
        }
        _ => None,
    }
}

pub(in crate::structure) fn for_loop_exit_owner<'a>(
    cfg: &Cfg,
    loop_candidates: &'a [LoopCandidate],
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
    boundary: BlockRef,
) -> Option<&'a LoopCandidate> {
    find_for_loop_exit_owner(
        cfg,
        loop_candidates.iter(),
        header,
        then_entry,
        else_entry,
        boundary,
    )
}

pub(super) fn find_for_loop_exit_owner<'a>(
    cfg: &Cfg,
    loop_candidates: impl Iterator<Item = &'a LoopCandidate>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
    boundary: BlockRef,
) -> Option<&'a LoopCandidate> {
    loop_candidates
        .filter(|candidate| {
            matches!(
                candidate.kind_hint,
                LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
            ) && candidate.body_scope_blocks.contains(&header)
                && candidate.body_scope_blocks.contains(&then_entry)
                && candidate.body_scope_blocks.contains(&else_entry)
                && loop_exits_at(cfg, candidate, boundary)
        })
        .min_by_key(|candidate| candidate.body_scope_blocks.len())
}

pub(super) fn loop_exits_at(cfg: &Cfg, candidate: &LoopCandidate, boundary: BlockRef) -> bool {
    candidate.exits.contains(&boundary)
        || (!candidate.exits.is_empty()
            && candidate
                .exits
                .iter()
                .all(|exit| cfg.unique_reachable_successor(*exit) == Some(boundary)))
}

pub(in crate::structure) fn for_loop_body_entry(
    cfg: &Cfg,
    candidate: &LoopCandidate,
) -> Option<BlockRef> {
    match candidate.kind_hint {
        LoopKindHint::NumericForLike => Some(candidate.header),
        LoopKindHint::GenericForLike => {
            let mut entries = cfg.succs[candidate.header.index()]
                .iter()
                .map(|edge| cfg.edges[edge.index()].to)
                .filter(|target| candidate.blocks.contains(target));
            let entry = entries.next()?;
            entries.next().is_none().then_some(entry)
        }
        LoopKindHint::Unknown
        | LoopKindHint::WhileLike
        | LoopKindHint::WhileTrueLike
        | LoopKindHint::RepeatLike => None,
    }
}

pub(super) fn classify_loop_bounded_one_arm_branch(
    branch_index: &BranchIndex<'_>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    // dominance frontier 只接受当前 arm 真正贡献前驱的 join，不会沿回边绕一整圈后
    // 把另一条 arm 误当 continuation；nested loop header 也已在稠密索引中单独标记。
    let then_reaches_else = branch_index.joins_at(then_entry, else_entry);
    let else_reaches_then = branch_index.joins_at(else_entry, then_entry);

    match (then_reaches_else, else_reaches_then) {
        (true, false) => Some(BranchCandidate {
            header,
            then_entry,
            else_entry: None,
            merge: Some(else_entry),
            kind: BranchKind::IfThen,
            invert_hint: false,
        }),
        (false, true) => Some(BranchCandidate {
            header,
            then_entry: else_entry,
            else_entry: None,
            merge: Some(then_entry),
            kind: BranchKind::IfThen,
            invert_hint: true,
        }),
        _ => None,
    }
}
