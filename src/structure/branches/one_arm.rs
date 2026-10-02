//! 分类 postdom/reachable/terminal/loop-bounded 的 one-arm 分支；依赖 BranchIndex 与 loop 出口，不负责普通 if/else。

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
    // 带 break 的无限循环中，tail 可能必须先回到 header、下一轮进入另一臂才能
    // 最终退出函数。此时另一臂虽严格后支配 tail，却不是本轮 continuation。
    // 例如 `repeat if a then repeat step() until b; if c then break end end;
    // while not b do step() end until false`：共享 while tail 应留在 if 外。
    // 两臂都属于当前 natural loop 时，优先使用真实 frontier 汇入的单臂证明；
    // 直接进入 header 的 continue 仍交给下面既有的控制出口分类。
    if [then_entry, else_entry]
        .into_iter()
        .any(|entry| graph_facts.post_dominates(header, entry))
        && branch_index.endpoint_loops(header).any(|owner| {
            owner.header == header
                && [then_entry, else_entry]
                    .into_iter()
                    .all(|entry| entry != header && owner.blocks.contains(&entry))
        })
        && let Some(candidate) =
            classify_loop_bounded_one_arm_branch(branch_index, header, then_entry, else_entry)
    {
        return Some(candidate);
    }
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
    for (escape, normal, invert_hint) in [
        (then_entry, else_entry, false),
        (else_entry, then_entry, true),
    ] {
        if owner.continue_target == Some(escape)
            && escape != owner.header
            && normal != escape
            && owner.blocks.contains(&normal)
            && cfg.blocks[escape.index()].instrs.len == 1
            && cfg.branch_edges(escape).is_some()
        {
            // 直接进入纯条件块的是 continue 臂。把它反选成 merge
            // 会让 enclosing branch 后的共享正文也落到这条已退出正文的路径上。
            // 含正文更新前缀的控制块不由这个证明覆盖，不能把其原位计算提出分支。
            return Some(BranchCandidate {
                header,
                then_entry: escape,
                else_entry: None,
                merge: Some(normal),
                kind: BranchKind::Guard,
                invert_hint,
            });
        }
        if owner.continue_target == Some(owner.header)
            && header != owner.header
            && escape != owner.header
            && owner.blocks.contains(&normal)
            && !branch_index.joins_at(normal, owner.header)
            && cfg.unique_reachable_successor(escape) == Some(owner.header)
            && graph_facts.dominates(header, escape)
            && !branch_index.joins_at(normal, escape)
            && cfg.succs[escape.index()]
                .iter()
                .all(|edge| cfg.edges[edge.index()].kind == EdgeKind::Jump)
        {
            // 同轮正常路径绕过这条直接回边时，它是含前缀的 continue 臂。
            // 不能因该臂在 header 有 frontier 就把它选作 continuation，
            // 否则另一臂原本汇入共享 tail 的路径也会执行此前缀和 continue。
            // 正常端点必须仍在本轮内，且先汇入更内侧的共享尾；若它直接
            // 回到 header 或已经离开循环，则属于原来的 if/else 或退出分类。
            return Some(BranchCandidate {
                header,
                then_entry: escape,
                else_entry: None,
                merge: Some(normal),
                kind: BranchKind::Guard,
                invert_hint,
            });
        }
    }
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

    one_arm_candidate(
        header,
        then_entry,
        else_entry,
        then_reaches_else,
        else_reaches_then,
    )
}
