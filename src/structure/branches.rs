//! 这个文件实现共享分支候选提取。
//!
//! 它依赖 CFG/GraphFacts 已经提供好的 branch 边和后支配信息，负责回答
//! “这个 block 更像哪种 branch 形态”，以及后续多个 pass 共用的 branch-region 事实。
//! 它不会越权做短路、scope 或最终 HIR 结构决策。
//!
//! 例子：
//! - `if cond then ... end` 会产出 `BranchKind::IfThen`
//! - `if cond then ... else ... end` 会产出 `BranchKind::IfElse`
//! - `if not cond then return end; ...` 这种守卫形状会被标成 `BranchKind::Guard`
//! - loop 内嵌套 early return 把严格后支配点推到 synthetic exit 时，单臂归属
//!   仍由截断本轮回边的可达性证明，不直接猜 if/else

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::structure::{BlockRef, Cfg, DominatorTree, GraphFacts};

use super::common::{BranchCandidate, BranchKind, BranchRegionFact, LoopCandidate, LoopKindHint};
use super::helpers::{collect_forward_region_blocks, collect_merge_arm_preds};

pub(super) fn analyze_branches(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    loop_candidates: &[LoopCandidate],
) -> Vec<BranchCandidate> {
    let mut reachability = ReachabilityCache::new(cfg, loop_candidates);
    let mut branch_candidates: Vec<_> = cfg
        .block_order
        .iter()
        .copied()
        .filter(|header| cfg.reachable_blocks.contains(header))
        .filter_map(|header| {
            let (then_edge_ref, else_edge_ref) = cfg.branch_edges(header)?;
            let then_entry = cfg.edges[then_edge_ref.index()].to;
            let else_entry = cfg.edges[else_edge_ref.index()].to;
            if then_entry == else_entry {
                return None;
            }
            classify_infinite_loop_bounded_branch(
                &mut reachability,
                loop_candidates,
                header,
                then_entry,
                else_entry,
            )
            .or_else(|| {
                classify_postdom_one_arm_branch(graph_facts, header, then_entry, else_entry)
            })
            .or_else(|| {
                classify_for_loop_exit_branch(
                    cfg,
                    graph_facts,
                    loop_candidates,
                    header,
                    then_entry,
                    else_entry,
                )
            })
            .or_else(|| classify_one_arm_branch(&mut reachability, header, then_entry, else_entry))
            .or_else(|| {
                classify_loop_exit_bounded_one_arm_branch(
                    cfg,
                    graph_facts,
                    loop_candidates,
                    &mut reachability,
                    header,
                    then_entry,
                    else_entry,
                )
            })
            .or_else(|| classify_if_else_branch(cfg, graph_facts, header, then_entry, else_entry))
            .or_else(|| {
                classify_loop_bounded_one_arm_branch(
                    &mut reachability,
                    header,
                    then_entry,
                    else_entry,
                )
            })
            .or_else(|| {
                classify_guard_branch(cfg, &mut reachability, header, then_entry, else_entry)
            })
        })
        .collect();
    refine_loop_iteration_if_else_branches(
        cfg,
        graph_facts,
        loop_candidates,
        &mut reachability,
        &mut branch_candidates,
    );
    branch_candidates.sort_by_key(|candidate| candidate.header);
    branch_candidates
}

fn refine_loop_iteration_if_else_branches(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    loop_candidates: &[LoopCandidate],
    reachability: &mut ReachabilityCache<'_>,
    branch_candidates: &mut [BranchCandidate],
) {
    let candidates_by_header = branch_candidates
        .iter()
        .map(|candidate| (candidate.header, candidate.clone()))
        .collect::<BTreeMap<_, _>>();

    for candidate in branch_candidates {
        let Some(downstream_header) = candidate
            .else_entry
            .is_none()
            .then_some(candidate.merge)
            .flatten()
        else {
            continue;
        };
        let Some(downstream) = candidates_by_header.get(&downstream_header) else {
            continue;
        };
        let Some((then_edge, else_edge)) = cfg.branch_edges(candidate.header) else {
            continue;
        };
        let then_entry = cfg.edges[then_edge.index()].to;
        let else_entry = cfg.edges[else_edge.index()].to;
        let Some(owner) = loop_candidates
            .iter()
            .filter(|owner| {
                owner.blocks.contains(&candidate.header)
                    && owner.blocks.contains(&then_entry)
                    && owner.blocks.contains(&else_entry)
                    && owner.blocks.contains(&downstream.header)
                    && downstream
                        .merge
                        .is_some_and(|merge| owner.exits.contains(&merge))
            })
            .min_by_key(|owner| owner.blocks.len())
        else {
            continue;
        };
        if reachability.can_reach_without_entering_loop_header(then_entry, else_entry)
            || reachability.can_reach_without_entering_loop_header(else_entry, then_entry)
        {
            continue;
        }
        let Some(merge) =
            find_soft_merge(cfg, graph_facts, candidate.header, then_entry, else_entry)
        else {
            continue;
        };
        if !owner.blocks.contains(&merge)
            || !reachability.can_reach_without_entering_loop_header(then_entry, merge)
            || !reachability.can_reach_without_entering_loop_header(else_entry, merge)
        {
            continue;
        }

        candidate.then_entry = then_entry;
        candidate.else_entry = Some(else_entry);
        candidate.merge = Some(merge);
        candidate.kind = BranchKind::IfElse;
        candidate.invert_hint = false;
    }
}

pub(super) fn analyze_branch_regions(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    loop_candidates: &[LoopCandidate],
    branch_candidates: &[BranchCandidate],
) -> Vec<BranchRegionFact> {
    let mut branch_regions = Vec::new();

    for candidate in branch_candidates {
        let Some(merge) = candidate.merge else {
            continue;
        };
        let disambiguate_overlap = candidate.else_entry.is_some_and(|else_entry| {
            graph_facts
                .nearest_common_postdom(candidate.then_entry, else_entry)
                .is_some_and(|strict_merge| {
                    strict_merge != merge
                        && for_loop_exit_owner(
                            cfg,
                            loop_candidates,
                            candidate.header,
                            candidate.then_entry,
                            else_entry,
                            strict_merge,
                        )
                        .is_some_and(|owner| {
                            for_loop_body_entry(cfg, owner) == Some(candidate.header)
                                && owner.blocks.contains(&candidate.then_entry)
                                && owner.blocks.contains(&else_entry)
                        })
                })
        });
        let (then_merge_preds, else_merge_preds) = if disambiguate_overlap {
            collect_branch_merge_preds(cfg, graph_facts, candidate, merge)
        } else {
            (
                collect_merge_arm_preds(cfg, candidate.then_entry, merge),
                candidate
                    .else_entry
                    .map(|else_entry| collect_merge_arm_preds(cfg, else_entry, merge))
                    .unwrap_or_default(),
            )
        };

        branch_regions.push(BranchRegionFact {
            header: candidate.header,
            merge,
            kind: candidate.kind,
            flow_blocks: collect_branch_region_blocks(cfg, candidate, merge, None),
            structured_blocks: collect_branch_region_blocks(
                cfg,
                candidate,
                merge,
                Some(&graph_facts.dominator_tree),
            ),
            then_merge_preds,
            else_merge_preds,
        });
    }

    branch_regions.sort_by_key(|fact| (fact.header, fact.merge));
    branch_regions
}

fn collect_branch_merge_preds(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    candidate: &BranchCandidate,
    merge: BlockRef,
) -> (BTreeSet<BlockRef>, BTreeSet<BlockRef>) {
    let mut then_preds = collect_merge_arm_preds(cfg, candidate.then_entry, merge);
    let Some(else_entry) = candidate.else_entry else {
        return (then_preds, BTreeSet::new());
    };
    let mut else_preds = collect_merge_arm_preds(cfg, else_entry, merge);
    let overlap = then_preds
        .intersection(&else_preds)
        .copied()
        .collect::<BTreeSet<_>>();
    then_preds.retain(|pred| {
        !overlap.contains(pred)
            || !graph_facts.dominates(else_entry, *pred)
            || graph_facts.dominates(candidate.then_entry, *pred)
    });
    else_preds.retain(|pred| {
        !overlap.contains(pred)
            || !graph_facts.dominates(candidate.then_entry, *pred)
            || graph_facts.dominates(else_entry, *pred)
    });
    (then_preds, else_preds)
}

fn collect_branch_region_blocks(
    cfg: &Cfg,
    candidate: &BranchCandidate,
    merge: BlockRef,
    dom_tree: Option<&DominatorTree>,
) -> BTreeSet<BlockRef> {
    let mut blocks = BTreeSet::from([candidate.header]);
    blocks.extend(collect_forward_region_blocks(
        cfg,
        std::iter::once(candidate.then_entry).chain(candidate.else_entry),
        Some(merge),
        dom_tree.map(|tree| (candidate.header, tree)),
    ));

    blocks
}

struct ReachabilityCache<'a> {
    cfg: &'a Cfg,
    memo: BTreeMap<(BlockRef, BlockRef), bool>,
    loop_bounded_memo: BTreeMap<BlockRef, BTreeSet<BlockRef>>,
    loops_by_header: BTreeMap<BlockRef, Vec<&'a LoopCandidate>>,
}

impl<'a> ReachabilityCache<'a> {
    fn new(cfg: &'a Cfg, loop_candidates: &'a [LoopCandidate]) -> Self {
        let mut loops_by_header = BTreeMap::<_, Vec<_>>::new();
        for candidate in loop_candidates {
            loops_by_header
                .entry(candidate.header)
                .or_default()
                .push(candidate);
        }
        Self {
            cfg,
            memo: BTreeMap::new(),
            loop_bounded_memo: BTreeMap::new(),
            loops_by_header,
        }
    }

    fn can_reach(&mut self, from: BlockRef, to: BlockRef) -> bool {
        *self
            .memo
            .entry((from, to))
            .or_insert_with(|| self.cfg.can_reach(from, to))
    }

    fn can_reach_without_entering_loop_header(&mut self, from: BlockRef, to: BlockRef) -> bool {
        self.loop_bounded_memo
            .entry(from)
            .or_insert_with(|| {
                reachable_without_entering_loop_bodies(self.cfg, from, &self.loops_by_header)
            })
            .contains(&to)
    }
}

fn loop_candidate_for_entry<'a>(
    candidates: &[&'a LoopCandidate],
    predecessor: Option<BlockRef>,
) -> Option<&'a LoopCandidate> {
    if let Some(predecessor) = predecessor {
        let mut matching = candidates
            .iter()
            .copied()
            .filter(|candidate| candidate.preheader == Some(predecessor));
        if let Some(candidate) = matching.next()
            && matching.next().is_none()
        {
            return Some(candidate);
        }
    }

    match candidates {
        [candidate] => Some(*candidate),
        _ => None,
    }
}

fn reachable_without_entering_loop_bodies(
    cfg: &Cfg,
    from: BlockRef,
    loops_by_header: &BTreeMap<BlockRef, Vec<&LoopCandidate>>,
) -> BTreeSet<BlockRef> {
    let mut reachable = BTreeSet::from([from]);
    if loops_by_header.contains_key(&from) {
        return reachable;
    }

    let mut visited = BTreeSet::new();
    let mut worklist = VecDeque::from([(None, from)]);
    while let Some((predecessor, block)) = worklist.pop_front() {
        reachable.insert(block);
        if !visited.insert((predecessor, block)) {
            continue;
        }
        if let Some(candidates) = loops_by_header.get(&block) {
            let Some(candidate) = loop_candidate_for_entry(candidates, predecessor) else {
                // 同 header 候选无法按入口唯一选择时，不猜测任意 loop owner。
                continue;
            };
            worklist.extend(candidate.exits.iter().map(|exit| (None, *exit)));
            continue;
        }
        for edge_ref in &cfg.succs[block.index()] {
            worklist.push_back((Some(block), cfg.edges[edge_ref.index()].to));
        }
    }

    reachable
}

fn classify_one_arm_branch(
    reachability: &mut ReachabilityCache<'_>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let then_reaches_else = reachability.can_reach(then_entry, else_entry);
    let else_reaches_then = reachability.can_reach(else_entry, then_entry);

    one_arm_candidate(
        header,
        then_entry,
        else_entry,
        then_reaches_else,
        else_reaches_then,
    )
}

fn one_arm_candidate(
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

fn classify_postdom_one_arm_branch(
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

fn classify_infinite_loop_bounded_branch(
    reachability: &mut ReachabilityCache<'_>,
    loop_candidates: &[LoopCandidate],
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let loop_candidate = loop_candidates
        .iter()
        .filter(|candidate| {
            candidate.exits.is_empty()
                && candidate.blocks.contains(&header)
                && candidate.blocks.contains(&then_entry)
                && candidate.blocks.contains(&else_entry)
        })
        .min_by_key(|candidate| candidate.blocks.len())?;

    let then_reaches_else =
        reachability.can_reach_without_entering_loop_header(then_entry, else_entry);
    let else_reaches_then =
        reachability.can_reach_without_entering_loop_header(else_entry, then_entry);
    let local_merge = loop_candidate
        .blocks
        .iter()
        .copied()
        .filter(|candidate| *candidate != header && *candidate != loop_candidate.header)
        .find(|candidate| {
            reachability.can_reach_without_entering_loop_header(then_entry, *candidate)
                && reachability.can_reach_without_entering_loop_header(else_entry, *candidate)
        });

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
            if reachability
                .can_reach_without_entering_loop_header(then_entry, loop_candidate.header)
                && reachability
                    .can_reach_without_entering_loop_header(else_entry, loop_candidate.header) =>
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

fn classify_loop_exit_bounded_one_arm_branch(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    loop_candidates: &[LoopCandidate],
    reachability: &mut ReachabilityCache<'_>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let strict_merge = graph_facts.nearest_common_postdom(then_entry, else_entry)?;
    // 局部 break 会把严格后支配点推到外层 loop exit；但若一臂进入单跳回边 pad，
    // 它表达的是下一轮 continue，不能借整轮回边伪装成对另一臂的局部可达。
    let enters_continue_pad = loop_candidates.iter().any(|candidate| {
        candidate.blocks.contains(&header)
            && [then_entry, else_entry].into_iter().any(|entry| {
                cfg.succs[entry.index()].len() == 1
                    && candidate
                        .backedges
                        .iter()
                        .any(|edge| cfg.edges[edge.index()].from == entry)
            })
    });
    if enters_continue_pad {
        return None;
    }
    loop_candidates
        .iter()
        .any(|candidate| {
            candidate.blocks.contains(&header)
                && candidate.blocks.contains(&then_entry)
                && candidate.blocks.contains(&else_entry)
                && (candidate.exits.contains(&strict_merge) || strict_merge == cfg.exit_block)
        })
        .then(|| {
            classify_loop_bounded_one_arm_branch(reachability, header, then_entry, else_entry)
        })?
}

fn classify_for_loop_exit_branch(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    loop_candidates: &[LoopCandidate],
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let strict_merge = graph_facts.nearest_common_postdom(then_entry, else_entry)?;
    let owner = for_loop_exit_owner(
        cfg,
        loop_candidates,
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
                .binding_scope_blocks
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

fn for_loop_exit_owner<'a>(
    cfg: &Cfg,
    loop_candidates: &'a [LoopCandidate],
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
    boundary: BlockRef,
) -> Option<&'a LoopCandidate> {
    loop_candidates
        .iter()
        .filter(|candidate| {
            matches!(
                candidate.kind_hint,
                LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
            ) && candidate.binding_scope_blocks.contains(&header)
                && candidate.binding_scope_blocks.contains(&then_entry)
                && candidate.binding_scope_blocks.contains(&else_entry)
                && for_loop_exits_at(cfg, candidate, boundary)
        })
        .min_by_key(|candidate| candidate.binding_scope_blocks.len())
}

fn for_loop_exits_at(cfg: &Cfg, candidate: &LoopCandidate, boundary: BlockRef) -> bool {
    candidate.exits.contains(&boundary)
        || (!candidate.exits.is_empty()
            && candidate
                .exits
                .iter()
                .all(|exit| cfg.unique_reachable_successor(*exit) == Some(boundary)))
}

fn for_loop_body_entry(cfg: &Cfg, candidate: &LoopCandidate) -> Option<BlockRef> {
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

fn classify_loop_bounded_one_arm_branch(
    reachability: &mut ReachabilityCache<'_>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    // 普通可达性在无出口或嵌套 loop 里会被回边污染：两个分支臂可能都能绕一整圈
    // 回到对方，看起来不像 if-then。这里把 reducible nested loop 当成“只通向 exits
    // 的结构化节点”，既保留 `if ... then skip nested-for end` 这种正常出口，又避免沿
    // loop body/backedge 绕回另一条臂。
    let then_reaches_else =
        reachability.can_reach_without_entering_loop_header(then_entry, else_entry);
    let else_reaches_then =
        reachability.can_reach_without_entering_loop_header(else_entry, then_entry);

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

fn classify_if_else_branch(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let merge = graph_facts.nearest_common_postdom(then_entry, else_entry)?;
    if merge == cfg.exit_block {
        // 严格后支配合流是 exit block，说明两侧都有提前 return 的路径。
        // 但如果一侧的 ipostdom 是非 exit 块且从另一侧可达，那它仍然是
        // 合法的 if-else merge：提前 return 只是 body 内的 early exit，
        // 不影响外层的 merge 恢复。
        let soft = find_soft_merge(cfg, graph_facts, header, then_entry, else_entry);
        return Some(BranchCandidate {
            header,
            then_entry,
            else_entry: Some(else_entry),
            merge: soft,
            kind: BranchKind::IfElse,
            invert_hint: false,
        });
    }

    if merge == then_entry {
        return Some(BranchCandidate {
            header,
            then_entry: else_entry,
            else_entry: None,
            merge: Some(then_entry),
            kind: BranchKind::IfThen,
            invert_hint: true,
        });
    }

    if merge == else_entry {
        return Some(BranchCandidate {
            header,
            then_entry,
            else_entry: None,
            merge: Some(else_entry),
            kind: BranchKind::IfThen,
            invert_hint: false,
        });
    }

    Some(BranchCandidate {
        header,
        then_entry,
        else_entry: Some(else_entry),
        merge: Some(merge),
        kind: BranchKind::IfElse,
        invert_hint: false,
    })
}

fn classify_guard_branch(
    cfg: &Cfg,
    reachability: &mut ReachabilityCache<'_>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    if reachability.can_reach(then_entry, else_entry)
        || reachability.can_reach(else_entry, then_entry)
    {
        return None;
    }

    let then_score = branch_continuation_score(cfg, then_entry);
    let else_score = branch_continuation_score(cfg, else_entry);
    if then_score == else_score {
        return None;
    }

    let (continuation, side, invert_hint) = if then_score > else_score {
        (then_entry, else_entry, true)
    } else {
        (else_entry, then_entry, false)
    };

    Some(BranchCandidate {
        header,
        then_entry: side,
        else_entry: None,
        merge: Some(continuation),
        kind: BranchKind::Guard,
        invert_hint,
    })
}

fn branch_continuation_score(cfg: &Cfg, start: BlockRef) -> usize {
    let mut visited = BTreeSet::new();
    let mut stack = vec![start];

    while let Some(block) = stack.pop() {
        if !cfg.reachable_blocks.contains(&block)
            || block == cfg.exit_block
            || !visited.insert(block)
        {
            continue;
        }

        for edge_ref in &cfg.succs[block.index()] {
            stack.push(cfg.edges[edge_ref.index()].to);
        }
    }

    visited.len()
}

/// 当严格后支配合流 = exit block 时，从两臂共同的 dominance frontier 中找一个
/// "软合流"。它必须是两臂控制流真实汇入的 join，而不是只在全图上绕路可达。
///
/// 典型触发形状：
/// ```text
/// if A then        ← header
///     if B then return end   ← then 侧提前 return，导致 postdom(then)=exit
///     C
/// else
///     D
/// end
/// E                ← 软合流 = 两臂共同的 dominance frontier
/// ```
fn find_soft_merge(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BlockRef> {
    let else_frontier = graph_facts
        .dominance_frontier_blocks(else_entry)
        .collect::<BTreeSet<_>>();
    let common = graph_facts
        .dominance_frontier_blocks(then_entry)
        .filter(|candidate| {
            *candidate != cfg.exit_block
                && graph_facts.dominates(header, *candidate)
                && else_frontier.contains(candidate)
        })
        .collect::<BTreeSet<_>>();

    common.iter().copied().find(|candidate| {
        common
            .iter()
            .all(|other| graph_facts.dominates(*candidate, *other))
    })
}
