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

use crate::structure::{BlockRef, Cfg, DominatorTree, EdgeKind, GraphFacts};

use super::common::{
    BranchCandidate, BranchKind, BranchRegionFact, LoopCandidate, LoopKindHint, SinglePassFenceFact,
};
use super::helpers::collect_forward_region_blocks;

pub(super) fn analyze_branches(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    loop_candidates: &[LoopCandidate],
) -> (
    Vec<BranchCandidate>,
    BTreeMap<BlockRef, SinglePassFenceFact>,
) {
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
    let single_pass_fences = refine_nested_escape_if_else_merges(
        cfg,
        graph_facts,
        loop_candidates,
        &mut branch_candidates,
    );
    branch_candidates.sort_by_key(|candidate| candidate.header);
    (branch_candidates, single_pass_fences)
}

fn refine_nested_escape_if_else_merges(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    loop_candidates: &[LoopCandidate],
    branch_candidates: &mut [BranchCandidate],
) -> BTreeMap<BlockRef, SinglePassFenceFact> {
    let loop_headers = loop_candidates
        .iter()
        .map(|candidate| candidate.header)
        .collect::<BTreeSet<_>>();
    let mut nested_escapes =
        BTreeMap::<(BlockRef, BlockRef), Vec<(BlockRef, crate::structure::EdgeRef)>>::new();
    for nested in branch_candidates.iter() {
        let Some((then_edge, else_edge)) = cfg.branch_edges(nested.header) else {
            continue;
        };
        let then_entry = cfg.edges[then_edge.index()].to;
        let else_entry = cfg.edges[else_edge.index()].to;
        let then_target = transparent_jump_target(cfg, then_entry).unwrap_or(then_entry);
        let else_target = transparent_jump_target(cfg, else_entry).unwrap_or(else_entry);
        if then_target == else_target {
            continue;
        }
        nested_escapes
            .entry((then_target, else_target))
            .or_default()
            .push((nested.header, then_edge));
        nested_escapes
            .entry((else_target, then_target))
            .or_default()
            .push((nested.header, else_edge));
    }

    let mut single_pass_fences = BTreeMap::new();
    for candidate in branch_candidates {
        if loop_headers.contains(&candidate.header) {
            continue;
        }
        let (Some(strict_merge), Some(else_entry)) = (candidate.merge, candidate.else_entry) else {
            continue;
        };
        if candidate.kind != BranchKind::IfElse || strict_merge == cfg.exit_block {
            continue;
        }
        let Some(soft_merge) = find_soft_merge(
            cfg,
            graph_facts,
            candidate.header,
            candidate.then_entry,
            else_entry,
        ) else {
            continue;
        };
        let escape_edges = nested_escapes
            .get(&(strict_merge, soft_merge))
            .into_iter()
            .flatten()
            .filter(|(nested_header, _)| {
                graph_facts.dominates(candidate.then_entry, *nested_header)
                    != graph_facts.dominates(else_entry, *nested_header)
            })
            .map(|(_, edge)| *edge)
            .collect::<BTreeSet<_>>();
        if !escape_edges.is_empty()
            && !enclosing_loop_owns_escape(
                cfg,
                loop_candidates,
                candidate,
                else_entry,
                soft_merge,
                strict_merge,
                &escape_edges,
            )
            && cfg.can_reach(candidate.then_entry, soft_merge)
            && cfg.can_reach(else_entry, soft_merge)
        {
            // 一臂内的透明 jump pad 直接跳过共同 fallthrough，严格后支配点因此
            // 落在 escape 之后；外层 if/else 的正常路径仍在 soft merge 汇合。
            candidate.merge = Some(soft_merge);
            single_pass_fences.insert(
                candidate.header,
                SinglePassFenceFact {
                    exit: strict_merge,
                    escape_edges,
                },
            );
        }
    }
    single_pass_fences
}

/// 若全部 escape 已从同一 loop body 直达其显式出口，它们表达的是该 loop 的 break；
/// synthetic fence 会让这些 break 只退出新包的一次性 repeat，从而继续执行原 loop body。
fn enclosing_loop_owns_escape(
    cfg: &Cfg,
    loop_candidates: &[LoopCandidate],
    branch: &BranchCandidate,
    else_entry: BlockRef,
    soft_merge: BlockRef,
    strict_merge: BlockRef,
    escape_edges: &BTreeSet<crate::structure::EdgeRef>,
) -> bool {
    loop_candidates.iter().any(|owner| {
        owner.exits.contains(&strict_merge)
            && [branch.header, branch.then_entry, else_entry, soft_merge]
                .into_iter()
                .all(|block| owner.body_scope_blocks.contains(&block))
            && escape_edges.iter().all(|edge_ref| {
                let edge = cfg.edges[edge_ref.index()];
                owner.body_scope_blocks.contains(&edge.from) && owner.exits.contains(&edge.to)
            })
    })
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
    branch_candidates: &[BranchCandidate],
    single_pass_fences: &BTreeMap<BlockRef, SinglePassFenceFact>,
) -> Vec<BranchRegionFact> {
    let mut branch_regions = branch_candidates
        .iter()
        .filter_map(|candidate| {
            let merge = candidate.merge?;
            let explicit_structured_blocks =
                graph_facts.dominates(merge, candidate.header).then(|| {
                    collect_branch_region_blocks(cfg, candidate, merge, &graph_facts.dominator_tree)
                });
            Some(BranchRegionFact {
                header: candidate.header,
                merge,
                kind: candidate.kind,
                single_pass_fence: single_pass_fences.get(&candidate.header).cloned(),
                explicit_structured_blocks,
            })
        })
        .collect::<Vec<_>>();

    branch_regions.sort_by_key(|fact| (fact.header, fact.merge));
    branch_regions
}

fn collect_branch_region_blocks(
    cfg: &Cfg,
    candidate: &BranchCandidate,
    merge: BlockRef,
    dom_tree: &DominatorTree,
) -> BTreeSet<BlockRef> {
    let mut blocks = BTreeSet::from([candidate.header]);
    blocks.extend(collect_forward_region_blocks(
        cfg,
        std::iter::once(candidate.then_entry).chain(candidate.else_entry),
        Some(merge),
        Some((candidate.header, dom_tree)),
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
                transparent_jump_target(cfg, entry).is_some()
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

pub(super) fn for_loop_exit_owner<'a>(
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
            ) && candidate.body_scope_blocks.contains(&header)
                && candidate.body_scope_blocks.contains(&then_entry)
                && candidate.body_scope_blocks.contains(&else_entry)
                && for_loop_exits_at(cfg, candidate, boundary)
        })
        .min_by_key(|candidate| candidate.body_scope_blocks.len())
}

fn for_loop_exits_at(cfg: &Cfg, candidate: &LoopCandidate, boundary: BlockRef) -> bool {
    candidate.exits.contains(&boundary)
        || (!candidate.exits.is_empty()
            && candidate
                .exits
                .iter()
                .all(|exit| cfg.unique_reachable_successor(*exit) == Some(boundary)))
}

pub(super) fn for_loop_body_entry(cfg: &Cfg, candidate: &LoopCandidate) -> Option<BlockRef> {
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

pub(super) fn transparent_jump_target(cfg: &Cfg, block: BlockRef) -> Option<BlockRef> {
    let [edge_ref] = cfg.succs[block.index()].as_slice() else {
        return None;
    };
    let edge = cfg.edges[edge_ref.index()];
    (cfg.blocks[block.index()].instrs.len == 1 && edge.kind == EdgeKind::Jump).then_some(edge.to)
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
        // 两臂入口互不可达且没有共同后支配点时，大小相等只表示无法为 guard
        // 选择展示层 continuation，不能据此丢掉整个 branch owner。显式 if/else
        // 先不声明强制 merge；HIR 仍可用更严格的路径证明选出可选共享 continuation。
        return Some(BranchCandidate {
            header,
            then_entry,
            else_entry: Some(else_entry),
            merge: None,
            kind: BranchKind::IfElse,
            invert_hint: false,
        });
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
