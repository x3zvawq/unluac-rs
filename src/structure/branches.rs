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

use std::collections::{BTreeMap, BTreeSet};

use crate::structure::{BlockRef, Cfg, DominatorTree, GraphFacts};

use super::common::{BranchCandidate, BranchKind, BranchRegionFact, LoopCandidate};
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
    branch_candidates.sort_by_key(|candidate| candidate.header);
    branch_candidates
}

pub(super) fn analyze_branch_regions(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    branch_candidates: &[BranchCandidate],
) -> Vec<BranchRegionFact> {
    let mut branch_regions = Vec::new();

    for candidate in branch_candidates {
        let Some(merge) = candidate.merge else {
            continue;
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
            then_merge_preds: collect_merge_arm_preds(cfg, candidate.then_entry, merge),
            else_merge_preds: candidate
                .else_entry
                .map(|else_entry| collect_merge_arm_preds(cfg, else_entry, merge))
                .unwrap_or_default(),
        });
    }

    branch_regions.sort_by_key(|fact| (fact.header, fact.merge));
    branch_regions
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
    loop_bounded_memo: BTreeMap<(BlockRef, BlockRef), bool>,
    loop_exits_by_header: BTreeMap<BlockRef, BTreeSet<BlockRef>>,
}

impl<'a> ReachabilityCache<'a> {
    fn new(cfg: &'a Cfg, loop_candidates: &[LoopCandidate]) -> Self {
        let mut loop_exits_by_header = BTreeMap::new();
        for candidate in loop_candidates {
            loop_exits_by_header
                .entry(candidate.header)
                .or_insert_with(|| candidate.exits.clone());
        }
        Self {
            cfg,
            memo: BTreeMap::new(),
            loop_bounded_memo: BTreeMap::new(),
            loop_exits_by_header,
        }
    }

    fn can_reach(&mut self, from: BlockRef, to: BlockRef) -> bool {
        *self
            .memo
            .entry((from, to))
            .or_insert_with(|| self.cfg.can_reach(from, to))
    }

    fn can_reach_without_entering_loop_header(&mut self, from: BlockRef, to: BlockRef) -> bool {
        *self.loop_bounded_memo.entry((from, to)).or_insert_with(|| {
            can_reach_without_entering_loop_body(self.cfg, from, to, &self.loop_exits_by_header)
        })
    }
}

fn can_reach_without_entering_loop_body(
    cfg: &Cfg,
    from: BlockRef,
    to: BlockRef,
    loop_exits_by_header: &BTreeMap<BlockRef, BTreeSet<BlockRef>>,
) -> bool {
    if from == to {
        return true;
    }
    if loop_exits_by_header.contains_key(&from) {
        return false;
    }

    let mut visited = BTreeSet::new();
    let mut stack = vec![from];
    while let Some(block) = stack.pop() {
        if block == to {
            return true;
        }
        if !visited.insert(block) {
            continue;
        }
        if let Some(exits) = loop_exits_by_header.get(&block) {
            stack.extend(exits.iter().copied());
            continue;
        }
        for edge_ref in &cfg.succs[block.index()] {
            stack.push(cfg.edges[edge_ref.index()].to);
        }
    }

    false
}

fn classify_one_arm_branch(
    reachability: &mut ReachabilityCache<'_>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let then_reaches_else = reachability.can_reach(then_entry, else_entry);
    let else_reaches_then = reachability.can_reach(else_entry, then_entry);

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
                && candidate.exits.contains(&strict_merge)
        })
        .then(|| {
            classify_loop_bounded_one_arm_branch(reachability, header, then_entry, else_entry)
        })?
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
