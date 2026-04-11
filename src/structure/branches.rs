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

use std::collections::BTreeSet;

use crate::cfg::{BlockRef, Cfg, DominatorTree, GraphFacts};

use super::common::{BranchCandidate, BranchKind, BranchRegionFact};
use super::helpers::{collect_forward_region_blocks, collect_merge_arm_preds};

pub(super) fn analyze_branches(cfg: &Cfg, graph_facts: &GraphFacts) -> Vec<BranchCandidate> {
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
            classify_one_arm_branch(cfg, header, then_entry, else_entry)
                .or_else(|| {
                    classify_if_else_branch(cfg, graph_facts, header, then_entry, else_entry)
                })
                .or_else(|| classify_guard_branch(cfg, header, then_entry, else_entry))
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
            then_merge_preds: collect_merge_arm_preds(
                cfg,
                candidate.then_entry,
                merge,
            ),
            else_merge_preds: candidate
                .else_entry
                .map(|else_entry| {
                    collect_merge_arm_preds(cfg, else_entry, merge)
                })
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

fn classify_one_arm_branch(
    cfg: &Cfg,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let then_reaches_else = cfg.can_reach(then_entry, else_entry);
    let else_reaches_then = cfg.can_reach(else_entry, then_entry);

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
        let soft = find_soft_merge(cfg, graph_facts, then_entry, else_entry);
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
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    if cfg.can_reach(then_entry, else_entry) || cfg.can_reach(else_entry, then_entry) {
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

/// 当严格后支配合流 = exit block 时，沿各分支的 ipostdom 链向上找一个
/// "软合流"：它不是 exit block，且从另一侧可达。
///
/// 典型触发形状：
/// ```text
/// if A then        ← header
///     if B then return end   ← then 侧提前 return，导致 postdom(then)=exit
///     C
/// else
///     D
/// end
/// E                ← 软合流 = ipostdom(else)，且从 then 侧也可达
/// ```
fn find_soft_merge(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BlockRef> {
    let pdom_parent = &graph_facts.post_dominator_tree.parent;

    // 沿 ipostdom 链向上搜索，找到第一个非 exit 且从 `other` 可达的祖先。
    let walk_chain = |start: BlockRef, other: BlockRef| -> Option<BlockRef> {
        let mut cursor = start;
        loop {
            let parent = (*pdom_parent.get(cursor.index())?)?;
            if parent == cfg.exit_block {
                return None;
            }
            if cfg.can_reach(other, parent) {
                return Some(parent);
            }
            cursor = parent;
        }
    };

    let else_candidate = walk_chain(else_entry, then_entry);
    let then_candidate = walk_chain(then_entry, else_entry);

    match (else_candidate, then_candidate) {
        (Some(e), Some(t)) => {
            // 两侧都找到候选，取离分支更近的（被另一侧后支配的那个）
            if graph_facts.post_dominates(t, e) {
                Some(e)
            } else {
                Some(t)
            }
        }
        (Some(e), None) => Some(e),
        (None, Some(t)) => Some(t),
        (None, None) => None,
    }
}
