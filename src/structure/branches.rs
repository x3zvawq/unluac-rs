//! 这个文件实现共享分支候选提取。
//!
//! 它只回答“这个 block 更像哪种 branch 形态”，不提前做短路、scope 或最终
//! HIR 结构决策。

use std::collections::{BTreeSet, VecDeque};

use crate::cfg::{BlockRef, Cfg, GraphFacts};

use super::common::{BranchCandidate, BranchKind};
use super::helpers::{branch_edges, can_reach, dominates, nearest_common_postdom};

pub(super) fn analyze_branches(cfg: &Cfg, graph_facts: &GraphFacts) -> Vec<BranchCandidate> {
    let mut branch_candidates = Vec::new();

    for header in &cfg.block_order {
        let header = *header;
        if !cfg.reachable_blocks.contains(&header) {
            continue;
        }

        let Some((&then_edge_ref, &else_edge_ref)) = branch_edges(cfg, header) else {
            continue;
        };
        let then_entry = cfg.edges[then_edge_ref.index()].to;
        let else_entry = cfg.edges[else_edge_ref.index()].to;

        if then_entry == else_entry {
            continue;
        }

        if let Some(candidate) = classify_one_arm_branch(cfg, header, then_entry, else_entry)
            .or_else(|| classify_if_else_branch(cfg, graph_facts, header, then_entry, else_entry))
            .or_else(|| classify_guard_branch(cfg, header, then_entry, else_entry))
        {
            branch_candidates.push(candidate);
        }
    }

    branch_candidates.sort_by_key(|candidate| candidate.header);
    branch_candidates
}

pub(super) fn collect_branch_region_blocks(
    cfg: &Cfg,
    candidate: &BranchCandidate,
    merge: BlockRef,
    dom_parent: Option<&[Option<BlockRef>]>,
) -> BTreeSet<BlockRef> {
    let mut blocks = BTreeSet::from([candidate.header]);
    let mut worklist = VecDeque::new();
    worklist.push_back(candidate.then_entry);
    if let Some(else_entry) = candidate.else_entry {
        worklist.push_back(else_entry);
    }

    while let Some(block) = worklist.pop_front() {
        if block == merge
            || !cfg.reachable_blocks.contains(&block)
            || !blocks.insert(block)
            || dom_parent.is_some_and(|parent| !dominates(parent, candidate.header, block))
        {
            continue;
        }

        for edge_ref in &cfg.succs[block.index()] {
            let succ = cfg.edges[edge_ref.index()].to;
            if succ != merge {
                worklist.push_back(succ);
            }
        }
    }

    blocks
}

fn classify_one_arm_branch(
    cfg: &Cfg,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let then_reaches_else = can_reach(cfg, then_entry, else_entry);
    let else_reaches_then = can_reach(cfg, else_entry, then_entry);

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
    let merge = nearest_common_postdom(
        &graph_facts.post_dominator_tree.parent,
        then_entry,
        else_entry,
    )?;
    if merge == cfg.exit_block {
        return Some(BranchCandidate {
            header,
            then_entry,
            else_entry: Some(else_entry),
            merge: None,
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
    if can_reach(cfg, then_entry, else_entry) || can_reach(cfg, else_entry, then_entry) {
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
