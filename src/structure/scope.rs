//! 这个文件实现 scope 候选提取。
//!
//! 这里不试图直接恢复最终词法块，只把 loop/branch 的天然边界以及显式 `Close`
//! 指令整理成后续 HIR 可消费的候选。

use std::collections::{BTreeMap, BTreeSet};

use crate::cfg::{BlockRef, Cfg, GraphFacts};
use crate::transformer::{InstrRef, LowInstr, LoweredProto};

use super::branches::collect_branch_region_blocks;
use super::common::{BranchCandidate, LoopCandidate, ScopeCandidate, ScopeKind};

pub(super) fn analyze_scopes(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    loop_candidates: &[LoopCandidate],
    branch_candidates: &[BranchCandidate],
) -> Vec<ScopeCandidate> {
    let close_points_by_block = collect_close_points_by_block(proto, cfg);
    let mut scopes = Vec::new();

    for loop_candidate in loop_candidates {
        scopes.push(ScopeCandidate {
            entry: loop_candidate.header,
            exit: single_exit(&loop_candidate.exits),
            close_points: collect_close_points(&loop_candidate.blocks, &close_points_by_block),
            kind: ScopeKind::LoopScope,
        });
    }

    for branch_candidate in branch_candidates {
        let Some(merge) = branch_candidate.merge else {
            continue;
        };
        let blocks = collect_branch_region_blocks(
            cfg,
            branch_candidate,
            merge,
            Some(&graph_facts.dominator_tree.parent),
        );
        scopes.push(ScopeCandidate {
            entry: branch_candidate.header,
            exit: Some(merge),
            close_points: collect_close_points(&blocks, &close_points_by_block),
            kind: ScopeKind::BranchScope,
        });
    }

    for (block, close_points) in close_points_by_block {
        scopes.push(ScopeCandidate {
            entry: block,
            exit: immediate_postdom_exit(cfg, graph_facts, block),
            close_points,
            kind: ScopeKind::BlockScope,
        });
    }

    scopes.sort_by_key(|scope| {
        (
            scope.entry,
            scope_kind_rank(scope.kind),
            scope.exit,
            scope
                .close_points
                .iter()
                .map(|instr| instr.index())
                .collect::<Vec<_>>(),
        )
    });
    scopes.dedup_by(|left, right| {
        left.entry == right.entry
            && left.exit == right.exit
            && left.kind == right.kind
            && left.close_points == right.close_points
    });
    scopes
}

fn collect_close_points_by_block(
    proto: &LoweredProto,
    cfg: &Cfg,
) -> BTreeMap<BlockRef, Vec<InstrRef>> {
    let mut close_points_by_block = BTreeMap::<BlockRef, Vec<InstrRef>>::new();

    for (instr_index, instr) in proto.instrs.iter().enumerate() {
        if !matches!(instr, LowInstr::Close(_instr)) {
            continue;
        }

        let block = cfg.instr_to_block[instr_index];
        if !cfg.reachable_blocks.contains(&block) {
            continue;
        }

        close_points_by_block
            .entry(block)
            .or_default()
            .push(InstrRef(instr_index));
    }

    close_points_by_block
}

fn collect_close_points(
    blocks: &BTreeSet<BlockRef>,
    close_points_by_block: &BTreeMap<BlockRef, Vec<InstrRef>>,
) -> Vec<InstrRef> {
    let mut close_points = blocks
        .iter()
        .filter_map(|block| close_points_by_block.get(block))
        .flat_map(|points| points.iter().copied())
        .collect::<Vec<_>>();
    close_points.sort_by_key(|instr| instr.index());
    close_points
}

fn single_exit(exits: &BTreeSet<BlockRef>) -> Option<BlockRef> {
    if exits.len() == 1 {
        exits.iter().next().copied()
    } else {
        None
    }
}

fn immediate_postdom_exit(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    block: BlockRef,
) -> Option<BlockRef> {
    graph_facts.post_dominator_tree.parent[block.index()].filter(|exit| *exit != cfg.exit_block)
}

fn scope_kind_rank(kind: ScopeKind) -> u8 {
    match kind {
        ScopeKind::BlockScope => 0,
        ScopeKind::LoopScope => 1,
        ScopeKind::BranchScope => 2,
    }
}
