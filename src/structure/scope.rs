//! 这个文件实现 scope 候选提取。
//!
//! 它依赖 loop/branch/graph facts 已经给好的结构边界和显式 `Close` 指令，负责把
//! “哪些 block 天然形成一个词法收束点”整理成 `ScopeCandidate`。
//! 它不会越权恢复最终词法块，只保留 HIR 需要的 entry/exit/close-point 事实。
//!
//! 例子：
//! - `while ... do ... end` 会产出一条 `LoopScope`，entry 是 loop header，exit 是
//!   结构层已经识别出的单出口
//! - 含 `Close` 的普通 block 会额外产出 `BlockScope`，让后面的结构化阶段直接知道
//!   这些 cleanup 点属于词法边界，而不是把 `Close` 当普通语句往后拖

use std::collections::{BTreeMap, BTreeSet};

use crate::cfg::{BlockRef, Cfg, GraphFacts};
use crate::transformer::{InstrRef, LowInstr, LoweredProto};

use super::common::{BranchRegionFact, LoopCandidate, ScopeCandidate, ScopeKind};

pub(super) fn analyze_scopes(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    loop_candidates: &[LoopCandidate],
    branch_regions: &[BranchRegionFact],
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

    for branch_region in branch_regions {
        scopes.push(ScopeCandidate {
            entry: branch_region.header,
            exit: Some(branch_region.merge),
            close_points: collect_close_points(
                &branch_region.structured_blocks,
                &close_points_by_block,
            ),
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
