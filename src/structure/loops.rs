//! 这个文件实现共享循环候选提取。
//!
//! 循环形态只产出 hint，不在这里过早绑定成最终 `while/repeat/for` 语法。

use std::collections::{BTreeMap, BTreeSet};

use crate::cfg::{BlockRef, Cfg, EdgeRef, GraphFacts};
use crate::transformer::{LowInstr, LoweredProto};

use super::common::{LoopCandidate, LoopKindHint};
use super::helpers::{branch_edges, collect_region_exits};

pub(super) fn analyze_loops(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
) -> Vec<LoopCandidate> {
    let mut grouped_loops = BTreeMap::<BlockRef, (BTreeSet<BlockRef>, Vec<EdgeRef>)>::new();
    for natural_loop in &graph_facts.natural_loops {
        let entry = grouped_loops
            .entry(natural_loop.header)
            .or_insert_with(|| (BTreeSet::new(), Vec::new()));
        entry.0.extend(natural_loop.blocks.iter().copied());
        entry.1.push(natural_loop.backedge);
    }

    let mut loop_candidates = grouped_loops
        .into_iter()
        .map(|(header, (blocks, mut backedges))| {
            backedges.sort();
            backedges.dedup();
            let exits = collect_region_exits(cfg, &blocks);
            let reducible = is_reducible_loop(cfg, header, &blocks);
            let (kind_hint, continue_target) =
                infer_loop_shape(proto, cfg, header, &blocks, &backedges);

            LoopCandidate {
                header,
                blocks,
                backedges,
                exits,
                continue_target,
                kind_hint,
                reducible,
            }
        })
        .collect::<Vec<_>>();

    loop_candidates.sort_by_key(|candidate| candidate.header);
    loop_candidates
}

fn infer_loop_shape(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: BlockRef,
    blocks: &BTreeSet<BlockRef>,
    backedges: &[EdgeRef],
) -> (LoopKindHint, Option<BlockRef>) {
    let backedge_sources = backedges
        .iter()
        .map(|edge_ref| cfg.edges[edge_ref.index()].from)
        .collect::<BTreeSet<_>>();

    if backedge_sources.len() == 1 {
        let source = *backedge_sources
            .iter()
            .next()
            .expect("set length already checked");
        if let Some(terminator) = cfg.terminator(&proto.instrs, source) {
            match terminator {
                LowInstr::NumericForLoop(_instr) => {
                    return (LoopKindHint::NumericForLike, Some(source));
                }
                LowInstr::GenericForLoop(_instr) => {
                    return (LoopKindHint::GenericForLike, Some(source));
                }
                LowInstr::Branch(_instr)
                    if branch_has_header_and_exit(cfg, source, header, blocks) =>
                {
                    return (LoopKindHint::RepeatLike, Some(source));
                }
                _ => {}
            }
        }
    }

    if matches!(
        cfg.terminator(&proto.instrs, header),
        Some(LowInstr::Branch(_instr)) if branch_has_loop_body_and_exit(cfg, header, blocks)
    ) {
        return (LoopKindHint::WhileLike, Some(header));
    }

    let continue_target = if backedge_sources.len() == 1 {
        backedge_sources.iter().next().copied()
    } else {
        None
    };

    (LoopKindHint::Unknown, continue_target)
}

fn branch_has_loop_body_and_exit(cfg: &Cfg, header: BlockRef, blocks: &BTreeSet<BlockRef>) -> bool {
    let Some((then_edge_ref, else_edge_ref)) = branch_edges(cfg, header) else {
        return false;
    };
    let then_block = cfg.edges[then_edge_ref.index()].to;
    let else_block = cfg.edges[else_edge_ref.index()].to;

    (blocks.contains(&then_block) && !blocks.contains(&else_block))
        || (!blocks.contains(&then_block) && blocks.contains(&else_block))
}

fn branch_has_header_and_exit(
    cfg: &Cfg,
    block: BlockRef,
    header: BlockRef,
    blocks: &BTreeSet<BlockRef>,
) -> bool {
    let Some((then_edge_ref, else_edge_ref)) = branch_edges(cfg, block) else {
        return false;
    };
    let then_block = cfg.edges[then_edge_ref.index()].to;
    let else_block = cfg.edges[else_edge_ref.index()].to;

    (then_block == header && !blocks.contains(&else_block))
        || (else_block == header && !blocks.contains(&then_block))
}

fn is_reducible_loop(cfg: &Cfg, header: BlockRef, blocks: &BTreeSet<BlockRef>) -> bool {
    blocks.iter().all(|block| {
        if *block == header {
            true
        } else {
            cfg.preds[block.index()].iter().all(|edge_ref| {
                let pred = cfg.edges[edge_ref.index()].from;
                !cfg.reachable_blocks.contains(&pred) || blocks.contains(&pred)
            })
        }
    })
}
