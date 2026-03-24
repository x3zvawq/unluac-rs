//! 这个文件实现短路候选提取。
//!
//! 规则保持保守：优先识别一臂 branch 沿 `then_entry` 形成的链，并结合 phi merge
//! 判断它是否更像值产生型控制流。

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::cfg::{Cfg, DataflowFacts, GraphFacts};
use crate::transformer::{LowInstr, LoweredProto, Reg};

use super::common::{BranchCandidate, BranchKind, ShortCircuitCandidate, ShortCircuitKindHint};
use super::helpers::dominates;

pub(super) fn analyze_short_circuits(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    branch_candidates: &[BranchCandidate],
) -> Vec<ShortCircuitCandidate> {
    let branch_by_header = branch_candidates
        .iter()
        .filter(|candidate| is_short_circuit_seed(candidate))
        .map(|candidate| (candidate.header, candidate))
        .collect::<BTreeMap<_, _>>();

    let mut candidates = Vec::new();
    for candidate in branch_candidates {
        if !is_short_circuit_seed(candidate) {
            continue;
        }

        let Some(mut current) = branch_by_header.get(&candidate.header).copied() else {
            continue;
        };
        let mut visited = BTreeSet::new();
        let mut kind_hints = Vec::new();
        let mut chain_len = 0usize;
        let mut merge = current
            .merge
            .expect("short-circuit seed should always have a merge");

        loop {
            if !visited.insert(current.header) {
                break;
            }

            chain_len += 1;
            merge = current
                .merge
                .expect("short-circuit seed should always have a merge");
            kind_hints.push(infer_kind_hint(proto, cfg, current.header));

            let Some(next) = branch_by_header.get(&current.then_entry).copied() else {
                break;
            };
            current = next;
        }

        let blocks = collect_short_circuit_blocks(
            cfg,
            &graph_facts.dominator_tree.parent,
            candidate.header,
            merge,
        );

        let result_reg = infer_result_reg(dataflow, merge, &blocks);
        if result_reg.is_none() && chain_len == 1 {
            continue;
        }
        if result_reg.is_none() && blocks.len() == 1 {
            continue;
        }

        let reducible = is_reducible_candidate(cfg, candidate.header, &blocks);
        candidates.push(ShortCircuitCandidate {
            header: candidate.header,
            blocks,
            merge,
            result_reg,
            kind_hint: merge_kind_hints(&kind_hints),
            reducible,
        });
    }

    candidates.sort_by_key(|candidate| {
        (
            candidate.header,
            candidate.merge,
            candidate.result_reg.map(Reg::index),
        )
    });
    candidates.dedup_by(|left, right| {
        left.header == right.header
            && left.merge == right.merge
            && left.blocks == right.blocks
            && left.result_reg == right.result_reg
            && left.kind_hint == right.kind_hint
    });
    candidates
}

fn is_short_circuit_seed(candidate: &BranchCandidate) -> bool {
    candidate.kind == BranchKind::IfThen && candidate.merge.is_some()
}

fn infer_kind_hint(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: crate::cfg::BlockRef,
) -> ShortCircuitKindHint {
    match cfg.terminator(&proto.instrs, header) {
        Some(LowInstr::Branch(instr)) if instr.cond.negated => ShortCircuitKindHint::AndLike,
        Some(LowInstr::Branch(_instr)) => ShortCircuitKindHint::OrLike,
        _ => ShortCircuitKindHint::Unknown,
    }
}

fn merge_kind_hints(kind_hints: &[ShortCircuitKindHint]) -> ShortCircuitKindHint {
    let Some(first) = kind_hints.first().copied() else {
        return ShortCircuitKindHint::Unknown;
    };
    if kind_hints.iter().all(|kind| *kind == first) {
        first
    } else {
        ShortCircuitKindHint::Unknown
    }
}

fn infer_result_reg(
    dataflow: &DataflowFacts,
    merge: crate::cfg::BlockRef,
    blocks: &BTreeSet<crate::cfg::BlockRef>,
) -> Option<Reg> {
    let mut result_regs = dataflow
        .phi_candidates
        .iter()
        .filter(|phi| phi.block == merge)
        .filter(|phi| {
            phi.incoming
                .iter()
                .filter(|incoming| blocks.contains(&incoming.pred))
                .count()
                >= 2
        })
        .map(|phi| phi.reg)
        .collect::<Vec<_>>();

    result_regs.sort_by_key(|reg| reg.index());
    result_regs.dedup();
    match result_regs.as_slice() {
        [reg] => Some(*reg),
        _ => None,
    }
}

fn is_reducible_candidate(
    cfg: &Cfg,
    header: crate::cfg::BlockRef,
    blocks: &BTreeSet<crate::cfg::BlockRef>,
) -> bool {
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

fn collect_short_circuit_blocks(
    cfg: &Cfg,
    dom_parent: &[Option<crate::cfg::BlockRef>],
    header: crate::cfg::BlockRef,
    merge: crate::cfg::BlockRef,
) -> BTreeSet<crate::cfg::BlockRef> {
    let mut blocks = BTreeSet::from([header]);
    let mut worklist = VecDeque::new();

    for edge_ref in &cfg.succs[header.index()] {
        let succ = cfg.edges[edge_ref.index()].to;
        if succ != merge {
            worklist.push_back(succ);
        }
    }

    while let Some(block) = worklist.pop_front() {
        if block == merge
            || block == cfg.exit_block
            || !cfg.reachable_blocks.contains(&block)
            || !dominates(dom_parent, header, block)
            || !blocks.insert(block)
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
