//! 这个文件提取普通 branch 的值合流候选。
//!
//! `BranchCandidate` 只回答控制骨架，而 merge 点上的 phi 只回答“这里发生了值合流”。
//! 真正让 HIR 少走弯路的关键信息，是“这批 phi 到底是不是某个结构化 if/else 的两臂
//! 产物”。这里就专门把这层关系显式化，避免 HIR 再从 branch + phi 里反推一次。

use std::collections::{BTreeSet, VecDeque};

use crate::cfg::{BlockRef, Cfg, DataflowFacts, GraphFacts};

use super::common::{
    BranchCandidate, BranchKind, BranchValueMergeCandidate, BranchValueMergeValue,
    ShortCircuitCandidate, ShortCircuitExit, ShortCircuitTarget,
};
use super::helpers::{can_reach, dominates};

pub(super) fn analyze_branch_value_merges(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    branch_candidates: &[BranchCandidate],
    short_circuit_candidates: &[ShortCircuitCandidate],
) -> Vec<BranchValueMergeCandidate> {
    let short_circuit_merges = short_circuit_candidates
        .iter()
        .filter_map(|candidate| match candidate.exit {
            ShortCircuitExit::ValueMerge(merge) => {
                Some((candidate.header, merge, candidate.result_reg))
            }
            ShortCircuitExit::BranchExit { .. } => None,
        })
        .collect::<BTreeSet<_>>();

    let mut candidates = Vec::new();

    for branch in branch_candidates {
        let Some(candidate) = analyze_branch_value_merge_candidate(
            cfg,
            graph_facts,
            dataflow,
            branch,
            &short_circuit_merges,
        ) else {
            continue;
        };
        candidates.push(candidate);
    }

    candidates.extend(analyze_guard_short_circuit_branch_value_merges(
        cfg,
        graph_facts,
        dataflow,
        short_circuit_candidates,
    ));

    candidates.sort_by_key(|candidate| (candidate.header, candidate.merge));
    candidates
}

fn analyze_guard_short_circuit_branch_value_merges(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    short_circuit_candidates: &[ShortCircuitCandidate],
) -> Vec<BranchValueMergeCandidate> {
    let mut candidates = Vec::new();

    for short in short_circuit_candidates {
        let ShortCircuitExit::BranchExit { truthy, falsy } = short.exit else {
            continue;
        };
        if !can_reach(cfg, truthy, falsy) || can_reach(cfg, falsy, truthy) {
            continue;
        }

        let then_preds =
            collect_merge_arm_preds(cfg, &graph_facts.dominator_tree.parent, truthy, falsy);
        let else_preds = collect_branch_exit_leaf_preds(short, false);
        if then_preds.is_empty() || else_preds.is_empty() || !then_preds.is_disjoint(&else_preds) {
            continue;
        }

        let mut values = Vec::new();
        for phi in dataflow
            .phi_candidates
            .iter()
            .filter(|phi| phi.block == falsy)
        {
            let mut phi_then_preds = BTreeSet::new();
            let mut phi_else_preds = BTreeSet::new();
            let mut valid = true;

            for incoming in &phi.incoming {
                if then_preds.contains(&incoming.pred) {
                    phi_then_preds.insert(incoming.pred);
                } else if else_preds.contains(&incoming.pred) {
                    phi_else_preds.insert(incoming.pred);
                } else {
                    valid = false;
                    break;
                }
            }

            if !valid || phi_then_preds.is_empty() || phi_else_preds.is_empty() {
                continue;
            }

            values.push(BranchValueMergeValue {
                phi_id: phi.id,
                reg: phi.reg,
                then_preds: phi_then_preds,
                else_preds: phi_else_preds,
            });
        }

        if !values.is_empty() {
            candidates.push(BranchValueMergeCandidate {
                header: short.header,
                merge: falsy,
                values,
            });
        }
    }

    candidates
}

fn analyze_branch_value_merge_candidate(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    branch: &BranchCandidate,
    short_circuit_merges: &BTreeSet<(BlockRef, BlockRef, Option<crate::transformer::Reg>)>,
) -> Option<BranchValueMergeCandidate> {
    if branch.kind != BranchKind::IfElse {
        return None;
    }

    let merge = branch.merge?;
    let else_entry = branch.else_entry?;
    let then_preds = collect_merge_arm_preds(
        cfg,
        &graph_facts.dominator_tree.parent,
        branch.then_entry,
        merge,
    );
    let else_preds =
        collect_merge_arm_preds(cfg, &graph_facts.dominator_tree.parent, else_entry, merge);
    if then_preds.is_empty() || else_preds.is_empty() || !then_preds.is_disjoint(&else_preds) {
        return None;
    }

    let mut values = Vec::new();
    for phi in dataflow
        .phi_candidates
        .iter()
        .filter(|phi| phi.block == merge)
    {
        if short_circuit_merges.contains(&(branch.header, merge, Some(phi.reg))) {
            continue;
        }

        let mut phi_then_preds = BTreeSet::new();
        let mut phi_else_preds = BTreeSet::new();
        let mut valid = true;

        for incoming in &phi.incoming {
            if then_preds.contains(&incoming.pred) {
                phi_then_preds.insert(incoming.pred);
            } else if else_preds.contains(&incoming.pred) {
                phi_else_preds.insert(incoming.pred);
            } else {
                valid = false;
                break;
            }
        }

        if !valid || phi_then_preds.is_empty() || phi_else_preds.is_empty() {
            continue;
        }

        values.push(BranchValueMergeValue {
            phi_id: phi.id,
            reg: phi.reg,
            then_preds: phi_then_preds,
            else_preds: phi_else_preds,
        });
    }

    (!values.is_empty()).then_some(BranchValueMergeCandidate {
        header: branch.header,
        merge,
        values,
    })
}

fn collect_merge_arm_preds(
    cfg: &Cfg,
    dom_parent: &[Option<BlockRef>],
    entry: BlockRef,
    merge: BlockRef,
) -> BTreeSet<BlockRef> {
    let mut visited = BTreeSet::new();
    let mut merge_preds = BTreeSet::new();
    let mut worklist = VecDeque::from([entry]);

    while let Some(block) = worklist.pop_front() {
        if !cfg.reachable_blocks.contains(&block)
            || block == merge
            || !visited.insert(block)
            || !dominates(dom_parent, entry, block)
        {
            continue;
        }

        for edge_ref in &cfg.succs[block.index()] {
            let succ = cfg.edges[edge_ref.index()].to;
            if succ == merge {
                merge_preds.insert(block);
            } else {
                worklist.push_back(succ);
            }
        }
    }

    merge_preds
}

fn collect_branch_exit_leaf_preds(
    short: &ShortCircuitCandidate,
    want_truthy: bool,
) -> BTreeSet<BlockRef> {
    short
        .nodes
        .iter()
        .filter_map(|node| {
            let matches_exit = if want_truthy {
                matches!(&node.truthy, ShortCircuitTarget::TruthyExit)
                    || matches!(&node.falsy, ShortCircuitTarget::TruthyExit)
            } else {
                matches!(&node.truthy, ShortCircuitTarget::FalsyExit)
                    || matches!(&node.falsy, ShortCircuitTarget::FalsyExit)
            };
            matches_exit.then_some(node.header)
        })
        .collect()
}
