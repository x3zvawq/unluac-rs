//! 这个文件提取普通 branch 的值合流候选。
//!
//! 这个 pass 依赖 CFG / GraphFacts / Dataflow 已经给好的 branch 骨架和 phi 事实，
//! 负责把“结构臂归属 + HIR 真正要用的 canonical SSA 身份”一次性前移到 StructureFacts。
//! 它不会越权做 decision/alias 最终选择，那一步仍留给 HIR。
//!
//! 例子：
//! - `if cond then x = 1 else x = 2 end` 会把 merge phi 记录成
//!   `then_arm = {preds, values_of_1}`、`else_arm = {preds, values_of_2}`
//! - 这样 HIR 只消费 `then/else` 两臂已经分好的 SSA values，不再自己回头拆
//!   `phi.incoming`

use std::collections::{BTreeMap, BTreeSet};

use crate::structure::{BlockRef, Cfg, DataflowFacts, GraphFacts};

use super::common::{
    BranchCandidate, BranchKind, BranchValueMergeCandidate, LoopCandidate, ShortCircuitCandidate,
    ShortCircuitExit,
};
use super::helpers::collect_merge_arm_preds;
use super::phi_facts::{BranchValueMergeContext, branch_value_merges_in_block};
use super::{branches::for_loop_body_entry, branches::for_loop_exit_owner};

#[derive(Debug, Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
enum CandidateSource {
    BranchRegion,
    BranchExitShortCircuit,
}

pub(super) fn analyze_branch_value_merges(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    branch_candidates: &[BranchCandidate],
    short_circuit_candidates: &[ShortCircuitCandidate],
    loop_candidates: &[LoopCandidate],
) -> Vec<BranchValueMergeCandidate> {
    let loop_owned_preds_by_header = loop_owned_preds_by_header(loop_candidates);
    let short_circuit_merges = short_circuit_candidates
        .iter()
        .filter_map(|candidate| match candidate.exit {
            ShortCircuitExit::ValueMerge(merge) => {
                Some((candidate.header, merge, candidate.result_reg))
            }
            ShortCircuitExit::BranchExit { .. } => None,
        })
        .collect::<BTreeSet<_>>();

    let candidates = branch_candidates
        .iter()
        .filter_map(|branch_candidate| {
            analyze_branch_value_merge_candidate(
                cfg,
                graph_facts,
                dataflow,
                branch_candidate,
                &short_circuit_merges,
                &loop_owned_preds_by_header,
                loop_candidates,
            )
        })
        .map(|candidate| (CandidateSource::BranchRegion, candidate))
        .chain(
            analyze_branch_exit_short_circuit_branch_value_merges(
                cfg,
                graph_facts,
                dataflow,
                short_circuit_candidates,
                &loop_owned_preds_by_header,
            )
            .into_iter()
            .map(|candidate| (CandidateSource::BranchExitShortCircuit, candidate)),
        );

    let mut best_by_region =
        BTreeMap::<(BlockRef, BlockRef), (CandidateSource, BranchValueMergeCandidate)>::new();
    for (source, candidate) in candidates {
        let key = (candidate.header, candidate.merge);
        match best_by_region.get(&key) {
            Some((existing_source, existing))
                if (existing.values.len(), *existing_source)
                    >= (candidate.values.len(), source) => {}
            _ => {
                best_by_region.insert(key, (source, candidate));
            }
        }
    }

    best_by_region
        .into_values()
        .map(|(_, candidate)| candidate)
        .collect()
}

fn analyze_branch_exit_short_circuit_branch_value_merges(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    short_circuit_candidates: &[ShortCircuitCandidate],
    loop_owned_preds_by_header: &BTreeMap<BlockRef, BTreeSet<BlockRef>>,
) -> Vec<BranchValueMergeCandidate> {
    let mut candidates = Vec::new();

    for short in short_circuit_candidates {
        let ShortCircuitExit::BranchExit { truthy, falsy } = short.exit else {
            continue;
        };

        // early-return guard 的 body 不一定被 continuation 后支配，但只要可达关系是
        // 单向的，另一出口仍是实际 merge；双臂互不可达时才取共同后支配点。
        let merge = if graph_facts.post_dominates(falsy, truthy) {
            falsy
        } else if graph_facts.post_dominates(truthy, falsy) {
            truthy
        } else {
            match (cfg.can_reach(truthy, falsy), cfg.can_reach(falsy, truthy)) {
                (true, false) => falsy,
                (false, true) => truthy,
                _ => {
                    let Some(merge) = graph_facts.nearest_common_postdom(truthy, falsy) else {
                        continue;
                    };
                    merge
                }
            }
        };
        if merge == cfg.exit_block || dataflow.phi_candidates_in_block(merge).is_empty() {
            continue;
        }

        // 短路根表达的是完整条件 DAG。两侧在 merge 前各自到达哪些 predecessor，
        // 应由这份根事实一次性划分；末端 branch header 可能被更早的短路边绕过，
        // 因而不能用“header 支配 merge”作为完整性的必要条件。
        let then_preds = if truthy == merge {
            short.branch_exit_leaf_preds(true)
        } else {
            collect_merge_arm_preds(cfg, truthy, merge)
        };
        let else_preds = if falsy == merge {
            short.branch_exit_leaf_preds(false)
        } else {
            collect_merge_arm_preds(cfg, falsy, merge)
        };
        if then_preds.is_empty() || else_preds.is_empty() || !then_preds.is_disjoint(&else_preds) {
            continue;
        }

        let values = branch_value_merges_in_block(
            &BranchValueMergeContext::new(cfg, short.header, graph_facts, dataflow),
            merge,
            &then_preds,
            &else_preds,
            loop_owned_preds_by_header.get(&merge),
        );

        if !values.is_empty() {
            candidates.push(BranchValueMergeCandidate {
                header: short.header,
                merge,
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
    loop_owned_preds_by_header: &BTreeMap<BlockRef, BTreeSet<BlockRef>>,
    loop_candidates: &[LoopCandidate],
) -> Option<BranchValueMergeCandidate> {
    let merge = branch.merge?;
    if dataflow.phi_candidates_in_block(merge).is_empty()
        || (!graph_facts.dominates(branch.header, merge)
            && !loop_owned_preds_by_header.contains_key(&merge))
    {
        return None;
    }

    let (then_preds, explicit_else_preds) =
        branch_merge_preds(cfg, graph_facts, branch, merge, loop_candidates);

    // IfElse：两臂的 merge predecessors 分别来自 then/else 侧。
    // IfThen：只有 then 侧有 merge preds，else 侧相当于 header 直接跳到 merge。
    // 需要用 header 作为 else_preds，这样 phi 的"保留当前值"语义才能被正确捕获。
    // Guard 的另一侧是外部 continuation，不是由两臂共同流入的 merge；这类形状
    // 没有可分配给 then/else 的值合流 owner。
    let header_as_else_preds;
    let else_preds = match branch.kind {
        BranchKind::IfElse => &explicit_else_preds,
        BranchKind::IfThen => {
            header_as_else_preds = BTreeSet::from([branch.header]);
            &header_as_else_preds
        }
        BranchKind::Guard => return None,
    };

    if then_preds.is_empty() || else_preds.is_empty() || !then_preds.is_disjoint(else_preds) {
        return None;
    }

    let values = branch_value_merges_in_block(
        &BranchValueMergeContext::new(cfg, branch.header, graph_facts, dataflow),
        merge,
        &then_preds,
        else_preds,
        loop_owned_preds_by_header.get(&merge),
    )
    .into_iter()
    .filter(|value| !short_circuit_merges.contains(&(branch.header, merge, Some(value.reg))))
    .collect::<Vec<_>>();

    (!values.is_empty()).then_some(BranchValueMergeCandidate {
        header: branch.header,
        merge,
        values,
    })
}

fn branch_merge_preds(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    candidate: &BranchCandidate,
    merge: BlockRef,
    loop_candidates: &[LoopCandidate],
) -> (BTreeSet<BlockRef>, BTreeSet<BlockRef>) {
    let mut then_preds = collect_merge_arm_preds(cfg, candidate.then_entry, merge);
    let Some(else_entry) = candidate.else_entry else {
        return (then_preds, BTreeSet::new());
    };
    let mut else_preds = collect_merge_arm_preds(cfg, else_entry, merge);
    let disambiguate_overlap = graph_facts
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
        });
    if !disambiguate_overlap {
        return (then_preds, else_preds);
    }

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

fn loop_owned_preds_by_header(
    loop_candidates: &[LoopCandidate],
) -> BTreeMap<BlockRef, BTreeSet<BlockRef>> {
    let mut by_header = BTreeMap::<BlockRef, BTreeSet<BlockRef>>::new();
    for candidate in loop_candidates {
        by_header
            .entry(candidate.header)
            .or_default()
            .extend(candidate.blocks.iter().copied());
    }
    by_header
}
