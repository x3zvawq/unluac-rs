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
    BranchKind, BranchRegionFact, BranchValueMergeCandidate, LoopCandidate, ShortCircuitCandidate,
    ShortCircuitExit,
};
use super::helpers::collect_merge_arm_preds;
use super::phi_facts::{BranchValueMergeContext, branch_value_merges_in_block};

#[derive(Debug, Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
enum CandidateSource {
    BranchRegion,
    GuardShortCircuit,
}

pub(super) fn analyze_branch_value_merges(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    branch_regions: &[BranchRegionFact],
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

    let candidates = branch_regions
        .iter()
        .filter_map(|branch_region| {
            analyze_branch_value_merge_candidate(
                cfg,
                graph_facts,
                dataflow,
                branch_region,
                &short_circuit_merges,
                &loop_owned_preds_by_header,
            )
        })
        .map(|candidate| (CandidateSource::BranchRegion, candidate))
        .chain(
            analyze_guard_short_circuit_branch_value_merges(
                cfg,
                graph_facts,
                dataflow,
                short_circuit_candidates,
                &loop_owned_preds_by_header,
            )
            .into_iter()
            .map(|candidate| (CandidateSource::GuardShortCircuit, candidate)),
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

fn analyze_guard_short_circuit_branch_value_merges(
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

        // 常规 guard 的 merge 会后支配 body，直接复用 GraphFacts 可避免为每个顺序
        // branch 重跑一次全图 BFS。early-return 等不满足后支配的形状才退回普通可达性；
        // 两个方向都保留，确保 LuaJIT 反向比较仍按真实控制流分类。
        let (truthy_reaches_falsy, falsy_reaches_truthy) =
            if graph_facts.post_dominates(falsy, truthy) {
                (true, false)
            } else if graph_facts.post_dominates(truthy, falsy) {
                (false, true)
            } else {
                (cfg.can_reach(truthy, falsy), cfg.can_reach(falsy, truthy))
            };
        let (body, merge, body_is_truthy) = match (truthy_reaches_falsy, falsy_reaches_truthy) {
            (true, false) => (truthy, falsy, true),
            (false, true) => (falsy, truthy, false),
            _ => continue,
        };

        let then_preds = collect_merge_arm_preds(cfg, body, merge);
        let else_preds = short.branch_exit_leaf_preds(!body_is_truthy);
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
    branch_region: &BranchRegionFact,
    short_circuit_merges: &BTreeSet<(BlockRef, BlockRef, Option<crate::transformer::Reg>)>,
    loop_owned_preds_by_header: &BTreeMap<BlockRef, BTreeSet<BlockRef>>,
) -> Option<BranchValueMergeCandidate> {
    let merge = branch_region.merge;
    let then_preds = &branch_region.then_merge_preds;

    // IfElse：两臂的 merge predecessors 分别来自 then/else 侧。
    // IfThen：只有 then 侧有 merge preds，else 侧相当于 header 直接跳到 merge。
    // 需要用 header 作为 else_preds，这样 phi 的"保留当前值"语义才能被正确捕获。
    // Guard 的另一侧是外部 continuation，不是由两臂共同流入的 merge；这类形状
    // 没有可分配给 then/else 的值合流 owner。
    let header_as_else_preds;
    let else_preds = match branch_region.kind {
        BranchKind::IfElse => &branch_region.else_merge_preds,
        BranchKind::IfThen => {
            header_as_else_preds = BTreeSet::from([branch_region.header]);
            &header_as_else_preds
        }
        BranchKind::Guard => return None,
    };

    if then_preds.is_empty() || else_preds.is_empty() || !then_preds.is_disjoint(else_preds) {
        return None;
    }

    let values = branch_value_merges_in_block(
        &BranchValueMergeContext::new(cfg, branch_region.header, graph_facts, dataflow),
        merge,
        then_preds,
        else_preds,
        loop_owned_preds_by_header.get(&merge),
    )
    .into_iter()
    .filter(|value| !short_circuit_merges.contains(&(branch_region.header, merge, Some(value.reg))))
    .collect::<Vec<_>>();

    (!values.is_empty()).then_some(BranchValueMergeCandidate {
        header: branch_region.header,
        merge,
        values,
    })
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
