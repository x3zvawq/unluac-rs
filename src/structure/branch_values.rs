//! 这个文件提取普通 branch 的值合流候选。
//!
//! 这个 pass 依赖 CFG / GraphFacts / Dataflow 已经给好的 branch 骨架和 phi 事实，
//! 负责把“结构臂归属 + HIR 真正要用的 def 身份”一次性前移到 StructureFacts。
//! 它不会越权做 decision/alias 最终选择，那一步仍留给 HIR。
//!
//! 例子：
//! - `if cond then x = 1 else x = 2 end` 会把 merge phi 记录成
//!   `then_arm = {preds, defs_of_1}`、`else_arm = {preds, defs_of_2}`
//! - 这样 HIR 只消费 `then/else` 两臂已经分好的 defs，不再自己回头拆 `phi.incoming`

use std::collections::BTreeSet;

use crate::cfg::{BlockRef, Cfg, DataflowFacts, GraphFacts};

use super::common::{
    BranchKind, BranchRegionFact, BranchValueMergeCandidate, ShortCircuitCandidate,
    ShortCircuitExit,
};
use super::helpers::collect_merge_arm_preds;
use super::phi_facts::branch_value_merges_in_block;

pub(super) fn analyze_branch_value_merges(
    cfg: &Cfg,
    _graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    branch_regions: &[BranchRegionFact],
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

    let mut candidates: Vec<_> = branch_regions
        .iter()
        .filter_map(|branch_region| {
            analyze_branch_value_merge_candidate(dataflow, branch_region, &short_circuit_merges)
        })
        .collect();

    candidates.extend(analyze_guard_short_circuit_branch_value_merges(
        cfg,
        dataflow,
        short_circuit_candidates,
    ));

    candidates.sort_by_key(|candidate| (candidate.header, candidate.merge));
    candidates
}

fn analyze_guard_short_circuit_branch_value_merges(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    short_circuit_candidates: &[ShortCircuitCandidate],
) -> Vec<BranchValueMergeCandidate> {
    let mut candidates = Vec::new();

    for short in short_circuit_candidates {
        let ShortCircuitExit::BranchExit { truthy, falsy } = short.exit else {
            continue;
        };

        // Determine direction: one exit must reach the other (the "body" flows
        // into the "merge"). Handle both truthy→falsy and falsy→truthy so that
        // inverted comparisons (e.g. LuaJIT ISGE) work correctly.
        let (body, merge, body_is_truthy) =
            if cfg.can_reach(truthy, falsy) && !cfg.can_reach(falsy, truthy) {
                (truthy, falsy, true)
            } else if cfg.can_reach(falsy, truthy) && !cfg.can_reach(truthy, falsy) {
                (falsy, truthy, false)
            } else {
                continue;
            };

        let then_preds = collect_merge_arm_preds(cfg, body, merge);
        let else_preds = short.branch_exit_leaf_preds(!body_is_truthy);
        if then_preds.is_empty() || else_preds.is_empty() || !then_preds.is_disjoint(&else_preds) {
            continue;
        }

        let values =
            branch_value_merges_in_block(short.header, dataflow, merge, &then_preds, &else_preds);

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
    dataflow: &DataflowFacts,
    branch_region: &BranchRegionFact,
    short_circuit_merges: &BTreeSet<(BlockRef, BlockRef, Option<crate::transformer::Reg>)>,
) -> Option<BranchValueMergeCandidate> {
    let merge = branch_region.merge;
    let then_preds = &branch_region.then_merge_preds;

    // IfElse：两臂的 merge predecessors 分别来自 then/else 侧。
    // IfThen：只有 then 侧有 merge preds，else 侧相当于 header 直接跳到 merge。
    // 需要用 header 作为 else_preds，这样 phi 的"保留当前值"语义才能被正确捕获。
    // Guard：暂不处理值合流。
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
        branch_region.header,
        dataflow,
        merge,
        then_preds,
        else_preds,
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
