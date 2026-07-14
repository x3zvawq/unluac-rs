//! 这个文件负责把平铺候选收敛成带稳定 identity 的 Structure plan。
//!
//! 候选提取可以保留同一 header 的多个合法形状；冲突消解必须在这里完成，HIR 只消费
//! 已选 owner，不能用临时 map 的覆盖顺序代替结构决策。

use std::collections::BTreeMap;

use super::{BlockRef, BranchCandidate, BranchValueMergeCandidate, LoopCandidate, StructurePlan};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BranchValueMergeId(pub usize);

impl BranchValueMergeId {
    pub const fn index(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LoopCandidateId(pub usize);

impl LoopCandidateId {
    pub const fn index(self) -> usize {
        self.0
    }
}

pub(super) fn build_structure_plan(
    branch_candidates: &[BranchCandidate],
    branch_value_merges: &[BranchValueMergeCandidate],
    loop_candidates: &[LoopCandidate],
) -> StructurePlan {
    let branch_value_merge_by_region = branch_value_merges
        .iter()
        .enumerate()
        .map(|(index, candidate)| {
            (
                (candidate.header, candidate.merge),
                BranchValueMergeId(index),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let branch_value_merge_by_header = branch_candidates
        .iter()
        .filter_map(|branch| {
            let merge = branch.merge?;
            branch_value_merge_by_region
                .get(&(branch.header, merge))
                .copied()
                .map(|id| (branch.header, id))
        })
        .collect();

    let mut loops_by_header = BTreeMap::<BlockRef, Vec<LoopCandidateId>>::new();
    for (index, candidate) in loop_candidates.iter().enumerate() {
        loops_by_header
            .entry(candidate.header)
            .or_default()
            .push(LoopCandidateId(index));
    }

    StructurePlan {
        branch_value_merge_by_header,
        branch_value_merge_by_region,
        loops_by_header,
    }
}
