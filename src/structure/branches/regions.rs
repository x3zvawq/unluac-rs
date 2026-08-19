//! 为已选 branch 计算 arm 区域并建立稠密 branch 索引；依赖图事实和 loop 边界，不负责 one-arm 形态判断；例如收集 then/else frontier。

use super::*;

pub(in crate::structure) fn analyze_branch_regions(
    _cfg: &Cfg,
    graph_facts: &GraphFacts,
    branch_candidates: &[BranchCandidate],
    single_pass_fences: &BTreeMap<BlockRef, SinglePassFenceFact>,
) -> Vec<BranchRegionFact> {
    let mut branch_regions = branch_candidates
        .iter()
        .filter_map(|candidate| {
            let merge = candidate.merge?;
            let single_pass_fence = single_pass_fences.get(&candidate.header).cloned();
            Some(BranchRegionFact::new(
                graph_facts,
                candidate.header,
                merge,
                candidate.kind,
                single_pass_fence,
            ))
        })
        .collect::<Vec<_>>();

    branch_regions.sort_by_key(|fact| (fact.header, fact.merge));
    branch_regions
}

/// Branch 分析只消费已经计算好的 dominance frontier 与稠密 loop containment。
///
/// `dominance_frontier[from]` 包含 `to` 时，存在一条由 `from` 支配的路径真实汇入
/// `to`；这正是 branch arm 可以把 `to` 当作词法 continuation 的证明。它比任意
/// CFG reachability 更强，也避免按每个 branch source 重新遍历整张图。
pub(super) struct BranchIndex<'a> {
    graph_facts: &'a GraphFacts,
    loop_candidates: &'a [LoopCandidate],
    loops_by_endpoint: Vec<Vec<usize>>,
    loops_by_body_block: Vec<Vec<usize>>,
    loop_headers: Vec<bool>,
    local_frontiers: Vec<FrontierShape>,
    exit_block: BlockRef,
}

#[derive(Clone, Copy)]
pub(super) enum FrontierShape {
    Empty,
    One(BlockRef),
    Multiple,
}

impl FrontierShape {
    pub(super) fn push(self, block: BlockRef) -> Self {
        match self {
            Self::Empty => Self::One(block),
            Self::One(existing) if existing == block => self,
            Self::One(_) | Self::Multiple => Self::Multiple,
        }
    }
}

impl<'a> BranchIndex<'a> {
    pub(super) fn new(
        cfg: &Cfg,
        graph_facts: &'a GraphFacts,
        loop_candidates: &'a [LoopCandidate],
    ) -> Self {
        let mut loops_by_endpoint = vec![Vec::new(); cfg.blocks.len()];
        let mut loops_by_body_block = vec![Vec::new(); cfg.blocks.len()];
        let mut loop_headers = vec![false; cfg.blocks.len()];
        let mut seen = vec![usize::MAX; cfg.blocks.len()];

        for (candidate_id, candidate) in loop_candidates.iter().enumerate() {
            loop_headers[candidate.header.index()] = true;
            for block in candidate.body_scope_blocks.iter().copied() {
                loops_by_body_block[block.index()].push(candidate_id);
            }

            let mut add_endpoint = |block: BlockRef| {
                if seen[block.index()] != candidate_id {
                    seen[block.index()] = candidate_id;
                    loops_by_endpoint[block.index()].push(candidate_id);
                }
            };
            for block in candidate
                .body_scope_blocks
                .iter()
                .chain(&candidate.blocks)
                .chain(&candidate.control_blocks)
                .copied()
            {
                add_endpoint(block);
            }
            if let Some(target) = candidate.continue_target {
                add_endpoint(target);
            }
            for edge in &candidate.backedges {
                add_endpoint(cfg.edges[edge.index()].from);
            }
        }

        let local_frontiers = graph_facts
            .dominance_frontier
            .iter()
            .map(|frontier| {
                frontier
                    .iter()
                    .copied()
                    .filter(|block| *block != cfg.exit_block && !loop_headers[block.index()])
                    .fold(FrontierShape::Empty, FrontierShape::push)
            })
            .collect();

        Self {
            graph_facts,
            loop_candidates,
            loops_by_endpoint,
            loops_by_body_block,
            loop_headers,
            local_frontiers,
            exit_block: cfg.exit_block,
        }
    }

    pub(super) fn endpoint_loops(
        &self,
        block: BlockRef,
    ) -> impl Iterator<Item = &'a LoopCandidate> + '_ {
        self.loops_by_endpoint[block.index()]
            .iter()
            .map(|candidate| &self.loop_candidates[*candidate])
    }

    pub(super) fn body_loops(
        &self,
        block: BlockRef,
    ) -> impl Iterator<Item = &'a LoopCandidate> + '_ {
        self.loops_by_body_block[block.index()]
            .iter()
            .map(|candidate| &self.loop_candidates[*candidate])
    }

    pub(super) fn joins_at(&self, from: BlockRef, target: BlockRef) -> bool {
        self.graph_facts
            .dominance_frontier
            .get(from.index())
            .is_some_and(|frontier| frontier.contains(&target))
    }

    pub(super) fn has_single_local_join(&self, from: BlockRef, target: BlockRef) -> bool {
        if target == self.exit_block || !self.joins_at(from, target) {
            return false;
        }
        match self.local_frontiers[from.index()] {
            FrontierShape::Empty => self.loop_headers[target.index()],
            FrontierShape::One(join) => join == target,
            FrontierShape::Multiple => false,
        }
    }
}
