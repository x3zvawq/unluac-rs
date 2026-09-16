//! 提取条件出口型短路链与值合流型短路 DAG。
//!
//! 消费 branch 骨架、Dataflow phi 和 CFG 查询，发布候选及其结构约束；最终选择
//! 逻辑表达式、if 或赋值仍由 HIR 决定。branch_exit 处理 if a and b 这类真假出口，
//! value_merge 处理 (a and b) or (c and d) 这类共享 continuation。
//! 候选 DAG 必须无环，循环回边留给 loop/branch owner。

mod branch_exit;
mod shared;
mod value_merge;

use std::collections::{BTreeMap, BTreeSet};

use crate::structure::{BlockRef, Cfg, DataflowFacts, GraphFacts};
use crate::transformer::{LoweredProto, Reg};

use super::common::{BranchCandidate, IrreducibleRegion, LoopCandidate, ShortCircuitCandidate};

pub(super) use branch_exit::{ClosedControlDagEvidence, ConditionArcEvidence};

struct ReverseReachability {
    marks: Vec<u32>,
    reachable: Vec<bool>,
    pending: Vec<BlockRef>,
    next_epoch: u32,
}

impl ReverseReachability {
    fn new(cfg: &Cfg) -> Self {
        let mut reachable = vec![false; cfg.blocks.len()];
        for block in &cfg.reachable_blocks {
            reachable[block.index()] = true;
        }
        Self {
            marks: vec![0; cfg.blocks.len()],
            reachable,
            pending: Vec::with_capacity(cfg.blocks.len()),
            next_epoch: 1,
        }
    }

    fn mark_reaching(&mut self, cfg: &Cfg, target: BlockRef) -> u32 {
        if self.next_epoch == u32::MAX {
            self.marks.fill(0);
            self.next_epoch = 1;
        }
        let epoch = self.next_epoch;
        self.next_epoch += 1;
        self.pending.clear();
        if let Some(mark) = self.marks.get_mut(target.index()) {
            *mark = epoch;
            self.pending.push(target);
        }

        while let Some(block) = self.pending.pop() {
            for edge in &cfg.preds[block.index()] {
                let predecessor = cfg.edges[edge.index()].from;
                if !self.reachable[predecessor.index()] || self.marks[predecessor.index()] == epoch
                {
                    continue;
                }
                self.marks[predecessor.index()] = epoch;
                self.pending.push(predecessor);
            }
        }
        epoch
    }

    fn reaches(&self, block: BlockRef, epoch: u32) -> bool {
        self.marks.get(block.index()).copied() == Some(epoch)
    }
}

pub(super) struct ClosedControlDagContext<'a> {
    pub(super) proto: &'a LoweredProto,
    pub(super) cfg: &'a Cfg,
    pub(super) graph_facts: &'a GraphFacts,
    pub(super) dataflow: &'a DataflowFacts,
}

pub(super) fn analyze_closed_control_dags(
    context: ClosedControlDagContext<'_>,
    irreducible_regions: &[IrreducibleRegion],
    loops: &[LoopCandidate],
    branches: &[BranchCandidate],
    value_decision_blocks: &BTreeSet<BlockRef>,
) -> Vec<ClosedControlDagEvidence> {
    let ClosedControlDagContext {
        proto,
        cfg,
        graph_facts,
        dataflow,
    } = context;
    let mut evidence = branch_exit::analyze_closed_control_dag_candidates(
        proto,
        cfg,
        graph_facts,
        dataflow,
        irreducible_regions,
        loops,
    );
    evidence.extend(branch_exit::analyze_closed_branch_components(
        proto,
        cfg,
        graph_facts,
        dataflow,
        irreducible_regions,
        loops,
        value_decision_blocks,
    ));
    evidence.extend(branch_exit::analyze_closed_branch_control_dag_candidates(
        proto,
        cfg,
        graph_facts,
        dataflow,
        branches,
    ));
    evidence
}

pub(super) fn analyze_short_circuits(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    branch_candidates: &[BranchCandidate],
) -> Vec<ShortCircuitCandidate> {
    let branch_by_header = branch_candidates
        .iter()
        .map(|candidate| (candidate.header, candidate))
        .collect::<BTreeMap<BlockRef, _>>();

    // 值 decision 的 entry 是表达式 body 的语义边界。条件 DAG 若继续穿过这个
    // header，会把 body 自己的判断也吞成外层条件，最终得到三个以上的伪出口。
    // 先提取 value evidence，再让条件恢复把这些 entry 当作 opaque exit。
    let value_candidates = value_merge::analyze_value_merge_candidates(
        proto,
        cfg,
        graph_facts,
        dataflow,
        &branch_by_header,
    );
    let value_decision_headers = value_candidates
        .iter()
        .map(|candidate| candidate.header)
        .collect::<BTreeSet<_>>();

    let mut candidates = branch_exit::analyze_linear_branch_exit_candidates(
        proto,
        cfg,
        &branch_by_header,
        branch_candidates,
    );
    candidates.extend(branch_exit::analyze_if_else_branch_exit_candidates(
        proto,
        cfg,
        &branch_by_header,
        branch_candidates,
    ));
    let closed_linear_interiors =
        branch_exit::closed_linear_interior_headers(cfg, &branch_by_header, &candidates);
    candidates.extend(branch_exit::analyze_guard_branch_exit_dag_candidates(
        proto,
        cfg,
        graph_facts,
        &branch_by_header,
        branch_candidates,
        &closed_linear_interiors,
        &value_decision_headers,
    ));
    candidates.extend(value_candidates);
    candidates = candidates
        .into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    candidates.sort_by_key(|candidate| {
        (
            candidate.header,
            candidate.blocks.len(),
            candidate.nodes.len(),
            candidate.result_reg.map(Reg::index),
        )
    });
    candidates
}

pub(super) fn analyze_cfg_linear_branch_exits(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch_candidates: &[BranchCandidate],
) -> Vec<ShortCircuitCandidate> {
    let branch_by_header = branch_candidates
        .iter()
        .map(|candidate| (candidate.header, candidate))
        .collect::<BTreeMap<BlockRef, _>>();
    branch_exit::analyze_cfg_linear_branch_exit_candidates(
        proto,
        cfg,
        &branch_by_header,
        branch_candidates,
    )
}
