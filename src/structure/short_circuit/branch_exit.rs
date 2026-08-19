//! 这个文件负责“条件出口型”短路候选提取。
//!
//! 它解决的是 `if a and b then ... end`、`if a or b then ... end`，以及
//! `if a or b then ... else ... end` 这类最终直接流向“整体为真/整体为假”两个出口的
//! 形状。这里特意不碰 value merge，让“条件出口识别”和“值合流 DAG 提取”各自拥有
//! 单一职责。
//!
//! 它依赖 branch 候选、支配/后支配关系和共享线性跟随规则，只负责回答
//! “这一串判断是不是一个纯条件出口短路”；它不会越权去拆 phi，也不会替 value merge
//! 做值来源分类。
//!
//! 例子：
//! - `if a and b then return end` 会产出“整体真时流向 then、整体假时流向 fallthrough”的
//!   短路候选
//! - `if a or b then body() end` 会产出“整体真时进入 body、整体假时直接跳过”的候选
//!
//! `IfElse` 链的每个 root 都可能看到同一条长后缀，因此前缀选择只前向扫描一次：
//! 增量维护当前前缀的外部出口计数和严格真假出口约束，仍保留最长候选及其原始
//! strict-before-relaxed 优先级，最后才构造 nodes/blocks。

use std::collections::{BTreeMap, BTreeSet};

use crate::structure::{BlockRef, Cfg, DataflowFacts, EdgeRef, GraphFacts, PostDominatorTree};
use crate::transformer::{LowInstr, LoweredProto};

use super::super::common::{
    BranchCandidate, BranchKind, IrreducibleRegion, LoopCandidate, ShortCircuitCandidate,
    ShortCircuitExit, ShortCircuitNode, ShortCircuitNodeRef, ShortCircuitTarget,
};
use super::ReverseReachability;
use super::shared::{
    LinearFollowCtx, LinearFollowTarget, is_reducible_candidate, prefer_short_circuit_candidate,
    short_circuit_nodes_are_acyclic, truthy_falsy_targets,
};

mod closed_components;
mod closed_dag;
mod guard_builder;
mod linear_candidates;
mod linear_chain;

pub(super) use closed_components::{
    analyze_closed_branch_components, analyze_closed_branch_control_dag_candidates,
    analyze_closed_control_dag_candidates,
};
use closed_dag::*;
use guard_builder::*;
pub(super) use linear_candidates::{
    analyze_cfg_linear_branch_exit_candidates, analyze_guard_branch_exit_dag_candidates,
    analyze_if_else_branch_exit_candidates, analyze_linear_branch_exit_candidates,
    closed_linear_interior_headers,
};
use linear_chain::*;

/// raw CFG condition arc 的物理路径证据。
///
/// `source`/`target` 描述逻辑 decision DAG，`edges` 则保留两者之间实际执行的 CFG
/// 路径。connector 只能是无可观察副作用的单后继 block；后续 final plan 必须冻结并
/// 消费这条路径，不能只凭逻辑 target 跳过其中的 value action。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::structure) struct ConditionArcEvidence {
    pub(in crate::structure) source: ShortCircuitNodeRef,
    pub(in crate::structure) truthy: bool,
    pub(in crate::structure) edges: Vec<EdgeRef>,
    pub(in crate::structure) connector_blocks: Vec<BlockRef>,
    pub(in crate::structure) target: ShortCircuitTarget,
}

/// 不依赖最终 `BranchCandidate` 的 closed control DAG evidence。
///
/// 只有单入口、无环、恰好两个出口的完整候选会到达这里。`candidate.blocks` 同时包含
/// decision 与 connector blocks，`arcs` 保存每条逻辑边对应的物理 CFG route；raw
/// evidence 本身不会创建 branch owner。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::structure) struct ClosedControlDagEvidence {
    pub(in crate::structure) candidate: ShortCircuitCandidate,
    pub(in crate::structure) arcs: Vec<ConditionArcEvidence>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RawConditionArc {
    source: BlockRef,
    truthy: bool,
    edges: Vec<EdgeRef>,
    connector_blocks: Vec<BlockRef>,
    target: RawConditionTarget,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RawConditionTarget {
    Node(BlockRef),
    Exit(BlockRef),
}

#[derive(Debug, Clone, Copy)]
struct RawConditionRoot {
    owner: usize,
    header: BlockRef,
}

#[derive(Debug, Clone, Copy)]
struct ConnectorClaim {
    owner: usize,
}

struct RawConditionIndex {
    roots: Vec<RawConditionRoot>,
    owner_by_block: Vec<Option<usize>>,
    arcs_by_header: Vec<Option<[RawConditionArc; 2]>>,
    owner_conflicts: Vec<bool>,
}

struct DenseConditionWorkspace {
    raw: DenseMarks,
    blocked: DenseMarks,
    retained: DenseMarks,
    node_refs: Vec<Option<ShortCircuitNodeRef>>,
}

struct DenseMarks {
    values: Vec<u32>,
    next_epoch: u32,
}

struct DenseNodeRefs {
    epochs: Vec<u32>,
    refs: Vec<ShortCircuitNodeRef>,
    next_epoch: u32,
}

impl DenseMarks {
    fn new(len: usize) -> Self {
        Self {
            values: vec![0; len],
            next_epoch: 1,
        }
    }

    fn begin(&mut self) -> u32 {
        if self.next_epoch == u32::MAX {
            self.values.fill(0);
            self.next_epoch = 1;
        }
        let epoch = self.next_epoch;
        self.next_epoch += 1;
        epoch
    }

    fn insert(&mut self, block: BlockRef, epoch: u32) -> bool {
        let slot = &mut self.values[block.index()];
        if *slot == epoch {
            false
        } else {
            *slot = epoch;
            true
        }
    }

    fn contains(&self, block: BlockRef, epoch: u32) -> bool {
        self.values.get(block.index()).copied() == Some(epoch)
    }
}

impl DenseNodeRefs {
    fn new(len: usize) -> Self {
        Self {
            epochs: vec![0; len],
            refs: vec![ShortCircuitNodeRef(0); len],
            next_epoch: 1,
        }
    }

    fn begin(&mut self) -> u32 {
        if self.next_epoch == u32::MAX {
            self.epochs.fill(0);
            self.next_epoch = 1;
        }
        let epoch = self.next_epoch;
        self.next_epoch += 1;
        epoch
    }

    fn get(&self, block: BlockRef, epoch: u32) -> Option<ShortCircuitNodeRef> {
        (self.epochs.get(block.index()).copied() == Some(epoch)).then(|| self.refs[block.index()])
    }

    fn insert(&mut self, block: BlockRef, node_ref: ShortCircuitNodeRef, epoch: u32) {
        self.epochs[block.index()] = epoch;
        self.refs[block.index()] = node_ref;
    }
}
