//! 这个文件集中声明 StructureFacts 层的共享类型。
//!
//! 这些类型只表达“结构候选”和“必须保留的约束”，刻意不提前做最终语法决定，
//! 这样 HIR 还能基于完整证据再做一次更稳的恢复取舍。

use std::collections::BTreeSet;

use crate::cfg::{BlockRef, EdgeRef};
use crate::transformer::{InstrRef, Reg};

/// 一个 proto 的结构候选集合，以及它的子 proto 结果。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct StructureFacts {
    pub branch_candidates: Vec<BranchCandidate>,
    pub loop_candidates: Vec<LoopCandidate>,
    pub short_circuit_candidates: Vec<ShortCircuitCandidate>,
    pub goto_requirements: Vec<GotoRequirement>,
    pub region_facts: Vec<RegionFact>,
    pub scope_candidates: Vec<ScopeCandidate>,
    pub children: Vec<StructureFacts>,
}

/// 一个分支结构候选。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchCandidate {
    pub header: BlockRef,
    pub then_entry: BlockRef,
    pub else_entry: Option<BlockRef>,
    pub merge: Option<BlockRef>,
    pub kind: BranchKind,
    pub invert_hint: bool,
}

/// 分支形态提示。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum BranchKind {
    IfThen,
    IfElse,
    Guard,
}

/// 一个循环候选。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopCandidate {
    pub header: BlockRef,
    pub blocks: BTreeSet<BlockRef>,
    pub backedges: Vec<EdgeRef>,
    pub exits: BTreeSet<BlockRef>,
    pub continue_target: Option<BlockRef>,
    pub kind_hint: LoopKindHint,
    pub reducible: bool,
}

/// 循环形态提示。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum LoopKindHint {
    WhileLike,
    RepeatLike,
    NumericForLike,
    GenericForLike,
    Unknown,
}

/// 一个短路表达式候选。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShortCircuitCandidate {
    pub header: BlockRef,
    pub blocks: BTreeSet<BlockRef>,
    pub merge: BlockRef,
    pub result_reg: Option<Reg>,
    pub kind_hint: ShortCircuitKindHint,
    pub reducible: bool,
}

/// 短路表达式形态提示。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ShortCircuitKindHint {
    AndLike,
    OrLike,
    Unknown,
}

/// 一个必须保留跳转的要求。
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct GotoRequirement {
    pub from: BlockRef,
    pub to: BlockRef,
    pub reason: GotoReason,
}

/// 为什么这条边当前不能被结构候选吸收。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum GotoReason {
    IrreducibleFlow,
    CrossStructureJump,
    MultiEntryRegion,
    UnstructuredBreakLike,
    UnstructuredContinueLike,
}

/// 某片 block 集合的区域事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegionFact {
    pub blocks: BTreeSet<BlockRef>,
    pub entry: BlockRef,
    pub exits: BTreeSet<BlockRef>,
    pub kind: RegionKind,
    pub reducible: bool,
    pub structureable: bool,
}

/// 区域种类。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum RegionKind {
    Linear,
    BranchRegion,
    LoopRegion,
    Irreducible,
}

/// 一个潜在的词法 scope。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScopeCandidate {
    pub entry: BlockRef,
    pub exit: Option<BlockRef>,
    pub close_points: Vec<InstrRef>,
    pub kind: ScopeKind,
}

/// scope 形态。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ScopeKind {
    BlockScope,
    LoopScope,
    BranchScope,
}
