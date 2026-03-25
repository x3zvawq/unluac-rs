//! 这个文件集中声明 StructureFacts 层的共享类型。
//!
//! 这些类型只表达“结构候选”和“必须保留的约束”，刻意不提前做最终语法决定，
//! 这样 HIR 还能基于完整证据再做一次更稳的恢复取舍。

use std::collections::BTreeSet;

use crate::cfg::{BlockRef, EdgeRef, PhiId};
use crate::transformer::{InstrRef, Reg};

/// 一个 proto 的结构候选集合，以及它的子 proto 结果。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct StructureFacts {
    pub branch_candidates: Vec<BranchCandidate>,
    pub branch_value_merge_candidates: Vec<BranchValueMergeCandidate>,
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

/// 一个普通 branch 在 merge 点上产生的值合流候选。
///
/// 它和 `ShortCircuitCandidate::ValueMerge` 的区别是：这里不假设整片区域更像 `and/or`，
/// 只表达“这个结构化 branch 的两臂分别给 merge 提供了哪些值版本”。这样 HIR 可以
/// 统一决定要不要继续当成同一 lvalue、还是保守物化成 `Decision` / 临时值。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchValueMergeCandidate {
    pub header: BlockRef,
    pub merge: BlockRef,
    pub values: Vec<BranchValueMergeValue>,
}

/// 一个 merge 值在两臂上的来源分布。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchValueMergeValue {
    pub phi_id: PhiId,
    pub reg: Reg,
    pub then_preds: BTreeSet<BlockRef>,
    pub else_preds: BTreeSet<BlockRef>,
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
    pub entry: ShortCircuitNodeRef,
    pub nodes: Vec<ShortCircuitNode>,
    pub exit: ShortCircuitExit,
    pub result_reg: Option<Reg>,
    pub reducible: bool,
}

/// 短路 DAG 中的稳定节点引用。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ShortCircuitNodeRef(pub usize);

impl ShortCircuitNodeRef {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 一个短路决策节点。
///
/// 这里显式用 `truthy/falsy` 语义连边，而不是 raw `then/else`。原因是结构层的职责
/// 是把 CFG 重新翻译成“按 Lua 求值语义理解”的候选，方便 HIR 直接基于真值流恢复
/// `and/or`，而不用再次反查 `negated` 和 branch 边方向。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShortCircuitNode {
    pub id: ShortCircuitNodeRef,
    pub header: BlockRef,
    pub truthy: ShortCircuitTarget,
    pub falsy: ShortCircuitTarget,
}

/// 短路 DAG 上的目标。
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum ShortCircuitTarget {
    /// 继续进入下一个短路决策节点。
    Node(ShortCircuitNodeRef),
    /// 值型短路的一条叶子。`BlockRef` 指向把值送进 merge 的前驱 block。
    Value(BlockRef),
    /// 条件型短路的“整体为真”出口。
    TruthyExit,
    /// 条件型短路的“整体为假”出口。
    FalsyExit,
}

/// 短路控制流最终如何离开候选区域。
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum ShortCircuitExit {
    /// 这条短路 DAG 最终在某个 block 合流，并通常伴随 phi/result 语义。
    ValueMerge(BlockRef),
    /// 这条短路 DAG 最终直接分流到“整体为真/整体为假”的两个出口。
    BranchExit { truthy: BlockRef, falsy: BlockRef },
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
