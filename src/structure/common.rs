//! 这个文件集中声明 Structure 的内部 evidence 与最终 `StructureFacts` 容器。
//!
//! branch/loop/short-circuit 类型只在 Structure 内参与冲突消解；对下游公开的成功事实已经
//! 收窄为冻结的 `StructurePlan + DebugBindingFacts`。失败 proto 则保留 `ProtoFailure` 和原
//! children 位置，HIR 不会对失败节点重新选择候选，也不会因跳过节点而改变 child slot。

use std::collections::BTreeSet;

mod plan_access;
pub use plan_access::StructurePlan;

use crate::recovery::ProtoFailure;
use crate::structure::{BlockRef, DefId, EdgeRef, PhiId, SsaValue};
use crate::transformer::{InstrRef, Reg, RegRange};

use super::cfg::GraphFacts;

use super::plan::{
    BlockEmissionPlan, BlockTerminatorPlan, BranchPlanData, BranchPlanId, CleanupDisposition,
    ConditionPlan, ConditionPlanId, EdgePlan, EdgeRegionRelation, ForwardRouteId, ForwardRouteKind,
    ForwardRoutePlan, LabelPlan, LabelPlanId, LoopExitTailPlan, LoopPlanData, LoopPlanId,
    LoopValueActions, LoopVmProtocol, PlanRequirements, RegionBoundarySummary, RegionId,
    RegionNavigation, RegionPlan, ScopePlanId, SinglePassPlan, SinglePassPlanId, TbcScopePlan,
    TbcScopePlanId, ValueDecisionPlan, ValueDecisionPlanId,
};

/// 一个 proto 的 Structure 结果，以及保持原顺序的子 proto 结果。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructureFacts {
    pub outcome: StructureOutcome,
    pub children: Vec<StructureFacts>,
}

/// 单个 proto 要么拥有完整冻结计划，要么保留停止推进时的失败事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StructureOutcome {
    Ready(Box<ReadyStructureFacts>),
    Failed(ProtoFailure),
}

/// HIR 可消费的完整 Structure 事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReadyStructureFacts {
    pub plan: StructurePlan,
    pub debug_bindings: DebugBindingFacts,
}

/// debug local 在其源码生命周期入口对应的 canonical SSA 身份。
///
/// `scope` 是 Transformer 归一化 debug local arena 的稳定索引。这里不携带名称，避免
/// Structure 越权处理字符串和命名合法性；HIR 只需把这个索引与归一化 local 事实连接，
/// 就能在 table/closure 等跨多条指令的初始化之后仍找回正确 binding。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DebugBindingFact {
    pub scope: usize,
    pub reg: Reg,
    pub start_pc: u32,
    pub end_pc: u32,
    pub value: SsaValue,
}

/// 多个源码 scope 竞争同一 canonical SSA 时保留的拒绝证据。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DebugBindingConflict {
    pub value: SsaValue,
    pub scopes: Vec<usize>,
}

/// 一个 proto 已冻结的 debug binding 映射及被拒绝的冲突证据。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DebugBindingFacts {
    pub accepted: Vec<DebugBindingFact>,
    pub conflicts: Vec<DebugBindingConflict>,
}

impl StructureFacts {
    pub const fn ready(&self) -> Option<&ReadyStructureFacts> {
        match &self.outcome {
            StructureOutcome::Ready(facts) => Some(facts),
            StructureOutcome::Failed(_) => None,
        }
    }

    pub const fn failure(&self) -> Option<&ProtoFailure> {
        match &self.outcome {
            StructureOutcome::Ready(_) => None,
            StructureOutcome::Failed(failure) => Some(failure),
        }
    }
}

impl ReadyStructureFacts {
    pub const fn plan(&self) -> &StructurePlan {
        &self.plan
    }

    pub const fn debug_bindings(&self) -> &DebugBindingFacts {
        &self.debug_bindings
    }
}

/// 显式 CFG edge 离开 predecessor 时需要执行的一条 phi copy。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PhiEdgeCopy {
    pub phi_id: PhiId,
    pub value: SsaValue,
}

/// Structure 内部 evidence 可附带的既有 island 布局提示。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnstructuredRegionLayout {
    pub blocks: BTreeSet<BlockRef>,
    pub continuation: BlockRef,
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

/// 一个普通 branch 区域的共享边界事实。
///
/// 普通非回环 branch 的结构区域精确等于 `header` 的支配子树减去若干支配子树。
/// 必须冻结特殊改写的精确边界时，也只保存 dominator preorder 的连续区间，不再为
/// 每个嵌套 branch 复制完整 block 集。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchRegionFact {
    pub header: BlockRef,
    pub merge: BlockRef,
    pub kind: BranchKind,
    pub single_pass_fence: Option<SinglePassFenceFact>,
    pub(super) domain: BranchRegionDomain,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct BranchRegionDomain {
    pub spans: Vec<BranchRegionSpan>,
    pub included_blocks: Vec<BlockRef>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct BranchRegionSpan {
    pub root: BlockRef,
    pub excluded_subtrees: Vec<BlockRef>,
}

impl BranchRegionDomain {
    pub(super) fn from_span(
        root: BlockRef,
        excluded_subtrees: impl IntoIterator<Item = BlockRef>,
    ) -> Self {
        Self {
            spans: vec![BranchRegionSpan {
                root,
                excluded_subtrees: excluded_subtrees.into_iter().collect(),
            }],
            included_blocks: Vec::new(),
        }
    }

    pub(super) fn is_empty(&self) -> bool {
        self.spans.is_empty() && self.included_blocks.is_empty()
    }

    pub(super) fn contains(&self, graph_facts: &GraphFacts, block: BlockRef) -> bool {
        self.included_blocks.binary_search(&block).is_ok()
            || self.spans.iter().any(|span| {
                graph_facts.dominates(span.root, block)
                    && span
                        .excluded_subtrees
                        .iter()
                        .all(|excluded| !graph_facts.dominates(*excluded, block))
            })
    }
}

/// 编译器消去 `repeat ... until true` 回边后仍保留的单次 fence 控制事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SinglePassFenceFact {
    pub exit: BlockRef,
    pub escape_edges: BTreeSet<EdgeRef>,
}

impl BranchRegionFact {
    pub(super) fn new(
        graph_facts: &GraphFacts,
        header: BlockRef,
        merge: BlockRef,
        kind: BranchKind,
        single_pass_fence: Option<SinglePassFenceFact>,
    ) -> Self {
        let excluded_subtrees = if let Some(fence) = &single_pass_fence {
            vec![merge, fence.exit]
        } else if graph_facts.dominates(merge, header) {
            Vec::new()
        } else {
            vec![merge]
        };
        let domain = BranchRegionDomain {
            spans: vec![BranchRegionSpan {
                root: header,
                excluded_subtrees,
            }],
            included_blocks: Vec::new(),
        };
        Self {
            header,
            merge,
            kind,
            single_pass_fence,
            domain,
        }
    }

    pub(super) fn replace_domain(&mut self, mut domain: BranchRegionDomain) {
        domain.included_blocks.sort_unstable();
        domain.included_blocks.dedup();
        self.domain = domain;
    }

    pub(super) fn preorder_intervals(
        &self,
        graph_facts: &GraphFacts,
    ) -> Result<Vec<std::ops::Range<usize>>, BlockRef> {
        let position = |block: BlockRef| {
            graph_facts
                .dominator_tree
                .preorder_index
                .get(block.index())
                .copied()
                .flatten()
                .ok_or(block)
        };
        let subtree_end = |block: BlockRef| {
            graph_facts
                .dominator_tree
                .subtree_end
                .get(block.index())
                .copied()
                .flatten()
                .ok_or(block)
        };

        let mut intervals = Vec::<std::ops::Range<usize>>::new();
        for span in &self.domain.spans {
            let start = position(span.root)?;
            let end = subtree_end(span.root)?;
            let mut holes = span
                .excluded_subtrees
                .iter()
                .copied()
                .map(|block| Ok(position(block)?..subtree_end(block)?))
                .collect::<Result<Vec<_>, BlockRef>>()?;
            holes.sort_unstable_by_key(|hole| (hole.start, hole.end));

            let mut cursor = start;
            for hole in holes {
                let hole_start = hole.start.max(start).min(end);
                let hole_end = hole.end.max(start).min(end);
                if cursor < hole_start {
                    intervals.push(cursor..hole_start);
                }
                cursor = cursor.max(hole_end);
            }
            if cursor < end {
                intervals.push(cursor..end);
            }
        }
        intervals.extend(
            self.domain
                .included_blocks
                .iter()
                .copied()
                .map(|block| position(block).map(|position| position..position + 1))
                .collect::<Result<Vec<_>, _>>()?,
        );
        intervals.sort_unstable_by_key(|interval| (interval.start, interval.end));
        let mut merged = Vec::<std::ops::Range<usize>>::with_capacity(intervals.len());
        for interval in intervals {
            if let Some(last) = merged.last_mut()
                && interval.start <= last.end
            {
                last.end = last.end.max(interval.end);
            } else if !interval.is_empty() {
                merged.push(interval);
            }
        }
        Ok(merged)
    }

    pub fn structured_blocks<'a>(
        &'a self,
        graph_facts: &'a GraphFacts,
    ) -> Result<impl Iterator<Item = BlockRef> + 'a, BlockRef> {
        let intervals = self.preorder_intervals(graph_facts)?;
        for interval in &intervals {
            if graph_facts
                .dominator_tree
                .order
                .get(interval.clone())
                .is_none()
            {
                return Err(self.header);
            }
        }
        Ok(intervals.into_iter().flat_map(|interval| {
            graph_facts
                .dominator_tree
                .order
                .get(interval)
                .into_iter()
                .flatten()
                .copied()
        }))
    }
}

/// 一个不可规约区域的共享边界事实。
///
/// 它只表达 SCC 的入口和覆盖 block，不替后层决定最终 `goto/label` 语法。
/// `goto / regions` 都消费这份事实，不应再各自重复做 SCC 入口扫描。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct IrreducibleRegion {
    pub entry: BlockRef,
    pub blocks: BTreeSet<BlockRef>,
    pub entry_edges: Vec<EdgeRef>,
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
    pub then_arm: BranchValueMergeArm,
    pub else_arm: BranchValueMergeArm,
}

/// branch merge 某一臂已经收敛好的来源事实。
///
/// `preds` 保留结构边归属，`values` 记录这一臂在 merge 前实际可见的 canonical SSA
/// 身份。`entry_values` 是 branch header 带入的值，`update_values` 是各 arm 在本轮
/// 产生或传递更新的版本；同一个 Phi 可以同时属于两类。HIR 只消费这份分类，不再
/// 把 Phi 压回叶子 def 后重判来源。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchValueMergeArm {
    pub preds: BTreeSet<BlockRef>,
    pub values: BTreeSet<SsaValue>,
    pub entry_values: BTreeSet<SsaValue>,
    pub update_values: BTreeSet<SsaValue>,
}

/// 一个循环候选。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopCandidate {
    pub header: BlockRef,
    pub preheader: Option<BlockRef>,
    pub blocks: BTreeSet<BlockRef>,
    /// 源码 loop body 在词法上覆盖的 block。
    ///
    /// natural loop blocks 不包含提前退出 tail，也可能漏掉 repeat 分支进入的 nested
    /// loop。Structure 在这里统一保存源码 body 边界；HIR bindings 与结构降低只消费
    /// 这份事实，不回头用 CFG 扩张作用域。
    pub body_scope_blocks: BTreeSet<BlockRef>,
    /// 已被循环语法或规范化出口吸收、无需作为源码 body 单独降低的 block。
    ///
    /// 这类 block 只来自少量 latch/控制 pad，不值得为每个候选分配一棵
    /// `BTreeSet`；集合语义由排序且去重的紧凑向量维持。
    pub control_blocks: Vec<BlockRef>,
    /// VM latch 指向的重复终止块与 preheader 正常出口语义等价；源码只发射后者。
    pub normalized_exit_aliases: Vec<LoopExitAlias>,
    pub backedges: Vec<EdgeRef>,
    pub exits: BTreeSet<BlockRef>,
    pub continue_target: Option<BlockRef>,
    /// 已由当前循环认领的 branch -> continue target/pad 边。
    pub continue_edges: BTreeSet<EdgeRef>,
    /// 仅在短路候选参与 loop 形态精化时记录其条件入口。
    pub condition_header: Option<BlockRef>,
    pub kind_hint: LoopKindHint,
    pub source_bindings: Option<LoopSourceBindings>,
    pub header_value_merges: Vec<LoopValueMerge>,
    pub exit_value_merges: Vec<LoopExitValueMergeCandidate>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LoopExitAlias {
    pub block: BlockRef,
    pub continuation: BlockRef,
}

impl LoopCandidate {
    /// 加入一个已被循环控制吸收的 block，并保持稳定的集合顺序。
    pub(crate) fn add_control_block(&mut self, block: BlockRef) {
        if !self.control_blocks.contains(&block) {
            self.control_blocks.push(block);
            self.control_blocks.sort_unstable();
        }
    }

    /// 规范化跨候选合并后的控制 block 列表。
    pub(crate) fn normalize_control_blocks(&mut self) {
        self.control_blocks.sort_unstable();
        self.control_blocks.dedup();
    }
}

/// 循环头已经暴露给 HIR 的源码绑定证据。
///
/// 这里只记录“源码层确实会出现的绑定寄存器”，避免 HIR 再回头扫描 low-IR/CFG
/// 去猜 numeric-for / generic-for 的绑定槽位。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopSourceBindings {
    Numeric(Reg),
    Generic(RegRange),
}

/// loop merge 某一臂的稳定 incoming 事实。
///
/// 和 branch merge 不同，loop state 恢复需要保留“每个 predecessor 分别给了哪些 defs”，
/// 这样 HIR 才能直接消费 preheader/exit 的来源，不必再回头拆 `phi.incoming`。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopValueIncoming {
    pub pred: Option<BlockRef>,
    pub value: SsaValue,
}

/// 一个 loop value merge 某一臂的 incoming 集合。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LoopValueArm {
    pub incomings: Vec<LoopValueIncoming>,
}

impl LoopValueArm {
    pub fn is_empty(&self) -> bool {
        self.incomings.is_empty()
    }

    pub fn contains_pred(&self, pred: BlockRef) -> bool {
        self.incomings
            .iter()
            .any(|incoming| incoming.pred == Some(pred))
    }

    pub fn values(&self) -> impl Iterator<Item = SsaValue> + '_ {
        self.incomings.iter().map(|incoming| incoming.value)
    }
}

/// 一个 loop header/exit 上的值合流候选。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopValueMerge {
    pub phi_id: PhiId,
    pub reg: Reg,
    pub inside_arm: LoopValueArm,
    pub outside_arm: LoopValueArm,
}

/// 某个 loop exit block 上的值合流候选集合。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopExitValueMergeCandidate {
    pub exit: BlockRef,
    pub values: Vec<LoopValueMerge>,
}

/// 循环形态提示。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum LoopKindHint {
    WhileLike,
    WhileTrueLike,
    RepeatLike,
    NumericForLike,
    GenericForLike,
    Unknown,
}

/// 一个短路表达式候选。
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ShortCircuitCandidate {
    pub header: BlockRef,
    pub blocks: BTreeSet<BlockRef>,
    pub entry: ShortCircuitNodeRef,
    pub nodes: Vec<ShortCircuitNode>,
    pub exit: ShortCircuitExit,
    pub result_reg: Option<Reg>,
    pub result_phi_id: Option<PhiId>,
    pub entry_value: Option<SsaValue>,
    pub value_incomings: Vec<ShortCircuitValueIncoming>,
    pub reducible: bool,
}

impl ShortCircuitCandidate {
    pub(crate) fn branch_exit_leaf_preds(&self, want_truthy: bool) -> BTreeSet<BlockRef> {
        self.nodes
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
}

/// 值型 short-circuit merge 每个叶子最终送进 merge 的 canonical SSA 值。
///
/// 这份事实和 `result_phi_id` 一起构成了“叶子 -> merge 值身份”的前层表达，避免 HIR
/// 再顺着 `PhiCandidate.incoming` 去拆 value leaf。`latest_local_def` 进一步把
/// “这个 leaf block 自己最后一次写 result_reg 的 def”前移出来，避免 HIR 再回头扫描
/// block 指令去找叶子值来源。
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ShortCircuitValueIncoming {
    pub pred: BlockRef,
    pub value: SsaValue,
    pub latest_local_def: Option<DefId>,
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
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

/// 结构候选尚未吸收的一条控制边证据。
///
/// 这只是 Structure 内部冻结最终 edge transfer 的输入，不是对下游公开的
/// `goto` 语法需求。
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub(super) struct ResidualTransferEvidence {
    pub(super) edge: EdgeRef,
    pub(super) reason: GotoReason,
}

/// 最终计划为什么需要把这条边表达为显式 `goto`。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum GotoReason {
    IrreducibleFlow,
    MultiEntryRegion,
    UnstructuredBreakLike,
    UnstructuredContinueLike,
    CrossLoopContinueLike,
}

/// 某片 block 集合的区域事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegionFact {
    pub blocks: BTreeSet<BlockRef>,
    pub entry: BlockRef,
    pub exits: BTreeSet<BlockRef>,
}

/// 已冻结的词法 cleanup scope。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScopePlan {
    pub entry: BlockRef,
    pub exit: Option<BlockRef>,
    pub close_points: Vec<InstrRef>,
}
