//! 这个文件把 Structure 内部 evidence 收敛成可按稠密索引查询的执行计划。
//!
//! evidence 提取允许 branch、loop 与 irreducible region 重叠；这里为每个 block、edge、
//! phi incoming 与 cleanup 选择唯一 disposition。HIR 只消费冻结结果，不能再按 header
//! 或临时 map 的覆盖顺序重选候选。
//!
//! 输入形状：一个 branch region 与多入口 SCC 在部分 block 上重叠。
//! 输出形状：SCC membership 与直接 owner 分开；其中可规约 header 仍归 `Branch/Loop`，
//! 其余成员归 `Unstructured`，每条 CFG edge 同时得到唯一 owner。

mod arena;
mod cleanup;
mod finalize;
mod loop_protocol;
mod navigation;
mod terminator;
mod validate;
mod value;

pub use cleanup::CleanupDisposition;
pub use loop_protocol::{
    EdgeCopyOrigin, GenericForProtocol, LoopConditionProtocol, LoopIterationDisposition,
    LoopRepeatForm, LoopRepeatProtocol, LoopRepeatStagedResult, LoopRepeatValuePlan,
    LoopValueActionBatch, LoopValueActions, LoopValuePhase, LoopValueSource, LoopValueWrite,
    LoopVmProtocol, NumericForProtocol,
};
pub use navigation::{EdgeRegionRelation, RegionBoundarySummary, RegionNavigation};
pub use terminator::{BlockTerminatorKind, BlockTerminatorPlan};
pub use value::{PhiIncomingDisposition, PhiIncomingPlan, PhiPlan};

use std::collections::BTreeSet;

use super::common::ResidualTransferEvidence;
pub use super::error::StructureError;
use super::{
    BlockRef, BranchCandidate, BranchKind, BranchRegionFact, BranchValueMergeCandidate, Cfg,
    DataflowFacts, EdgeRef, GotoReason, GraphFacts, InstrRange, LoopCandidate,
    LoopExitValueMergeCandidate, LoopKindHint, LoopSourceBindings, LoopValueMerge, PhiEdgeCopy,
    RegionFact, ScopePlan, ShortCircuitCandidate, SsaValue, StructurePlan,
    UnstructuredRegionLayout,
};
use crate::decompile::ControlFlowCaps;
use crate::transformer::LoweredProto;

pub(super) use finalize::expected_block_emission;
pub(crate) use finalize::{
    build_final_structure_plan, finalize_block_emissions, finalize_loop_contracts,
    validate_final_structure_plan,
};
/// 已完成冲突消解并移入最终计划的 branch identity。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BranchPlanId(pub usize);

impl BranchPlanId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 被编译器消去回边后，由最终计划恢复的一次性词法 fence。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SinglePassPlanId(pub usize);

impl SinglePassPlanId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 已完成 same-header 消歧并移入最终计划的 loop identity。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LoopPlanId(pub usize);

impl LoopPlanId {
    pub const fn index(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConditionPlanId(pub usize);

impl ConditionPlanId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 已从 value-merge evidence 冻结出的值决策 identity。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ValueDecisionPlanId(pub usize);

impl ValueDecisionPlanId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 最终计划中的稳定 label identity。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LabelPlanId(pub usize);

impl LabelPlanId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 一条已冻结 forwarding route 的稠密 identity。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ForwardRouteId(pub usize);

impl ForwardRouteId {
    pub const fn index(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ScopePlanId(pub usize);

impl ScopePlanId {
    pub const fn index(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TbcScopePlanId(pub usize);

impl TbcScopePlanId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 一个显式 `<close>` 声明集合的冻结词法边界及其它 CFG 出口。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TbcScopePlan {
    pub origins: Vec<crate::transformer::InstrRef>,
    pub boundary: crate::transformer::InstrRef,
    pub exits: Vec<crate::transformer::InstrRef>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct RegionId(pub usize);

impl RegionId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// basic block 在最终 region layout 中的发射方式。
///
/// 透明 jump pad 的控制和值动作若已被所有入口 edge 的 forwarding route 吸收，
/// block 仍保留唯一 containment owner，但 HIR 不再单独发射它。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockEmissionPlan {
    Emit,
    ForwardedControl { outgoing: EdgeRef },
}

/// 最终 region arena 的一个节点。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegionPlan {
    /// 单个 basic block；block 只会在整个 arena 中出现一次。
    Block { parent: RegionId, block: BlockRef },
    /// 具有确定执行顺序的子 region 列表；root 也是一个 sequence。
    Sequence {
        parent: Option<RegionId>,
        children: Vec<RegionId>,
    },
    /// 已冻结边角色、条件与 continuation 的结构化分支。
    Branch {
        parent: RegionId,
        plan: BranchPlanId,
        entry: BlockRef,
        condition: RegionId,
        then_arm: RegionId,
        else_arm: Option<RegionId>,
        continuation: Option<BlockRef>,
    },
    /// 整片短路 CFG 产生一个最终值；内部 DAG 由 payload 完整描述，不再拆成 sibling branch。
    ValueDecision {
        parent: RegionId,
        plan: ValueDecisionPlanId,
        entry: BlockRef,
        continuation: BlockRef,
    },
    /// 同 header 候选完成消歧后的结构化循环。
    Loop {
        parent: RegionId,
        plan: LoopPlanId,
        entry: BlockRef,
        /// 仅 for VM loop 存在；初始化 block 由 loop 显式拥有，不依赖 sibling 邻接。
        preheader: Option<RegionId>,
        /// 被循环语法吸收的 condition / VM control blocks。
        control: RegionId,
        /// 只包含源码 loop body，不混入 control/preheader block。
        body: RegionId,
        /// 只允许 VM 正常退出进入的源码尾部；提前 `break` 必须跳过它。
        normal_tail: Option<RegionId>,
    },
    /// 无法完全结构化但可作为 mixed-lowering island 执行的区域。
    Unstructured {
        parent: RegionId,
        entry: BlockRef,
        /// 从 island 外部进入其 containment 子树的 CFG edge，按 `EdgeRef` 严格递增。
        entries: Vec<EdgeRef>,
        layout: Vec<UnstructuredLayoutItem>,
        /// 从 island containment 子树离开的 CFG edge，按 `EdgeRef` 严格递增。
        exits: Vec<EdgeRef>,
    },
}

/// 已冻结 label 及其目标处必须已激活的 VM `<close>` 声明。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LabelPlan {
    pub block: BlockRef,
    pub tbc_barriers: Vec<crate::transformer::InstrRef>,
    pub placement: LabelPlacement,
}

/// label 相对目标 block 入口 cleanup 的精确位置。
///
/// join block 可能只在部分入口仍有活跃 TBC，此时 VM 会以 block 开头的 `Close`
/// 统一状态。源码 label 必须放在该 cleanup 之后，避免把外部 goto 放进局部作用域。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LabelPlacement {
    BeforeBlock,
    /// island/sequence 边直接进入 structured child 时，label 必须位于
    /// `if`/loop 语句之前，不能落入该结构的内部 block 作用域。
    BeforeRegion(RegionId),
    AfterCleanup(crate::transformer::InstrRef),
}

/// branch value merge 的最终计划；不保留候选身份与重复 header。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchValuePlan {
    pub merge: BlockRef,
    pub(crate) values: Vec<crate::structure::common::BranchValueMergeValue>,
}

/// 已选 branch 的完整 lowering payload；HIR 只消费最终 edge 角色与 polarity。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchPlanData {
    pub header: BlockRef,
    pub kind: BranchKind,
    pub condition: ConditionPlanId,
    pub condition_inverted: bool,
    pub then_edge: EdgeRef,
    pub else_edge: EdgeRef,
    pub continuation: Option<BlockRef>,
    pub(crate) value_plan: Option<BranchValuePlan>,
}

/// 一个 `repeat ... until true` fence 的冻结控制合同。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SinglePassPlan {
    pub region: RegionId,
    pub entry: BlockRef,
    pub tail: BlockRef,
    pub continuation: BlockRef,
    pub escape_edges: Vec<EdgeRef>,
}

/// Structure arena 构建前的 branch evidence；不会写入最终 `StructurePlan`。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct BranchPlanInput {
    pub(super) branch: BranchCandidate,
    pub(super) region: Option<BranchRegionFact>,
    pub(super) value_merge: Option<BranchValueMergeCandidate>,
    pub(super) condition: Option<ConditionPlanId>,
}

/// Structure arena 的 loop 候选输入；raw candidate 不会进入最终计划。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct LoopPlanInput {
    pub(super) candidate: LoopCandidate,
    pub(super) condition: Option<ConditionPlanId>,
    pub(super) continuation: Option<BlockRef>,
    pub(super) carried_values: Vec<LoopValueMerge>,
    /// 最终复合 condition 与 loop owner 共同证明的显式 continue transfer。
    pub(super) semantic_continue_edges: BTreeSet<EdgeRef>,
}

/// 被循环语法吸收的 CFG edge 角色；HIR 只消费这份冻结结果。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LoopControlEdges {
    pub preheader_body: Option<EdgeRef>,
    pub preheader_exit: Option<EdgeRef>,
    pub body: Vec<EdgeRef>,
    pub exit: Vec<EdgeRef>,
    pub backedges: Vec<EdgeRef>,
    pub continues: Vec<EdgeRef>,
}

/// `for` 正常退出专属尾部的冻结控制契约。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopNormalTailPlan {
    pub entry: BlockRef,
    pub continuation: BlockRef,
    pub early_exits: Vec<EdgeRef>,
    pub normal_exits: Vec<EdgeRef>,
    pub completion_exits: Vec<EdgeRef>,
}

/// 普通 loop 正常退出边独占的 block 前缀。
///
/// 该范围仍属于 `block` 的 CFG identity，但只能在 `normal_exit` 上执行；其它提前退出
/// 必须跳过它。`continuation` 显式冻结范围结束后继续 lowering 的 block identity，HIR
/// 不得用指令邻接重新猜分割点。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopExitTailPlan {
    pub normal_exit: EdgeRef,
    pub block: BlockRef,
    pub range: InstrRange,
    pub continuation: BlockRef,
    pub early_exits: Vec<EdgeRef>,
    /// 被源码 `break` 的作用域退出吸收的 cleanup。某些 PUC 版本把它放在 tail block
    /// 的唯一后继前缀，因此 block/route 也必须由 Structure 一并冻结。
    pub cleanup_block: BlockRef,
    pub cleanup_route: Vec<EdgeRef>,
    pub cleanup: Vec<crate::transformer::InstrRef>,
}

/// loop condition 前缀相对源码 body 的冻结执行位置。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopConditionPrefixPlacement {
    BeforeBody,
    AfterBody,
}

/// 已选 loop 的归一化 lowering payload；不保留 raw `LoopCandidate`。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopPlanData {
    pub(crate) kind: LoopKindHint,
    pub(crate) header: BlockRef,
    pub(crate) preheader_block: Option<BlockRef>,
    pub(crate) condition_header: Option<BlockRef>,
    pub(crate) condition: Option<ConditionPlanId>,
    pub(crate) condition_prefix_placement: Option<LoopConditionPrefixPlacement>,
    pub(crate) continuation: Option<BlockRef>,
    pub(crate) continue_target: Option<BlockRef>,
    pub(crate) source_bindings: Option<LoopSourceBindings>,
    pub(crate) control_edges: LoopControlEdges,
    pub(crate) break_edges: Vec<EdgeRef>,
    pub(crate) normalized_exit_aliases: Vec<crate::structure::LoopExitAlias>,
    pub(crate) normal_tail: Option<LoopNormalTailPlan>,
    pub(crate) exit_tail: Option<LoopExitTailPlan>,
    /// 当前 loop 的所有可完成出口都会继续 break 同一个祖先 loop。
    pub(crate) propagated_break: Option<RegionId>,
    pub(crate) header_values: Vec<LoopValueMerge>,
    pub(crate) exit_values: Vec<LoopExitValueMergeCandidate>,
    pub(crate) carried_values: Vec<LoopValueMerge>,
    /// phi/cleanup 冻结完成后写入的唯一 VM lowering 合同。
    pub(crate) protocol: Option<LoopVmProtocol>,
    pub(crate) value_actions: Option<LoopValueActions>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConditionNodeId(pub usize);

impl ConditionNodeId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// condition DAG 的冻结边；终端只保留真假语义，不携带 raw block target。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConditionTarget {
    Node(ConditionNodeId),
    Truthy,
    Falsy,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConditionArcPolarity {
    BranchTrue,
    BranchFalse,
}

impl ConditionArcPolarity {
    pub const fn index(self) -> usize {
        match self {
            Self::BranchTrue => 0,
            Self::BranchFalse => 1,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConditionArcPlan {
    pub source: ConditionNodeId,
    pub polarity: ConditionArcPolarity,
    pub route: Vec<EdgeRef>,
    /// 此语义 arc 上唯一需要 HIR 执行的 edge；forward route 可从这里覆盖物理后缀。
    pub transfer: EdgeRef,
    pub connector_blocks: Vec<BlockRef>,
    pub target: ConditionTarget,
}

/// condition DAG 的稠密节点。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConditionNodePlan {
    pub id: ConditionNodeId,
    pub block: BlockRef,
    pub predicate: crate::transformer::InstrRef,
    pub predicate_negated: bool,
    pub arcs: [ConditionArcPlan; 2],
    /// 该分支只负责把谓词布尔化后交给后续 condition node 使用，不是外层短路测试。
    pub materialized_value: Option<ConditionValuePlan>,
}

impl ConditionNodePlan {
    pub fn arc(&self, polarity: ConditionArcPolarity) -> &ConditionArcPlan {
        &self.arcs[polarity.index()]
    }

    pub fn semantic_target(&self, truthy: bool) -> ConditionTarget {
        let polarity = match truthy ^ self.predicate_negated {
            true => ConditionArcPolarity::BranchTrue,
            false => ConditionArcPolarity::BranchFalse,
        };
        self.arc(polarity).target
    }
}

/// condition 内部由一对布尔叶合流出的值。
///
/// 物理分支与两条 route 仍保留在所属 `ConditionNodePlan` 中；HIR 只能把这里冻结的
/// 谓词代入唯一消费节点，不能把该节点再次解释成外层控制分支。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConditionValuePlan {
    pub phi: crate::structure::PhiId,
    pub consumer: ConditionNodeId,
    pub use_instr: crate::transformer::InstrRef,
    pub negated: bool,
    /// 布尔物化前已经求值、随后与该值一起被 consumer 调用读取的 callee。
    pub forwarded_callee: Option<crate::structure::DefId>,
}

/// 证明 value-decision leaf 与当前 truthiness subject 是同一次求值。
///
/// 除了直接 SSA identity，只接受一条把 subject 搬到 result register 的透明 Move；
/// 不能用表达式相等替代 identity，否则带副作用的调用会被 HIR 重复求值。
pub(super) fn value_leaf_is_current(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    predicate_ref: crate::transformer::InstrRef,
    predicate: &crate::transformer::BranchInstr,
    result_reg: crate::transformer::Reg,
    leaf_value: SsaValue,
    latest_local_def: Option<crate::structure::DefId>,
) -> bool {
    let crate::transformer::BranchSubject::Truthy(crate::transformer::CondOperand::Reg(
        subject_reg,
    )) = predicate.cond.subject
    else {
        return false;
    };
    let subject_value = dataflow.use_value(predicate_ref, subject_reg);
    if leaf_value == subject_value {
        return true;
    }
    let Some(def) = latest_local_def else {
        return false;
    };
    if leaf_value != SsaValue::Def(def) || dataflow.def_reg(def) != result_reg {
        return false;
    }
    let Some(definition) = dataflow.defs.get(def.index()) else {
        return false;
    };
    let Some(crate::transformer::LowInstr::Move(move_)) =
        proto.instrs.get(definition.instr.index())
    else {
        return false;
    };
    move_.dst == result_reg && dataflow.use_value(definition.instr, move_.src) == subject_value
}

pub(super) fn condition_forwarded_callee(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    node: &ConditionNodePlan,
    value_phi: crate::structure::PhiId,
    use_instr: crate::transformer::InstrRef,
    prefix_emitted: bool,
) -> Option<Option<crate::structure::DefId>> {
    let mut owned_blocks = node
        .arcs
        .iter()
        .flat_map(|arc| arc.connector_blocks.iter().copied())
        .collect::<BTreeSet<_>>();
    owned_blocks.insert(node.block);
    let call_callee = match proto.instrs.get(use_instr.index())? {
        crate::transformer::LowInstr::Call(call) => Some(call.callee),
        _ => None,
    };
    let forwarded_candidate = call_callee
        .map(|callee| dataflow.use_value(use_instr, callee))
        .and_then(|value| match value {
            SsaValue::Def(def) if owned_blocks.contains(&dataflow.def_block(def)) => Some(def),
            SsaValue::Entry(_) | SsaValue::Def(_) | SsaValue::Phi(_) => None,
        });
    let mut forwarded = None;
    for block in &owned_blocks {
        let range = cfg.blocks.get(block.index())?.instrs;
        for instr in range.start.index()..range.end() {
            for def_id in dataflow.instr_defs.get(instr)? {
                let def = dataflow.defs.get(def_id.index())?;
                let external_uses = dataflow
                    .def_uses
                    .get(def.id.index())?
                    .iter()
                    .filter(|site| {
                        cfg.instr_to_block
                            .get(site.instr.index())
                            .is_none_or(|block| !owned_blocks.contains(block))
                    })
                    .copied()
                    .collect::<Vec<_>>();
                if dataflow
                    .def_phi_uses
                    .get(def.id.index())?
                    .iter()
                    .any(|phi| *phi != value_phi)
                {
                    return None;
                }
                if external_uses.is_empty() || prefix_emitted && def.block == node.block {
                    continue;
                }
                let [site] = external_uses.as_slice() else {
                    return None;
                };
                if Some(def.id) != forwarded_candidate
                    || site.instr != use_instr
                    || call_callee != Some(site.reg)
                    || dataflow.use_value(use_instr, site.reg) != SsaValue::Def(def.id)
                    || !matches!(
                        proto.instrs.get(def.instr.index()),
                        Some(
                            crate::transformer::LowInstr::GetUpvalue(_)
                                | crate::transformer::LowInstr::GetTable(_)
                                | crate::transformer::LowInstr::Move(_)
                        )
                    )
                    || forwarded.replace(def.id).is_some()
                {
                    return None;
                }
            }
        }
    }
    Some(forwarded)
}

/// 已归属到最终 branch/loop 的短路条件 payload。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConditionPlan {
    pub entry: ConditionNodeId,
    pub nodes: Vec<ConditionNodePlan>,
    /// 被 condition 表达式吸收的 node 与 transfer 前 connector；forward route 后缀不在内。
    pub blocks: Vec<BlockRef>,
    pub truthy: EdgeRef,
    pub falsy: EdgeRef,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ValueDecisionNodeId(pub usize);

impl ValueDecisionNodeId {
    pub const fn index(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ValueDecisionLeafId(pub usize);

impl ValueDecisionLeafId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// value decision 的语义连边。`CurrentValue` 表示当前 truthiness subject 本身就是结果值。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueDecisionTarget {
    Node(ValueDecisionNodeId),
    Leaf(ValueDecisionLeafId),
    CurrentValue(ValueDecisionLeafId),
}

/// 一条语义 decision arc 对应的完整物理 CFG 路径。
///
/// `polarity` 固定第一条边在 bytecode branch 上的实际方向；`route` 从 decision node
/// 一直延伸到下一个 node 或最终 merge。HIR 只读取 `target`，而校验器借助物理路径
/// 保证 connector、透明 phi carrier 与最终 value incoming 没有被静默丢弃。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueDecisionArcPlan {
    pub polarity: ConditionArcPolarity,
    pub route: Vec<EdgeRef>,
    pub target: ValueDecisionTarget,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueDecisionNodePlan {
    pub id: ValueDecisionNodeId,
    pub block: BlockRef,
    pub predicate: crate::transformer::InstrRef,
    pub predicate_negated: bool,
    pub truthy: ValueDecisionArcPlan,
    pub falsy: ValueDecisionArcPlan,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ValueDecisionLeafPlan {
    pub id: ValueDecisionLeafId,
    pub block: BlockRef,
    pub value: SsaValue,
    pub latest_local_def: Option<crate::structure::DefId>,
    pub terminal_edge: EdgeRef,
    pub physical_pred: BlockRef,
    pub physical_value: SsaValue,
}

/// value-merge short-circuit 的最终、稠密执行计划。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueDecisionPlan {
    pub entry: ValueDecisionNodeId,
    pub nodes: Vec<ValueDecisionNodePlan>,
    pub leaves: Vec<ValueDecisionLeafPlan>,
    pub blocks: Vec<BlockRef>,
    pub merge: BlockRef,
    /// 所有 leaf terminal edge 共有的边界 copy 由该 edge 唯一承载。
    ///
    /// decision 折叠了物理分支后，HIR 在结果表达式求值后执行一次这组 copy；Structure
    /// 校验所有 terminal edge 的 copy 完全相同，不能借此合并路径相关的值动作。
    pub shared_exit_action: EdgeRef,
    pub result_phi: crate::structure::PhiId,
    /// decision 内部被表达式 DAG 一并消去的中间 phi；按 PhiId 严格递增。
    pub absorbed_phis: Vec<crate::structure::PhiId>,
    pub result_reg: crate::transformer::Reg,
}

impl ValueDecisionPlan {
    pub fn blocks(&self) -> impl ExactSizeIterator<Item = BlockRef> + '_ {
        self.blocks.iter().copied()
    }

    pub fn header(&self) -> Option<BlockRef> {
        self.nodes.get(self.entry.index()).map(|node| node.block)
    }
}

impl ConditionPlan {
    pub fn blocks(&self) -> impl ExactSizeIterator<Item = BlockRef> + '_ {
        self.blocks.iter().copied()
    }

    pub fn header(&self) -> Option<BlockRef> {
        self.nodes.get(self.entry.index()).map(|node| node.block)
    }
}

/// Structure arena 构建前的 condition evidence；escaping-def 筛选已经完成。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ConditionPlanInput {
    pub(super) candidate: ShortCircuitCandidate,
    pub(super) arcs: Vec<crate::structure::short_circuit::ConditionArcEvidence>,
}

/// arena 构建前的 value-merge evidence；raw candidate 不会泄露给 HIR。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ValueDecisionPlanInput {
    pub(super) candidate: ShortCircuitCandidate,
}

/// 已移入最终计划的 mixed-lowering island payload。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct UnstructuredPlanData {
    pub(super) fact: RegionFact,
    pub(super) layout: Option<UnstructuredRegionLayout>,
}

/// arena builder 的唯一 evidence 输入；builder 在这里完成冲突消解并只冻结选中 payload。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(super) struct FinalPlanInput {
    pub(super) branches: Vec<BranchPlanInput>,
    pub(super) loops: Vec<LoopPlanInput>,
    pub(super) conditions: Vec<ConditionPlanInput>,
    pub(super) value_decisions: Vec<ValueDecisionPlanInput>,
    pub(super) scopes: Vec<ScopePlan>,
    pub(super) unstructured: Vec<UnstructuredPlanData>,
    pub(super) residual_transfers: Vec<ResidualTransferEvidence>,
}

/// 从已选 payload 一次性构建最终 region/edge/requirement arena。
impl RegionPlan {
    pub const fn parent(&self) -> Option<RegionId> {
        match self {
            Self::Block { parent, .. }
            | Self::Branch { parent, .. }
            | Self::ValueDecision { parent, .. }
            | Self::Loop { parent, .. }
            | Self::Unstructured { parent, .. } => Some(*parent),
            Self::Sequence { parent, .. } => *parent,
        }
    }
}

/// 不可规约 island 中的最终执行项。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnstructuredLayoutItem {
    Block(BlockRef),
    Region(RegionId),
}

/// 条件边在最终计划中的语义角色。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BranchArm {
    Truthy,
    Falsy,
    LoopBody,
    LoopExit,
}

/// 一条 CFG edge 在最终结构计划中的唯一控制转移。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeTransfer {
    /// source block 不可达；仍保留槽位以保证 `EdgeRef` 是稠密索引。
    Unreachable,
    Fallthrough,
    BranchArm(BranchArm),
    LoopBack(RegionId),
    Break(RegionId),
    Continue(RegionId),
    Return,
    TailCall,
    Goto(LabelPlanId, GotoReason),
}

/// repeat condition 中被 continue 吸收的精确物理 arc。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConditionArcRef {
    pub condition: ConditionPlanId,
    pub node: ConditionNodeId,
    pub polarity: ConditionArcPolarity,
}

/// forwarding route 的唯一控制语义。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ForwardRouteKind {
    ExclusiveBreak,
    ContinueToTarget,
    ContinueLatch,
    RepeatConditionArc(ConditionArcRef),
}

/// 多个入口可以共享同一条 route；物理 edge 链由 `StructurePlan::forward_next` 稠密保存。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ForwardRoutePlan {
    pub kind: ForwardRouteKind,
    pub loop_region: RegionId,
    pub first: EdgeRef,
    pub last: EdgeRef,
    pub start: BlockRef,
    pub target: BlockRef,
    pub len: usize,
}

/// edge 上的 value 动作相对 source 尾部指令的冻结执行位置。
///
/// 默认位置是在 source 指令全部执行后、控制转移前。若 loop latch 的尾部 cleanup 会
/// 结束产生 carried value 的局部作用域，Structure 必须冻结精确 cleanup 范围，让 value
/// 动作先于该范围执行；HIR 不得再从指令邻接推断这个顺序。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum EdgeActionPlacement {
    #[default]
    BeforeTransfer,
    BeforeTrailingCleanup {
        cleanup: InstrRange,
    },
}

/// 一条 CFG edge 的最终 lowering 计划。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EdgePlan {
    pub edge: EdgeRef,
    pub owner: RegionId,
    pub transfer: EdgeTransfer,
    pub action_placement: EdgeActionPlacement,
    /// 该 edge 被折叠成提前控制转移时共享的冻结物理 route。
    pub forward_route: Option<ForwardRouteId>,
    pub phi_copies: Vec<PhiEdgeCopy>,
    /// 提前 continue/goto 绕过源码 loop tail 时，该 edge 对 for 迭代结果槽的唯一处置。
    pub iteration: Vec<LoopIterationDisposition>,
}

impl EdgePlan {
    /// HIR 只读取冻结范围，不需要引用 Structure 内部的 placement 类型。
    pub const fn actions_before_trailing_cleanup(&self) -> Option<InstrRange> {
        match self.action_placement {
            EdgeActionPlacement::BeforeTransfer => None,
            EdgeActionPlacement::BeforeTrailingCleanup { cleanup } => Some(cleanup),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PlanRequirementId(pub usize);

impl PlanRequirementId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 最终 lowering 必须满足、但不依赖具体 AST 语法的约束。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PlanRequirement {
    Goto {
        edge: EdgeRef,
        label: LabelPlanId,
        reason: GotoReason,
    },
    Continue {
        edge: EdgeRef,
        loop_region: RegionId,
    },
    MultiEntryIsland {
        region: RegionId,
        entry_count: usize,
    },
    UnresolvedValue {
        phi_id: super::PhiId,
        block: BlockRef,
        reg: crate::transformer::Reg,
    },
}

/// 最终计划要求目标方言提供的非结构化控制流能力。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ControlFlowFeature {
    GotoLabel,
    ContinueStatement,
}

impl PlanRequirement {
    pub const fn edge(&self) -> Option<EdgeRef> {
        match self {
            Self::Goto { edge, .. } | Self::Continue { edge, .. } => Some(*edge),
            Self::MultiEntryIsland { .. } | Self::UnresolvedValue { .. } => None,
        }
    }
}

/// 稠密 requirement arena，以及从 edge 到 requirement 的反向索引。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct PlanRequirements {
    pub(super) entries: Vec<PlanRequirement>,
    pub(super) by_edge: Vec<Vec<PlanRequirementId>>,
    pub(super) unresolved_by_block: Vec<bool>,
    pub(super) required_features: BTreeSet<ControlFlowFeature>,
    pub(super) unavailable_features: BTreeSet<ControlFlowFeature>,
    pub(super) caps: ControlFlowCaps,
}

impl PlanRequirements {
    pub fn get(&self, id: PlanRequirementId) -> Option<&PlanRequirement> {
        self.entries.get(id.index())
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = (PlanRequirementId, &PlanRequirement)> {
        self.entries
            .iter()
            .enumerate()
            .map(|(index, requirement)| (PlanRequirementId(index), requirement))
    }

    pub fn for_edge(&self, edge: EdgeRef) -> &[PlanRequirementId] {
        self.by_edge.get(edge.index()).map_or(&[], Vec::as_slice)
    }

    pub fn has_unresolved_at(&self, block: BlockRef) -> bool {
        self.unresolved_by_block
            .get(block.index())
            .copied()
            .unwrap_or(false)
    }

    pub fn required_features(&self) -> &BTreeSet<ControlFlowFeature> {
        &self.required_features
    }

    pub fn unavailable_features(&self) -> &BTreeSet<ControlFlowFeature> {
        &self.unavailable_features
    }
}
