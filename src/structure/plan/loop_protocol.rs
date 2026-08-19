//! 冻结 loop 的 VM 协议与值动作批次。
//!
//! `loops.rs` 只负责识别候选形态；这里把最终 loop 会如何进入 body、如何回边、以及
//! numeric/generic-for 的 phi copy 应在什么阶段执行一次性写死。HIR 只能消费这些
//! 稳定协议，不能再扫整张 CFG 回推 loop 形状或值写回时序。

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::structure::{
    BlockRef, BlockTerminatorKind, Cfg, DataflowFacts, EdgeRef, GotoReason, GraphFacts,
    LoopSourceBindings, PhiId, SsaValue, StructurePlan,
};
use crate::transformer::{
    GenericForCallInstr, GenericForLoopInstr, GenericForPrepInstr, InstrRef, LowInstr,
    LoweredProto, Reg, RegRange,
};

use super::{
    ConditionPlanId, EdgeTransfer, LoopConditionPrefixPlacement, LoopKindHint, LoopPlanData,
    RegionId, RegionPlan, StructureError,
};

mod analysis;
mod finalize;
mod generic_for;
mod iterations;
mod protocol;
mod repeat;
mod value_actions;

pub(super) use finalize::{finalize, validate};
use generic_for::*;
use iterations::*;
use protocol::*;
use repeat::*;
use value_actions::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoopConditionProtocol {
    pub condition: ConditionPlanId,
    pub body_edge: EdgeRef,
    pub exit_edge: EdgeRef,
    pub body_on_truthy: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopRepeatForm {
    Native,
    TailBranchRepeat,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopRepeatProtocol {
    pub condition: LoopConditionProtocol,
    pub prefix_placement: LoopConditionPrefixPlacement,
    pub form: LoopRepeatForm,
    /// condition 成功后仍需在原生 repeat 外执行的祖先 transfer/value actions。
    pub exit_after_loop: bool,
    pub value_plan: LoopRepeatValuePlan,
}

/// 原生 repeat 退出时延迟提交的结果。每个结果使用独立、不可观察的 staging temp；
/// condition 路径和所有 early break 都先写 stage，离开 loop 后才提交 final phi。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoopRepeatStagedResult {
    pub target: PhiId,
    pub normal_value: SsaValue,
}

/// repeat terminal edge 的唯一值协议。Structure 证明 staged result 覆盖全部退出路径后，
/// HIR 才能选择原生 `repeat ... until`，不得把 final captured local 提前暴露在 loop 内。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LoopRepeatValuePlan {
    /// 可在原生 repeat 的 `until` 条件求值前执行的 loop-carried copies。
    pub backedge_copies: Vec<crate::structure::PhiEdgeCopy>,
    pub exit_copies: Vec<crate::structure::PhiEdgeCopy>,
    /// 祖先 VM-for 已由源码循环语法隐式推进的控制槽，不得在内层 repeat 退出前读取。
    /// 这些 copy 仍由外层 loop-carried owner 消费，不是无 owner 的丢弃动作。
    pub outer_loop_owned_exit_copies: Vec<crate::structure::PhiEdgeCopy>,
    pub staged_results: Vec<LoopRepeatStagedResult>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NumericForProtocol {
    pub init_instr: InstrRef,
    pub body_edge: EdgeRef,
    pub exit_edge: EdgeRef,
    /// planned body 是否存在一条可落入 protocol tail 的普通完成路径；空 body 为 true。
    pub body_completes_normally: bool,
    pub index: Reg,
    pub limit: Reg,
    pub step: Reg,
    pub binding: Reg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GenericForProtocol {
    pub prep_instr: Option<InstrRef>,
    pub call_instr: InstrRef,
    pub loop_instr: InstrRef,
    pub body_edge: EdgeRef,
    pub exit_edge: EdgeRef,
    /// planned body 是否存在一条可落入 protocol tail 的普通完成路径；空 body 为 true。
    pub body_completes_normally: bool,
    pub iterator: RegRange,
    pub bindings: RegRange,
    /// 空 body 的 yield edge 是否等价于立即退出本 generic-for。
    pub immediate_break: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoopVmProtocol {
    While(LoopConditionProtocol),
    Repeat(LoopRepeatProtocol),
    WhileTrue,
    NumericFor(NumericForProtocol),
    GenericFor(GenericForProtocol),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EdgeCopyOrigin {
    pub edge: EdgeRef,
    pub target: PhiId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopValueSource {
    Ssa(SsaValue),
    Binding(Reg),
    Carried(PhiId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopValueWrite {
    pub target: PhiId,
    pub source: LoopValueSource,
    pub origins: Vec<EdgeCopyOrigin>,
}

/// 提前离开本轮源码 body 的 edge 对 IterationEpilogue 结果槽的冻结写回。
/// 即使当前值等于旧槽也显式写入 canonical incoming，避免再引入一套 carried 等价证明。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoopIterationDisposition {
    pub loop_region: RegionId,
    pub target: PhiId,
    pub incoming: SsaValue,
    pub source: LoopValueSource,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopValuePhase {
    BeforeLoop,
    BodyPrologue,
    IterationEpilogue,
    LatchEpilogue,
    AfterLoop,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopValueActionBatch {
    pub phase: LoopValuePhase,
    pub writes: Vec<LoopValueWrite>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LoopValueActions {
    pub batches: Vec<LoopValueActionBatch>,
    pub elided: Vec<EdgeCopyOrigin>,
}

#[derive(Default)]
struct FrozenExitActions {
    before_loop: Vec<LoopValueWrite>,
    iteration_epilogue: Vec<LoopValueWrite>,
    after_loop: Vec<LoopValueWrite>,
    elided: Vec<EdgeCopyOrigin>,
}

type UniformEdgeCopies = Vec<(crate::structure::PhiEdgeCopy, Vec<EdgeCopyOrigin>)>;

#[derive(Clone, Copy, Default)]
struct PhiUseExtent {
    first_region: usize,
    last_region: usize,
    has_region: bool,
    has_unowned_use: bool,
}

impl PhiUseExtent {
    fn include_region(&mut self, position: usize) {
        if self.has_region {
            self.first_region = self.first_region.min(position);
            self.last_region = self.last_region.max(position);
        } else {
            self.first_region = position;
            self.last_region = position;
            self.has_region = true;
        }
    }

    fn merge(&mut self, other: Self) {
        if other.has_region {
            self.include_region(other.first_region);
            self.include_region(other.last_region);
        }
        self.has_unowned_use |= other.has_unowned_use;
    }
}

/// loop value 分类只依赖冻结 SSA/containment，因此为整个 proto 一次性建立稠密摘要。
///
/// phi graph 先收缩 SCC，再沿 condensation DAG 传播 instruction-use 的 region
/// preorder 范围。一个 control region 的 subtree 也是连续 preorder 区间，所以
/// `phi_observed_outside` 无需再为每个 copy 递归遍历整张 use graph。
struct LoopValueAnalysis {
    vm_for_control: Vec<bool>,
    use_extents: Vec<PhiUseExtent>,
    absorbed_owner_by_edge: Vec<Option<super::LoopPlanId>>,
}

#[derive(Clone, Copy)]
struct LoopValueContext<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    dataflow: &'a DataflowFacts,
    plan: &'a StructurePlan,
    analysis: &'a LoopValueAnalysis,
    owner: RegionId,
    control: RegionId,
    payload: &'a LoopPlanData,
}
