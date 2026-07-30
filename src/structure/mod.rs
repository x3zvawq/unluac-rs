//! 这个模块把 CFG、图事实与 canonical SSA 冻结成下游唯一消费的 `StructurePlan`。
//!
//! branch、loop、short-circuit 与 island 候选只作为内部 evidence；冲突消解、edge
//! transfer、phi/cleanup owner、label 与目标能力要求都必须在进入 HIR 前确定。

mod analyze;
mod branch_values;
mod branches;
mod cfg;
mod common;
#[cfg(feature = "decompile-debug")]
mod debug;
mod error;
mod goto;
mod helpers;
mod loops;
mod phi_facts;
mod plan;
mod regions;
mod scope;
mod short_circuit;

pub(crate) use analyze::analyze_structure_stage;
pub use cfg::{
    BasicBlock, BlockKind, BlockRef, Cfg, CfgEdge, CfgGraph, DataflowFacts, Def, DefId,
    DominatorTree, EdgeKind, EdgeRef, EffectTag, GraphFacts, InstrEffect, InstrRange,
    InstrUseValues, NaturalLoop, OpenDef, OpenDefId, OpenUseSources, PhiCandidate, PhiId,
    PhiIncoming, PostDominatorTree, ReachableSuccessorShape, SideEffectSummary, SsaRegMap,
    SsaValue, UseSite, build_cfg_graph, compute_dataflow_facts,
};
pub(crate) use common::{
    BranchCandidate, BranchRegionFact, BranchValueMergeCandidate, LoopCandidate, LoopExitAlias,
    LoopExitValueMergeCandidate, LoopKindHint, LoopSourceBindings, LoopValueIncoming,
    LoopValueMerge, RegionFact, ScopePlan, ShortCircuitCandidate, ShortCircuitExit,
    ShortCircuitNode, ShortCircuitNodeRef, ShortCircuitTarget, ShortCircuitValueIncoming,
    UnstructuredRegionLayout,
};
pub use common::{BranchKind, GotoReason, PhiEdgeCopy, StructureFacts, StructurePlan};
#[cfg(feature = "decompile-debug")]
pub use debug::dump_structure;
pub use error::StructureError;
pub(crate) use phi_facts::CanonicalMoveIndex;
pub use plan::{
    BlockEmissionPlan, BlockTerminatorKind, BlockTerminatorPlan, BranchArm, BranchPlanData,
    BranchPlanId, BranchValuePlan, CleanupDisposition, ConditionArcPlan, ConditionArcPolarity,
    ConditionArcRef, ConditionNodeId, ConditionNodePlan, ConditionPlan, ConditionPlanId,
    ConditionTarget, ConditionValuePlan, ControlFlowFeature, EdgeCopyOrigin, EdgePlan,
    EdgeTransfer, ForwardRouteId, ForwardRouteKind, ForwardRoutePlan, GenericForProtocol,
    LabelPlacement, LabelPlan, LabelPlanId, LoopConditionPrefixPlacement, LoopConditionProtocol,
    LoopControlEdges, LoopIterationDisposition, LoopNormalTailPlan, LoopPlanData, LoopPlanId,
    LoopRepeatForm, LoopRepeatProtocol, LoopRepeatStagedResult, LoopRepeatValuePlan,
    LoopValueActionBatch, LoopValueActions, LoopValuePhase, LoopValueSource, LoopValueWrite,
    LoopVmProtocol, NumericForProtocol, PhiIncomingDisposition, PhiIncomingPlan, PhiPlan,
    PlanRequirement, PlanRequirementId, PlanRequirements, RegionId, RegionPlan, ScopePlanId,
    SinglePassPlan, SinglePassPlanId, TbcScopePlan, TbcScopePlanId, UnstructuredLayoutItem,
    ValueDecisionArcPlan, ValueDecisionLeafId, ValueDecisionLeafPlan, ValueDecisionNodeId,
    ValueDecisionNodePlan, ValueDecisionPlan, ValueDecisionPlanId, ValueDecisionTarget,
};
#[cfg(not(feature = "decompile-debug"))]
mod debug {
    crate::debug::define_unavailable_stage_dump!(dump_structure);
}
#[cfg(not(feature = "decompile-debug"))]
pub use debug::dump_structure;
