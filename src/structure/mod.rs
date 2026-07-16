//! 这个模块承载 Structure 层的共享实现。
//!
//! 从这一层开始，我们正式把图事实和数据流事实转成更贴近源码恢复的候选集合，
//! 但仍然刻意停在“候选/约束”层，不替 HIR 过早做最终语法决定。

mod analyze;
mod branch_values;
mod branches;
mod cfg;
mod common;
#[cfg(feature = "decompile-debug")]
mod debug;
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
pub use common::{
    BranchCandidate, BranchKind, BranchRegionFact, BranchValueMergeArm, BranchValueMergeCandidate,
    BranchValueMergeValue, GenericPhiMaterialization, GenericPhiSource, GotoReason,
    GotoRequirement, LoopCandidate, LoopExitValueMergeCandidate, LoopKindHint, LoopSourceBindings,
    LoopValueArm, LoopValueIncoming, LoopValueMerge, PhiEdgeCopy, RegionFact, ScopeCandidate,
    ShortCircuitCandidate, ShortCircuitExit, ShortCircuitNode, ShortCircuitNodeRef,
    ShortCircuitTarget, ShortCircuitValueIncoming, StructureFacts, StructurePlan,
    UnstructuredRegionLayout,
};
#[cfg(feature = "decompile-debug")]
pub use debug::dump_structure;
pub use plan::{
    BlockOwner, BranchCandidateId, BranchValueMergeId, CleanupDisposition, EdgeOwner,
    GotoRequirementId, LoopCandidateId, PhiIncomingDisposition, RegionId, ScopeCandidateId,
};
#[cfg(not(feature = "decompile-debug"))]
mod debug {
    crate::debug::define_unavailable_stage_dump!(dump_structure);
}
#[cfg(not(feature = "decompile-debug"))]
pub use debug::dump_structure;
