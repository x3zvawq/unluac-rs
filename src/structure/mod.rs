//! 这个模块承载 Structure 层的共享实现。
//!
//! 从这一层开始，我们正式把图事实和数据流事实转成更贴近源码恢复的候选集合，
//! 但仍然刻意停在“候选/约束”层，不替 HIR 过早做最终语法决定。

mod analyze;
mod branch_values;
mod branches;
mod cfg;
mod common;
mod debug;
mod goto;
mod helpers;
mod loops;
mod phi_facts;
mod regions;
mod scope;
mod short_circuit;

pub(crate) use analyze::analyze_structure_stage;
pub use cfg::{
    BasicBlock, BlockKind, BlockRef, Cfg, CfgEdge, CfgGraph, CompactSet, DataflowFacts, Def, DefId,
    DominatorTree, EdgeKind, EdgeRef, EffectTag, GraphFacts, InstrEffect, InstrRange,
    InstrReachingDefs, InstrReachingValues, InstrUseDefs, InstrUseValues, NaturalLoop, OpenDef,
    OpenDefId, OpenUseSite, PhiCandidate, PhiId, PhiIncoming, PostDominatorTree,
    ReachableSuccessorShape, RegValueMap, SideEffectSummary, SsaValue, UseSite, ValueMapRef,
    ValueSetRef, build_cfg_graph, compute_dataflow_facts,
};
pub use common::{
    BranchCandidate, BranchKind, BranchRegionFact, BranchValueMergeArm, BranchValueMergeCandidate,
    BranchValueMergeValue, GenericPhiMaterialization, GotoReason, GotoRequirement, LoopCandidate,
    LoopExitValueMergeCandidate, LoopKindHint, LoopSourceBindings, LoopValueArm, LoopValueIncoming,
    LoopValueMerge, RegionFact, RegionKind, ScopeCandidate, ScopeKind, ShortCircuitCandidate,
    ShortCircuitExit, ShortCircuitNode, ShortCircuitNodeRef, ShortCircuitTarget,
    ShortCircuitValueIncoming, StructureFacts,
};
pub use debug::dump_structure;
