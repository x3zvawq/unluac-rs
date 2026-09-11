//! 这个目录集中声明 CFG、图分析和数据流层共享的公共类型。
//!
//! 这些层都不再带 dialect-specific 语义，所以这里按“构图事实 / 图分析事实 /
//! 数据流事实”继续拆开，避免一个 `common.rs` 同时承载太多不同职责。

mod cfg;
mod dataflow;
mod graph;
mod phi_graph;
mod root_intervals;

pub(crate) use dataflow::{PhiIncomingSlot, RegCaptures};
pub(crate) use graph::{SccFacts, SccId};
pub(crate) use phi_graph::PhiGraphFacts;
pub(crate) use root_intervals::RootIntervalIndex;

pub use cfg::{
    BasicBlock, BlockKind, BlockRef, Cfg, CfgEdge, CfgGraph, EdgeKind, EdgeRef, InstrRange,
    ReachableSuccessorShape,
};
pub use dataflow::{
    DataflowFacts, Def, DefId, EffectTag, InstrEffect, InstrUseValues, OpenDef, OpenDefId,
    OpenUseSources, PhiCandidate, PhiId, PhiIncoming, RootObservation, SideEffectSummary,
    SsaRegMap, SsaValue, UseSite,
};
pub use graph::{
    DominatorTree, GraphFacts, NaturalLoop, NaturalLoopAncestors, NaturalLoopForest, NaturalLoopId,
    PostDominatorTree,
};
