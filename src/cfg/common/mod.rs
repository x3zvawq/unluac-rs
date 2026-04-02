//! 这个目录集中声明 CFG、图分析和数据流层共享的公共类型。
//!
//! 这些层都不再带 dialect-specific 语义，所以这里按“构图事实 / 图分析事实 /
//! 数据流事实 / 紧凑共享容器”继续拆开，避免一个 `common.rs` 同时承载太多不同职责。

mod cfg;
mod dataflow;
mod graph;
mod storage;

pub use cfg::{
    BasicBlock, BlockKind, BlockRef, Cfg, CfgEdge, CfgGraph, EdgeKind, EdgeRef, InstrRange,
};
pub use dataflow::{
    DataflowFacts, Def, DefId, EffectTag, InstrEffect, InstrReachingDefs, InstrReachingValues,
    InstrUseDefs, InstrUseValues, OpenDef, OpenDefId, OpenUseSite, PhiCandidate, PhiId,
    PhiIncoming, SideEffectSummary, SsaValue, UseSite, ValueMapRef, ValueSetRef,
};
pub(crate) use dataflow::ValueFactsStorage;
pub use graph::{DominatorTree, GraphFacts, NaturalLoop, PostDominatorTree};
pub use storage::{CompactSet, RegValueMap};
