//! 这个模块承载 low-IR 之上的共享分析层。
//!
//! 从 CFG 开始，这些逻辑已经不再依赖某个 Lua dialect 的原始 opcode 细节，
//! 因此统一收敛到一个共享模块里，后续 StructureFacts/HIR 也直接复用这里的事实。

mod build;
mod common;
mod dataflow;
mod debug;
mod graph;

pub use build::build_cfg_graph;
pub use common::{
    BasicBlock, BlockKind, BlockRef, Cfg, CfgEdge, CfgGraph, CompactSet, DataflowFacts, Def, DefId,
    DominatorTree, EdgeKind, EdgeRef, EffectTag, GraphFacts, InstrEffect, InstrRange,
    InstrReachingDefs, InstrReachingValues, InstrUseDefs, InstrUseValues, NaturalLoop, OpenDef,
    OpenDefId, OpenUseSite, PhiCandidate, PhiId, PhiIncoming, PostDominatorTree, RegValueMap,
    SideEffectSummary, SsaValue, UseSite, ValueMapRef, ValueSetRef,
};
pub use dataflow::analyze_dataflow;
pub use debug::{dump_cfg, dump_dataflow, dump_graph_facts};
pub use graph::analyze_graph_facts;
