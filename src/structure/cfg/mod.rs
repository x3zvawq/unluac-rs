//! 这个模块承载 Structure 层内部的 CFG / 图事实 / 数据流分析。
//!
//! 从 CFG 开始，这些逻辑已经不再依赖某个 Lua dialect 的原始 opcode 细节，
//! 因此统一收敛到一个共享模块里，后续 StructureFacts/HIR 也直接复用这里的事实。

mod build;
mod common;
mod dataflow;
#[cfg(feature = "decompile-debug")]
mod debug;
mod graph;

pub use build::build_cfg_graph;
pub(crate) use build::build_cfg_proto;
pub use common::{
    BasicBlock, BlockKind, BlockRef, Cfg, CfgEdge, CfgGraph, DataflowFacts, Def, DefId,
    DominatorTree, EdgeKind, EdgeRef, EffectTag, GraphFacts, InstrEffect, InstrRange,
    InstrUseValues, NaturalLoop, OpenDef, OpenDefId, OpenUseSources, PhiCandidate, PhiId,
    PhiIncoming, PostDominatorTree, ReachableSuccessorShape, SideEffectSummary, SsaRegMap,
    SsaValue, UseSite,
};
pub(crate) use dataflow::analyze_dataflow;
pub use dataflow::compute_dataflow_facts;
#[cfg(feature = "decompile-debug")]
pub(super) use debug::{dump_cfg_graph, dump_dataflow_facts, dump_graph_facts_tree};
pub(crate) use graph::analyze_graph_facts;
