//! 这个模块承载主反编译 pipeline 的库接口。
//!
//! 之所以单独抽这一层，是为了把“阶段顺序、跨层契约、调试导出”统一放在库里，
//! 避免 CLI、单测和后续 wasm 封装各自复制一套流程，最后行为慢慢分叉。

mod contracts;
mod debug;
mod error;
mod options;
mod pipeline;
mod state;

pub use crate::debug::{DebugDetail, DebugFilters};
pub use crate::readability::ReadabilityOptions;
pub use crate::timing::{TimingNode, TimingReport, render_timing_report};
pub use contracts::{
    AstChunk, CfgGraph, DataflowFacts, GeneratedChunk, GraphFacts, HirChunk, LoweredChunk,
    NamingResult, ReadabilityResult, StructureFacts,
};
pub use debug::{
    DebugOptions, StageDebugOutput, dump_ast, dump_cfg, dump_dataflow, dump_graph_facts, dump_hir,
    dump_lir, dump_parser, dump_readability, dump_structure,
};
pub use error::DecompileError;
pub use options::{DecompileDialect, DecompileOptions};
pub use pipeline::{DecompileResult, decompile};
pub use state::{DecompileStage, DecompileState};
