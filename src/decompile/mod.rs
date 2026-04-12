//! 这个模块承载主反编译 pipeline 的库接口。
//!
//! 之所以单独抽这一层，是为了把“阶段顺序、跨层契约、调试导出”统一放在库里，
//! 避免 CLI、单测和后续 wasm 封装各自复制一套流程，最后行为慢慢分叉。

mod contracts;
mod debug;
mod error;
mod options;
mod output_plan;
mod pipeline;
mod state;

#[cfg(test)]
mod tests;

pub use crate::debug::{DebugColorMode, DebugDetail, DebugFilters};
pub use crate::generate::{GenerateMode, GenerateOptions, QuoteStyle, TableStyle};
pub use crate::naming::{
    FunctionNameMap, NameInfo, NameMap, NameSource, NamingMode, NamingOptions,
};
pub use crate::readability::ReadabilityOptions;
pub use crate::timing::{TimingNode, TimingReport, render_timing_report};
pub use contracts::{
    AstChunk, CfgGraph, DataflowFacts, GeneratedChunk, GraphFacts, HirChunk, LoweredChunk,
    NamingResult, ReadabilityResult, StructureFacts,
};
pub use debug::{
    DebugOptions, StageDebugOutput, dump_ast, dump_cfg, dump_dataflow, dump_generate,
    dump_graph_facts, dump_hir, dump_lir, dump_naming, dump_parser, dump_readability,
    dump_structure,
};
pub use error::DecompileError;
pub use options::{DecompileDialect, DecompileOptions};
pub use pipeline::{DecompileResult, decompile};
pub use state::{DecompileStage, DecompileState};
