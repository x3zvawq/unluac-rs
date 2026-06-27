//! 这个模块承载主反编译 pipeline 的库接口。
//!
//! 之所以单独抽这一层，是为了把“阶段顺序、跨层契约、调试导出”统一放在库里，
//! 避免 CLI、单测和后续 wasm 封装各自复制一套流程，最后行为慢慢分叉。

mod contracts;
mod error;
mod options;
mod pipeline;
mod stages;
mod state;

pub use crate::ast::ReadabilityOptions;
pub use crate::ast::dump_ast;
pub use crate::ast::{FunctionNameMap, NameInfo, NameMap, NameSource, NamingMode, NamingOptions};
pub use crate::debug::{DebugColorMode, DebugDetail, DebugFilters, ProtoDepth};
pub use crate::generate::dump_generate;
pub use crate::generate::{GenerateMode, GenerateOptions, QuoteStyle, TableStyle};
pub use crate::hir::dump_hir;
pub use crate::parser::dump_parser;
pub use crate::structure::dump_structure;
pub use crate::timing::{TimingNode, TimingReport, render_timing_report};
pub use crate::transformer::dump_lir;
pub use contracts::{
    AstChunk, CfgGraph, DataflowFacts, GeneratedChunk, GraphFacts, HirChunk, LoweredChunk,
    NamingResult, ReadabilityResult, StructureFacts,
};
pub use error::DecompileError;
pub use options::{DebugOptions, DecompileDialect, DecompileOptions};
pub use pipeline::{DecompileResult, decompile};
pub(crate) use state::DecompileContext;
pub use state::{DecompileStage, DecompileState, StageDebugOutput};
