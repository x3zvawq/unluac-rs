//! 主反编译流水线的统一对外接口。

mod contracts;
mod error;
mod options;
mod pipeline;
mod stages;
mod state;
mod timing;

pub use crate::analysis::dump_analysis;
pub use crate::ast::dump_ast;
pub use crate::ast::{FunctionNameMap, NameInfo, NameMap, NameSource, NamingMode, NamingOptions};
pub use crate::debug::{DebugColorMode, DebugDetail, DebugFilters, ProtoDepth};
pub use crate::generate::dump_generate;
pub use crate::generate::{
    CommentStyle, GenerateMode, GenerateOptions, GeneratedChunkKind, LuauVectorConstructor,
    LuauVectorSize, NumberFormat, QuoteStyle, TableCellAlign, TableStyle, collect_error_protos,
    generate_proto_source,
};
pub use crate::parser::dump_parser;
pub use timing::{TimingNode, TimingReport, render_timing_report};
pub use crate::transformer::dump_lir;
pub use contracts::{
    AnalysisChunk, AstChunk, CfgGraph, GeneratedChunk, LoweredChunk, NamingResult,
};
pub use error::DecompileError;
pub use options::{
    ControlFlowCaps, DebugOptions, DecompileDialect, DecompileOptions, ReadabilityOptions,
};
pub use pipeline::{DecompileResult, decompile};
pub(crate) use state::DecompileContext;
pub use state::{DecompileStage, DecompileState, StageDebugOutput};
