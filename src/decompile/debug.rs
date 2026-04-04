//! 这个文件实现主 pipeline 共享的调试调度逻辑。
//!
//! 默认构建会保留完整调试导出能力，方便 CLI 和仓库内调试工作流复用；
//! 当关闭 `decompile-debug` feature 时，这里会退化成只保留公共类型与空实现，
//! 让 wasm 发布产物不再把各阶段 dump 渲染逻辑一起打包进去。

#[cfg(feature = "decompile-debug")]
use crate::ast;
#[cfg(feature = "decompile-debug")]
use crate::cfg;
use crate::debug::{DebugDetail, DebugFilters};
#[cfg(feature = "decompile-debug")]
use crate::generate;
#[cfg(feature = "decompile-debug")]
use crate::hir;
#[cfg(feature = "decompile-debug")]
use crate::naming;
#[cfg(feature = "decompile-debug")]
use crate::parser;
#[cfg(feature = "decompile-debug")]
use crate::structure;
#[cfg(feature = "decompile-debug")]
use crate::transformer;

use super::error::DecompileError;
use super::state::{DecompileStage, DecompileState};

/// 供主 pipeline 和 CLI 共享的调试选项。
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct DebugOptions {
    pub enable: bool,
    pub output_stages: Vec<DecompileStage>,
    pub timing: bool,
    pub color: crate::debug::DebugColorMode,
    pub detail: DebugDetail,
    pub filters: DebugFilters,
}

/// 某个阶段导出的调试文本。
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct StageDebugOutput {
    pub stage: DecompileStage,
    pub detail: DebugDetail,
    pub content: String,
}

/// 对外保留 parser 阶段的统一包装，方便库层调用方继续从 decompile 命名空间访问。
#[cfg(feature = "decompile-debug")]
pub fn dump_parser(
    chunk: &crate::parser::RawChunk,
    options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Ok(StageDebugOutput {
        stage: DecompileStage::Parse,
        detail: options.detail,
        content: parser::dump_parser(chunk, options.detail, &options.filters, options.color),
    })
}

/// 对外保留 parser 阶段的统一包装，方便库层调用方继续从 decompile 命名空间访问。
#[cfg(not(feature = "decompile-debug"))]
pub fn dump_parser(
    _chunk: &crate::parser::RawChunk,
    _options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Err(DecompileError::DebugUnavailable)
}

/// 对外保留 transformer 阶段的统一包装，方便库层调用方继续从 decompile 命名空间访问。
#[cfg(feature = "decompile-debug")]
pub fn dump_lir(
    chunk: &crate::transformer::LoweredChunk,
    options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Ok(StageDebugOutput {
        stage: DecompileStage::Transform,
        detail: options.detail,
        content: transformer::dump_lir(chunk, options.detail, &options.filters, options.color),
    })
}

/// 对外保留 transformer 阶段的统一包装，方便库层调用方继续从 decompile 命名空间访问。
#[cfg(not(feature = "decompile-debug"))]
pub fn dump_lir(
    _chunk: &crate::transformer::LoweredChunk,
    _options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Err(DecompileError::DebugUnavailable)
}

/// 对外保留 CFG 阶段的统一包装，方便库层调用方继续从 decompile 命名空间访问。
#[cfg(feature = "decompile-debug")]
pub fn dump_cfg(
    graph: &crate::cfg::CfgGraph,
    options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Ok(StageDebugOutput {
        stage: DecompileStage::Cfg,
        detail: options.detail,
        content: cfg::dump_cfg(graph, options.detail, &options.filters, options.color),
    })
}

/// 对外保留 CFG 阶段的统一包装，方便库层调用方继续从 decompile 命名空间访问。
#[cfg(not(feature = "decompile-debug"))]
pub fn dump_cfg(
    _graph: &crate::cfg::CfgGraph,
    _options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Err(DecompileError::DebugUnavailable)
}

/// 对外保留 GraphFacts 阶段的统一包装。
#[cfg(feature = "decompile-debug")]
pub fn dump_graph_facts(
    graph_facts: &crate::cfg::GraphFacts,
    options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Ok(StageDebugOutput {
        stage: DecompileStage::GraphFacts,
        detail: options.detail,
        content: cfg::dump_graph_facts(
            graph_facts,
            options.detail,
            &options.filters,
            options.color,
        ),
    })
}

/// 对外保留 GraphFacts 阶段的统一包装。
#[cfg(not(feature = "decompile-debug"))]
pub fn dump_graph_facts(
    _graph_facts: &crate::cfg::GraphFacts,
    _options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Err(DecompileError::DebugUnavailable)
}

/// 对外保留 Dataflow 阶段的统一包装。
#[cfg(feature = "decompile-debug")]
pub fn dump_dataflow(
    lowered: &crate::transformer::LoweredChunk,
    cfg_graph: &crate::cfg::CfgGraph,
    dataflow: &crate::cfg::DataflowFacts,
    options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Ok(StageDebugOutput {
        stage: DecompileStage::Dataflow,
        detail: options.detail,
        content: cfg::dump_dataflow(
            lowered,
            cfg_graph,
            dataflow,
            options.detail,
            &options.filters,
            options.color,
        ),
    })
}

/// 对外保留 Dataflow 阶段的统一包装。
#[cfg(not(feature = "decompile-debug"))]
pub fn dump_dataflow(
    _lowered: &crate::transformer::LoweredChunk,
    _cfg_graph: &crate::cfg::CfgGraph,
    _dataflow: &crate::cfg::DataflowFacts,
    _options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Err(DecompileError::DebugUnavailable)
}

/// 对外保留 StructureFacts 阶段的统一包装。
#[cfg(feature = "decompile-debug")]
pub fn dump_structure(
    structure_facts: &crate::structure::StructureFacts,
    options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Ok(StageDebugOutput {
        stage: DecompileStage::StructureFacts,
        detail: options.detail,
        content: structure::dump_structure(
            structure_facts,
            options.detail,
            &options.filters,
            options.color,
        ),
    })
}

/// 对外保留 StructureFacts 阶段的统一包装。
#[cfg(not(feature = "decompile-debug"))]
pub fn dump_structure(
    _structure_facts: &crate::structure::StructureFacts,
    _options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Err(DecompileError::DebugUnavailable)
}

/// 对外保留 HIR 阶段的统一包装。
#[cfg(feature = "decompile-debug")]
pub fn dump_hir(
    hir_module: &crate::hir::HirModule,
    options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Ok(StageDebugOutput {
        stage: DecompileStage::Hir,
        detail: options.detail,
        content: hir::dump_hir(hir_module, options.detail, &options.filters, options.color),
    })
}

/// 对外保留 HIR 阶段的统一包装。
#[cfg(not(feature = "decompile-debug"))]
pub fn dump_hir(
    _hir_module: &crate::hir::HirModule,
    _options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Err(DecompileError::DebugUnavailable)
}

/// 对外保留 AST 阶段的统一包装。
#[cfg(feature = "decompile-debug")]
pub fn dump_ast(
    ast_module: &crate::ast::AstModule,
    options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Ok(StageDebugOutput {
        stage: DecompileStage::Ast,
        detail: options.detail,
        content: ast::dump_ast(ast_module, options.detail, &options.filters, options.color),
    })
}

/// 对外保留 AST 阶段的统一包装。
#[cfg(not(feature = "decompile-debug"))]
pub fn dump_ast(
    _ast_module: &crate::ast::AstModule,
    _options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Err(DecompileError::DebugUnavailable)
}

/// 对外保留 Readability 阶段的统一包装。
#[cfg(feature = "decompile-debug")]
pub fn dump_readability(
    ast_module: &crate::ast::AstModule,
    options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Ok(StageDebugOutput {
        stage: DecompileStage::Readability,
        detail: options.detail,
        content: ast::dump_readability(ast_module, options.detail, &options.filters, options.color),
    })
}

/// 对外保留 Readability 阶段的统一包装。
#[cfg(not(feature = "decompile-debug"))]
pub fn dump_readability(
    _ast_module: &crate::ast::AstModule,
    _options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Err(DecompileError::DebugUnavailable)
}

/// 对外保留 Naming 阶段的统一包装。
#[cfg(feature = "decompile-debug")]
pub fn dump_naming(
    names: &crate::naming::NameMap,
    options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Ok(StageDebugOutput {
        stage: DecompileStage::Naming,
        detail: options.detail,
        content: naming::dump_naming(names, options.detail, &options.filters, options.color),
    })
}

/// 对外保留 Naming 阶段的统一包装。
#[cfg(not(feature = "decompile-debug"))]
pub fn dump_naming(
    _names: &crate::naming::NameMap,
    _options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Err(DecompileError::DebugUnavailable)
}

/// 对外保留 Generate 阶段的统一包装。
#[cfg(feature = "decompile-debug")]
pub fn dump_generate(
    chunk: &crate::generate::GeneratedChunk,
    options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Ok(StageDebugOutput {
        stage: DecompileStage::Generate,
        detail: options.detail,
        content: generate::dump_generate(chunk, options.detail, &options.filters, options.color),
    })
}

/// 对外保留 Generate 阶段的统一包装。
#[cfg(not(feature = "decompile-debug"))]
pub fn dump_generate(
    _chunk: &crate::generate::GeneratedChunk,
    _options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    Err(DecompileError::DebugUnavailable)
}

#[cfg(feature = "decompile-debug")]
pub(crate) fn collect_stage_dump(
    state: &DecompileState,
    stage: DecompileStage,
    options: &DebugOptions,
) -> Result<Option<StageDebugOutput>, DecompileError> {
    if !options.enable || !options.output_stages.contains(&stage) {
        return Ok(None);
    }

    match stage {
        DecompileStage::Parse => {
            let Some(chunk) = state.raw_chunk.as_ref() else {
                return Err(DecompileError::MissingStageOutput { stage });
            };
            dump_parser(chunk, options).map(Some)
        }
        DecompileStage::Transform => {
            let Some(chunk) = state.lowered.as_ref() else {
                return Err(DecompileError::MissingStageOutput { stage });
            };
            dump_lir(chunk, options).map(Some)
        }
        DecompileStage::Cfg => {
            let Some(graph) = state.cfg.as_ref() else {
                return Err(DecompileError::MissingStageOutput { stage });
            };
            dump_cfg(graph, options).map(Some)
        }
        DecompileStage::GraphFacts => {
            let Some(graph_facts) = state.graph_facts.as_ref() else {
                return Err(DecompileError::MissingStageOutput { stage });
            };
            dump_graph_facts(graph_facts, options).map(Some)
        }
        DecompileStage::Dataflow => {
            let Some(lowered) = state.lowered.as_ref() else {
                return Err(DecompileError::MissingStageOutput { stage });
            };
            let Some(cfg_graph) = state.cfg.as_ref() else {
                return Err(DecompileError::MissingStageOutput { stage });
            };
            let Some(dataflow) = state.dataflow.as_ref() else {
                return Err(DecompileError::MissingStageOutput { stage });
            };
            dump_dataflow(lowered, cfg_graph, dataflow, options).map(Some)
        }
        DecompileStage::StructureFacts => {
            let Some(structure_facts) = state.structure_facts.as_ref() else {
                return Err(DecompileError::MissingStageOutput { stage });
            };
            dump_structure(structure_facts, options).map(Some)
        }
        DecompileStage::Hir => {
            let Some(hir_module) = state.hir.as_ref() else {
                return Err(DecompileError::MissingStageOutput { stage });
            };
            dump_hir(hir_module, options).map(Some)
        }
        DecompileStage::Ast => {
            let Some(ast_module) = state.ast.as_ref() else {
                return Err(DecompileError::MissingStageOutput { stage });
            };
            dump_ast(ast_module, options).map(Some)
        }
        DecompileStage::Readability => {
            let Some(ast_module) = state.readability.as_ref() else {
                return Err(DecompileError::MissingStageOutput { stage });
            };
            dump_readability(ast_module, options).map(Some)
        }
        DecompileStage::Naming => {
            let Some(names) = state.naming.as_ref() else {
                return Err(DecompileError::MissingStageOutput { stage });
            };
            dump_naming(names, options).map(Some)
        }
        DecompileStage::Generate => {
            let Some(chunk) = state.generated.as_ref() else {
                return Err(DecompileError::MissingStageOutput { stage });
            };
            dump_generate(chunk, options).map(Some)
        }
    }
}

#[cfg(not(feature = "decompile-debug"))]
pub(crate) fn collect_stage_dump(
    _state: &DecompileState,
    _stage: DecompileStage,
    _options: &DebugOptions,
) -> Result<Option<StageDebugOutput>, DecompileError> {
    Ok(None)
}
