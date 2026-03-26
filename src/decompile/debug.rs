//! 这个文件实现主 pipeline 共享的调试调度逻辑。
//!
//! 各层具体如何渲染自己的 dump，应该尽量贴着实现放置；这里仅保留跨层共用的
//! 选项、阶段包装和主 pipeline 的分派逻辑，避免再次长成一个巨型总控文件。

use crate::ast;
use crate::cfg;
use crate::debug::{DebugDetail, DebugFilters};
use crate::hir;
use crate::parser;
use crate::structure;
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

/// 对外保留 transformer 阶段的统一包装，方便库层调用方继续从 decompile 命名空间访问。
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

/// 对外保留 CFG 阶段的统一包装，方便库层调用方继续从 decompile 命名空间访问。
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

/// 对外保留 GraphFacts 阶段的统一包装。
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

/// 对外保留 Dataflow 阶段的统一包装。
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

/// 对外保留 StructureFacts 阶段的统一包装。
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

/// 对外保留 HIR 阶段的统一包装。
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

/// 对外保留 AST 阶段的统一包装。
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

/// 对外保留 Readability 阶段的统一包装。
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
        _ => Err(DecompileError::MissingStageOutput { stage }),
    }
}
