//! 这个文件实现主 pipeline 共享的调试调度逻辑。
//!
//! 默认构建会保留完整调试导出能力，方便 CLI 和仓库内调试工作流复用；
//! 当关闭 `decompile-debug` feature 时，这里会退化成只保留公共类型与空实现，
//! 让 wasm 发布产物不再把各阶段 dump 渲染逻辑一起打包进去。
//!
//! 所有 `dump_*` 公共函数通过 `define_stage_dump!` 宏统一生成，
//! 避免每个阶段手写一对 `#[cfg]` / `#[cfg(not)]` 实现。

use crate::debug::{DebugDetail, DebugFilters};

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
    /// 需要输出 before/after 快照的 pass 名称列表。
    ///
    /// 支持 HIR simplify pass（如 `carried-locals`、`temp-inline`）和
    /// AST readability pass（如 `inline-exprs`、`branch-pretty`）。
    /// 当 pass 执行且产生了变化时，向 stderr 输出变化前后的 proto/function dump。
    pub dump_passes: Vec<String>,
}

/// 某个阶段导出的调试文本。
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct StageDebugOutput {
    pub stage: DecompileStage,
    pub detail: DebugDetail,
    pub content: String,
}

/// 生成一对 `#[cfg(feature)]` / `#[cfg(not)]` 的阶段 dump 包装函数。
///
/// 启用 `decompile-debug` 时调用底层模块的 dump 函数并包装为 `StageDebugOutput`；
/// 禁用时统一返回 `DebugUnavailable`，让 wasm 产物不带渲染逻辑。
macro_rules! define_stage_dump {
    (
        $(#[doc = $doc:literal])*
        pub fn $name:ident ( $($arg:ident : & $arg_ty:ty),+ $(,)? )
            => $stage:expr, $inner:expr
    ) => {
        $(#[doc = $doc])*
        #[cfg(feature = "decompile-debug")]
        pub fn $name(
            $($arg: &$arg_ty,)+
            options: &DebugOptions,
        ) -> Result<StageDebugOutput, DecompileError> {
            Ok(StageDebugOutput {
                stage: $stage,
                detail: options.detail,
                content: $inner($($arg,)+ options.detail, &options.filters, options.color),
            })
        }

        $(#[doc = $doc])*
        #[cfg(not(feature = "decompile-debug"))]
        pub fn $name(
            $(_: &$arg_ty,)+
            _options: &DebugOptions,
        ) -> Result<StageDebugOutput, DecompileError> {
            Err(DecompileError::DebugUnavailable)
        }
    };
}

define_stage_dump! {
    /// Parser 阶段的调试导出。
    pub fn dump_parser(chunk: &crate::parser::RawChunk)
        => DecompileStage::Parse, crate::parser::dump_parser
}

define_stage_dump! {
    /// Transformer 阶段的调试导出。
    pub fn dump_lir(chunk: &crate::transformer::LoweredChunk)
        => DecompileStage::Transform, crate::transformer::dump_lir
}

define_stage_dump! {
    /// CFG 阶段的调试导出。
    pub fn dump_cfg(graph: &crate::cfg::CfgGraph)
        => DecompileStage::Cfg, crate::cfg::dump_cfg
}

define_stage_dump! {
    /// GraphFacts 阶段的调试导出。
    pub fn dump_graph_facts(graph_facts: &crate::cfg::GraphFacts)
        => DecompileStage::GraphFacts, crate::cfg::dump_graph_facts
}

define_stage_dump! {
    /// Dataflow 阶段的调试导出。
    pub fn dump_dataflow(
        lowered: &crate::transformer::LoweredChunk,
        cfg_graph: &crate::cfg::CfgGraph,
        dataflow: &crate::cfg::DataflowFacts
    ) => DecompileStage::Dataflow, crate::cfg::dump_dataflow
}

define_stage_dump! {
    /// StructureFacts 阶段的调试导出。
    pub fn dump_structure(structure_facts: &crate::structure::StructureFacts)
        => DecompileStage::StructureFacts, crate::structure::dump_structure
}

define_stage_dump! {
    /// HIR 阶段的调试导出。
    pub fn dump_hir(hir_module: &crate::hir::HirModule)
        => DecompileStage::Hir, crate::hir::dump_hir
}

define_stage_dump! {
    /// AST 阶段的调试导出。
    pub fn dump_ast(ast_module: &crate::ast::AstModule)
        => DecompileStage::Ast, crate::ast::dump_ast
}

define_stage_dump! {
    /// Readability 阶段的调试导出。
    pub fn dump_readability(ast_module: &crate::ast::AstModule)
        => DecompileStage::Readability, crate::ast::dump_readability
}

define_stage_dump! {
    /// Naming 阶段的调试导出。
    pub fn dump_naming(names: &crate::naming::NameMap)
        => DecompileStage::Naming, crate::naming::dump_naming
}

define_stage_dump! {
    /// Generate 阶段的调试导出。
    pub fn dump_generate(chunk: &crate::generate::GeneratedChunk)
        => DecompileStage::Generate, crate::generate::dump_generate
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
