//! 这个文件实现主反编译 pipeline 的统一入口。
//!
//! 当前只真正接上 parser，但入口已经先按完整阶段序列搭好；
//! 这样后续补层时只需要往这个骨架里填实现，不需要重写调用约定。

use crate::ast::{
    AstDialectVersion, AstTargetDialect, lower_ast, make_readable_with_options_and_timing,
};
use crate::cfg::{analyze_dataflow, analyze_graph_facts, build_cfg_graph};
use crate::generate::generate_chunk;
use crate::hir::analyze_hir_with_timing;
use crate::naming::assign_names;
use crate::parser::{
    parse_lua51_chunk, parse_lua52_chunk, parse_lua53_chunk, parse_lua54_chunk, parse_lua55_chunk,
};
use crate::structure::analyze_structure;
use crate::timing::{TimingCollector, TimingReport};
use crate::transformer::lower_chunk;

use super::debug::{StageDebugOutput, collect_stage_dump};
use super::error::DecompileError;
use super::options::{DecompileDialect, DecompileOptions};
use super::state::{DecompileStage, DecompileState};

/// 一次主 pipeline 调用的返回值。
#[derive(Debug, Clone, PartialEq)]
pub struct DecompileResult {
    pub state: DecompileState,
    pub debug_output: Vec<StageDebugOutput>,
    pub timing_report: Option<TimingReport>,
}

/// 对外暴露唯一的主入口，统一完成默认值补齐和阶段调度。
pub fn decompile(
    bytes: &[u8],
    options: DecompileOptions,
) -> Result<DecompileResult, DecompileError> {
    DecompilerPipeline.run(bytes, options)
}

struct DecompilerPipeline;

impl DecompilerPipeline {
    fn run(
        self,
        bytes: &[u8],
        options: DecompileOptions,
    ) -> Result<DecompileResult, DecompileError> {
        let options = options.normalized();

        let mut state = DecompileState::new(options.dialect, options.target_stage);
        let mut debug_output = Vec::new();
        let timings = TimingCollector::new(options.debug.enable && options.debug.timing);

        state.raw_chunk =
            Some(
                timings.record(DecompileStage::Parse.label(), || match options.dialect {
                    DecompileDialect::Lua51 => parse_lua51_chunk(bytes, options.parse),
                    DecompileDialect::Lua52 => parse_lua52_chunk(bytes, options.parse),
                    DecompileDialect::Lua53 => parse_lua53_chunk(bytes, options.parse),
                    DecompileDialect::Lua54 => parse_lua54_chunk(bytes, options.parse),
                    DecompileDialect::Lua55 => parse_lua55_chunk(bytes, options.parse),
                })?,
            );
        state.mark_completed(DecompileStage::Parse);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Parse, &options.debug)? {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Parse {
            return Ok(finish_result(state, debug_output, &timings));
        }

        let raw_chunk = state
            .raw_chunk
            .as_ref()
            .expect("parse stage completed must leave raw_chunk in state");
        state.lowered =
            Some(timings.record(DecompileStage::Transform.label(), || lower_chunk(raw_chunk))?);
        state.mark_completed(DecompileStage::Transform);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Transform, &options.debug)?
        {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Transform {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.cfg = Some(timings.record(DecompileStage::Cfg.label(), || {
            let lowered = state
                .lowered
                .as_ref()
                .expect("transform stage completed must leave lowered in state");
            build_cfg_graph(lowered)
        }));
        state.mark_completed(DecompileStage::Cfg);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Cfg, &options.debug)? {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Cfg {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.graph_facts = Some(timings.record(DecompileStage::GraphFacts.label(), || {
            let cfg_graph = state
                .cfg
                .as_ref()
                .expect("cfg stage completed must leave cfg graph in state");
            analyze_graph_facts(cfg_graph)
        }));
        state.mark_completed(DecompileStage::GraphFacts);

        if let Some(output) =
            collect_stage_dump(&state, DecompileStage::GraphFacts, &options.debug)?
        {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::GraphFacts {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.dataflow = Some(timings.record(DecompileStage::Dataflow.label(), || {
            let lowered = state
                .lowered
                .as_ref()
                .expect("transform stage completed must leave lowered in state");
            let cfg_graph = state
                .cfg
                .as_ref()
                .expect("cfg stage completed must leave cfg graph in state");
            let graph_facts = state
                .graph_facts
                .as_ref()
                .expect("graph facts stage completed must leave graph facts in state");
            analyze_dataflow(lowered, cfg_graph, graph_facts)
        }));
        state.mark_completed(DecompileStage::Dataflow);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Dataflow, &options.debug)?
        {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Dataflow {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.structure_facts =
            Some(timings.record(DecompileStage::StructureFacts.label(), || {
                let lowered = state
                    .lowered
                    .as_ref()
                    .expect("transform stage completed must leave lowered in state");
                let cfg_graph = state
                    .cfg
                    .as_ref()
                    .expect("cfg stage completed must leave cfg graph in state");
                let graph_facts = state
                    .graph_facts
                    .as_ref()
                    .expect("graph facts stage completed must leave graph facts in state");
                let dataflow = state
                    .dataflow
                    .as_ref()
                    .expect("dataflow stage completed must leave dataflow in state");
                analyze_structure(lowered, cfg_graph, graph_facts, dataflow)
            }));
        state.mark_completed(DecompileStage::StructureFacts);

        if let Some(output) =
            collect_stage_dump(&state, DecompileStage::StructureFacts, &options.debug)?
        {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::StructureFacts {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.hir = Some(timings.record(DecompileStage::Hir.label(), || {
            let lowered = state
                .lowered
                .as_ref()
                .expect("transform stage completed must leave lowered in state");
            let cfg_graph = state
                .cfg
                .as_ref()
                .expect("cfg stage completed must leave cfg graph in state");
            let graph_facts = state
                .graph_facts
                .as_ref()
                .expect("graph facts stage completed must leave graph facts in state");
            let dataflow = state
                .dataflow
                .as_ref()
                .expect("dataflow stage completed must leave dataflow in state");
            let structure_facts = state
                .structure_facts
                .as_ref()
                .expect("structure stage completed must leave structure facts in state");
            analyze_hir_with_timing(
                lowered,
                cfg_graph,
                graph_facts,
                dataflow,
                structure_facts,
                &timings,
                options.readability,
            )
        }));
        state.mark_completed(DecompileStage::Hir);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Hir, &options.debug)? {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Hir {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.ast = Some(timings.record(DecompileStage::Ast.label(), || {
            let hir = state
                .hir
                .as_ref()
                .expect("hir stage completed must leave hir module in state");
            lower_ast(hir, target_ast_dialect(options.dialect))
        })?);
        state.mark_completed(DecompileStage::Ast);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Ast, &options.debug)? {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Ast {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.readability = Some(timings.record(DecompileStage::Readability.label(), || {
            let ast = state
                .ast
                .as_ref()
                .expect("ast stage completed must leave ast module in state");
            make_readable_with_options_and_timing(
                ast,
                target_ast_dialect(options.dialect),
                options.readability,
                &timings,
            )
        }));
        state.mark_completed(DecompileStage::Readability);

        if let Some(output) =
            collect_stage_dump(&state, DecompileStage::Readability, &options.debug)?
        {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Readability {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.naming = Some(timings.record(DecompileStage::Naming.label(), || {
            let ast = state
                .readability
                .as_ref()
                .expect("readability stage completed must leave readability result in state");
            let hir = state
                .hir
                .as_ref()
                .expect("hir stage completed must leave hir module in state");
            let raw_chunk = state
                .raw_chunk
                .as_ref()
                .expect("parse stage completed must leave raw chunk in state");
            assign_names(ast, hir, raw_chunk, options.naming)
        })?);
        state.mark_completed(DecompileStage::Naming);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Naming, &options.debug)? {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Naming {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.generated = Some(timings.record(DecompileStage::Generate.label(), || {
            let ast = state.readability.as_ref().expect(
                "readability stage completed must leave readability result in state",
            );
            let names = state
                .naming
                .as_ref()
                .expect("naming stage completed must leave name map in state");
            generate_chunk(ast, names, target_ast_dialect(options.dialect), options.generate)
        })?);
        state.mark_completed(DecompileStage::Generate);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Generate, &options.debug)? {
            debug_output.push(output);
        }

        Ok(finish_result(state, debug_output, &timings))
    }
}

fn finish_result(
    state: DecompileState,
    debug_output: Vec<StageDebugOutput>,
    timings: &TimingCollector,
) -> DecompileResult {
    DecompileResult {
        state,
        debug_output,
        timing_report: timings.finish(),
    }
}

fn target_ast_dialect(dialect: DecompileDialect) -> AstTargetDialect {
    let version = match dialect {
        DecompileDialect::Lua51 => AstDialectVersion::Lua51,
        DecompileDialect::Lua52 => AstDialectVersion::Lua52,
        DecompileDialect::Lua53 => AstDialectVersion::Lua53,
        DecompileDialect::Lua54 => AstDialectVersion::Lua54,
        DecompileDialect::Lua55 => AstDialectVersion::Lua55,
    };
    AstTargetDialect::new(version)
}
