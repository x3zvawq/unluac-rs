//! 这个文件实现主反编译 pipeline 的统一入口。
//!
//! 当前只真正接上 parser，但入口已经先按完整阶段序列搭好；
//! 这样后续补层时只需要往这个骨架里填实现，不需要重写调用约定。

use crate::ast::lower_ast;
use crate::cfg::{analyze_dataflow, analyze_graph_facts, build_cfg_proto};
use crate::generate::{
    GenerateChunkCommentMetadata, GenerateCommentMetadata, GenerateFunctionCommentMetadata,
    generate_chunk,
};
use crate::hir::{analyze_hir, PassDumpConfig};
use crate::naming::{assign_names_with_evidence, collect_naming_evidence};
use crate::structure::analyze_structure;
use crate::timing::{TimingCollector, TimingReport};
use crate::transformer::lower_chunk;

use super::debug::{StageDebugOutput, collect_stage_dump};
use super::error::DecompileError;
use super::options::DecompileOptions;
use super::output_plan::{ast_lowering_target, resolve_output_plan};
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
        let requested_target = crate::ast::AstTargetDialect::new(options.dialect.into());

        state.raw_chunk = Some({
            let _timing = timings.scope(DecompileStage::Parse.as_str());
            options.dialect.parse_chunk(bytes, options.parse)?
        });
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
        state.lowered = Some({
            let _timing = timings.scope(DecompileStage::Transform.as_str());
            lower_chunk(raw_chunk)?
        });
        state.mark_completed(DecompileStage::Transform);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Transform, &options.debug)?
        {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Transform {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.cfg = Some({
            let _timing = timings.scope(DecompileStage::Cfg.as_str());
            let lowered = state
                .lowered
                .as_ref()
                .expect("transform stage completed must leave lowered in state");
            build_cfg_proto(&lowered.main)
        });
        state.mark_completed(DecompileStage::Cfg);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Cfg, &options.debug)? {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Cfg {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.graph_facts = Some({
            let _timing = timings.scope(DecompileStage::GraphFacts.as_str());
            let cfg_graph = state
                .cfg
                .as_ref()
                .expect("cfg stage completed must leave cfg graph in state");
            analyze_graph_facts(cfg_graph)
        });
        state.mark_completed(DecompileStage::GraphFacts);

        if let Some(output) =
            collect_stage_dump(&state, DecompileStage::GraphFacts, &options.debug)?
        {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::GraphFacts {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.dataflow = Some({
            let _timing = timings.scope(DecompileStage::Dataflow.as_str());
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
            analyze_dataflow(&lowered.main, &cfg_graph.cfg, graph_facts, &cfg_graph.children)
        });
        state.mark_completed(DecompileStage::Dataflow);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Dataflow, &options.debug)?
        {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Dataflow {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.structure_facts = Some({
            let _timing = timings.scope(DecompileStage::StructureFacts.as_str());
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
                analyze_structure(&lowered.main, &cfg_graph.cfg, graph_facts, dataflow, &cfg_graph.children)
        });
        state.mark_completed(DecompileStage::StructureFacts);

        if let Some(output) =
            collect_stage_dump(&state, DecompileStage::StructureFacts, &options.debug)?
        {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::StructureFacts {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.hir = Some({
            let _timing = timings.scope(DecompileStage::Hir.as_str());
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
            let dump_config = PassDumpConfig {
                pass_names: options.debug.dump_passes.clone(),
                proto_filter: options.debug.filters.proto,
            };
            analyze_hir(
                lowered,
                cfg_graph,
                graph_facts,
                dataflow,
                structure_facts,
                &timings,
                options.readability,
                options.generate.mode,
                requested_target.version,
                &dump_config,
            )
        });
        state.mark_completed(DecompileStage::Hir);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Hir, &options.debug)? {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Hir {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.ast = Some({
            let _timing = timings.scope(DecompileStage::Ast.as_str());
            let hir = state
                .hir
                .as_ref()
                .expect("hir stage completed must leave hir module in state");
            lower_ast(
                hir,
                ast_lowering_target(requested_target, options.generate.mode),
                options.generate.mode,
            )
        }?);
        state.mark_completed(DecompileStage::Ast);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Ast, &options.debug)? {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Ast {
            return Ok(finish_result(state, debug_output, &timings));
        }

        let output_plan = {
            let _timing = timings.scope(DecompileStage::Readability.as_str());
            let ast = state
                .ast
                .as_ref()
                .expect("ast stage completed must leave ast module in state");
            resolve_output_plan(
                ast,
                requested_target,
                options.readability,
                options.generate.mode,
                &timings,
                &options.debug.dump_passes,
            )
        };
        let output_target = output_plan.target;
        let output_generate_mode = output_plan.generate_mode;
        let output_warnings = output_plan.warnings;
        state.readability = Some(output_plan.readability);
        state.mark_completed(DecompileStage::Readability);

        if let Some(output) =
            collect_stage_dump(&state, DecompileStage::Readability, &options.debug)?
        {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Readability {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.naming = Some({
            let _timing = timings.scope(DecompileStage::Naming.as_str());
            let ast = state
                .readability
                .as_ref()
                .expect("readability stage completed must leave readability result in state");
            let hir = state
                .hir
                .as_ref()
                .expect("hir stage completed must leave hir module in state");
            let evidence = {
                let _timing = timings.scope("collect-evidence");
                collect_naming_evidence(hir)
            }?;
            assign_names_with_evidence(ast, hir, &evidence, options.naming)
        }?);
        state.mark_completed(DecompileStage::Naming);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Naming, &options.debug)? {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Naming {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.generated = Some({
            let _timing = timings.scope(DecompileStage::Generate.as_str());
            let ast = state
                .readability
                .as_ref()
                .expect("readability stage completed must leave readability result in state");
            let names = state
                .naming
                .as_ref()
                .expect("naming stage completed must leave name map in state");
            let mut generate_options = options.generate;
            generate_options.mode = output_generate_mode;
            let comment_metadata = if generate_options.comment {
                let hir = state
                    .hir
                    .as_ref()
                    .expect("hir stage completed must leave hir module in state");
                Some(build_generate_comment_metadata(
                    hir,
                    options.parse.string_encoding.as_str(),
                ))
            } else {
                None
            };
            let mut generated = generate_chunk(
                ast,
                names,
                output_target,
                comment_metadata.as_ref(),
                generate_options,
            )?;
            generated.warnings = output_warnings;
            Ok::<_, crate::generate::GenerateError>(generated)
        }?);
        state.mark_completed(DecompileStage::Generate);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Generate, &options.debug)?
        {
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

fn build_generate_comment_metadata(
    hir: &crate::hir::HirModule,
    encoding: &str,
) -> GenerateCommentMetadata {
    let entry_source = hir
        .protos
        .get(hir.entry.index())
        .and_then(|proto| proto.source.clone());
    GenerateCommentMetadata {
        chunk: GenerateChunkCommentMetadata {
            file_name: entry_source,
            encoding: encoding.to_owned(),
        },
        functions: hir
            .protos
            .iter()
            .map(|proto| GenerateFunctionCommentMetadata {
                function: proto.id,
                source: proto.source.clone(),
                line_range: proto.line_range,
                signature: proto.signature,
                local_count: proto.locals.len(),
                upvalue_count: proto.upvalues.len(),
            })
            .collect(),
    }
}

