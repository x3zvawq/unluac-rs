//! 这个文件实现主反编译 pipeline 的统一入口。
//!
//! 当前只真正接上 parser，但入口已经先按完整阶段序列搭好；
//! 这样后续补层时只需要往这个骨架里填实现，不需要重写调用约定。

use crate::cfg::{analyze_dataflow, analyze_graph_facts, build_cfg_graph};
use crate::parser::parse_lua51_chunk;
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

        state.raw_chunk = Some(match options.dialect {
            DecompileDialect::Lua51 => parse_lua51_chunk(bytes, options.parse)?,
        });
        state.mark_completed(DecompileStage::Parse);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Parse, &options.debug)? {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Parse {
            return Ok(DecompileResult {
                state,
                debug_output,
            });
        }

        let raw_chunk = state
            .raw_chunk
            .as_ref()
            .expect("parse stage completed must leave raw_chunk in state");
        state.lowered = Some(lower_chunk(raw_chunk)?);
        state.mark_completed(DecompileStage::Transform);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Transform, &options.debug)?
        {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Transform {
            return Ok(DecompileResult {
                state,
                debug_output,
            });
        }

        state.cfg = Some({
            let lowered = state
                .lowered
                .as_ref()
                .expect("transform stage completed must leave lowered in state");
            build_cfg_graph(lowered)
        });
        state.mark_completed(DecompileStage::Cfg);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Cfg, &options.debug)? {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Cfg {
            return Ok(DecompileResult {
                state,
                debug_output,
            });
        }

        state.graph_facts = Some({
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
            return Ok(DecompileResult {
                state,
                debug_output,
            });
        }

        state.dataflow = Some({
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
        });
        state.mark_completed(DecompileStage::Dataflow);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Dataflow, &options.debug)?
        {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Dataflow {
            return Ok(DecompileResult {
                state,
                debug_output,
            });
        }

        Err(DecompileError::StageNotImplemented {
            stage: DecompileStage::StructureFacts,
            completed_stage: DecompileStage::Dataflow,
        })
    }
}
