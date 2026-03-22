//! 这个文件实现主 pipeline 共享的调试调度逻辑。
//!
//! 各层具体如何渲染自己的 dump，应该尽量贴着实现放置；这里仅保留跨层共用的
//! 选项、阶段包装和主 pipeline 的分派逻辑，避免再次长成一个巨型总控文件。

use crate::debug::{DebugDetail, DebugFilters};
use crate::parser;
use crate::transformer;

use super::error::DecompileError;
use super::state::{DecompileStage, DecompileState};

/// 供主 pipeline 和 CLI 共享的调试选项。
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct DebugOptions {
    pub enable: bool,
    pub output_stages: Vec<DecompileStage>,
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
        content: parser::dump_parser(chunk, options.detail, &options.filters),
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
        content: transformer::dump_lir(chunk, options.detail, &options.filters),
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
        _ => Err(DecompileError::MissingStageOutput { stage }),
    }
}
