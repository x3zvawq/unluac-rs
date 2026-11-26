//! 主反编译流水线的固定五阶段枚举与状态容器。

use crate::ast::AstTargetDialect;
use crate::debug::DebugDetail;
use crate::parser::RawChunk;
use super::timing::TimingCollector;
use strum_macros::{Display, EnumString, IntoStaticStr};

use super::contracts::{AnalysisChunk, AstChunk, GeneratedChunk, LoweredChunk, NamingResult};
use super::error::DecompileError;
use super::options::{DecompileDialect, DecompileOptions};

/// 主反编译流水线的五阶段顺序。
#[derive(
    Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Display, EnumString, IntoStaticStr,
)]
pub enum DecompileStage {
    #[strum(serialize = "parser", serialize = "parse")]
    Parser,
    #[strum(serialize = "transformer", serialize = "transform")]
    Transformer,
    #[strum(serialize = "analysis")]
    Analysis,
    #[strum(serialize = "ast")]
    Ast,
    #[strum(serialize = "generate")]
    Generate,
}

/// 某个阶段导出的调试文本。
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct StageDebugOutput {
    pub stage: DecompileStage,
    pub detail: DebugDetail,
    pub content: String,
}

/// 单次 pipeline 调用期间各阶段共享的只读上下文。
pub(crate) struct DecompileContext<'a> {
    pub(crate) bytes: &'a [u8],
    pub(crate) options: &'a DecompileOptions,
    pub(crate) timings: &'a TimingCollector,
    pub(crate) requested_target: AstTargetDialect,
}

impl DecompileStage {
    pub const fn next(self) -> Option<Self> {
        match self {
            Self::Parser => Some(Self::Transformer),
            Self::Transformer => Some(Self::Analysis),
            Self::Analysis => Some(Self::Ast),
            Self::Ast => Some(Self::Generate),
            Self::Generate => None,
        }
    }
}

/// 一次 pipeline 执行期间各层产物的状态容器。
#[derive(Debug)]
pub struct DecompileState {
    pub dialect: DecompileDialect,
    pub target_stage: DecompileStage,
    pub completed_stage: Option<DecompileStage>,
    pub raw_chunk: Option<RawChunk>,
    pub lowered: Option<LoweredChunk>,
    pub analysis: Option<AnalysisChunk>,
    pub ast: Option<AstChunk>,
    pub naming: Option<NamingResult>,
    pub generated: Option<GeneratedChunk>,
}

impl DecompileState {
    pub(crate) fn new(dialect: DecompileDialect, target_stage: DecompileStage) -> Self {
        Self {
            dialect,
            target_stage,
            completed_stage: None,
            raw_chunk: None,
            lowered: None,
            analysis: None,
            ast: None,
            naming: None,
            generated: None,
        }
    }

    pub(crate) fn mark_completed(&mut self, stage: DecompileStage) {
        self.completed_stage = Some(stage);
    }

    pub(crate) fn require_raw_chunk(&self) -> Result<&RawChunk, DecompileError> {
        require_stage_output(self.raw_chunk.as_ref(), DecompileStage::Parser)
    }

    pub(crate) fn require_lowered(&self) -> Result<&LoweredChunk, DecompileError> {
        require_stage_output(self.lowered.as_ref(), DecompileStage::Transformer)
    }

    pub(crate) fn require_analysis(&self) -> Result<&AnalysisChunk, DecompileError> {
        require_stage_output(self.analysis.as_ref(), DecompileStage::Analysis)
    }

    pub(crate) fn require_ast(&self) -> Result<&AstChunk, DecompileError> {
        require_stage_output(self.ast.as_ref(), DecompileStage::Ast)
    }

    pub(crate) fn require_naming(&self) -> Result<&NamingResult, DecompileError> {
        require_stage_output(self.naming.as_ref(), DecompileStage::Ast)
    }

    #[cfg(feature = "decompile-debug")]
    pub(crate) fn require_generated(&self) -> Result<&GeneratedChunk, DecompileError> {
        require_stage_output(self.generated.as_ref(), DecompileStage::Generate)
    }
}

fn require_stage_output<T>(
    output: Option<&T>,
    stage: DecompileStage,
) -> Result<&T, DecompileError> {
    output.ok_or(DecompileError::MissingStageOutput { stage })
}
