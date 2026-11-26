//! 主反编译流水线的统一错误类型。

use thiserror::Error;

use super::state::DecompileStage;
use crate::analysis::AnalysisError;
use crate::ast::{AstLowerError, NamingError};
use crate::generate::GenerateError;
use crate::parser::ParseError;
use crate::transformer::TransformError;

/// 主反编译流水线可能返回的错误。
#[derive(Debug, Error)]
pub enum DecompileError {
    #[error(transparent)]
    Parse(#[from] ParseError),
    #[error(transparent)]
    Transform(#[from] TransformError),
    #[error(transparent)]
    Analysis(#[from] AnalysisError),
    #[error(transparent)]
    Ast(#[from] AstLowerError),
    #[error(transparent)]
    Naming(#[from] NamingError),
    #[error(transparent)]
    Generate(#[from] GenerateError),
    #[error(
        "stage `{stage}` is not implemented yet; pipeline currently stops after `{completed_stage}`"
    )]
    StageNotImplemented {
        stage: DecompileStage,
        completed_stage: DecompileStage,
    },
    #[error("this build was compiled without debug dump support")]
    DebugUnavailable,
    #[error("requested debug output for stage `{stage}`, but that stage has no artifact yet")]
    MissingStageOutput { stage: DecompileStage },
}
