//! 这个文件定义主 pipeline 的错误类型。
//!
//! parser、调试视图和后续未实现阶段都通过同一个错误通道上抛，
//! 调用方只需要处理一套错误模型，不必知道内部到底在哪层失败。

use thiserror::Error;

use super::state::DecompileStage;
use crate::ast::AstLowerError;
use crate::naming::NamingError;
use crate::parser::ParseError;
use crate::transformer::TransformError;

/// 主反编译 pipeline 可能返回的错误。
#[derive(Debug, Error)]
pub enum DecompileError {
    #[error(transparent)]
    Parse(#[from] ParseError),
    #[error(transparent)]
    Transform(#[from] TransformError),
    #[error(transparent)]
    Ast(#[from] AstLowerError),
    #[error(transparent)]
    Naming(#[from] NamingError),
    #[error(
        "stage `{stage}` is not implemented yet; pipeline currently stops after `{completed_stage}`"
    )]
    StageNotImplemented {
        stage: DecompileStage,
        completed_stage: DecompileStage,
    },
    #[error("requested debug output for stage `{stage}`, but that stage has no artifact yet")]
    MissingStageOutput { stage: DecompileStage },
}
