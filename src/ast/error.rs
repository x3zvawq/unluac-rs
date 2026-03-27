//! AST lowering 的错误类型。

use thiserror::Error;

use super::common::AstDialectVersion;

/// HIR -> AST lowering 可能失败的原因。
#[derive(Debug, Error)]
pub enum AstLowerError {
    #[error(
        "target dialect `{dialect}` does not support feature `{feature}` required by {context}"
    )]
    UnsupportedFeature {
        dialect: AstDialectVersion,
        feature: &'static str,
        context: &'static str,
    },
    #[error("HIR proto#{proto} still contains residual {kind} during AST lowering")]
    ResidualHir { proto: usize, kind: &'static str },
    #[error("HIR proto#{proto} references missing child proto#{child}")]
    MissingChildProto { proto: usize, child: usize },
    #[error("HIR proto#{proto} marks a named vararg table but has no recoverable entry binding")]
    MissingNamedVarargBinding { proto: usize },
    #[error("HIR proto#{proto} has unsupported to-be-closed shape: {reason}")]
    InvalidToBeClosed { proto: usize, reason: &'static str },
    #[error(
        "HIR proto#{proto} still contains explicit close semantics that AST lowering cannot absorb yet"
    )]
    UnsupportedClose { proto: usize },
    #[error(
        "HIR proto#{proto} still contains table-set-list with trailing multivalue that AST lowering cannot safely express yet"
    )]
    UnsupportedSetListTrailingMultivalue { proto: usize },
    #[error("HIR proto#{proto} contains err-nnil that cannot be matched to a global declaration")]
    InvalidGlobalDeclPattern { proto: usize },
    #[error("HIR proto#{proto} has invalid method call lowering shape: {reason}")]
    InvalidMethodCallPattern { proto: usize, reason: &'static str },
}
