//! AST 阶段错误类型。

use thiserror::Error;

use crate::decompile::DecompileDialect;

use super::common::{AstBindingRef, AstLabelId};

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum AstLowerError {
    #[error("target dialect `{dialect}` does not support feature `{feature}` required by {context}")]
    UnsupportedFeature {
        dialect: DecompileDialect,
        feature: &'static str,
        context: &'static str,
    },
    #[error("proto#{proto} references missing child proto#{child}")]
    MissingChildProto { proto: usize, child: usize },
    #[error("proto#{function} defines duplicate goto label `{label}`")]
    DuplicateGotoLabel { function: usize, label: AstLabelId },
    #[error("proto#{function} jumps to missing goto label `{label}`")]
    MissingGotoLabel { function: usize, label: AstLabelId },
    #[error("proto#{function} jumps to invisible goto label `{label}`")]
    InvisibleGotoLabel { function: usize, label: AstLabelId },
    #[error("proto#{function} goto `{label}` enters scope of local {binding:?}")]
    GotoEntersLocalScope {
        function: usize,
        label: AstLabelId,
        binding: AstBindingRef,
    },
    #[error("proto#{function} goto `{label}` enters scope of to-be-closed local {binding:?}")]
    GotoEntersToBeClosedScope {
        function: usize,
        label: AstLabelId,
        binding: AstBindingRef,
    },
    #[error("proto#{function} has an invalid goto scope tree")]
    InvalidGotoScopeTree { function: usize },
    #[error("proto#{proto} structuring failed: {detail}")]
    StructureFailure { proto: usize, detail: String },
}
