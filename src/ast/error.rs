//! AST lowering 的错误类型。

use thiserror::Error;

use crate::ast::{AstBindingRef, DecompileDialect};
use crate::structure::{BlockRef, PhiId};
use crate::transformer::Reg;

/// HIR -> AST lowering 可能失败的原因。
#[derive(Debug, Error)]
pub enum AstLowerError {
    #[error(
        "target dialect `{dialect}` does not support feature `{feature}` required by {context}"
    )]
    UnsupportedFeature {
        dialect: DecompileDialect,
        feature: &'static str,
        context: &'static str,
    },
    #[error("StructurePlan proto#{proto} retains unresolved {phi_id} at {block} register {reg}")]
    UnresolvedStructureValue {
        proto: usize,
        phi_id: PhiId,
        block: BlockRef,
        reg: Reg,
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
    #[error("HIR proto#{proto} contains err-nnil that cannot be matched to a global declaration")]
    InvalidGlobalDeclPattern { proto: usize },
    #[error("HIR proto#{proto} has invalid method call lowering shape: {reason}")]
    InvalidMethodCallPattern { proto: usize, reason: &'static str },
    #[error("AST function#{function} defines goto label#{label} more than once")]
    DuplicateGotoLabel { function: usize, label: usize },
    #[error("AST function#{function} goto references missing label#{label} in the same function")]
    MissingGotoLabel { function: usize, label: usize },
    #[error("AST function#{function} goto label#{label} is not visible from its lexical block")]
    InvisibleGotoLabel { function: usize, label: usize },
    #[error("AST function#{function} goto label#{label} enters local binding {binding:?} scope")]
    GotoEntersLocalScope {
        function: usize,
        label: usize,
        binding: AstBindingRef,
    },
    #[error(
        "AST function#{function} goto label#{label} enters to-be-closed binding {binding:?} scope"
    )]
    GotoEntersToBeClosedScope {
        function: usize,
        label: usize,
        binding: AstBindingRef,
    },
    #[error("AST function#{function} has an inconsistent goto scope tree")]
    InvalidGotoScopeTree { function: usize },
}
