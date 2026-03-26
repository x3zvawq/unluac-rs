//! AST 层入口。

mod build;
mod common;
mod debug;
mod error;
pub(crate) mod pretty;
mod readability;

pub use crate::readability::ReadabilityOptions;
pub use build::lower_ast;
pub use common::{
    AstAssign, AstBinaryExpr, AstBinaryOpKind, AstBindingRef, AstBlock, AstCallExpr, AstCallKind,
    AstCallStmt, AstDialectCaps, AstDialectVersion, AstExpr, AstFieldAccess, AstFunctionDecl,
    AstFunctionExpr, AstFunctionName, AstGenericFor, AstGlobalAttr, AstGlobalBinding,
    AstGlobalBindingTarget, AstGlobalDecl, AstGlobalName, AstGoto, AstIf, AstIndexAccess,
    AstLValue, AstLabel, AstLabelId, AstLocalAttr, AstLocalBinding, AstLocalDecl,
    AstLocalFunctionDecl, AstLogicalExpr, AstMethodCallExpr, AstModule, AstNamePath, AstNameRef,
    AstNumericFor, AstRecordField, AstRepeat, AstReturn, AstStmt, AstSyntheticLocalId,
    AstTableConstructor, AstTableField, AstTableKey, AstTargetDialect, AstUnaryExpr,
    AstUnaryOpKind, AstWhile,
};
pub use debug::{dump_ast, dump_readability};
pub use error::AstLowerError;
pub(crate) use readability::make_readable_with_options_and_timing;
pub use readability::{make_readable, make_readable_with_options};
