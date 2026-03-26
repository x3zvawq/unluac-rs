//! AST 层入口。

mod build;
mod common;
mod debug;
mod error;
mod readability;

pub use common::{
    AstAssign, AstBinaryExpr, AstBinaryOpKind, AstBindingRef, AstBlock, AstCallExpr, AstCallKind,
    AstCallStmt, AstDialectCaps, AstDialectVersion, AstExpr, AstFieldAccess, AstFunctionDecl,
    AstFunctionExpr, AstFunctionName, AstGenericFor, AstGlobalAttr, AstGlobalBinding,
    AstGlobalDecl, AstGlobalName, AstGoto, AstIf, AstIndexAccess, AstLValue, AstLabel,
    AstLabelId, AstLocalAttr, AstLocalBinding, AstLocalDecl, AstLocalFunctionDecl, AstLogicalExpr,
    AstMethodCallExpr, AstModule, AstNamePath, AstNameRef, AstNumericFor, AstRecordField,
    AstRepeat, AstReturn, AstStmt, AstTableConstructor, AstTableField, AstTableKey,
    AstTargetDialect, AstUnaryExpr, AstUnaryOpKind, AstWhile,
};
pub use debug::{dump_ast, dump_readability};
pub use error::AstLowerError;
pub use build::lower_ast;
pub use readability::{make_readable, make_readable_with_options};
pub use crate::readability::ReadabilityOptions;
