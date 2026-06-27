//! AST 层入口。

mod build;
mod common;
mod debug;
mod error;
mod features;
mod naming;
pub(crate) mod pretty;
mod readability;
pub(crate) mod traverse;

pub use crate::decompile::DecompileDialect;
pub use build::lower_ast;
pub use common::{
    AstAssign, AstBinaryExpr, AstBinaryOpKind, AstBindingRef, AstBlock, AstCallExpr, AstCallKind,
    AstCallStmt, AstDialectCaps, AstExpr, AstFeature, AstFieldAccess, AstFunctionDecl,
    AstFunctionExpr, AstFunctionName, AstGenericFor, AstGlobalAttr, AstGlobalBinding,
    AstGlobalBindingTarget, AstGlobalDecl, AstGlobalName, AstGoto, AstIf, AstIndexAccess,
    AstLValue, AstLabel, AstLabelId, AstLocalAttr, AstLocalBinding, AstLocalDecl,
    AstLocalFunctionDecl, AstLocalOrigin, AstLogicalExpr, AstMethodCallExpr, AstModule,
    AstNamePath, AstNameRef, AstNumericFor, AstRecordField, AstRepeat, AstReturn, AstStmt,
    AstSyntheticLocalId, AstTableConstructor, AstTableField, AstTableKey, AstTargetDialect,
    AstUnaryExpr, AstUnaryOpKind, AstWhile,
};
pub use debug::dump_ast;
pub use error::AstLowerError;
pub(crate) use features::collect_ast_features;
pub use naming::{
    FunctionNameMap, NameInfo, NameMap, NameSource, NamingError, NamingEvidence, NamingMode,
    NamingOptions, assign_name_map, assign_names_with_evidence, collect_naming_evidence,
};
pub use readability::ReadabilityOptions;

pub(crate) fn analyze_ast_stage(
    state: &mut crate::decompile::DecompileState,
    context: &crate::decompile::DecompileContext<'_>,
) -> Result<(), crate::decompile::DecompileError> {
    {
        let _timing = context.timings.scope("build");
        build::lower_ast_for_generate(state, context)?;
    }
    {
        let _timing = context.timings.scope("readability");
        readability::make_readable(state, context)?;
    }
    {
        let _timing = context.timings.scope("naming");
        naming::assign_names(state, context)?;
    }

    Ok(())
}
