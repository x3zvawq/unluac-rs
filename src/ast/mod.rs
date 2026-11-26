//! AST 阶段入口：串联控制流结构化、直接表达式提升、轻量语法整形与命名。

mod common;
#[cfg(feature = "decompile-debug")]
mod debug;
mod error;
mod features;
mod goto_scope;
pub mod lift;
mod naming;
pub mod polish;
pub(crate) mod pretty;
pub mod structure;
pub(crate) mod traverse;
mod visit;

pub use crate::decompile::{DecompileDialect, ReadabilityOptions};
pub use common::{
    AstAssign, AstBinaryExpr, AstBinaryOpKind, AstBindingRef, AstBlock, AstCallExpr, AstCallKind,
    AstCallStmt, AstCapture, AstCaptureBinding, AstCaptureMode, AstDialectCaps, AstExpr,
    AstFeature, AstFieldAccess, AstFunctionDecl, AstFunctionExpr, AstFunctionName, AstGenericFor,
    AstGlobalAttr, AstGlobalBinding, AstGlobalBindingTarget, AstGlobalDecl, AstGlobalName, AstGoto,
    AstIf, AstIfExpr, AstIndexAccess, AstLValue, AstLabel, AstLabelId, AstLocalAttr,
    AstLocalBinding, AstLocalDecl, AstLocalFunctionDecl, AstLogicalExpr, AstMethodCallExpr,
    AstModule, AstNamePath, AstNameRef, AstNumericFor, AstProtoMeta, AstRecordField, AstRepeat,
    AstReturn, AstStmt, AstSyntheticLocalId, AstTableConstructor, AstTableField, AstTableKey,
    AstTargetDialect, AstUnaryExpr, AstUnaryOpKind, AstWhile, LocalId, ParamId, ProtoId, UpvalueId,
};
#[cfg(feature = "decompile-debug")]
pub use debug::dump_ast;
#[cfg(not(feature = "decompile-debug"))]
mod debug {
    crate::debug::define_unavailable_stage_dump!(dump_ast);
}
#[cfg(not(feature = "decompile-debug"))]
pub use debug::dump_ast;
pub use error::AstLowerError;
pub(crate) use features::collect_ast_features;
pub use naming::{
    FunctionNameMap, NameInfo, NameMap, NameSource, NamingError, NamingEvidence, NamingMode,
    NamingOptions, assign_name_map, assign_names_with_evidence, collect_naming_evidence,
};

/// 主流水线 AST 阶段入口：Structure + Lift → Polish + Goto Scope → Naming。
pub(crate) fn analyze_ast_stage(
    state: &mut crate::decompile::DecompileState,
    context: &crate::decompile::DecompileContext<'_>,
) -> Result<(), crate::decompile::DecompileError> {
    let lowered = state.require_lowered()?;
    let analysis = state.require_analysis()?;

    let mut ast = {
        let _timing = context.timings.scope("structure-and-lift");
        lift::lift_module(
            lowered,
            analysis,
            context.requested_target,
            context.options.generate.mode,
        )?
    };
    {
        let _timing = context.timings.scope("polish");
        polish::polish_module(&mut ast, context.requested_target, context.options.generate.mode)?;
    }
    let names = {
        let _timing = context.timings.scope("naming");
        naming::assign_name_map(&ast, context.options.naming)?
    };

    state.ast = Some(ast);
    state.naming = Some(names);
    Ok(())
}
