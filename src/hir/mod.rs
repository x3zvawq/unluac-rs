//! 这个模块承载 HIR 层的共享实现。
//!
//! 这一层正式消费 StructureFacts 做恢复决策，把 low-IR 提升到变量世界，并让
//! 后续 AST/Readability 有稳定的语义中间表示可消费。

mod analyze;
mod common;
#[cfg(feature = "decompile-debug")]
mod debug;
mod decision;
mod expr_safety;
mod promotion;
mod simplify;
pub(crate) mod traverse;

pub use crate::parser::{ProtoLineRange, ProtoSignature};
pub(crate) use analyze::analyze_hir;
pub use common::{
    HirAssign, HirBinaryExpr, HirBinaryOpKind, HirBlock, HirCallExpr, HirCallStmt, HirCapture,
    HirClose, HirClosureExpr, HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef,
    HirDecisionTarget, HirExpr, HirGenericFor, HirGlobalRef, HirGoto, HirIf, HirLValue, HirLabel,
    HirLabelId, HirLocalDecl, HirLogicalExpr, HirModule, HirNumericFor, HirPackTail, HirProto,
    HirProtoRef, HirRecordField, HirRepeat, HirReturn, HirStmt, HirTableAccess,
    HirTableConstructor, HirTableField, HirTableKey, HirTableSetList, HirToBeClosed, HirUnaryExpr,
    HirUnaryOpKind, HirUnresolvedExpr, HirValuePack, HirWhile, LocalId, ParamId, TempId, UpvalueId,
};
#[cfg(feature = "decompile-debug")]
pub use debug::dump_hir;
#[cfg(not(feature = "decompile-debug"))]
mod debug {
    crate::debug::define_unavailable_stage_dump!(dump_hir);
}
#[cfg(not(feature = "decompile-debug"))]
pub use debug::dump_hir;
