//! 这个模块承载 HIR 层的共享实现。
//!
//! 这一层开始正式做“恢复决策”，但第一版仍然允许大量 fallback，重点是先把
//! low-IR 可靠提升到变量世界，并让后续 AST/Readability 有稳定的中间表示可吃。

mod analyze;
mod common;
mod debug;
mod decision;
mod simplify;

pub use analyze::analyze_hir;
pub use common::{
    HirAssign, HirBinaryExpr, HirBinaryOpKind, HirBlock, HirCallExpr, HirCallStmt, HirCapture,
    HirClosureExpr, HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget,
    HirExpr, HirGenericFor, HirGlobalRef, HirGoto, HirIf, HirLValue, HirLabel, HirLabelId,
    HirLocalDecl, HirModule, HirNumericFor, HirProto, HirProtoRef, HirRecordField, HirRepeat,
    HirReturn, HirStmt, HirTableAccess, HirTableConstructor, HirTableField, HirTableKey,
    HirTableSetList, HirUnaryExpr, HirUnaryOpKind, HirUnresolvedExpr, HirUnstructured, HirWhile,
    LocalId, ParamId, TempId, UpvalueId,
};
pub use debug::dump_hir;
