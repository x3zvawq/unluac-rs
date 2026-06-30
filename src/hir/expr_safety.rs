//! HIR 表达式求值安全性的共享判断。
//!
//! HIR analyze 和 simplify 都会判断某个表达式是否能被挪动或折进别的表达式。
//! 这个文件只放跨 pass 共用、和具体恢复策略无关的谓词，避免求值序规则散落后漂移。

use super::common::HirExpr;

pub(crate) fn expr_observes_eval_order(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::GlobalRef(_) | HirExpr::TableAccess(_) | HirExpr::Call(_) => true,
        HirExpr::Unary(_) | HirExpr::Binary(_) | HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_) => {
            true
        }
        HirExpr::Decision(_) | HirExpr::TableConstructor(_) => true,
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_observes_eval_order(&capture.value)),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
    }
}
