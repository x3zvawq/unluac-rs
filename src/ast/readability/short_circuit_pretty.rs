//! 让纯短路表达式更像源码。
//!
//! 这里不负责“反内联”。它只处理一类可证明纯净的表达式子集，然后借用 HIR 侧的等价
//! 综合工具把 `and/or/not` 重新收成更自然的 guarded 结构。

use super::super::common::{
    AstBinaryExpr, AstBinaryOpKind, AstExpr, AstLogicalExpr, AstModule, AstUnaryExpr,
    AstUnaryOpKind,
};
use super::ReadabilityContext;
use super::walk::{self, AstRewritePass};
use crate::hir::{
    HirBinaryExpr, HirBinaryOpKind, HirExpr, HirLogicalExpr, HirUnaryExpr, HirUnaryOpKind,
    synthesize_readable_pure_logical_expr,
};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let _ = context.target;
    walk::rewrite_module(module, &mut ShortCircuitPrettyPass)
}

struct ShortCircuitPrettyPass;

impl AstRewritePass for ShortCircuitPrettyPass {
    fn rewrite_expr(&mut self, expr: &mut AstExpr) -> bool {
        rewrite_short_circuit_expr(expr)
    }

    fn rewrite_condition_expr(&mut self, _expr: &mut AstExpr) -> bool {
        false
    }
}

fn rewrite_short_circuit_expr(expr: &mut AstExpr) -> bool {
    if let Some(hir_expr) = hir_from_ast_expr(expr)
        && let Some(pretty_hir) = synthesize_readable_pure_logical_expr(&hir_expr)
        && pretty_hir != hir_expr
        && let Some(pretty_ast) = ast_from_hir_expr(&pretty_hir)
    {
        *expr = pretty_ast;
        return true;
    }

    false
}

fn hir_from_ast_expr(expr: &AstExpr) -> Option<HirExpr> {
    match expr {
        AstExpr::Nil => Some(HirExpr::Nil),
        AstExpr::Boolean(value) => Some(HirExpr::Boolean(*value)),
        AstExpr::Integer(value) => Some(HirExpr::Integer(*value)),
        AstExpr::Number(value) => Some(HirExpr::Number(*value)),
        AstExpr::String(value) => Some(HirExpr::String(value.clone())),
        AstExpr::Int64(value) => Some(HirExpr::Int64(*value)),
        AstExpr::UInt64(value) => Some(HirExpr::UInt64(*value)),
        AstExpr::Complex { real, imag } => Some(HirExpr::Complex {
            real: *real,
            imag: *imag,
        }),
        AstExpr::Var(name) => match name {
            super::super::common::AstNameRef::Param(param) => Some(HirExpr::ParamRef(*param)),
            super::super::common::AstNameRef::Local(local) => Some(HirExpr::LocalRef(*local)),
            super::super::common::AstNameRef::Temp(temp) => Some(HirExpr::TempRef(*temp)),
            super::super::common::AstNameRef::SyntheticLocal(_) => None,
            super::super::common::AstNameRef::Upvalue(upvalue) => {
                Some(HirExpr::UpvalueRef(*upvalue))
            }
            super::super::common::AstNameRef::Global(_) => None,
        },
        AstExpr::Unary(unary) if unary.op == AstUnaryOpKind::Not => {
            Some(HirExpr::Unary(Box::new(HirUnaryExpr {
                op: HirUnaryOpKind::Not,
                expr: hir_from_ast_expr(&unary.expr)?,
            })))
        }
        AstExpr::Binary(binary) if binary.op == AstBinaryOpKind::Eq => {
            Some(HirExpr::Binary(Box::new(HirBinaryExpr {
                op: HirBinaryOpKind::Eq,
                lhs: hir_from_ast_expr(&binary.lhs)?,
                rhs: hir_from_ast_expr(&binary.rhs)?,
            })))
        }
        AstExpr::LogicalAnd(logical) => Some(HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            lhs: hir_from_ast_expr(&logical.lhs)?,
            rhs: hir_from_ast_expr(&logical.rhs)?,
        }))),
        AstExpr::LogicalOr(logical) => Some(HirExpr::LogicalOr(Box::new(HirLogicalExpr {
            lhs: hir_from_ast_expr(&logical.lhs)?,
            rhs: hir_from_ast_expr(&logical.rhs)?,
        }))),
        AstExpr::SingleValue(expr) => hir_from_ast_expr(expr),
        AstExpr::FieldAccess(_)
        | AstExpr::IndexAccess(_)
        | AstExpr::Unary(_)
        | AstExpr::Binary(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_)
        | AstExpr::Error(_) => None,
    }
}

fn ast_from_hir_expr(expr: &HirExpr) -> Option<AstExpr> {
    match expr {
        HirExpr::Nil => Some(AstExpr::Nil),
        HirExpr::Boolean(value) => Some(AstExpr::Boolean(*value)),
        HirExpr::Integer(value) => Some(AstExpr::Integer(*value)),
        HirExpr::Number(value) => Some(AstExpr::Number(*value)),
        HirExpr::String(value) => Some(AstExpr::String(value.clone())),
        HirExpr::Int64(value) => Some(AstExpr::Int64(*value)),
        HirExpr::UInt64(value) => Some(AstExpr::UInt64(*value)),
        HirExpr::Complex { real, imag } => Some(AstExpr::Complex {
            real: *real,
            imag: *imag,
        }),
        HirExpr::ParamRef(param) => Some(AstExpr::Var(super::super::common::AstNameRef::Param(
            *param,
        ))),
        HirExpr::LocalRef(local) => Some(AstExpr::Var(super::super::common::AstNameRef::Local(
            *local,
        ))),
        HirExpr::TempRef(temp) => Some(AstExpr::Var(super::super::common::AstNameRef::Temp(*temp))),
        HirExpr::UpvalueRef(upvalue) => Some(AstExpr::Var(
            super::super::common::AstNameRef::Upvalue(*upvalue),
        )),
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            Some(AstExpr::Unary(Box::new(AstUnaryExpr {
                op: AstUnaryOpKind::Not,
                expr: ast_from_hir_expr(&unary.expr)?,
            })))
        }
        HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Eq => {
            Some(AstExpr::Binary(Box::new(AstBinaryExpr {
                op: AstBinaryOpKind::Eq,
                lhs: ast_from_hir_expr(&binary.lhs)?,
                rhs: ast_from_hir_expr(&binary.rhs)?,
            })))
        }
        HirExpr::LogicalAnd(logical) => Some(AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
            lhs: ast_from_hir_expr(&logical.lhs)?,
            rhs: ast_from_hir_expr(&logical.rhs)?,
        }))),
        HirExpr::LogicalOr(logical) => Some(AstExpr::LogicalOr(Box::new(AstLogicalExpr {
            lhs: ast_from_hir_expr(&logical.lhs)?,
            rhs: ast_from_hir_expr(&logical.rhs)?,
        }))),
        HirExpr::Decision(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => None,
    }
}
