//! AST binding 改写工具。
//!
//! `binding_tree` 主模块负责只读查询；这个文件只处理已经证明安全后的表达式 use-site
//! 替换。这里不重新判断控制流或作用域安全性，调用方必须先完成对应 owner 的语义校验。

use crate::ast::common::{AstBindingRef, AstExpr, AstTableField, AstTableKey};

use super::super::binding_ref::name_matches_binding;

pub(in crate::ast::readability) fn replace_binding_use_in_expr(
    expr: &mut AstExpr,
    binding: AstBindingRef,
    replacement: &AstExpr,
) -> bool {
    if matches!(expr, AstExpr::Var(name) if name_matches_binding(name, binding)) {
        *expr = replacement.clone();
        return true;
    }

    match expr {
        AstExpr::FieldAccess(access) => {
            replace_binding_use_in_expr(&mut access.base, binding, replacement)
        }
        AstExpr::IndexAccess(access) => {
            replace_binding_use_in_expr(&mut access.base, binding, replacement)
                | replace_binding_use_in_expr(&mut access.index, binding, replacement)
        }
        AstExpr::Unary(unary) => replace_binding_use_in_expr(&mut unary.expr, binding, replacement),
        AstExpr::Binary(binary) => {
            replace_binding_use_in_expr(&mut binary.lhs, binding, replacement)
                | replace_binding_use_in_expr(&mut binary.rhs, binding, replacement)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            replace_binding_use_in_expr(&mut logical.lhs, binding, replacement)
                | replace_binding_use_in_expr(&mut logical.rhs, binding, replacement)
        }
        AstExpr::Call(call) => {
            let mut changed = replace_binding_use_in_expr(&mut call.callee, binding, replacement);
            for arg in &mut call.args {
                changed |= replace_binding_use_in_expr(arg, binding, replacement);
            }
            changed
        }
        AstExpr::MethodCall(call) => {
            let mut changed = replace_binding_use_in_expr(&mut call.receiver, binding, replacement);
            for arg in &mut call.args {
                changed |= replace_binding_use_in_expr(arg, binding, replacement);
            }
            changed
        }
        AstExpr::SingleValue(expr) => replace_binding_use_in_expr(expr, binding, replacement),
        AstExpr::TableConstructor(table) => {
            let mut changed = false;
            for field in &mut table.fields {
                changed |= match field {
                    AstTableField::Array(value) => {
                        replace_binding_use_in_expr(value, binding, replacement)
                    }
                    AstTableField::Record(record) => {
                        let key_changed = match &mut record.key {
                            AstTableKey::Name(_) => false,
                            AstTableKey::Expr(key) => {
                                replace_binding_use_in_expr(key, binding, replacement)
                            }
                        };
                        key_changed
                            | replace_binding_use_in_expr(&mut record.value, binding, replacement)
                    }
                };
            }
            changed
        }
        AstExpr::FunctionExpr(_)
        | AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::VarArg
        | AstExpr::Error(_) => false,
    }
}
