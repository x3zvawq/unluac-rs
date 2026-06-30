//! AST binding 改写工具。
//!
//! `binding_tree` 主模块负责只读查询；这个文件只处理已经证明安全后的局部 binding
//! 替换，例如把 carried local 的使用点认回 seed binding。这里不重新判断控制流或
//! 作用域安全性，调用方必须先完成对应 owner 的语义校验。

use crate::ast::common::{
    AstBindingRef, AstCallKind, AstExpr, AstLValue, AstNameRef, AstStmt, AstTableField, AstTableKey,
};

use super::super::binding_ref::{name_matches_binding, name_ref_from_binding};

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
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::VarArg
        | AstExpr::Error(_) => false,
    }
}

pub(in crate::ast::readability) fn rewrite_binding_in_stmt(
    stmt: &mut AstStmt,
    from: AstBindingRef,
    to: AstBindingRef,
) {
    rewrite_binding_as_name_in_stmt(stmt, from, &name_ref_from_binding(to));
}

fn rewrite_binding_as_name_in_stmt(stmt: &mut AstStmt, from: AstBindingRef, to: &AstNameRef) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for value in &mut local_decl.values {
                rewrite_binding_as_name_in_expr(value, from, to);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &mut global_decl.values {
                rewrite_binding_as_name_in_expr(value, from, to);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &mut assign.targets {
                rewrite_binding_as_name_in_lvalue(target, from, to);
            }
            for value in &mut assign.values {
                rewrite_binding_as_name_in_expr(value, from, to);
            }
        }
        AstStmt::CallStmt(call_stmt) => {
            rewrite_binding_as_name_in_call(&mut call_stmt.call, from, to)
        }
        AstStmt::Return(ret) => {
            for value in &mut ret.values {
                rewrite_binding_as_name_in_expr(value, from, to);
            }
        }
        AstStmt::If(if_stmt) => {
            rewrite_binding_as_name_in_expr(&mut if_stmt.cond, from, to);
            rewrite_binding_as_name_in_stmts_with_ref(&mut if_stmt.then_block.stmts, from, to);
            if let Some(else_block) = &mut if_stmt.else_block {
                rewrite_binding_as_name_in_stmts_with_ref(&mut else_block.stmts, from, to);
            }
        }
        AstStmt::While(while_stmt) => {
            rewrite_binding_as_name_in_expr(&mut while_stmt.cond, from, to);
            rewrite_binding_as_name_in_stmts_with_ref(&mut while_stmt.body.stmts, from, to);
        }
        AstStmt::Repeat(repeat_stmt) => {
            rewrite_binding_as_name_in_stmts_with_ref(&mut repeat_stmt.body.stmts, from, to);
            rewrite_binding_as_name_in_expr(&mut repeat_stmt.cond, from, to);
        }
        AstStmt::NumericFor(numeric_for) => {
            rewrite_binding_as_name_in_expr(&mut numeric_for.start, from, to);
            rewrite_binding_as_name_in_expr(&mut numeric_for.limit, from, to);
            rewrite_binding_as_name_in_expr(&mut numeric_for.step, from, to);
            rewrite_binding_as_name_in_stmts_with_ref(&mut numeric_for.body.stmts, from, to);
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &mut generic_for.iterator {
                rewrite_binding_as_name_in_expr(expr, from, to);
            }
            rewrite_binding_as_name_in_stmts_with_ref(&mut generic_for.body.stmts, from, to);
        }
        AstStmt::DoBlock(block) => {
            rewrite_binding_as_name_in_stmts_with_ref(&mut block.stmts, from, to)
        }
        AstStmt::FunctionDecl(_) | AstStmt::LocalFunctionDecl(_) => {}
        AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => {}
    }
}

fn rewrite_binding_as_name_in_stmts_with_ref(
    stmts: &mut [AstStmt],
    from: AstBindingRef,
    to: &AstNameRef,
) {
    for stmt in stmts {
        rewrite_binding_as_name_in_stmt(stmt, from, to);
    }
}

fn rewrite_binding_as_name_in_call(call: &mut AstCallKind, from: AstBindingRef, to: &AstNameRef) {
    match call {
        AstCallKind::Call(call) => {
            rewrite_binding_as_name_in_expr(&mut call.callee, from, to);
            for arg in &mut call.args {
                rewrite_binding_as_name_in_expr(arg, from, to);
            }
        }
        AstCallKind::MethodCall(call) => {
            rewrite_binding_as_name_in_expr(&mut call.receiver, from, to);
            for arg in &mut call.args {
                rewrite_binding_as_name_in_expr(arg, from, to);
            }
        }
    }
}

fn rewrite_binding_as_name_in_lvalue(target: &mut AstLValue, from: AstBindingRef, to: &AstNameRef) {
    match target {
        AstLValue::Name(name) => rewrite_binding_as_name_in_name(name, from, to),
        AstLValue::FieldAccess(access) => {
            rewrite_binding_as_name_in_expr(&mut access.base, from, to)
        }
        AstLValue::IndexAccess(access) => {
            rewrite_binding_as_name_in_expr(&mut access.base, from, to);
            rewrite_binding_as_name_in_expr(&mut access.index, from, to);
        }
    }
}

fn rewrite_binding_as_name_in_expr(expr: &mut AstExpr, from: AstBindingRef, to: &AstNameRef) {
    match expr {
        AstExpr::Var(name) => rewrite_binding_as_name_in_name(name, from, to),
        AstExpr::FieldAccess(access) => rewrite_binding_as_name_in_expr(&mut access.base, from, to),
        AstExpr::IndexAccess(access) => {
            rewrite_binding_as_name_in_expr(&mut access.base, from, to);
            rewrite_binding_as_name_in_expr(&mut access.index, from, to);
        }
        AstExpr::Unary(unary) => rewrite_binding_as_name_in_expr(&mut unary.expr, from, to),
        AstExpr::Binary(binary) => {
            rewrite_binding_as_name_in_expr(&mut binary.lhs, from, to);
            rewrite_binding_as_name_in_expr(&mut binary.rhs, from, to);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            rewrite_binding_as_name_in_expr(&mut logical.lhs, from, to);
            rewrite_binding_as_name_in_expr(&mut logical.rhs, from, to);
        }
        AstExpr::Call(call) => {
            rewrite_binding_as_name_in_expr(&mut call.callee, from, to);
            for arg in &mut call.args {
                rewrite_binding_as_name_in_expr(arg, from, to);
            }
        }
        AstExpr::MethodCall(call) => {
            rewrite_binding_as_name_in_expr(&mut call.receiver, from, to);
            for arg in &mut call.args {
                rewrite_binding_as_name_in_expr(arg, from, to);
            }
        }
        AstExpr::SingleValue(expr) => rewrite_binding_as_name_in_expr(expr, from, to),
        AstExpr::TableConstructor(table) => {
            for field in &mut table.fields {
                match field {
                    AstTableField::Array(value) => rewrite_binding_as_name_in_expr(value, from, to),
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &mut record.key {
                            rewrite_binding_as_name_in_expr(key, from, to);
                        }
                        rewrite_binding_as_name_in_expr(&mut record.value, from, to);
                    }
                }
            }
        }
        AstExpr::FunctionExpr(_)
        | AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::VarArg
        | AstExpr::Error(_) => {}
    }
}

fn rewrite_binding_as_name_in_name(name: &mut AstNameRef, from: AstBindingRef, to: &AstNameRef) {
    if name_matches_binding(name, from) {
        *name = to.clone();
    }
}
