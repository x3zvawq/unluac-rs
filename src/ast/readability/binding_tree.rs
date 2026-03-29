//! 这个文件集中承载“当前函数体内 AST binding 树遍历”的共享 helper。
//!
//! `binding_flow` 更偏向整段语句流上的 use-count / reachability 分析；这里则只处理
//! 单棵 stmt/expr/lvalue 树上的递归查询与重写，并且故意不继续钻进嵌套函数体，
//! 避免把不同函数里碰巧同号的 binding 混成同一个局部变量。

use crate::ast::common::{
    AstBindingRef, AstCallKind, AstExpr, AstLValue, AstNameRef, AstStmt, AstTableField, AstTableKey,
};

use super::binding_flow::name_matches_binding;

pub(super) fn binding_from_name_ref(name: &AstNameRef) -> Option<AstBindingRef> {
    match name {
        AstNameRef::Local(local) => Some(AstBindingRef::Local(*local)),
        AstNameRef::SyntheticLocal(local) => Some(AstBindingRef::SyntheticLocal(*local)),
        AstNameRef::Temp(temp) => Some(AstBindingRef::Temp(*temp)),
        AstNameRef::Param(_) | AstNameRef::Upvalue(_) | AstNameRef::Global(_) => None,
    }
}

pub(super) fn expr_references_binding(expr: &AstExpr, binding: AstBindingRef) -> bool {
    match expr {
        AstExpr::Var(name) => name_matches_binding(name, binding),
        AstExpr::FieldAccess(access) => expr_references_binding(&access.base, binding),
        AstExpr::IndexAccess(access) => {
            expr_references_binding(&access.base, binding)
                || expr_references_binding(&access.index, binding)
        }
        AstExpr::Unary(unary) => expr_references_binding(&unary.expr, binding),
        AstExpr::Binary(binary) => {
            expr_references_binding(&binary.lhs, binding)
                || expr_references_binding(&binary.rhs, binding)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_references_binding(&logical.lhs, binding)
                || expr_references_binding(&logical.rhs, binding)
        }
        AstExpr::Call(call) => {
            expr_references_binding(&call.callee, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_binding(arg, binding))
        }
        AstExpr::MethodCall(call) => {
            expr_references_binding(&call.receiver, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_binding(arg, binding))
        }
        AstExpr::SingleValue(expr) => expr_references_binding(expr, binding),
        AstExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            AstTableField::Array(value) => expr_references_binding(value, binding),
            AstTableField::Record(record) => {
                let key_references = match &record.key {
                    AstTableKey::Name(_) => false,
                    AstTableKey::Expr(key) => expr_references_binding(key, binding),
                };
                key_references || expr_references_binding(&record.value, binding)
            }
        }),
        AstExpr::FunctionExpr(_)
        | AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::VarArg => false,
    }
}

pub(super) fn call_references_binding(call: &AstCallKind, binding: AstBindingRef) -> bool {
    match call {
        AstCallKind::Call(call) => {
            expr_references_binding(&call.callee, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_binding(arg, binding))
        }
        AstCallKind::MethodCall(call) => {
            expr_references_binding(&call.receiver, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_binding(arg, binding))
        }
    }
}

pub(super) fn lvalue_references_binding(target: &AstLValue, binding: AstBindingRef) -> bool {
    match target {
        AstLValue::Name(name) => name_matches_binding(name, binding),
        AstLValue::FieldAccess(access) => expr_references_binding(&access.base, binding),
        AstLValue::IndexAccess(access) => {
            expr_references_binding(&access.base, binding)
                || expr_references_binding(&access.index, binding)
        }
    }
}

pub(super) fn count_name_expr_uses(expr: &AstExpr, binding: AstBindingRef) -> usize {
    match expr {
        AstExpr::Var(name) if name_matches_binding(name, binding) => 1,
        AstExpr::FieldAccess(access) => count_name_expr_uses(&access.base, binding),
        AstExpr::IndexAccess(access) => {
            count_name_expr_uses(&access.base, binding)
                + count_name_expr_uses(&access.index, binding)
        }
        AstExpr::Unary(unary) => count_name_expr_uses(&unary.expr, binding),
        AstExpr::Binary(binary) => {
            count_name_expr_uses(&binary.lhs, binding) + count_name_expr_uses(&binary.rhs, binding)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            count_name_expr_uses(&logical.lhs, binding)
                + count_name_expr_uses(&logical.rhs, binding)
        }
        AstExpr::Call(call) => {
            count_name_expr_uses(&call.callee, binding)
                + call
                    .args
                    .iter()
                    .map(|arg| count_name_expr_uses(arg, binding))
                    .sum::<usize>()
        }
        AstExpr::MethodCall(call) => {
            count_name_expr_uses(&call.receiver, binding)
                + call
                    .args
                    .iter()
                    .map(|arg| count_name_expr_uses(arg, binding))
                    .sum::<usize>()
        }
        AstExpr::SingleValue(expr) => count_name_expr_uses(expr, binding),
        AstExpr::TableConstructor(table) => table
            .fields
            .iter()
            .map(|field| match field {
                AstTableField::Array(value) => count_name_expr_uses(value, binding),
                AstTableField::Record(record) => {
                    let key_uses = match &record.key {
                        AstTableKey::Name(_) => 0,
                        AstTableKey::Expr(key) => count_name_expr_uses(key, binding),
                    };
                    key_uses + count_name_expr_uses(&record.value, binding)
                }
            })
            .sum(),
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
        | AstExpr::VarArg => 0,
    }
}

pub(super) fn replace_binding_use_in_expr(
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
        | AstExpr::VarArg => false,
    }
}

pub(super) fn rewrite_binding_in_stmt(stmt: &mut AstStmt, from: AstBindingRef, to: AstBindingRef) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for value in &mut local_decl.values {
                rewrite_binding_in_expr(value, from, to);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &mut global_decl.values {
                rewrite_binding_in_expr(value, from, to);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &mut assign.targets {
                rewrite_binding_in_lvalue(target, from, to);
            }
            for value in &mut assign.values {
                rewrite_binding_in_expr(value, from, to);
            }
        }
        AstStmt::CallStmt(call_stmt) => rewrite_binding_in_call(&mut call_stmt.call, from, to),
        AstStmt::Return(ret) => {
            for value in &mut ret.values {
                rewrite_binding_in_expr(value, from, to);
            }
        }
        AstStmt::If(if_stmt) => {
            rewrite_binding_in_expr(&mut if_stmt.cond, from, to);
            rewrite_binding_in_stmts(&mut if_stmt.then_block.stmts, from, to);
            if let Some(else_block) = &mut if_stmt.else_block {
                rewrite_binding_in_stmts(&mut else_block.stmts, from, to);
            }
        }
        AstStmt::While(while_stmt) => {
            rewrite_binding_in_expr(&mut while_stmt.cond, from, to);
            rewrite_binding_in_stmts(&mut while_stmt.body.stmts, from, to);
        }
        AstStmt::Repeat(repeat_stmt) => {
            rewrite_binding_in_stmts(&mut repeat_stmt.body.stmts, from, to);
            rewrite_binding_in_expr(&mut repeat_stmt.cond, from, to);
        }
        AstStmt::NumericFor(numeric_for) => {
            rewrite_binding_in_expr(&mut numeric_for.start, from, to);
            rewrite_binding_in_expr(&mut numeric_for.limit, from, to);
            rewrite_binding_in_expr(&mut numeric_for.step, from, to);
            rewrite_binding_in_stmts(&mut numeric_for.body.stmts, from, to);
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &mut generic_for.iterator {
                rewrite_binding_in_expr(expr, from, to);
            }
            rewrite_binding_in_stmts(&mut generic_for.body.stmts, from, to);
        }
        AstStmt::DoBlock(block) => rewrite_binding_in_stmts(&mut block.stmts, from, to),
        AstStmt::FunctionDecl(_) | AstStmt::LocalFunctionDecl(_) => {}
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => {}
    }
}

pub(super) fn rewrite_binding_in_stmts(
    stmts: &mut [AstStmt],
    from: AstBindingRef,
    to: AstBindingRef,
) {
    for stmt in stmts {
        rewrite_binding_in_stmt(stmt, from, to);
    }
}

pub(super) fn stmt_mentions_binding_target(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .bindings
            .iter()
            .any(|local_binding| local_binding.id == binding),
        AstStmt::Assign(assign) => assign
            .targets
            .iter()
            .any(|target| lvalue_mentions_binding_target(target, binding)),
        AstStmt::If(if_stmt) => {
            block_mentions_binding_target(&if_stmt.then_block, binding)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|else_block| block_mentions_binding_target(else_block, binding))
        }
        AstStmt::While(while_stmt) => block_mentions_binding_target(&while_stmt.body, binding),
        AstStmt::Repeat(repeat_stmt) => block_mentions_binding_target(&repeat_stmt.body, binding),
        AstStmt::NumericFor(numeric_for) => {
            numeric_for.binding == binding
                || block_mentions_binding_target(&numeric_for.body, binding)
        }
        AstStmt::GenericFor(generic_for) => {
            generic_for.bindings.contains(&binding)
                || block_mentions_binding_target(&generic_for.body, binding)
        }
        AstStmt::DoBlock(block) => block_mentions_binding_target(block, binding),
        AstStmt::LocalFunctionDecl(function_decl) => function_decl.name == binding,
        AstStmt::GlobalDecl(_)
        | AstStmt::CallStmt(_)
        | AstStmt::Return(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_) => false,
    }
}

pub(super) fn stmt_has_nested_binding_use(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .any(|value| expr_has_nested_binding_use(value, binding, false)),
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .any(|value| expr_has_nested_binding_use(value, binding, false)),
        AstStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .any(|target| lvalue_has_nested_binding_use(target, binding))
                || assign
                    .values
                    .iter()
                    .any(|value| expr_has_nested_binding_use(value, binding, false))
        }
        AstStmt::CallStmt(call_stmt) => call_has_nested_binding_use(&call_stmt.call, binding),
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .any(|value| expr_has_nested_binding_use(value, binding, false)),
        AstStmt::If(if_stmt) => expr_has_nested_binding_use(&if_stmt.cond, binding, false),
        AstStmt::While(while_stmt) => expr_has_nested_binding_use(&while_stmt.cond, binding, false),
        AstStmt::Repeat(repeat_stmt) => {
            expr_has_nested_binding_use(&repeat_stmt.cond, binding, false)
        }
        AstStmt::NumericFor(numeric_for) => {
            expr_has_nested_binding_use(&numeric_for.start, binding, false)
                || expr_has_nested_binding_use(&numeric_for.limit, binding, false)
                || expr_has_nested_binding_use(&numeric_for.step, binding, false)
        }
        AstStmt::GenericFor(generic_for) => generic_for
            .iterator
            .iter()
            .any(|expr| expr_has_nested_binding_use(expr, binding, false)),
        AstStmt::DoBlock(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_) => false,
    }
}

fn block_mentions_binding_target(
    block: &crate::ast::common::AstBlock,
    binding: AstBindingRef,
) -> bool {
    block
        .stmts
        .iter()
        .any(|stmt| stmt_mentions_binding_target(stmt, binding))
}

fn lvalue_mentions_binding_target(lvalue: &AstLValue, binding: AstBindingRef) -> bool {
    match lvalue {
        AstLValue::Name(name) => binding_from_name_ref(name) == Some(binding),
        AstLValue::FieldAccess(_) | AstLValue::IndexAccess(_) => false,
    }
}

fn call_has_nested_binding_use(call: &AstCallKind, binding: AstBindingRef) -> bool {
    match call {
        AstCallKind::Call(call) => {
            expr_has_nested_binding_use(&call.callee, binding, false)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_has_nested_binding_use(arg, binding, false))
        }
        AstCallKind::MethodCall(call) => {
            expr_has_nested_binding_use(&call.receiver, binding, false)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_has_nested_binding_use(arg, binding, false))
        }
    }
}

fn lvalue_has_nested_binding_use(target: &AstLValue, binding: AstBindingRef) -> bool {
    match target {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => expr_has_nested_binding_use(&access.base, binding, true),
        AstLValue::IndexAccess(access) => {
            expr_has_nested_binding_use(&access.base, binding, true)
                || expr_has_nested_binding_use(&access.index, binding, true)
        }
    }
}

fn expr_has_nested_binding_use(expr: &AstExpr, binding: AstBindingRef, nested: bool) -> bool {
    match expr {
        AstExpr::Var(name) if name_matches_binding(name, binding) => nested,
        AstExpr::FieldAccess(access) => expr_has_nested_binding_use(&access.base, binding, true),
        AstExpr::IndexAccess(access) => {
            expr_has_nested_binding_use(&access.base, binding, true)
                || expr_has_nested_binding_use(&access.index, binding, true)
        }
        AstExpr::Unary(unary) => expr_has_nested_binding_use(&unary.expr, binding, true),
        AstExpr::Binary(binary) => {
            expr_has_nested_binding_use(&binary.lhs, binding, true)
                || expr_has_nested_binding_use(&binary.rhs, binding, true)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_has_nested_binding_use(&logical.lhs, binding, true)
                || expr_has_nested_binding_use(&logical.rhs, binding, true)
        }
        AstExpr::Call(call) => {
            expr_has_nested_binding_use(&call.callee, binding, true)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_has_nested_binding_use(arg, binding, true))
        }
        AstExpr::MethodCall(call) => {
            expr_has_nested_binding_use(&call.receiver, binding, true)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_has_nested_binding_use(arg, binding, true))
        }
        AstExpr::SingleValue(expr) => expr_has_nested_binding_use(expr, binding, true),
        AstExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            AstTableField::Array(value) => expr_has_nested_binding_use(value, binding, true),
            AstTableField::Record(record) => {
                let key_matches = match &record.key {
                    AstTableKey::Name(_) => false,
                    AstTableKey::Expr(key) => expr_has_nested_binding_use(key, binding, true),
                };
                key_matches || expr_has_nested_binding_use(&record.value, binding, true)
            }
        }),
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
        | AstExpr::VarArg => false,
    }
}

fn rewrite_binding_in_call(call: &mut AstCallKind, from: AstBindingRef, to: AstBindingRef) {
    match call {
        AstCallKind::Call(call) => {
            rewrite_binding_in_expr(&mut call.callee, from, to);
            for arg in &mut call.args {
                rewrite_binding_in_expr(arg, from, to);
            }
        }
        AstCallKind::MethodCall(call) => {
            rewrite_binding_in_expr(&mut call.receiver, from, to);
            for arg in &mut call.args {
                rewrite_binding_in_expr(arg, from, to);
            }
        }
    }
}

fn rewrite_binding_in_lvalue(target: &mut AstLValue, from: AstBindingRef, to: AstBindingRef) {
    match target {
        AstLValue::Name(name) => rewrite_binding_in_name(name, from, to),
        AstLValue::FieldAccess(access) => rewrite_binding_in_expr(&mut access.base, from, to),
        AstLValue::IndexAccess(access) => {
            rewrite_binding_in_expr(&mut access.base, from, to);
            rewrite_binding_in_expr(&mut access.index, from, to);
        }
    }
}

fn rewrite_binding_in_expr(expr: &mut AstExpr, from: AstBindingRef, to: AstBindingRef) {
    match expr {
        AstExpr::Var(name) => rewrite_binding_in_name(name, from, to),
        AstExpr::FieldAccess(access) => rewrite_binding_in_expr(&mut access.base, from, to),
        AstExpr::IndexAccess(access) => {
            rewrite_binding_in_expr(&mut access.base, from, to);
            rewrite_binding_in_expr(&mut access.index, from, to);
        }
        AstExpr::Unary(unary) => rewrite_binding_in_expr(&mut unary.expr, from, to),
        AstExpr::Binary(binary) => {
            rewrite_binding_in_expr(&mut binary.lhs, from, to);
            rewrite_binding_in_expr(&mut binary.rhs, from, to);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            rewrite_binding_in_expr(&mut logical.lhs, from, to);
            rewrite_binding_in_expr(&mut logical.rhs, from, to);
        }
        AstExpr::Call(call) => {
            rewrite_binding_in_expr(&mut call.callee, from, to);
            for arg in &mut call.args {
                rewrite_binding_in_expr(arg, from, to);
            }
        }
        AstExpr::MethodCall(call) => {
            rewrite_binding_in_expr(&mut call.receiver, from, to);
            for arg in &mut call.args {
                rewrite_binding_in_expr(arg, from, to);
            }
        }
        AstExpr::SingleValue(expr) => rewrite_binding_in_expr(expr, from, to),
        AstExpr::TableConstructor(table) => {
            for field in &mut table.fields {
                match field {
                    AstTableField::Array(value) => rewrite_binding_in_expr(value, from, to),
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &mut record.key {
                            rewrite_binding_in_expr(key, from, to);
                        }
                        rewrite_binding_in_expr(&mut record.value, from, to);
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
        | AstExpr::VarArg => {}
    }
}

fn rewrite_binding_in_name(name: &mut AstNameRef, from: AstBindingRef, to: AstBindingRef) {
    if name_matches_binding(name, from) {
        *name = binding_to_name(to);
    }
}

fn binding_to_name(binding: AstBindingRef) -> AstNameRef {
    match binding {
        AstBindingRef::Local(local) => AstNameRef::Local(local),
        AstBindingRef::Temp(temp) => AstNameRef::Temp(temp),
        AstBindingRef::SyntheticLocal(local) => AstNameRef::SyntheticLocal(local),
    }
}
