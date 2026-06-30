//! 当前函数体内 AST binding 树遍历的共享 helper。
//!
//! `binding_flow` 更偏向整段语句流上的 use-count / reachability 分析；这里则只处理
//! 单棵 stmt/expr/lvalue 树上的递归查询与重写，并且故意不继续钻进嵌套函数体，
//! 避免把不同函数里碰巧同号的 binding 混成同一个局部变量。

mod rewrite;

use crate::ast::common::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstStmt,
    AstTableField, AstTableKey,
};

use super::binding_ref::{binding_from_name_ref, name_matches_binding};

pub(super) use rewrite::{replace_binding_use_in_expr, rewrite_binding_in_stmt};

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
        | AstExpr::VarArg
        | AstExpr::Error(_) => false,
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

pub(super) fn stmt_references_or_captures_binding(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    if stmt_captures_binding(stmt, binding) {
        return true;
    }

    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .any(|value| expr_references_binding(value, binding)),
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .any(|value| expr_references_binding(value, binding)),
        AstStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .any(|target| lvalue_references_binding(target, binding))
                || assign
                    .values
                    .iter()
                    .any(|value| expr_references_binding(value, binding))
        }
        AstStmt::CallStmt(call_stmt) => call_references_binding(&call_stmt.call, binding),
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .any(|value| expr_references_binding(value, binding)),
        AstStmt::If(if_stmt) => {
            expr_references_binding(&if_stmt.cond, binding)
                || block_references_or_captures_binding(&if_stmt.then_block, binding)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| block_references_or_captures_binding(block, binding))
        }
        AstStmt::While(while_stmt) => {
            expr_references_binding(&while_stmt.cond, binding)
                || block_references_or_captures_binding(&while_stmt.body, binding)
        }
        AstStmt::Repeat(repeat_stmt) => {
            block_references_or_captures_binding(&repeat_stmt.body, binding)
                || expr_references_binding(&repeat_stmt.cond, binding)
        }
        AstStmt::NumericFor(numeric_for) => {
            expr_references_binding(&numeric_for.start, binding)
                || expr_references_binding(&numeric_for.limit, binding)
                || expr_references_binding(&numeric_for.step, binding)
                || block_references_or_captures_binding(&numeric_for.body, binding)
        }
        AstStmt::GenericFor(generic_for) => {
            generic_for
                .iterator
                .iter()
                .any(|expr| expr_references_binding(expr, binding))
                || block_references_or_captures_binding(&generic_for.body, binding)
        }
        AstStmt::DoBlock(block) => block_references_or_captures_binding(block, binding),
        AstStmt::FunctionDecl(_) | AstStmt::LocalFunctionDecl(_) => false,
        AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => false,
    }
}

fn block_references_or_captures_binding(block: &AstBlock, binding: AstBindingRef) -> bool {
    block
        .stmts
        .iter()
        .any(|stmt| stmt_references_or_captures_binding(stmt, binding))
}

pub(super) fn stmt_captures_binding(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .any(|value| expr_captures_binding(value, binding)),
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .any(|value| expr_captures_binding(value, binding)),
        AstStmt::Assign(assign) => {
            assign
                .values
                .iter()
                .any(|value| expr_captures_binding(value, binding))
                || assign
                    .targets
                    .iter()
                    .any(|target| lvalue_captures_binding(target, binding))
        }
        AstStmt::CallStmt(call_stmt) => call_captures_binding(&call_stmt.call, binding),
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .any(|value| expr_captures_binding(value, binding)),
        AstStmt::If(if_stmt) => {
            expr_captures_binding(&if_stmt.cond, binding)
                || block_captures_binding(&if_stmt.then_block, binding)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| block_captures_binding(block, binding))
        }
        AstStmt::While(while_stmt) => {
            expr_captures_binding(&while_stmt.cond, binding)
                || block_captures_binding(&while_stmt.body, binding)
        }
        AstStmt::Repeat(repeat_stmt) => {
            block_captures_binding(&repeat_stmt.body, binding)
                || expr_captures_binding(&repeat_stmt.cond, binding)
        }
        AstStmt::NumericFor(numeric_for) => {
            expr_captures_binding(&numeric_for.start, binding)
                || expr_captures_binding(&numeric_for.limit, binding)
                || expr_captures_binding(&numeric_for.step, binding)
                || block_captures_binding(&numeric_for.body, binding)
        }
        AstStmt::GenericFor(generic_for) => {
            generic_for
                .iterator
                .iter()
                .any(|expr| expr_captures_binding(expr, binding))
                || block_captures_binding(&generic_for.body, binding)
        }
        AstStmt::DoBlock(block) => block_captures_binding(block, binding),
        AstStmt::FunctionDecl(function_decl) => {
            function_expr_captures_binding(&function_decl.func, binding)
        }
        AstStmt::LocalFunctionDecl(function_decl) => {
            function_expr_captures_binding(&function_decl.func, binding)
        }
        AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => false,
    }
}

pub(super) fn block_captures_binding(block: &AstBlock, binding: AstBindingRef) -> bool {
    block
        .stmts
        .iter()
        .any(|stmt| stmt_captures_binding(stmt, binding))
}

fn lvalue_captures_binding(lvalue: &AstLValue, binding: AstBindingRef) -> bool {
    match lvalue {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => expr_captures_binding(&access.base, binding),
        AstLValue::IndexAccess(access) => {
            expr_captures_binding(&access.base, binding)
                || expr_captures_binding(&access.index, binding)
        }
    }
}

fn call_captures_binding(call: &AstCallKind, binding: AstBindingRef) -> bool {
    match call {
        AstCallKind::Call(call) => {
            expr_captures_binding(&call.callee, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_captures_binding(arg, binding))
        }
        AstCallKind::MethodCall(call) => {
            expr_captures_binding(&call.receiver, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_captures_binding(arg, binding))
        }
    }
}

fn expr_captures_binding(expr: &AstExpr, binding: AstBindingRef) -> bool {
    match expr {
        AstExpr::FieldAccess(access) => expr_captures_binding(&access.base, binding),
        AstExpr::IndexAccess(access) => {
            expr_captures_binding(&access.base, binding)
                || expr_captures_binding(&access.index, binding)
        }
        AstExpr::Unary(unary) => expr_captures_binding(&unary.expr, binding),
        AstExpr::Binary(binary) => {
            expr_captures_binding(&binary.lhs, binding)
                || expr_captures_binding(&binary.rhs, binding)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_captures_binding(&logical.lhs, binding)
                || expr_captures_binding(&logical.rhs, binding)
        }
        AstExpr::Call(call) => {
            expr_captures_binding(&call.callee, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_captures_binding(arg, binding))
        }
        AstExpr::MethodCall(call) => {
            expr_captures_binding(&call.receiver, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_captures_binding(arg, binding))
        }
        AstExpr::SingleValue(expr) => expr_captures_binding(expr, binding),
        AstExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            AstTableField::Array(value) => expr_captures_binding(value, binding),
            AstTableField::Record(record) => {
                (match &record.key {
                    AstTableKey::Name(_) => false,
                    AstTableKey::Expr(key) => expr_captures_binding(key, binding),
                }) || expr_captures_binding(&record.value, binding)
            }
        }),
        AstExpr::FunctionExpr(function) => function_expr_captures_binding(function, binding),
        AstExpr::Nil
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

fn function_expr_captures_binding(function: &AstFunctionExpr, binding: AstBindingRef) -> bool {
    function.captured_bindings.contains(&binding)
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
        | AstExpr::VarArg
        | AstExpr::Error(_) => 0,
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
        | AstStmt::Label(_)
        | AstStmt::Error(_) => false,
    }
}

/// stmt 级别的 binding 使用查询统一入口。
fn stmt_has_binding_use_by(
    stmt: &AstStmt,
    binding: AstBindingRef,
    check_expr: impl Fn(&AstExpr, AstBindingRef) -> bool,
    check_call: impl Fn(&AstCallKind, AstBindingRef) -> bool,
    check_assign_target: impl Fn(&AstLValue, AstBindingRef) -> bool,
) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .any(|value| check_expr(value, binding)),
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .any(|value| check_expr(value, binding)),
        AstStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .any(|target| check_assign_target(target, binding))
                || assign.values.iter().any(|value| check_expr(value, binding))
        }
        AstStmt::CallStmt(call_stmt) => check_call(&call_stmt.call, binding),
        AstStmt::Return(ret) => ret.values.iter().any(|value| check_expr(value, binding)),
        AstStmt::If(if_stmt) => check_expr(&if_stmt.cond, binding),
        AstStmt::While(while_stmt) => check_expr(&while_stmt.cond, binding),
        AstStmt::Repeat(repeat_stmt) => check_expr(&repeat_stmt.cond, binding),
        AstStmt::NumericFor(numeric_for) => {
            check_expr(&numeric_for.start, binding)
                || check_expr(&numeric_for.limit, binding)
                || check_expr(&numeric_for.step, binding)
        }
        AstStmt::GenericFor(generic_for) => generic_for
            .iterator
            .iter()
            .any(|expr| check_expr(expr, binding)),
        AstStmt::DoBlock(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => false,
    }
}

pub(super) fn stmt_has_nested_binding_use(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    stmt_has_binding_use_by(
        stmt,
        binding,
        |e, b| expr_has_nested_binding_use(e, b, false),
        call_has_nested_binding_use,
        lvalue_has_nested_binding_use,
    )
}

pub(super) fn stmt_has_access_base_binding_use(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    stmt_has_binding_use_by(
        stmt,
        binding,
        |e, b| expr_has_access_base_binding_use(e, b, false),
        call_has_access_base_binding_use,
        lvalue_has_access_base_binding_use,
    )
}

pub(super) fn stmt_has_index_binding_use(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    stmt_has_binding_use_by(
        stmt,
        binding,
        |e, b| expr_has_index_binding_use(e, b, false),
        call_has_index_binding_use,
        lvalue_has_index_binding_use,
    )
}

pub(super) fn stmt_has_direct_call_arg_binding_use(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    stmt_has_binding_use_by(
        stmt,
        binding,
        expr_has_direct_call_arg_binding_use,
        call_has_direct_call_arg_binding_use,
        |_, _| false,
    )
}

pub(super) fn stmt_has_call_callee_binding_use(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    stmt_has_binding_use_by(
        stmt,
        binding,
        |e, b| expr_has_call_callee_binding_use(e, b, false),
        call_has_call_callee_binding_use,
        |_, _| false,
    )
}

pub(super) fn stmt_has_nested_binding_value_use(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    stmt_has_binding_use_by(
        stmt,
        binding,
        |e, b| expr_has_nested_binding_use(e, b, false),
        call_has_nested_binding_use,
        |_, _| false,
    )
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
    call_has_contextual_binding_use(call, binding, BindingUseContext::Nested { active: false })
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

fn call_has_access_base_binding_use(call: &AstCallKind, binding: AstBindingRef) -> bool {
    call_has_contextual_binding_use(
        call,
        binding,
        BindingUseContext::AccessBase { active: false },
    )
}

fn call_has_index_binding_use(call: &AstCallKind, binding: AstBindingRef) -> bool {
    call_has_contextual_binding_use(call, binding, BindingUseContext::Index { active: false })
}

fn call_has_direct_call_arg_binding_use(call: &AstCallKind, binding: AstBindingRef) -> bool {
    call_has_contextual_binding_use(call, binding, BindingUseContext::DirectCallArg)
}

fn args_have_direct_call_arg_binding_use(args: &[AstExpr], binding: AstBindingRef) -> bool {
    args.iter()
        .any(|arg| matches!(arg, AstExpr::Var(name) if name_matches_binding(name, binding)))
}

fn call_has_contextual_binding_use(
    call: &AstCallKind,
    binding: AstBindingRef,
    context: BindingUseContext,
) -> bool {
    match call {
        AstCallKind::Call(call) => {
            call_parts_have_contextual_binding_use(&call.callee, &call.args, binding, context)
        }
        AstCallKind::MethodCall(call) => {
            call_parts_have_contextual_binding_use(&call.receiver, &call.args, binding, context)
        }
    }
}

fn call_parts_have_contextual_binding_use(
    target: &AstExpr,
    args: &[AstExpr],
    binding: AstBindingRef,
    context: BindingUseContext,
) -> bool {
    match context {
        // direct-call-arg 只关心“当前这次调用”的顶层实参；如果实参本身又是调用，
        // 那个内层调用是否可折叠应由它自己的父级表达式位置决定。
        BindingUseContext::DirectCallArg => args_have_direct_call_arg_binding_use(args, binding),
        _ => {
            expr_has_contextual_binding_use(target, binding, context.call_target())
                || args
                    .iter()
                    .any(|arg| expr_has_contextual_binding_use(arg, binding, context.call_arg()))
        }
    }
}

fn call_has_call_callee_binding_use(call: &AstCallKind, binding: AstBindingRef) -> bool {
    call_has_contextual_binding_use(
        call,
        binding,
        BindingUseContext::CallCallee { active: false },
    )
}

fn lvalue_has_access_base_binding_use(target: &AstLValue, binding: AstBindingRef) -> bool {
    match target {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => {
            expr_has_access_base_binding_use(&access.base, binding, true)
        }
        AstLValue::IndexAccess(access) => {
            expr_has_access_base_binding_use(&access.base, binding, true)
                || expr_has_access_base_binding_use(&access.index, binding, false)
        }
    }
}

fn lvalue_has_index_binding_use(target: &AstLValue, binding: AstBindingRef) -> bool {
    match target {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => expr_has_index_binding_use(&access.base, binding, false),
        AstLValue::IndexAccess(access) => {
            expr_has_index_binding_use(&access.base, binding, false)
                || expr_has_index_binding_use(&access.index, binding, true)
        }
    }
}

/// 单棵表达式里的 binding use 位置状态。
///
/// Readability 的多个 pass 会问“这个 binding 是否出现在字段基底 / 索引 / 调用
/// callee / 嵌套表达式”等类似问题；用同一个状态机递归，避免每加一种位置查询
/// 都复制一整套 AST match。
#[derive(Clone, Copy)]
enum BindingUseContext {
    AccessBase { active: bool },
    Index { active: bool },
    DirectCallArg,
    CallCallee { active: bool },
    Nested { active: bool },
}

impl BindingUseContext {
    fn matches_var(self) -> bool {
        match self {
            Self::AccessBase { active } | Self::Index { active } => active,
            Self::CallCallee { active } | Self::Nested { active } => active,
            Self::DirectCallArg => false,
        }
    }

    fn field_base(self) -> Self {
        match self {
            Self::AccessBase { .. } => Self::AccessBase { active: true },
            Self::Index { .. } => Self::Index { active: false },
            Self::CallCallee { active } => Self::CallCallee { active },
            Self::Nested { .. } => Self::Nested { active: true },
            Self::DirectCallArg => Self::DirectCallArg,
        }
    }

    fn index_base(self) -> Self {
        match self {
            Self::AccessBase { .. } => Self::AccessBase { active: true },
            Self::Index { .. } => Self::Index { active: false },
            Self::CallCallee { active } => Self::CallCallee { active },
            Self::Nested { .. } => Self::Nested { active: true },
            Self::DirectCallArg => Self::DirectCallArg,
        }
    }

    fn index_key(self) -> Self {
        match self {
            Self::AccessBase { .. } => Self::AccessBase { active: false },
            Self::Index { .. } => Self::Index { active: true },
            Self::CallCallee { .. } => Self::CallCallee { active: false },
            Self::Nested { .. } => Self::Nested { active: true },
            Self::DirectCallArg => Self::DirectCallArg,
        }
    }

    fn nested_expr(self) -> Self {
        match self {
            Self::AccessBase { .. } => Self::AccessBase { active: false },
            Self::Index { .. } => Self::Index { active: false },
            Self::CallCallee { .. } => Self::CallCallee { active: false },
            Self::Nested { .. } => Self::Nested { active: true },
            Self::DirectCallArg => Self::DirectCallArg,
        }
    }

    fn single_value(self) -> Self {
        match self {
            Self::CallCallee { active } => Self::CallCallee { active },
            other => other.nested_expr(),
        }
    }

    fn call_target(self) -> Self {
        match self {
            Self::CallCallee { .. } => Self::CallCallee { active: true },
            Self::Nested { .. } => Self::Nested { active: true },
            Self::AccessBase { .. } => Self::AccessBase { active: false },
            Self::Index { .. } => Self::Index { active: false },
            Self::DirectCallArg => Self::DirectCallArg,
        }
    }

    fn call_arg(self) -> Self {
        self.nested_expr()
    }
}

fn expr_has_access_base_binding_use(
    expr: &AstExpr,
    binding: AstBindingRef,
    access_base: bool,
) -> bool {
    expr_has_contextual_binding_use(
        expr,
        binding,
        BindingUseContext::AccessBase {
            active: access_base,
        },
    )
}

fn expr_has_index_binding_use(expr: &AstExpr, binding: AstBindingRef, index: bool) -> bool {
    expr_has_contextual_binding_use(expr, binding, BindingUseContext::Index { active: index })
}

fn expr_has_direct_call_arg_binding_use(expr: &AstExpr, binding: AstBindingRef) -> bool {
    expr_has_contextual_binding_use(expr, binding, BindingUseContext::DirectCallArg)
}

fn expr_has_call_callee_binding_use(
    expr: &AstExpr,
    binding: AstBindingRef,
    callee_position: bool,
) -> bool {
    expr_has_contextual_binding_use(
        expr,
        binding,
        BindingUseContext::CallCallee {
            active: callee_position,
        },
    )
}

fn expr_has_nested_binding_use(expr: &AstExpr, binding: AstBindingRef, nested: bool) -> bool {
    expr_has_contextual_binding_use(expr, binding, BindingUseContext::Nested { active: nested })
}

fn expr_has_contextual_binding_use(
    expr: &AstExpr,
    binding: AstBindingRef,
    context: BindingUseContext,
) -> bool {
    match expr {
        AstExpr::Var(name) if name_matches_binding(name, binding) => context.matches_var(),
        AstExpr::FieldAccess(access) => {
            expr_has_contextual_binding_use(&access.base, binding, context.field_base())
        }
        AstExpr::IndexAccess(access) => {
            expr_has_contextual_binding_use(&access.base, binding, context.index_base())
                || expr_has_contextual_binding_use(&access.index, binding, context.index_key())
        }
        AstExpr::Call(call) => {
            call_parts_have_contextual_binding_use(&call.callee, &call.args, binding, context)
        }
        AstExpr::MethodCall(call) => {
            call_parts_have_contextual_binding_use(&call.receiver, &call.args, binding, context)
        }
        AstExpr::SingleValue(expr) => {
            expr_has_contextual_binding_use(expr, binding, context.single_value())
        }
        AstExpr::Unary(unary) => {
            expr_has_contextual_binding_use(&unary.expr, binding, context.nested_expr())
        }
        AstExpr::Binary(binary) => {
            expr_has_contextual_binding_use(&binary.lhs, binding, context.nested_expr())
                || expr_has_contextual_binding_use(&binary.rhs, binding, context.nested_expr())
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_has_contextual_binding_use(&logical.lhs, binding, context.nested_expr())
                || expr_has_contextual_binding_use(&logical.rhs, binding, context.nested_expr())
        }
        AstExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            AstTableField::Array(value) => {
                expr_has_contextual_binding_use(value, binding, context.nested_expr())
            }
            AstTableField::Record(record) => {
                let key_matches = match &record.key {
                    AstTableKey::Name(_) => false,
                    AstTableKey::Expr(key) => {
                        expr_has_contextual_binding_use(key, binding, context.nested_expr())
                    }
                };
                key_matches
                    || expr_has_contextual_binding_use(
                        &record.value,
                        binding,
                        context.nested_expr(),
                    )
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
        | AstExpr::VarArg
        | AstExpr::Error(_) => false,
    }
}
