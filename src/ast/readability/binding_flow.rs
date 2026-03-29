//! 这个文件集中承载 AST readability 里的局部 binding 流分析工具。
//!
//! 这些 pass 经常需要回答同一类问题：
//! - 某个 binding 在一段语句里还会不会再被读取？
//! - 某个语句/块会不会提前引用一组待下沉的 hoisted local？
//! - 某个 binding 在当前函数体里一共被用了几次？
//!
//! 这里故意把“当前函数体”作为边界，不继续钻进嵌套函数体。
//! 原因是 AST 的 `LocalId` / `SyntheticLocalId` 都是按函数局部编号的，跨闭包继续统计
//! 很容易把不同函数里碰巧同号的 binding 错算成同一个变量。

use super::super::common::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstLValue, AstLocalBinding, AstNameRef, AstStmt,
    AstTableField, AstTableKey,
};

#[derive(Clone, Copy)]
enum BindingUseScope {
    CurrentFunctionOnly,
    IncludingNestedFunctions,
}

pub(super) fn name_matches_binding(name: &AstNameRef, binding: AstBindingRef) -> bool {
    match (binding, name) {
        (AstBindingRef::Local(local), AstNameRef::Local(target)) => local == *target,
        (AstBindingRef::Temp(temp), AstNameRef::Temp(target)) => temp == *target,
        (AstBindingRef::SyntheticLocal(local), AstNameRef::SyntheticLocal(target)) => {
            local == *target
        }
        _ => false,
    }
}

pub(super) fn count_binding_uses_in_stmts(stmts: &[AstStmt], binding: AstBindingRef) -> usize {
    count_binding_uses_in_stmts_with_scope(stmts, binding, BindingUseScope::CurrentFunctionOnly)
}

pub(super) fn count_binding_uses_in_stmts_deep(stmts: &[AstStmt], binding: AstBindingRef) -> usize {
    count_binding_uses_in_stmts_with_scope(
        stmts,
        binding,
        BindingUseScope::IncludingNestedFunctions,
    )
}

pub(super) fn count_binding_uses_in_block_deep(block: &AstBlock, binding: AstBindingRef) -> usize {
    count_binding_uses_in_block_with_scope(
        block,
        binding,
        BindingUseScope::IncludingNestedFunctions,
    )
}

pub(super) fn count_binding_mentions_in_block(block: &AstBlock, binding: AstBindingRef) -> usize {
    block
        .stmts
        .iter()
        .map(|stmt| count_binding_mentions_in_stmt(stmt, binding))
        .sum()
}

pub(super) fn count_binding_uses_in_stmt(stmt: &AstStmt, binding: AstBindingRef) -> usize {
    count_binding_uses_in_stmt_with_scope(stmt, binding, BindingUseScope::CurrentFunctionOnly)
}

fn count_binding_uses_in_stmts_with_scope(
    stmts: &[AstStmt],
    binding: AstBindingRef,
    scope: BindingUseScope,
) -> usize {
    stmts
        .iter()
        .map(|stmt| count_binding_uses_in_stmt_with_scope(stmt, binding, scope))
        .sum()
}

fn count_binding_uses_in_block_with_scope(
    block: &AstBlock,
    binding: AstBindingRef,
    scope: BindingUseScope,
) -> usize {
    count_binding_uses_in_stmts_with_scope(&block.stmts, binding, scope)
}

fn count_binding_uses_in_stmt_with_scope(
    stmt: &AstStmt,
    binding: AstBindingRef,
    scope: BindingUseScope,
) -> usize {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .map(|value| count_binding_uses_in_expr_with_scope(value, binding, scope))
            .sum(),
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .map(|value| count_binding_uses_in_expr_with_scope(value, binding, scope))
            .sum(),
        AstStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .map(|target| count_binding_uses_in_lvalue_with_scope(target, binding, scope))
                .sum::<usize>()
                + assign
                    .values
                    .iter()
                    .map(|value| count_binding_uses_in_expr_with_scope(value, binding, scope))
                    .sum::<usize>()
        }
        AstStmt::CallStmt(call_stmt) => {
            count_binding_uses_in_call_with_scope(&call_stmt.call, binding, scope)
        }
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .map(|value| count_binding_uses_in_expr_with_scope(value, binding, scope))
            .sum(),
        AstStmt::If(if_stmt) => {
            count_binding_uses_in_expr_with_scope(&if_stmt.cond, binding, scope)
                + count_binding_uses_in_block_with_scope(&if_stmt.then_block, binding, scope)
                + if_stmt
                    .else_block
                    .as_ref()
                    .map(|else_block| {
                        count_binding_uses_in_block_with_scope(else_block, binding, scope)
                    })
                    .unwrap_or(0)
        }
        AstStmt::While(while_stmt) => {
            count_binding_uses_in_expr_with_scope(&while_stmt.cond, binding, scope)
                + count_binding_uses_in_block_with_scope(&while_stmt.body, binding, scope)
        }
        AstStmt::Repeat(repeat_stmt) => {
            count_binding_uses_in_block_with_scope(&repeat_stmt.body, binding, scope)
                + count_binding_uses_in_expr_with_scope(&repeat_stmt.cond, binding, scope)
        }
        AstStmt::NumericFor(numeric_for) => {
            count_binding_uses_in_expr_with_scope(&numeric_for.start, binding, scope)
                + count_binding_uses_in_expr_with_scope(&numeric_for.limit, binding, scope)
                + count_binding_uses_in_expr_with_scope(&numeric_for.step, binding, scope)
                + count_binding_uses_in_block_with_scope(&numeric_for.body, binding, scope)
        }
        AstStmt::GenericFor(generic_for) => {
            generic_for
                .iterator
                .iter()
                .map(|expr| count_binding_uses_in_expr_with_scope(expr, binding, scope))
                .sum::<usize>()
                + count_binding_uses_in_block_with_scope(&generic_for.body, binding, scope)
        }
        AstStmt::DoBlock(block) => count_binding_uses_in_block_with_scope(block, binding, scope),
        AstStmt::FunctionDecl(function_decl) => {
            if matches!(scope, BindingUseScope::IncludingNestedFunctions) {
                count_binding_uses_in_block_with_scope(&function_decl.func.body, binding, scope)
            } else {
                0
            }
        }
        AstStmt::LocalFunctionDecl(function_decl) => {
            if matches!(scope, BindingUseScope::IncludingNestedFunctions) {
                count_binding_uses_in_block_with_scope(&function_decl.func.body, binding, scope)
            } else {
                0
            }
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => 0,
    }
}

fn count_binding_mentions_in_stmt(stmt: &AstStmt, binding: AstBindingRef) -> usize {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .map(|value| count_binding_uses_in_expr(value, binding))
            .sum(),
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .map(|value| count_binding_uses_in_expr(value, binding))
            .sum(),
        AstStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .map(|target| count_binding_mentions_in_lvalue(target, binding))
                .sum::<usize>()
                + assign
                    .values
                    .iter()
                    .map(|value| count_binding_uses_in_expr(value, binding))
                    .sum::<usize>()
        }
        AstStmt::CallStmt(call_stmt) => count_binding_uses_in_call(&call_stmt.call, binding),
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .map(|value| count_binding_uses_in_expr(value, binding))
            .sum(),
        AstStmt::If(if_stmt) => {
            count_binding_uses_in_expr(&if_stmt.cond, binding)
                + count_binding_mentions_in_block(&if_stmt.then_block, binding)
                + if_stmt
                    .else_block
                    .as_ref()
                    .map(|else_block| count_binding_mentions_in_block(else_block, binding))
                    .unwrap_or(0)
        }
        AstStmt::While(while_stmt) => {
            count_binding_uses_in_expr(&while_stmt.cond, binding)
                + count_binding_mentions_in_block(&while_stmt.body, binding)
        }
        AstStmt::Repeat(repeat_stmt) => {
            count_binding_mentions_in_block(&repeat_stmt.body, binding)
                + count_binding_uses_in_expr(&repeat_stmt.cond, binding)
        }
        AstStmt::NumericFor(numeric_for) => {
            count_binding_uses_in_expr(&numeric_for.start, binding)
                + count_binding_uses_in_expr(&numeric_for.limit, binding)
                + count_binding_uses_in_expr(&numeric_for.step, binding)
                + count_binding_mentions_in_block(&numeric_for.body, binding)
        }
        AstStmt::GenericFor(generic_for) => {
            generic_for
                .iterator
                .iter()
                .map(|expr| count_binding_uses_in_expr(expr, binding))
                .sum::<usize>()
                + count_binding_mentions_in_block(&generic_for.body, binding)
        }
        AstStmt::DoBlock(block) => count_binding_mentions_in_block(block, binding),
        AstStmt::FunctionDecl(_) | AstStmt::LocalFunctionDecl(_) => 0,
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => 0,
    }
}

fn count_binding_uses_in_call(call: &AstCallKind, binding: AstBindingRef) -> usize {
    count_binding_uses_in_call_with_scope(call, binding, BindingUseScope::CurrentFunctionOnly)
}

fn count_binding_uses_in_expr(expr: &AstExpr, binding: AstBindingRef) -> usize {
    count_binding_uses_in_expr_with_scope(expr, binding, BindingUseScope::CurrentFunctionOnly)
}

fn count_binding_uses_in_call_with_scope(
    call: &AstCallKind,
    binding: AstBindingRef,
    scope: BindingUseScope,
) -> usize {
    match call {
        AstCallKind::Call(call) => {
            count_binding_uses_in_expr_with_scope(&call.callee, binding, scope)
                + call
                    .args
                    .iter()
                    .map(|arg| count_binding_uses_in_expr_with_scope(arg, binding, scope))
                    .sum::<usize>()
        }
        AstCallKind::MethodCall(call) => {
            count_binding_uses_in_expr_with_scope(&call.receiver, binding, scope)
                + call
                    .args
                    .iter()
                    .map(|arg| count_binding_uses_in_expr_with_scope(arg, binding, scope))
                    .sum::<usize>()
        }
    }
}

fn count_binding_uses_in_lvalue_with_scope(
    target: &AstLValue,
    binding: AstBindingRef,
    scope: BindingUseScope,
) -> usize {
    match target {
        AstLValue::Name(_) => 0,
        AstLValue::FieldAccess(access) => {
            count_binding_uses_in_expr_with_scope(&access.base, binding, scope)
        }
        AstLValue::IndexAccess(access) => {
            count_binding_uses_in_expr_with_scope(&access.base, binding, scope)
                + count_binding_uses_in_expr_with_scope(&access.index, binding, scope)
        }
    }
}

fn count_binding_uses_in_expr_with_scope(
    expr: &AstExpr,
    binding: AstBindingRef,
    scope: BindingUseScope,
) -> usize {
    match expr {
        AstExpr::Var(name) if name_matches_binding(name, binding) => 1,
        AstExpr::FieldAccess(access) => {
            count_binding_uses_in_expr_with_scope(&access.base, binding, scope)
        }
        AstExpr::IndexAccess(access) => {
            count_binding_uses_in_expr_with_scope(&access.base, binding, scope)
                + count_binding_uses_in_expr_with_scope(&access.index, binding, scope)
        }
        AstExpr::Unary(unary) => count_binding_uses_in_expr_with_scope(&unary.expr, binding, scope),
        AstExpr::Binary(binary) => {
            count_binding_uses_in_expr_with_scope(&binary.lhs, binding, scope)
                + count_binding_uses_in_expr_with_scope(&binary.rhs, binding, scope)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            count_binding_uses_in_expr_with_scope(&logical.lhs, binding, scope)
                + count_binding_uses_in_expr_with_scope(&logical.rhs, binding, scope)
        }
        AstExpr::Call(call) => {
            count_binding_uses_in_call_with_scope(&AstCallKind::Call(call.clone()), binding, scope)
        }
        AstExpr::MethodCall(call) => count_binding_uses_in_call_with_scope(
            &AstCallKind::MethodCall(call.clone()),
            binding,
            scope,
        ),
        AstExpr::SingleValue(expr) => count_binding_uses_in_expr_with_scope(expr, binding, scope),
        AstExpr::TableConstructor(table) => table
            .fields
            .iter()
            .map(|field| match field {
                AstTableField::Array(value) => {
                    count_binding_uses_in_expr_with_scope(value, binding, scope)
                }
                AstTableField::Record(record) => {
                    let key_count = if let AstTableKey::Expr(key) = &record.key {
                        count_binding_uses_in_expr_with_scope(key, binding, scope)
                    } else {
                        0
                    };
                    key_count + count_binding_uses_in_expr_with_scope(&record.value, binding, scope)
                }
            })
            .sum(),
        AstExpr::FunctionExpr(function) => {
            if matches!(scope, BindingUseScope::IncludingNestedFunctions) {
                count_binding_uses_in_block_with_scope(&function.body, binding, scope)
            } else {
                0
            }
        }
        AstExpr::Nil
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

pub(super) fn stmt_references_any_binding(stmt: &AstStmt, bindings: &[AstLocalBinding]) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            local_decl
                .bindings
                .iter()
                .any(|binding| bindings.iter().any(|pending| pending.id == binding.id))
                || local_decl
                    .values
                    .iter()
                    .any(|value| expr_references_any_binding(value, bindings))
        }
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .any(|value| expr_references_any_binding(value, bindings)),
        AstStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .any(|target| lvalue_references_any_binding(target, bindings))
                || assign
                    .values
                    .iter()
                    .any(|value| expr_references_any_binding(value, bindings))
        }
        AstStmt::CallStmt(call_stmt) => call_references_any_binding(&call_stmt.call, bindings),
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .any(|value| expr_references_any_binding(value, bindings)),
        AstStmt::If(if_stmt) => {
            expr_references_any_binding(&if_stmt.cond, bindings)
                || block_references_any_binding(&if_stmt.then_block, bindings)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| block_references_any_binding(block, bindings))
        }
        AstStmt::While(while_stmt) => {
            expr_references_any_binding(&while_stmt.cond, bindings)
                || block_references_any_binding(&while_stmt.body, bindings)
        }
        AstStmt::Repeat(repeat_stmt) => {
            block_references_any_binding(&repeat_stmt.body, bindings)
                || expr_references_any_binding(&repeat_stmt.cond, bindings)
        }
        AstStmt::NumericFor(numeric_for) => {
            bindings
                .iter()
                .any(|binding| binding.id == numeric_for.binding)
                || expr_references_any_binding(&numeric_for.start, bindings)
                || expr_references_any_binding(&numeric_for.limit, bindings)
                || expr_references_any_binding(&numeric_for.step, bindings)
                || block_references_any_binding(&numeric_for.body, bindings)
        }
        AstStmt::GenericFor(generic_for) => {
            generic_for
                .bindings
                .iter()
                .any(|binding| bindings.iter().any(|pending| pending.id == *binding))
                || generic_for
                    .iterator
                    .iter()
                    .any(|expr| expr_references_any_binding(expr, bindings))
                || block_references_any_binding(&generic_for.body, bindings)
        }
        AstStmt::DoBlock(block) => block_references_any_binding(block, bindings),
        AstStmt::FunctionDecl(function_decl) => {
            function_name_references_any_binding(&function_decl.target, bindings)
        }
        AstStmt::LocalFunctionDecl(function_decl) => bindings
            .iter()
            .any(|binding| binding.id == function_decl.name),
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => false,
    }
}

pub(super) fn block_references_any_binding(block: &AstBlock, bindings: &[AstLocalBinding]) -> bool {
    block
        .stmts
        .iter()
        .any(|stmt| stmt_references_any_binding(stmt, bindings))
}

pub(super) fn expr_references_any_binding(expr: &AstExpr, bindings: &[AstLocalBinding]) -> bool {
    match expr {
        AstExpr::Var(name) => name_ref_matches_any_binding(name, bindings),
        AstExpr::FieldAccess(access) => expr_references_any_binding(&access.base, bindings),
        AstExpr::IndexAccess(access) => {
            expr_references_any_binding(&access.base, bindings)
                || expr_references_any_binding(&access.index, bindings)
        }
        AstExpr::Unary(unary) => expr_references_any_binding(&unary.expr, bindings),
        AstExpr::Binary(binary) => {
            expr_references_any_binding(&binary.lhs, bindings)
                || expr_references_any_binding(&binary.rhs, bindings)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_references_any_binding(&logical.lhs, bindings)
                || expr_references_any_binding(&logical.rhs, bindings)
        }
        AstExpr::Call(call) => {
            expr_references_any_binding(&call.callee, bindings)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_any_binding(arg, bindings))
        }
        AstExpr::MethodCall(call) => {
            expr_references_any_binding(&call.receiver, bindings)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_any_binding(arg, bindings))
        }
        AstExpr::SingleValue(expr) => expr_references_any_binding(expr, bindings),
        AstExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            AstTableField::Array(value) => expr_references_any_binding(value, bindings),
            AstTableField::Record(record) => {
                let key_references_binding = match &record.key {
                    AstTableKey::Name(_) => false,
                    AstTableKey::Expr(expr) => expr_references_any_binding(expr, bindings),
                };
                key_references_binding || expr_references_any_binding(&record.value, bindings)
            }
        }),
        AstExpr::FunctionExpr(_) => false,
        AstExpr::Nil
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

fn count_binding_mentions_in_lvalue(target: &AstLValue, binding: AstBindingRef) -> usize {
    match target {
        AstLValue::Name(name) if name_ref_matches_binding(name, binding) => 1,
        AstLValue::Name(_) => 0,
        AstLValue::FieldAccess(access) => count_binding_uses_in_expr(&access.base, binding),
        AstLValue::IndexAccess(access) => {
            count_binding_uses_in_expr(&access.base, binding)
                + count_binding_uses_in_expr(&access.index, binding)
        }
    }
}

fn call_references_any_binding(call: &AstCallKind, bindings: &[AstLocalBinding]) -> bool {
    match call {
        AstCallKind::Call(call) => {
            expr_references_any_binding(&call.callee, bindings)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_any_binding(arg, bindings))
        }
        AstCallKind::MethodCall(call) => {
            expr_references_any_binding(&call.receiver, bindings)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_any_binding(arg, bindings))
        }
    }
}

fn function_name_references_any_binding(
    target: &super::super::common::AstFunctionName,
    bindings: &[AstLocalBinding],
) -> bool {
    let path = match target {
        super::super::common::AstFunctionName::Plain(path) => path,
        super::super::common::AstFunctionName::Method(path, _) => path,
    };
    name_ref_matches_any_binding(&path.root, bindings)
}

fn lvalue_references_any_binding(target: &AstLValue, bindings: &[AstLocalBinding]) -> bool {
    match target {
        AstLValue::Name(name) => name_ref_matches_any_binding(name, bindings),
        AstLValue::FieldAccess(access) => expr_references_any_binding(&access.base, bindings),
        AstLValue::IndexAccess(access) => {
            expr_references_any_binding(&access.base, bindings)
                || expr_references_any_binding(&access.index, bindings)
        }
    }
}

fn name_ref_matches_any_binding(name: &AstNameRef, bindings: &[AstLocalBinding]) -> bool {
    bindings
        .iter()
        .any(|binding| name_ref_matches_binding(name, binding.id))
}

fn name_ref_matches_binding(name: &AstNameRef, binding: AstBindingRef) -> bool {
    name_matches_binding(name, binding)
}
