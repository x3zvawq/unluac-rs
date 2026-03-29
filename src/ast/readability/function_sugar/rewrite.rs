//! 这个子模块是 `function_sugar` pass 的主调度器。
//!
//! 它依赖 `analysis/direct/forwarded/constructor/chain/method_alias` 已提供的局部规则，
//! 只负责按固定顺序在 block 上收敛这些 sugar，不会回头改 AST build 语义。
//! 例如：一段 `local f = function...; t.f = f` 会先在这里被路由到 forwarded 规则处理。

use std::collections::BTreeSet;

use super::super::ReadabilityContext;
use super::analysis::{collect_method_field_names, collect_method_field_names_in_block};
use super::chain::try_chain_local_method_call_stmt;
use super::constructor::try_inline_terminal_constructor_call;
use super::direct::lower_direct_function_stmt;
use super::forwarded::try_lower_forwarded_function_stmt;
use super::method_alias::try_recover_method_alias_stmt;
use crate::ast::common::{
    AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstModule, AstStmt, AstTableField,
    AstTableKey, AstTargetDialect,
};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let method_fields = collect_method_field_names(module);
    rewrite_block(&mut module.body, context.target, &method_fields)
}

fn rewrite_block(
    block: &mut AstBlock,
    target: AstTargetDialect,
    method_fields: &BTreeSet<String>,
) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        changed |= rewrite_nested(stmt, target, method_fields);
    }

    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut index = 0;
    while index < old_stmts.len() {
        if let Some((stmt, consumed)) =
            try_inline_terminal_constructor_call(&old_stmts[index..], method_fields)
        {
            new_stmts.push(stmt);
            changed = true;
            index += consumed;
            continue;
        }

        if let Some((stmt, consumed)) = try_recover_method_alias_stmt(&old_stmts[index..]) {
            new_stmts.push(stmt);
            changed = true;
            index += consumed;
            continue;
        }

        if let Some((stmt, consumed)) = try_chain_local_method_call_stmt(&old_stmts[index..]) {
            new_stmts.push(stmt);
            changed = true;
            index += consumed;
            continue;
        }

        if let Some((stmt, consumed)) =
            try_lower_forwarded_function_stmt(&old_stmts[index..], target, method_fields)
        {
            new_stmts.push(stmt);
            changed = true;
            index += consumed;
            continue;
        }

        let stmt = lower_direct_function_stmt(old_stmts[index].clone(), target, method_fields);
        changed |= stmt != old_stmts[index];
        new_stmts.push(stmt);
        index += 1;
    }
    block.stmts = new_stmts;
    changed
}

fn rewrite_nested(
    stmt: &mut AstStmt,
    target: AstTargetDialect,
    method_fields: &BTreeSet<String>,
) -> bool {
    match stmt {
        AstStmt::If(if_stmt) => {
            let mut changed = rewrite_block(&mut if_stmt.then_block, target, method_fields);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= rewrite_block(else_block, target, method_fields);
            }
            changed |= rewrite_function_exprs_in_expr(&mut if_stmt.cond, target);
            changed
        }
        AstStmt::While(while_stmt) => {
            rewrite_function_exprs_in_expr(&mut while_stmt.cond, target)
                | rewrite_block(&mut while_stmt.body, target, method_fields)
        }
        AstStmt::Repeat(repeat_stmt) => {
            rewrite_block(&mut repeat_stmt.body, target, method_fields)
                | rewrite_function_exprs_in_expr(&mut repeat_stmt.cond, target)
        }
        AstStmt::NumericFor(numeric_for) => {
            let mut changed = rewrite_function_exprs_in_expr(&mut numeric_for.start, target);
            changed |= rewrite_function_exprs_in_expr(&mut numeric_for.limit, target);
            changed |= rewrite_function_exprs_in_expr(&mut numeric_for.step, target);
            changed |= rewrite_block(&mut numeric_for.body, target, method_fields);
            changed
        }
        AstStmt::GenericFor(generic_for) => {
            let mut changed = false;
            for expr in &mut generic_for.iterator {
                changed |= rewrite_function_exprs_in_expr(expr, target);
            }
            changed |= rewrite_block(&mut generic_for.body, target, method_fields);
            changed
        }
        AstStmt::DoBlock(block) => rewrite_block(block, target, method_fields),
        AstStmt::FunctionDecl(function_decl) => {
            rewrite_function_expr(&mut function_decl.func, target)
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            rewrite_function_expr(&mut local_function_decl.func, target)
        }
        AstStmt::LocalDecl(local_decl) => {
            let mut changed = false;
            for value in &mut local_decl.values {
                changed |= rewrite_function_exprs_in_expr(value, target);
            }
            changed
        }
        AstStmt::GlobalDecl(global_decl) => {
            let mut changed = false;
            for value in &mut global_decl.values {
                changed |= rewrite_function_exprs_in_expr(value, target);
            }
            changed
        }
        AstStmt::Assign(assign) => {
            let mut changed = false;
            for target_lvalue in &mut assign.targets {
                changed |= rewrite_function_exprs_in_lvalue(target_lvalue, target);
            }
            for value in &mut assign.values {
                changed |= rewrite_function_exprs_in_expr(value, target);
            }
            changed
        }
        AstStmt::CallStmt(call_stmt) => rewrite_function_exprs_in_call(&mut call_stmt.call, target),
        AstStmt::Return(ret) => {
            let mut changed = false;
            for value in &mut ret.values {
                changed |= rewrite_function_exprs_in_expr(value, target);
            }
            changed
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => false,
    }
}

fn rewrite_function_expr(function: &mut AstFunctionExpr, target: AstTargetDialect) -> bool {
    let mut method_fields = BTreeSet::new();
    collect_method_field_names_in_block(&function.body, &mut method_fields);
    rewrite_block(&mut function.body, target, &method_fields)
}

fn rewrite_function_exprs_in_call(call: &mut AstCallKind, target: AstTargetDialect) -> bool {
    match call {
        AstCallKind::Call(call) => {
            let mut changed = rewrite_function_exprs_in_expr(&mut call.callee, target);
            for arg in &mut call.args {
                changed |= rewrite_function_exprs_in_expr(arg, target);
            }
            changed
        }
        AstCallKind::MethodCall(call) => {
            let mut changed = rewrite_function_exprs_in_expr(&mut call.receiver, target);
            for arg in &mut call.args {
                changed |= rewrite_function_exprs_in_expr(arg, target);
            }
            changed
        }
    }
}

fn rewrite_function_exprs_in_lvalue(
    target_lvalue: &mut AstLValue,
    target: AstTargetDialect,
) -> bool {
    match target_lvalue {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => rewrite_function_exprs_in_expr(&mut access.base, target),
        AstLValue::IndexAccess(access) => {
            rewrite_function_exprs_in_expr(&mut access.base, target)
                | rewrite_function_exprs_in_expr(&mut access.index, target)
        }
    }
}

fn rewrite_function_exprs_in_expr(expr: &mut AstExpr, target: AstTargetDialect) -> bool {
    match expr {
        AstExpr::FieldAccess(access) => rewrite_function_exprs_in_expr(&mut access.base, target),
        AstExpr::IndexAccess(access) => {
            rewrite_function_exprs_in_expr(&mut access.base, target)
                | rewrite_function_exprs_in_expr(&mut access.index, target)
        }
        AstExpr::Unary(unary) => rewrite_function_exprs_in_expr(&mut unary.expr, target),
        AstExpr::Binary(binary) => {
            rewrite_function_exprs_in_expr(&mut binary.lhs, target)
                | rewrite_function_exprs_in_expr(&mut binary.rhs, target)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            rewrite_function_exprs_in_expr(&mut logical.lhs, target)
                | rewrite_function_exprs_in_expr(&mut logical.rhs, target)
        }
        AstExpr::Call(call) => {
            let mut changed = rewrite_function_exprs_in_expr(&mut call.callee, target);
            for arg in &mut call.args {
                changed |= rewrite_function_exprs_in_expr(arg, target);
            }
            changed
        }
        AstExpr::MethodCall(call) => {
            let mut changed = rewrite_function_exprs_in_expr(&mut call.receiver, target);
            for arg in &mut call.args {
                changed |= rewrite_function_exprs_in_expr(arg, target);
            }
            changed
        }
        AstExpr::SingleValue(expr) => rewrite_function_exprs_in_expr(expr, target),
        AstExpr::TableConstructor(table) => {
            let mut changed = false;
            for field in &mut table.fields {
                match field {
                    AstTableField::Array(value) => {
                        changed |= rewrite_function_exprs_in_expr(value, target);
                    }
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &mut record.key {
                            changed |= rewrite_function_exprs_in_expr(key, target);
                        }
                        changed |= rewrite_function_exprs_in_expr(&mut record.value, target);
                    }
                }
            }
            changed
        }
        AstExpr::FunctionExpr(function) => rewrite_function_expr(function, target),
        AstExpr::Nil
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
