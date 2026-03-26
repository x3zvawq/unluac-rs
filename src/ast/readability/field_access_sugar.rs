//! 把等价的字符串索引收敛成字段访问。
//!
//! `obj["name"]` 和 `obj.name` 在 `name` 是合法标识符时语义等价。
//! 这里尽早把它规整成字段访问，是为了让后续的 alias inline / method sugar
//! 都能直接面对更稳定的 AST 形状，而不是各自重复理解字符串索引。

use super::super::common::{
    AstBlock, AstCallKind, AstExpr, AstFieldAccess, AstFunctionExpr, AstIndexAccess, AstLValue,
    AstModule, AstStmt, AstTableField, AstTableKey,
};
use super::ReadabilityContext;

pub(super) fn apply(module: &mut AstModule, _context: ReadabilityContext) -> bool {
    rewrite_block(&mut module.body)
}

fn rewrite_block(block: &mut AstBlock) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        changed |= rewrite_stmt(stmt);
    }
    changed
}

fn rewrite_stmt(stmt: &mut AstStmt) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter_mut()
            .fold(false, |changed, expr| rewrite_expr(expr) | changed),
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter_mut()
            .fold(false, |changed, expr| rewrite_expr(expr) | changed),
        AstStmt::Assign(assign) => {
            let mut changed = assign
                .targets
                .iter_mut()
                .fold(false, |changed, target| rewrite_lvalue(target) | changed);
            changed |= assign
                .values
                .iter_mut()
                .fold(false, |changed, expr| rewrite_expr(expr) | changed);
            changed
        }
        AstStmt::CallStmt(call_stmt) => rewrite_call(&mut call_stmt.call),
        AstStmt::Return(ret) => ret
            .values
            .iter_mut()
            .fold(false, |changed, expr| rewrite_expr(expr) | changed),
        AstStmt::If(ast_if) => {
            let mut changed = rewrite_expr(&mut ast_if.cond);
            changed |= rewrite_block(&mut ast_if.then_block);
            if let Some(else_block) = &mut ast_if.else_block {
                changed |= rewrite_block(else_block);
            }
            changed
        }
        AstStmt::While(ast_while) => {
            let mut changed = rewrite_expr(&mut ast_while.cond);
            changed |= rewrite_block(&mut ast_while.body);
            changed
        }
        AstStmt::Repeat(ast_repeat) => {
            let mut changed = rewrite_block(&mut ast_repeat.body);
            changed |= rewrite_expr(&mut ast_repeat.cond);
            changed
        }
        AstStmt::NumericFor(numeric_for) => {
            let mut changed = rewrite_expr(&mut numeric_for.start);
            changed |= rewrite_expr(&mut numeric_for.limit);
            changed |= rewrite_expr(&mut numeric_for.step);
            changed |= rewrite_block(&mut numeric_for.body);
            changed
        }
        AstStmt::GenericFor(generic_for) => {
            let mut changed = generic_for
                .iterator
                .iter_mut()
                .fold(false, |changed, expr| rewrite_expr(expr) | changed);
            changed |= rewrite_block(&mut generic_for.body);
            changed
        }
        AstStmt::DoBlock(block) => rewrite_block(block),
        AstStmt::FunctionDecl(function_decl) => rewrite_function(&mut function_decl.func),
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            rewrite_function(&mut local_function_decl.func)
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => false,
    }
}

fn rewrite_function(function: &mut AstFunctionExpr) -> bool {
    rewrite_block(&mut function.body)
}

fn rewrite_call(call: &mut AstCallKind) -> bool {
    match call {
        AstCallKind::Call(call) => {
            let mut changed = rewrite_expr(&mut call.callee);
            changed |= call
                .args
                .iter_mut()
                .fold(false, |changed, expr| rewrite_expr(expr) | changed);
            changed
        }
        AstCallKind::MethodCall(call) => {
            let mut changed = rewrite_expr(&mut call.receiver);
            changed |= call
                .args
                .iter_mut()
                .fold(false, |changed, expr| rewrite_expr(expr) | changed);
            changed
        }
    }
}

fn rewrite_lvalue(target: &mut AstLValue) -> bool {
    match target {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => rewrite_expr(&mut access.base),
        AstLValue::IndexAccess(access) => {
            let mut changed = rewrite_expr(&mut access.base);
            changed |= rewrite_expr(&mut access.index);
            if let Some(field_access) = field_access_from_index(access) {
                *target = AstLValue::FieldAccess(Box::new(field_access));
                return true;
            }
            changed
        }
    }
}

fn rewrite_expr(expr: &mut AstExpr) -> bool {
    match expr {
        AstExpr::FieldAccess(access) => rewrite_expr(&mut access.base),
        AstExpr::IndexAccess(access) => {
            let mut changed = rewrite_expr(&mut access.base);
            changed |= rewrite_expr(&mut access.index);
            if let Some(field_access) = field_access_from_index(access) {
                *expr = AstExpr::FieldAccess(Box::new(field_access));
                return true;
            }
            changed
        }
        AstExpr::Unary(unary) => rewrite_expr(&mut unary.expr),
        AstExpr::Binary(binary) => {
            let mut changed = rewrite_expr(&mut binary.lhs);
            changed |= rewrite_expr(&mut binary.rhs);
            changed
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            let mut changed = rewrite_expr(&mut logical.lhs);
            changed |= rewrite_expr(&mut logical.rhs);
            changed
        }
        AstExpr::Call(call) => {
            let mut changed = rewrite_expr(&mut call.callee);
            changed |= call
                .args
                .iter_mut()
                .fold(false, |changed, expr| rewrite_expr(expr) | changed);
            changed
        }
        AstExpr::MethodCall(call) => {
            let mut changed = rewrite_expr(&mut call.receiver);
            changed |= call
                .args
                .iter_mut()
                .fold(false, |changed, expr| rewrite_expr(expr) | changed);
            changed
        }
        AstExpr::TableConstructor(table) => {
            let mut changed = false;
            for field in &mut table.fields {
                match field {
                    AstTableField::Array(value) => {
                        changed |= rewrite_expr(value);
                    }
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &mut record.key {
                            changed |= rewrite_expr(key);
                        }
                        changed |= rewrite_expr(&mut record.value);
                    }
                }
            }
            changed
        }
        AstExpr::FunctionExpr(function) => rewrite_function(function),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => false,
    }
}

fn field_access_from_index(access: &AstIndexAccess) -> Option<AstFieldAccess> {
    let AstExpr::String(field) = &access.index else {
        return None;
    };
    if !is_lua_identifier(field) {
        return None;
    }
    Some(AstFieldAccess {
        base: access.base.clone(),
        field: field.clone(),
    })
}

fn is_lua_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first == '_' || first.is_ascii_alphabetic()) {
        return false;
    }
    if !chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric()) {
        return false;
    }
    !matches!(
        name,
        "and"
            | "break"
            | "do"
            | "else"
            | "elseif"
            | "end"
            | "false"
            | "for"
            | "function"
            | "goto"
            | "if"
            | "in"
            | "local"
            | "nil"
            | "not"
            | "or"
            | "repeat"
            | "return"
            | "then"
            | "true"
            | "until"
            | "while"
            | "global"
    )
}

#[cfg(test)]
mod tests;
