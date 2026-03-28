//! LuaJIT 对 `return`/`break` 的块尾约束比我们当前 AST fallback 更敏感。
//!
//! 当 block 里还有后续 label/goto 需要继续承载控制流时，直接把 `return` 或 `break`
//! 留在同一层 block 中会导致 LuaJIT parser 在后续 `::label::` 处报语法错误。
//! 这里把这类终止语句包进一个窄 `do ... end`，既保留控制流，又满足目标语法。

use super::super::common::{
    AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstModule, AstStmt,
};
use super::ReadabilityContext;

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    if context.target.version != crate::ast::AstDialectVersion::LuaJit {
        return false;
    }
    rewrite_block(&mut module.body)
}

fn rewrite_block(block: &mut AstBlock) -> bool {
    let mut changed = false;

    for stmt in &mut block.stmts {
        changed |= rewrite_stmt(stmt);
    }

    let needs_wrap = block
        .stmts
        .iter()
        .enumerate()
        .filter_map(|(index, stmt)| {
            matches!(stmt, AstStmt::Return(_) | AstStmt::Break).then_some(index)
        })
        .collect::<Vec<_>>();

    for index in needs_wrap.into_iter().rev() {
        if index + 1 >= block.stmts.len() {
            continue;
        }
        let stmt = block.stmts.remove(index);
        block.stmts.insert(
            index,
            AstStmt::DoBlock(Box::new(AstBlock { stmts: vec![stmt] })),
        );
        changed = true;
    }

    changed
}

fn rewrite_stmt(stmt: &mut AstStmt) -> bool {
    match stmt {
        AstStmt::If(ast_if) => {
            let mut changed = rewrite_block(&mut ast_if.then_block);
            if let Some(else_block) = &mut ast_if.else_block {
                changed |= rewrite_block(else_block);
            }
            changed
        }
        AstStmt::While(ast_while) => rewrite_block(&mut ast_while.body),
        AstStmt::Repeat(ast_repeat) => rewrite_block(&mut ast_repeat.body),
        AstStmt::NumericFor(ast_for) => rewrite_block(&mut ast_for.body),
        AstStmt::GenericFor(ast_for) => rewrite_block(&mut ast_for.body),
        AstStmt::DoBlock(block) => rewrite_block(block),
        AstStmt::FunctionDecl(function_decl) => rewrite_block(&mut function_decl.func.body),
        AstStmt::LocalFunctionDecl(function_decl) => rewrite_block(&mut function_decl.func.body),
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter_mut()
            .fold(false, |changed, expr| rewrite_expr(expr) | changed),
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter_mut()
            .fold(false, |changed, expr| rewrite_expr(expr) | changed),
        AstStmt::Assign(assign) => {
            let mut changed = false;
            for target in &mut assign.targets {
                changed |= rewrite_lvalue(target);
            }
            for value in &mut assign.values {
                changed |= rewrite_expr(value);
            }
            changed
        }
        AstStmt::CallStmt(call_stmt) => rewrite_call(&mut call_stmt.call),
        AstStmt::Return(ret) => ret
            .values
            .iter_mut()
            .fold(false, |changed, expr| rewrite_expr(expr) | changed),
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => false,
    }
}

fn rewrite_call(call: &mut AstCallKind) -> bool {
    match call {
        AstCallKind::Call(call) => {
            let mut changed = rewrite_expr(&mut call.callee);
            for arg in &mut call.args {
                changed |= rewrite_expr(arg);
            }
            changed
        }
        AstCallKind::MethodCall(call) => {
            let mut changed = rewrite_expr(&mut call.receiver);
            for arg in &mut call.args {
                changed |= rewrite_expr(arg);
            }
            changed
        }
    }
}

fn rewrite_lvalue(lvalue: &mut AstLValue) -> bool {
    match lvalue {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => rewrite_expr(&mut access.base),
        AstLValue::IndexAccess(access) => {
            rewrite_expr(&mut access.base) | rewrite_expr(&mut access.index)
        }
    }
}

fn rewrite_function(function: &mut AstFunctionExpr) -> bool {
    rewrite_block(&mut function.body)
}

fn rewrite_expr(expr: &mut AstExpr) -> bool {
    match expr {
        AstExpr::FunctionExpr(function) => rewrite_function(function),
        AstExpr::FieldAccess(access) => rewrite_expr(&mut access.base),
        AstExpr::IndexAccess(access) => {
            rewrite_expr(&mut access.base) | rewrite_expr(&mut access.index)
        }
        AstExpr::Unary(unary) => rewrite_expr(&mut unary.expr),
        AstExpr::Binary(binary) => rewrite_expr(&mut binary.lhs) | rewrite_expr(&mut binary.rhs),
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            rewrite_expr(&mut logical.lhs) | rewrite_expr(&mut logical.rhs)
        }
        AstExpr::Call(call) => {
            let mut changed = rewrite_expr(&mut call.callee);
            for arg in &mut call.args {
                changed |= rewrite_expr(arg);
            }
            changed
        }
        AstExpr::MethodCall(call) => {
            let mut changed = rewrite_expr(&mut call.receiver);
            for arg in &mut call.args {
                changed |= rewrite_expr(arg);
            }
            changed
        }
        AstExpr::Var(_)
        | AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_) => false,
    }
}
