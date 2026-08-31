//! 校验 closure capture 与 local 声明顺序的 AST 层间合同。
//!
//! HIR 必须在 ByReference closure 之前声明对应 local，readability 只能保留或收缩已有
//! 词法关系，不能通过前移声明修复错误 binding。这里在 AST build 与 readability 出口复用
//! 同一校验：允许 `local function f()` 的同语句 self capture，拒绝同 block 的后置声明。

use std::collections::BTreeMap;

use super::common::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstModule, AstStmt,
};
use super::error::AstLowerError;
use crate::ast::traverse::{
    traverse_call_children, traverse_expr_children, traverse_lvalue_children,
    traverse_stmt_children,
};

pub(super) fn verify_forward_local_captures(module: &AstModule) -> Result<(), AstLowerError> {
    verify_block(module.entry_function.index(), &module.body)
}

fn verify_block(function: usize, block: &AstBlock) -> Result<(), AstLowerError> {
    let declarations = block
        .stmts
        .iter()
        .enumerate()
        .flat_map(|(index, stmt)| match stmt {
            AstStmt::LocalDecl(decl) => decl
                .bindings
                .iter()
                .map(move |binding| (binding.id, index))
                .collect::<Vec<_>>(),
            AstStmt::LocalFunctionDecl(decl) => vec![(decl.name, index)],
            _ => Vec::new(),
        })
        .collect::<BTreeMap<_, _>>();

    for (index, stmt) in block.stmts.iter().enumerate() {
        verify_direct_local_closure(function, index, stmt, &declarations)?;
        verify_stmt_children(function, stmt)?;
    }
    Ok(())
}

fn verify_direct_local_closure(
    function: usize,
    index: usize,
    stmt: &AstStmt,
    declarations: &BTreeMap<AstBindingRef, usize>,
) -> Result<(), AstLowerError> {
    let (closures, self_binding) = match stmt {
        AstStmt::LocalDecl(decl) => {
            let closures = decl.values.iter().filter_map(|value| match value {
                AstExpr::FunctionExpr(function) => Some(function.as_ref()),
                _ => None,
            });
            let self_binding =
                (decl.bindings.len() == 1 && decl.values.len() == 1).then_some(decl.bindings[0].id);
            (closures.collect::<Vec<_>>(), self_binding)
        }
        AstStmt::LocalFunctionDecl(decl) => (vec![&decl.func], Some(decl.name)),
        _ => return Ok(()),
    };

    for closure in closures {
        for &capture in &closure.captured_bindings {
            let valid = declarations
                .get(&capture)
                .is_none_or(|&declaration| declaration < index)
                || declarations.get(&capture) == Some(&index) && self_binding == Some(capture);
            if !valid {
                return Err(AstLowerError::InvalidForwardLocalCapture {
                    function,
                    binding: capture,
                });
            }
        }
    }
    Ok(())
}

fn verify_stmt_children(function: usize, stmt: &AstStmt) -> Result<(), AstLowerError> {
    traverse_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(expr) => { verify_expr(expr)?; },
        lvalue(lvalue) => { verify_lvalue(lvalue)?; },
        block(block) => { verify_block(function, block)?; },
        function(child) => { verify_function(child)?; },
        condition(condition) => { verify_expr(condition)?; },
        call(call) => { verify_call(call)?; }
    );
    Ok(())
}

fn verify_expr(expr: &AstExpr) -> Result<(), AstLowerError> {
    traverse_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(child) => { verify_expr(child)?; },
        function(child) => { verify_function(child)?; }
    );
    Ok(())
}

fn verify_lvalue(lvalue: &AstLValue) -> Result<(), AstLowerError> {
    traverse_lvalue_children!(lvalue, borrow = [&], expr(expr) => {
        verify_expr(expr)?;
    });
    Ok(())
}

fn verify_call(call: &AstCallKind) -> Result<(), AstLowerError> {
    traverse_call_children!(call, iter = iter, borrow = [&], expr(expr) => {
        verify_expr(expr)?;
    });
    Ok(())
}

fn verify_function(function: &AstFunctionExpr) -> Result<(), AstLowerError> {
    verify_block(function.function.index(), &function.body)
}
