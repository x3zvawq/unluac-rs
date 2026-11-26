//! Naming 前的 AST 结构校验。
//!
//! 确保所有嵌套函数引用均存在于 `module.protos`，并校验局部环境 `_ENV` 活动范围。

use crate::ast::traverse::{
    traverse_call_children, traverse_lvalue_children, traverse_stmt_children,
};
use crate::ast::visit::{ExprNode, expr_nodes};
use crate::ast::{
    AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstModule, AstStmt, ProtoId,
};

use super::NamingError;

mod environment;

/// 确保函数 proto 存在。
fn ensure_function_exists(module: &AstModule, function: ProtoId) -> Result<(), NamingError> {
    if module.protos.get(function.index()).is_some() {
        Ok(())
    } else {
        Err(NamingError::MissingFunction {
            function: function.index(),
        })
    }
}

/// 校验 AST 输出可以安全进入 Naming。
pub(super) fn validate_ast(module: &AstModule) -> Result<(), NamingError> {
    let function = module.entry_function;
    ensure_function_exists(module, function)?;
    environment::validate(&module.body, &module.protos[function.index()])?;
    validate_block(&module.body, module)
}

fn validate_block(block: &AstBlock, module: &AstModule) -> Result<(), NamingError> {
    for stmt in &block.stmts {
        validate_stmt(stmt, module)?;
    }
    Ok(())
}

fn validate_stmt(stmt: &AstStmt, module: &AstModule) -> Result<(), NamingError> {
    traverse_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(expr) => {
            validate_expr(expr, module)?;
        },
        lvalue(lvalue) => {
            validate_lvalue(lvalue, module)?;
        },
        block(block) => {
            validate_block(block, module)?;
        },
        function(func) => {
            validate_function_expr(func, module)?;
        },
        condition(cond) => {
            validate_expr(cond, module)?;
        },
        call(call) => {
            validate_call(call, module)?;
        }
    );
    Ok(())
}

fn validate_function_expr(
    function_expr: &AstFunctionExpr,
    module: &AstModule,
) -> Result<(), NamingError> {
    ensure_function_exists(module, function_expr.function)?;
    environment::validate(
        &function_expr.body,
        &module.protos[function_expr.function.index()],
    )?;
    validate_block(&function_expr.body, module)
}

fn validate_call(call: &AstCallKind, module: &AstModule) -> Result<(), NamingError> {
    traverse_call_children!(call, iter = iter, borrow = [&], expr(expr) => {
        validate_expr(expr, module)?;
    });
    Ok(())
}

fn validate_lvalue(target: &AstLValue, module: &AstModule) -> Result<(), NamingError> {
    traverse_lvalue_children!(target, borrow = [&], expr(expr) => {
        validate_expr(expr, module)?;
    });
    Ok(())
}

fn validate_expr(expr: &AstExpr, module: &AstModule) -> Result<(), NamingError> {
    for node in expr_nodes(expr) {
        if let ExprNode::Function(func) = node {
            validate_function_expr(func, module)?;
        }
    }
    Ok(())
}
