//! 这个文件负责 Naming 前的 AST 结构校验。
//!
//! Naming 假定 Readability 已经把 raw temp 完全物化掉，所以这里先把这些边界钉死。
//! 一旦检测到 temp 泄漏或函数引用缺失，就直接报结构错误，而不是让 Naming 继续兜底。

use crate::ast::traverse::{
    traverse_call_children, traverse_expr_children, traverse_lvalue_children,
    traverse_stmt_children,
};
use crate::ast::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstFunctionName, AstLValue,
    AstModule, AstNameRef, AstStmt,
};
use crate::hir::{HirModule, HirProtoRef};

use super::NamingError;

/// 确保函数 proto 存在。
pub(super) fn ensure_function_exists(
    hir: &HirModule,
    function: HirProtoRef,
) -> Result<(), NamingError> {
    if hir.protos.get(function.index()).is_some() {
        Ok(())
    } else {
        Err(NamingError::MissingFunction {
            function: function.index(),
        })
    }
}

/// 校验 Readability 输出可以安全进入 Naming。
pub(super) fn validate_readability_ast(
    module: &AstModule,
    function: HirProtoRef,
    hir: &HirModule,
) -> Result<(), NamingError> {
    ensure_function_exists(hir, function)?;
    validate_block_has_no_temps(&module.body, function, hir)
}

fn validate_block_has_no_temps(
    block: &AstBlock,
    function: HirProtoRef,
    hir: &HirModule,
) -> Result<(), NamingError> {
    for stmt in &block.stmts {
        validate_stmt_has_no_temps(stmt, function, hir)?;
    }
    Ok(())
}

fn validate_stmt_has_no_temps(
    stmt: &AstStmt,
    function: HirProtoRef,
    hir: &HirModule,
) -> Result<(), NamingError> {
    // 只有少数变体有自定义 temp 检查，先处理
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for binding in &local_decl.bindings {
                validate_binding_has_no_temp(binding.id, function)?;
            }
        }
        AstStmt::NumericFor(numeric_for) => {
            validate_binding_has_no_temp(numeric_for.binding, function)?;
        }
        AstStmt::GenericFor(generic_for) => {
            for &binding in &generic_for.bindings {
                validate_binding_has_no_temp(binding, function)?;
            }
        }
        AstStmt::FunctionDecl(function_decl) => {
            validate_function_name_has_no_temps(&function_decl.target, function)?;
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            validate_binding_has_no_temp(local_function_decl.name, function)?;
        }
        _ => {}
    }
    // 子节点递归全部交给宏
    traverse_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(expr) => {
            validate_expr_has_no_temps(expr, function, hir)?;
        },
        lvalue(lvalue) => {
            validate_lvalue_has_no_temps(lvalue, function, hir)?;
        },
        block(block) => {
            validate_block_has_no_temps(block, function, hir)?;
        },
        function(func) => {
            validate_function_expr_has_no_temps(func, function, hir)?;
        },
        condition(cond) => {
            validate_expr_has_no_temps(cond, function, hir)?;
        },
        call(call) => {
            validate_call_has_no_temps(call, function, hir)?;
        }
    );
    Ok(())
}

fn validate_function_expr_has_no_temps(
    function_expr: &AstFunctionExpr,
    parent_function: HirProtoRef,
    hir: &HirModule,
) -> Result<(), NamingError> {
    ensure_function_exists(hir, function_expr.function)?;
    if let Some(named_vararg) = function_expr.named_vararg {
        validate_binding_has_no_temp(named_vararg, function_expr.function)?;
    }
    for &binding in &function_expr.captured_bindings {
        validate_binding_has_no_temp(binding, parent_function)?;
    }
    validate_block_has_no_temps(&function_expr.body, function_expr.function, hir)
}

fn validate_binding_has_no_temp(
    binding: AstBindingRef,
    function: HirProtoRef,
) -> Result<(), NamingError> {
    let AstBindingRef::Temp(temp) = binding else {
        return Ok(());
    };
    Err(NamingError::UnexpectedTemp {
        function: function.index(),
        temp: temp.index(),
    })
}

fn validate_function_name_has_no_temps(
    target: &AstFunctionName,
    function: HirProtoRef,
) -> Result<(), NamingError> {
    let path = match target {
        AstFunctionName::Plain(path) => path,
        AstFunctionName::Method(path, _) => path,
    };
    if let AstNameRef::Temp(temp) = path.root {
        return Err(NamingError::UnexpectedTemp {
            function: function.index(),
            temp: temp.index(),
        });
    }
    Ok(())
}

fn validate_call_has_no_temps(
    call: &AstCallKind,
    function: HirProtoRef,
    hir: &HirModule,
) -> Result<(), NamingError> {
    traverse_call_children!(call, iter = iter, borrow = [&], expr(expr) => {
        validate_expr_has_no_temps(expr, function, hir)?;
    });
    Ok(())
}

fn validate_lvalue_has_no_temps(
    target: &AstLValue,
    function: HirProtoRef,
    hir: &HirModule,
) -> Result<(), NamingError> {
    if let AstLValue::Name(AstNameRef::Temp(temp)) = target {
        return Err(NamingError::UnexpectedTemp {
            function: function.index(),
            temp: temp.index(),
        });
    }
    traverse_lvalue_children!(target, borrow = [&], expr(expr) => {
        validate_expr_has_no_temps(expr, function, hir)?;
    });
    Ok(())
}

fn validate_expr_has_no_temps(
    expr: &AstExpr,
    function: HirProtoRef,
    hir: &HirModule,
) -> Result<(), NamingError> {
    if let AstExpr::Var(AstNameRef::Temp(temp)) = expr {
        return Err(NamingError::UnexpectedTemp {
            function: function.index(),
            temp: temp.index(),
        });
    }
    traverse_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(child) => {
            validate_expr_has_no_temps(child, function, hir)?;
        },
        function(func) => {
            validate_function_expr_has_no_temps(func, function, hir)?;
        }
    );
    Ok(())
}
