//! 这个文件负责 Naming 前的 AST 结构校验。
//!
//! Naming 假定 Readability 已经把 raw temp 完全物化掉，所以这里先把这些边界钉死。
//! 一旦检测到 temp 泄漏或函数引用缺失，就直接报结构错误，而不是让 Naming 继续兜底。

use crate::ast::{
    AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstFunctionName, AstLValue, AstModule,
    AstNameRef, AstStmt, AstTableField, AstTableKey,
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
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for binding in &local_decl.bindings {
                if let crate::ast::AstBindingRef::Temp(temp) = binding.id {
                    return Err(NamingError::UnexpectedTemp {
                        function: function.index(),
                        temp: temp.index(),
                    });
                }
            }
            for value in &local_decl.values {
                validate_expr_has_no_temps(value, function, hir)?;
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &global_decl.values {
                validate_expr_has_no_temps(value, function, hir)?;
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                validate_lvalue_has_no_temps(target, function, hir)?;
            }
            for value in &assign.values {
                validate_expr_has_no_temps(value, function, hir)?;
            }
        }
        AstStmt::CallStmt(call_stmt) => validate_call_has_no_temps(&call_stmt.call, function, hir)?,
        AstStmt::Return(ret) => {
            for value in &ret.values {
                validate_expr_has_no_temps(value, function, hir)?;
            }
        }
        AstStmt::If(if_stmt) => {
            validate_expr_has_no_temps(&if_stmt.cond, function, hir)?;
            validate_block_has_no_temps(&if_stmt.then_block, function, hir)?;
            if let Some(else_block) = &if_stmt.else_block {
                validate_block_has_no_temps(else_block, function, hir)?;
            }
        }
        AstStmt::While(while_stmt) => {
            validate_expr_has_no_temps(&while_stmt.cond, function, hir)?;
            validate_block_has_no_temps(&while_stmt.body, function, hir)?;
        }
        AstStmt::Repeat(repeat_stmt) => {
            validate_block_has_no_temps(&repeat_stmt.body, function, hir)?;
            validate_expr_has_no_temps(&repeat_stmt.cond, function, hir)?;
        }
        AstStmt::NumericFor(numeric_for) => {
            validate_expr_has_no_temps(&numeric_for.start, function, hir)?;
            validate_expr_has_no_temps(&numeric_for.limit, function, hir)?;
            validate_expr_has_no_temps(&numeric_for.step, function, hir)?;
            validate_block_has_no_temps(&numeric_for.body, function, hir)?;
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &generic_for.iterator {
                validate_expr_has_no_temps(expr, function, hir)?;
            }
            validate_block_has_no_temps(&generic_for.body, function, hir)?;
        }
        AstStmt::DoBlock(block) => validate_block_has_no_temps(block, function, hir)?,
        AstStmt::FunctionDecl(function_decl) => {
            validate_function_name_has_no_temps(&function_decl.target, function)?;
            validate_function_expr_has_no_temps(&function_decl.func, hir)?;
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            if let crate::ast::AstBindingRef::Temp(temp) = local_function_decl.name {
                return Err(NamingError::UnexpectedTemp {
                    function: function.index(),
                    temp: temp.index(),
                });
            }
            validate_function_expr_has_no_temps(&local_function_decl.func, hir)?;
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => {}
    }
    Ok(())
}

fn validate_function_expr_has_no_temps(
    function_expr: &AstFunctionExpr,
    hir: &HirModule,
) -> Result<(), NamingError> {
    ensure_function_exists(hir, function_expr.function)?;
    validate_block_has_no_temps(&function_expr.body, function_expr.function, hir)
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
    match call {
        AstCallKind::Call(call) => {
            validate_expr_has_no_temps(&call.callee, function, hir)?;
            for arg in &call.args {
                validate_expr_has_no_temps(arg, function, hir)?;
            }
        }
        AstCallKind::MethodCall(call) => {
            validate_expr_has_no_temps(&call.receiver, function, hir)?;
            for arg in &call.args {
                validate_expr_has_no_temps(arg, function, hir)?;
            }
        }
    }
    Ok(())
}

fn validate_lvalue_has_no_temps(
    target: &AstLValue,
    function: HirProtoRef,
    hir: &HirModule,
) -> Result<(), NamingError> {
    match target {
        AstLValue::Name(AstNameRef::Temp(temp)) => Err(NamingError::UnexpectedTemp {
            function: function.index(),
            temp: temp.index(),
        }),
        AstLValue::Name(_) => Ok(()),
        AstLValue::FieldAccess(access) => validate_expr_has_no_temps(&access.base, function, hir),
        AstLValue::IndexAccess(access) => {
            validate_expr_has_no_temps(&access.base, function, hir)?;
            validate_expr_has_no_temps(&access.index, function, hir)
        }
    }
}

fn validate_expr_has_no_temps(
    expr: &AstExpr,
    function: HirProtoRef,
    hir: &HirModule,
) -> Result<(), NamingError> {
    match expr {
        AstExpr::Var(AstNameRef::Temp(temp)) => Err(NamingError::UnexpectedTemp {
            function: function.index(),
            temp: temp.index(),
        }),
        AstExpr::Var(_)
        | AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::VarArg => Ok(()),
        AstExpr::FieldAccess(access) => validate_expr_has_no_temps(&access.base, function, hir),
        AstExpr::IndexAccess(access) => {
            validate_expr_has_no_temps(&access.base, function, hir)?;
            validate_expr_has_no_temps(&access.index, function, hir)
        }
        AstExpr::Unary(unary) => validate_expr_has_no_temps(&unary.expr, function, hir),
        AstExpr::Binary(binary) => {
            validate_expr_has_no_temps(&binary.lhs, function, hir)?;
            validate_expr_has_no_temps(&binary.rhs, function, hir)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            validate_expr_has_no_temps(&logical.lhs, function, hir)?;
            validate_expr_has_no_temps(&logical.rhs, function, hir)
        }
        AstExpr::Call(call) => {
            validate_expr_has_no_temps(&call.callee, function, hir)?;
            for arg in &call.args {
                validate_expr_has_no_temps(arg, function, hir)?;
            }
            Ok(())
        }
        AstExpr::MethodCall(call) => {
            validate_expr_has_no_temps(&call.receiver, function, hir)?;
            for arg in &call.args {
                validate_expr_has_no_temps(arg, function, hir)?;
            }
            Ok(())
        }
        AstExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    AstTableField::Array(value) => {
                        validate_expr_has_no_temps(value, function, hir)?
                    }
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &record.key {
                            validate_expr_has_no_temps(key, function, hir)?;
                        }
                        validate_expr_has_no_temps(&record.value, function, hir)?;
                    }
                }
            }
            Ok(())
        }
        AstExpr::FunctionExpr(function_expr) => {
            validate_function_expr_has_no_temps(function_expr, hir)
        }
    }
}
