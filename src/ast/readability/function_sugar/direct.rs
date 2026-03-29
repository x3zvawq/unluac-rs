//! 这个子模块负责最直接的 function sugar 降糖。
//!
//! 它依赖 AST build 已经保留好的合法声明/赋值形状，只把“右值就是函数表达式”的语句改成
//! `function ... end` 形式，不会处理转发壳或 method alias。
//! 例如：`local f = function() end` 会在这里变成 `local function f() end`。

use std::collections::BTreeSet;

use crate::ast::common::{
    AstAssign, AstExpr, AstFunctionDecl, AstFunctionExpr, AstFunctionName, AstGlobalBindingTarget,
    AstGlobalDecl, AstLValue, AstLocalAttr, AstLocalDecl, AstLocalFunctionDecl, AstNamePath,
    AstNameRef, AstStmt, AstTargetDialect,
};

pub(super) fn lower_direct_function_stmt(
    stmt: AstStmt,
    target: AstTargetDialect,
    method_fields: &BTreeSet<String>,
) -> AstStmt {
    match &stmt {
        AstStmt::LocalDecl(local_decl) => try_lower_local_function_decl((**local_decl).clone()),
        AstStmt::GlobalDecl(global_decl) => {
            try_lower_global_function_decl((**global_decl).clone(), target).unwrap_or(stmt)
        }
        AstStmt::Assign(assign) => {
            try_lower_function_assign((**assign).clone(), method_fields).unwrap_or(stmt)
        }
        _ => stmt,
    }
}

fn try_lower_local_function_decl(local_decl: AstLocalDecl) -> AstStmt {
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return AstStmt::LocalDecl(Box::new(local_decl));
    }
    let binding = &local_decl.bindings[0];
    if binding.attr != AstLocalAttr::None {
        return AstStmt::LocalDecl(Box::new(local_decl));
    }
    let name = match binding.id {
        crate::ast::common::AstBindingRef::Local(name) => {
            crate::ast::common::AstBindingRef::Local(name)
        }
        crate::ast::common::AstBindingRef::SyntheticLocal(name) => {
            crate::ast::common::AstBindingRef::SyntheticLocal(name)
        }
        crate::ast::common::AstBindingRef::Temp(_) => {
            return AstStmt::LocalDecl(Box::new(local_decl));
        }
    };
    let AstExpr::FunctionExpr(func) = &local_decl.values[0] else {
        return AstStmt::LocalDecl(Box::new(local_decl));
    };
    AstStmt::LocalFunctionDecl(Box::new(AstLocalFunctionDecl {
        name,
        func: func.as_ref().clone(),
    }))
}

fn try_lower_global_function_decl(
    global_decl: AstGlobalDecl,
    target: AstTargetDialect,
) -> Option<AstStmt> {
    if !target.caps.global_decl || global_decl.bindings.len() != 1 || global_decl.values.len() != 1
    {
        return None;
    }
    if global_decl.bindings[0].attr != crate::ast::common::AstGlobalAttr::None {
        return None;
    }
    let AstGlobalBindingTarget::Name(name) = &global_decl.bindings[0].target else {
        return None;
    };
    let AstExpr::FunctionExpr(func) = &global_decl.values[0] else {
        return None;
    };
    Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
        target: AstFunctionName::Plain(AstNamePath {
            root: AstNameRef::Global(name.clone()),
            fields: Vec::new(),
        }),
        func: func.as_ref().clone(),
    })))
}

fn try_lower_function_assign(
    assign: AstAssign,
    method_fields: &BTreeSet<String>,
) -> Option<AstStmt> {
    if assign.targets.len() != 1 || assign.values.len() != 1 {
        return None;
    }
    let AstExpr::FunctionExpr(func) = &assign.values[0] else {
        return None;
    };
    let (target, func) = function_decl_target_from_lvalue(&assign.targets[0], func, method_fields)?;
    Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
        target,
        func,
    })))
}

pub(super) fn function_decl_target_from_lvalue(
    target: &AstLValue,
    func: &AstFunctionExpr,
    method_fields: &BTreeSet<String>,
) -> Option<(AstFunctionName, AstFunctionExpr)> {
    match target {
        AstLValue::Name(AstNameRef::Global(global)) => Some((
            AstFunctionName::Plain(AstNamePath {
                root: AstNameRef::Global(global.clone()),
                fields: Vec::new(),
            }),
            func.clone(),
        )),
        AstLValue::Name(_) => None,
        AstLValue::FieldAccess(access) => {
            let (root, mut fields) = name_path_from_expr(&access.base)?;
            if method_fields.contains(&access.field) && !func.params.is_empty() {
                return Some((
                    AstFunctionName::Method(AstNamePath { root, fields }, access.field.clone()),
                    func.clone(),
                ));
            }
            fields.push(access.field.clone());
            Some((
                AstFunctionName::Plain(AstNamePath { root, fields }),
                func.clone(),
            ))
        }
        AstLValue::IndexAccess(_) => None,
    }
}

fn name_path_from_expr(expr: &AstExpr) -> Option<(AstNameRef, Vec<String>)> {
    match expr {
        AstExpr::Var(
            name @ (AstNameRef::Param(_)
            | AstNameRef::Local(_)
            | AstNameRef::SyntheticLocal(_)
            | AstNameRef::Upvalue(_)
            | AstNameRef::Global(_)),
        ) => Some((name.clone(), Vec::new())),
        AstExpr::FieldAccess(access) => {
            let (root, mut fields) = name_path_from_expr(&access.base)?;
            fields.push(access.field.clone());
            Some((root, fields))
        }
        _ => None,
    }
}
