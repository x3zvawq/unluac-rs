//! 这个子模块负责最直接的 function sugar 降糖。
//!
//! 它依赖 AST build 已经保留好的合法声明/赋值形状，只把“右值就是函数表达式”的语句改成
//! `function ... end` 形式，不会处理转发壳或 method alias。
//! 例如：`local f = function() end` 会在这里变成 `local function f() end`。

use crate::ast::common::{
    AstAssign, AstBindingRef, AstExpr, AstFunctionDecl, AstFunctionExpr, AstFunctionName,
    AstGlobalBindingTarget, AstGlobalDecl, AstLValue, AstLocalAttr, AstLocalDecl,
    AstLocalFunctionDecl, AstNamePath, AstNameRef, AstStmt, AstTargetDialect,
};

pub(super) fn lower_direct_function_stmt(
    stmt: &AstStmt,
    target: AstTargetDialect,
) -> Option<AstStmt> {
    match stmt {
        AstStmt::LocalDecl(local_decl) => try_lower_local_function_decl(local_decl),
        AstStmt::GlobalDecl(global_decl) => try_lower_global_function_decl(global_decl, target),
        AstStmt::Assign(assign) => try_lower_function_assign(assign),
        _ => None,
    }
}

fn try_lower_local_function_decl(local_decl: &AstLocalDecl) -> Option<AstStmt> {
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return None;
    }
    let binding = &local_decl.bindings[0];
    if binding.attr != AstLocalAttr::None {
        return None;
    }
    let name = match binding.id {
        AstBindingRef::Local(name) => AstBindingRef::Local(name),
        AstBindingRef::SyntheticLocal(name) => AstBindingRef::SyntheticLocal(name),
        crate::ast::common::AstBindingRef::Temp(_) => {
            return None;
        }
    };
    let AstExpr::FunctionExpr(func) = &local_decl.values[0] else {
        return None;
    };
    Some(AstStmt::LocalFunctionDecl(Box::new(AstLocalFunctionDecl {
        name,
        origin: binding.origin,
        func: func.as_ref().clone(),
    })))
}

fn try_lower_global_function_decl(
    global_decl: &AstGlobalDecl,
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

fn try_lower_function_assign(assign: &AstAssign) -> Option<AstStmt> {
    if assign.targets.len() != 1 || assign.values.len() != 1 {
        return None;
    }
    let AstExpr::FunctionExpr(func) = &assign.values[0] else {
        return None;
    };
    let (target, func) = function_decl_target_from_lvalue(&assign.targets[0], func)?;
    Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
        target,
        func,
    })))
}

pub(super) fn function_decl_target_from_lvalue(
    target: &AstLValue,
    func: &AstFunctionExpr,
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
            // 候选拒绝[ProofIncomplete]：assignment 与 method 的字节码形状相同，缺少绑定到
            // 该函数定义的语法 provenance；保留显式首参，避免隐式 `self` 改变调用结果。
            let AstNamePath { root, mut fields } = name_path_from_expr(&access.base)?;
            fields.push(access.field.clone());
            Some((
                AstFunctionName::Plain(AstNamePath { root, fields }),
                func.clone(),
            ))
        }
        AstLValue::IndexAccess(_) => None,
    }
}

fn name_path_from_expr(expr: &AstExpr) -> Option<AstNamePath> {
    match expr {
        AstExpr::Var(
            name @ (AstNameRef::Param(_)
            | AstNameRef::Local(_)
            | AstNameRef::SyntheticLocal(_)
            | AstNameRef::Upvalue(_)
            | AstNameRef::Global(_)),
        ) => Some(AstNamePath {
            root: name.clone(),
            fields: Vec::new(),
        }),
        AstExpr::FieldAccess(access) => {
            let mut path = name_path_from_expr(&access.base)?;
            path.fields.push(access.field.clone());
            Some(path)
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;
    use crate::ast::common::AstLocalOrigin;
    use crate::hir::{HirProtoRef, LocalId};

    fn local_function(origin: AstLocalOrigin) -> AstLocalDecl {
        AstLocalDecl {
            bindings: vec![crate::ast::common::AstLocalBinding {
                id: AstBindingRef::Local(LocalId(0)),
                attr: AstLocalAttr::None,
                origin,
            }],
            values: vec![AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
                function: HirProtoRef(0),
                params: Vec::new(),
                is_vararg: false,
                named_vararg: None,
                body: crate::ast::common::AstBlock::default(),
                captured_bindings: BTreeSet::new(),
                captured_params: BTreeSet::new(),
            }))],
        }
    }

    #[test]
    fn local_function_sugar_preserves_origin() {
        for origin in [
            AstLocalOrigin::Recovered,
            AstLocalOrigin::DebugHinted,
            AstLocalOrigin::PhysicalRoot,
        ] {
            let Some(AstStmt::LocalFunctionDecl(decl)) =
                try_lower_local_function_decl(&local_function(origin))
            else {
                panic!("eligible local function should retain sugar")
            };
            assert_eq!(decl.origin, origin);
        }
    }
}
