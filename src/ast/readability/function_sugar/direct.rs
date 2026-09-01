//! 这个子模块负责最直接的 function sugar 降糖。
//!
//! 它依赖 AST build 已经保留好的合法声明/赋值形状，只把“右值就是函数表达式”的语句改成
//! `function ... end` 形式，不会处理转发壳或 method alias。
//! 例如：`local f = function() end` 会在这里变成 `local function f() end`。

use crate::ast::common::{
    AstAssign, AstExpr, AstFunctionDecl, AstFunctionExpr, AstFunctionName, AstGlobalBindingTarget,
    AstGlobalDecl, AstLValue, AstLocalAttr, AstLocalDecl, AstLocalFunctionDecl, AstNamePath,
    AstNameRef, AstStmt, AstTargetDialect,
};

pub(super) fn lower_direct_function_stmt(
    stmt: &AstStmt,
    target: AstTargetDialect,
) -> Option<AstStmt> {
    match stmt {
        AstStmt::LocalDecl(local_decl) => try_lower_local_function_decl(local_decl),
        AstStmt::GlobalDecl(global_decl) => try_lower_global_function_decl(global_decl, target),
        AstStmt::Assign(assign) => try_lower_function_assign(assign, target),
        _ => None,
    }
}

fn try_lower_local_function_decl(local_decl: &AstLocalDecl) -> Option<AstStmt> {
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return None;
    }
    let binding = &local_decl.bindings[0];
    let AstExpr::FunctionExpr(func) = &local_decl.values[0] else {
        return None;
    };
    if binding.attr != AstLocalAttr::None {
        // 候选拒绝[TargetConstraint]：Lua 的 `local function` 语法没有 `<const>`/`<close>` 属性槽，不能丢弃原声明属性。
        return None;
    }
    let name = binding.id;
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
    if global_decl.bindings.len() != 1 || global_decl.values.len() != 1 {
        return None;
    }
    let AstExpr::FunctionExpr(func) = &global_decl.values[0] else {
        return None;
    };
    if !target.caps.global_decl {
        // 候选拒绝[TargetConstraint]：当前目标方言没有 `global function` 声明语法。
        return None;
    }
    if global_decl.bindings[0].attr != crate::ast::common::AstGlobalAttr::None {
        // 候选拒绝[TargetConstraint]：`global function` 语法不能表达原 global 声明属性。
        return None;
    }
    let AstGlobalBindingTarget::Name(name) = &global_decl.bindings[0].target else {
        // 候选拒绝[TargetConstraint]：通配 global 没有可用于函数声明的名字。
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

fn try_lower_function_assign(assign: &AstAssign, target: AstTargetDialect) -> Option<AstStmt> {
    if assign.targets.len() != 1 || assign.values.len() != 1 {
        return None;
    }
    let AstExpr::FunctionExpr(func) = &assign.values[0] else {
        return None;
    };
    let (target, func) = function_decl_target_from_lvalue(&assign.targets[0], func, target)?;
    Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
        target,
        func,
    })))
}

pub(super) fn function_decl_target_from_lvalue(
    target: &AstLValue,
    func: &AstFunctionExpr,
    dialect: AstTargetDialect,
) -> Option<(AstFunctionName, AstFunctionExpr)> {
    match target {
        AstLValue::Name(AstNameRef::Global(_)) if dialect.caps.global_decl => {
            // 候选拒绝[SemanticBarrier:DeclarationIdentity]：普通赋值若输出成 `global function` 会重复声明已有 global，反例见 regress_411。
            None
        }
        AstLValue::Name(name) => {
            // 候选接受[BindingIdentityProof]：Lua 的 plain `function name()` 正是对当前
            // binding 的函数赋值；流水线中的 Temp 已由前置 materialize pass 物化。
            Some((
                AstFunctionName::Plain(AstNamePath {
                    root: name.clone(),
                    fields: Vec::new(),
                }),
                func.clone(),
            ))
        }
        AstLValue::FieldAccess(access) => {
            // 无 method-definition provenance 时只能生成 plain field function；冒号形式会删除
            // 显式首参并改变 parameter binding，反例见 regress_333。
            let Some(AstNamePath { root, mut fields }) = name_path_from_expr(&access.base) else {
                // 候选拒绝[TargetConstraint]：Lua function 声明的 field target 必须是静态点号 name path。
                return None;
            };
            fields.push(access.field.clone());
            Some((
                AstFunctionName::Plain(AstNamePath { root, fields }),
                func.clone(),
            ))
        }
        AstLValue::IndexAccess(_) => {
            // 候选拒绝[TargetConstraint]：Lua function 声明不能用动态索引作为 target。
            None
        }
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
    use crate::ast::common::{AstBindingRef, AstLocalOrigin};
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
                capture_names_by_upvalue: std::collections::BTreeMap::new(),
                capture_write_names: BTreeSet::new(),
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
