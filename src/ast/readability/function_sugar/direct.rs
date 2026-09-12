//! 这个子模块负责最直接的 function sugar 降糖。
//!
//! 它依赖 AST build 已经保留好的合法声明/赋值形状，只把“右值就是函数表达式”的语句改成
//! `function ... end` 形式，不会处理转发壳或 method alias。
//! 例如：`local f = function() end` 会在这里变成 `local function f() end`。
//! 共享声明 target 查询只投影名字与方言限制；函数内容由获准的直接/转发 owner 复制。

use crate::ast::common::{
    AstAssign, AstExpr, AstFunctionDecl, AstFunctionName, AstGlobalBindingTarget, AstGlobalDecl,
    AstLValue, AstLocalAttr, AstLocalDecl, AstLocalFunctionDecl, AstLocalOrigin, AstNamePath,
    AstNameRef, AstStmt, AstTargetDialect,
};

/// 空声明已把 binding 放进作用域；local function 保留这一点，普通 local initializer 则不保留。
pub(super) fn lower_declared_function(stmts: &[AstStmt]) -> Option<(AstStmt, usize)> {
    let [AstStmt::LocalDecl(decl), next, ..] = stmts else {
        return None;
    };
    let [binding] = decl.bindings.as_slice() else {
        return None;
    };
    if !decl.values.is_empty()
        || decl.initializer_merge_transaction.is_some()
        || binding.attr != AstLocalAttr::None
        || binding.origin != AstLocalOrigin::Recovered
    {
        // 候选拒绝[LayerBoundary]：只消费 recovered 空声明，不改写 debug 起点、属性或物理根清零事务。
        return None;
    }
    let function = match next {
        AstStmt::Assign(assign) => {
            let ([AstLValue::Name(name)], [AstExpr::FunctionExpr(function)]) =
                (assign.targets.as_slice(), assign.values.as_slice())
            else {
                return None;
            };
            if !binding.id.matches_name_ref(name) {
                return None;
            }
            function.as_ref()
        }
        AstStmt::FunctionDecl(decl) => {
            let AstFunctionName::Plain(path) = &decl.target else {
                return None;
            };
            if !path.fields.is_empty() || !binding.id.matches_name_ref(&path.root) {
                return None;
            }
            &decl.func
        }
        _ => return None,
    };
    // 不删除 binding、不改变 capture 的 value epoch；保留 HIR authority，递归函数也无需移出捕获域。
    Some((
        AstStmt::LocalFunctionDecl(Box::new(AstLocalFunctionDecl {
            name: binding.id,
            origin: binding.origin,
            rewrite_authority: binding.rewrite_authority.clone(),
            func: function.clone(),
        })),
        2,
    ))
}

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
    if !binding.rewrite_authority.may_move_scope_start() {
        // 候选拒绝[LayerBoundary]：`local f = function` 与 `local function f` 的 binding
        // 可见起点不同；HIR 已保留的身份不能由 AST 改写。
        return None;
    }
    let name = binding.id;
    Some(AstStmt::LocalFunctionDecl(Box::new(AstLocalFunctionDecl {
        name,
        origin: binding.origin,
        rewrite_authority: binding.rewrite_authority.clone(),
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
    let target = function_decl_target_from_lvalue(&assign.targets[0], target)?;
    Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
        target,
        func: func.as_ref().clone(),
    })))
}

pub(super) fn function_decl_target_from_lvalue(
    target: &AstLValue,
    dialect: AstTargetDialect,
) -> Option<AstFunctionName> {
    match target {
        AstLValue::Name(AstNameRef::Global(_)) if dialect.caps.global_decl => {
            // 候选拒绝[SemanticBarrier:DeclarationIdentity]：普通赋值若输出成 `global function` 会重复声明已有 global，反例见 regress_411。
            None
        }
        AstLValue::Name(name) => {
            // 候选接受[BindingIdentityProof]：Lua 的 plain `function name()` 正是对当前
            // binding 的函数赋值；流水线中的 Temp 已由前置 materialize pass 物化。
            Some(AstFunctionName::Plain(AstNamePath {
                root: name.clone(),
                fields: Vec::new(),
            }))
        }
        AstLValue::FieldAccess(access) => {
            // 先保留完整参数；冒号形式由 method_decl 独立审查 self 的命名与作用域。
            let Some(AstNamePath { root, mut fields }) = name_path_from_expr(&access.base) else {
                // 候选拒绝[TargetConstraint]：Lua function 声明的 field target 必须是静态点号 name path。
                return None;
            };
            fields.push(access.field.clone());
            Some(AstFunctionName::Plain(AstNamePath { root, fields }))
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
