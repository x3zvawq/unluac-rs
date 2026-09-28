//! 将直接函数声明或赋值整理为 function 语法。
//!
//! 消费 AST build 的合法节点与目标方言限制，转发壳和 method alias 由各自 owner 处理。

use super::super::binding_flow::MutableSnapshotNames;
use super::forwarded::lvalue_prefix_can_move_before_closure;
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
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<AstStmt> {
    match stmt {
        AstStmt::LocalDecl(local_decl) => try_lower_local_function_decl(local_decl),
        AstStmt::GlobalDecl(global_decl) => try_lower_global_function_decl(global_decl, target),
        AstStmt::Assign(assign) => try_lower_function_assign(assign, target, mutable_snapshots),
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
    if !binding.rewrite_authority.may_use_local_function_syntax() {
        // 候选拒绝[LayerBoundary]：除只要求原槽前缀的身份外，其它 HIR 起点保留不能
        // 由声明糖改写；这里保留 binding/capture 身份和同点 CLOSURE 初始化。
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
        global_declaration: true,
        func: func.as_ref().clone(),
    })))
}

fn try_lower_function_assign(
    assign: &AstAssign,
    target: AstTargetDialect,
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<AstStmt> {
    if assign.targets.len() != 1 || assign.values.len() != 1 {
        return None;
    }
    let AstExpr::FunctionExpr(func) = &assign.values[0] else {
        return None;
    };
    if target.version == crate::decompile::DecompileDialect::Luau
        && !lvalue_prefix_can_move_before_closure(&assign.targets[0], mutable_snapshots)
    {
        // 候选拒绝[SemanticBarrier:EvalOrder]：Luau 普通赋值先求目标，函数声明
        // 却先分配闭包；带读取事件的目标不能仅为语法糖与 CLOSURE 交换顺序。
        return None;
    }
    let target = function_decl_target_from_lvalue(&assign.targets[0])?;
    Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
        target,
        global_declaration: false,
        func: func.as_ref().clone(),
    })))
}

pub(super) fn function_decl_target_from_lvalue(target: &AstLValue) -> Option<AstFunctionName> {
    match target {
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
