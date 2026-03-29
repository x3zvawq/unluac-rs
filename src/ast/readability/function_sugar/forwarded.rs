//! 这个子模块负责吸收“先放进 local，再立刻转发出去”的函数壳。
//!
//! 它依赖 binding-flow 和 capture provenance 已确认这个局部只是纯转发壳，不会越权把
//! 真正有闭包依赖的 local function 折叠掉。
//! 例如：`local f = function() ... end; t.f = f` 会在这里尝试合成 `function t.f() ... end`。

use std::collections::BTreeSet;

use super::super::binding_flow::{
    count_binding_uses_in_block_deep, count_binding_uses_in_stmts_deep, name_matches_binding,
};
use super::direct::function_decl_target_from_lvalue;
use crate::ast::common::{
    AstBindingRef, AstExpr, AstFunctionDecl, AstFunctionExpr, AstGlobalBindingTarget, AstNamePath,
    AstNameRef, AstStmt, AstTargetDialect,
};

pub(super) fn try_lower_forwarded_function_stmt(
    stmts: &[AstStmt],
    target: AstTargetDialect,
    method_fields: &BTreeSet<String>,
) -> Option<(AstStmt, usize)> {
    let [AstStmt::LocalDecl(local_decl), next, ..] = stmts else {
        return None;
    };
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return None;
    }
    let binding = local_decl.bindings[0].id;
    if local_decl.bindings[0].attr != crate::ast::common::AstLocalAttr::None {
        return None;
    }
    let AstExpr::FunctionExpr(function) = &local_decl.values[0] else {
        return None;
    };
    // 只有“纯转发”的函数壳才适合被下一条语句吸收。
    // 递归 local function 这类 case 在 AST 函数体里往往已经只剩 `u0` 之类的 upvalue 引用，
    // 直接扫 body 看不到它对当前 binding 槽位的依赖；所以这里优先使用 AST build
    // 带下来的 capture provenance，确认这个局部槽位是不是闭包初始化的一部分。
    if function.captured_bindings.contains(&binding)
        || count_binding_uses_in_block_deep(&function.body, binding) != 0
    {
        return None;
    }
    if count_binding_uses_in_stmts_deep(&stmts[1..], binding) != 1 {
        return None;
    }
    let function = function.as_ref().clone();
    let stmt = inline_function_into_stmt(next, binding, function, target, method_fields)?;
    Some((stmt, 2))
}

fn inline_function_into_stmt(
    stmt: &AstStmt,
    binding: AstBindingRef,
    function: AstFunctionExpr,
    target: AstTargetDialect,
    method_fields: &BTreeSet<String>,
) -> Option<AstStmt> {
    match stmt {
        AstStmt::GlobalDecl(global_decl)
            if global_decl.bindings.len() == 1 && global_decl.values.len() == 1 =>
        {
            let AstExpr::Var(name) = &global_decl.values[0] else {
                return None;
            };
            if !name_matches_binding(name, binding) {
                return None;
            }
            if global_decl.bindings[0].attr == crate::ast::common::AstGlobalAttr::None
                && target.caps.global_decl
            {
                let AstGlobalBindingTarget::Name(name) = &global_decl.bindings[0].target else {
                    return None;
                };
                return Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
                    target: crate::ast::common::AstFunctionName::Plain(AstNamePath {
                        root: AstNameRef::Global(name.clone()),
                        fields: Vec::new(),
                    }),
                    func: function,
                })));
            }

            let mut global_decl = global_decl.as_ref().clone();
            global_decl.values[0] = AstExpr::FunctionExpr(Box::new(function));
            Some(AstStmt::GlobalDecl(Box::new(global_decl)))
        }
        AstStmt::Assign(assign) if assign.targets.len() == 1 && assign.values.len() == 1 => {
            let AstExpr::Var(name) = &assign.values[0] else {
                return None;
            };
            if !name_matches_binding(name, binding) {
                return None;
            }
            if let Some((target_name, function)) =
                function_decl_target_from_lvalue(&assign.targets[0], &function, method_fields)
            {
                return Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
                    target: target_name,
                    func: function,
                })));
            }

            let mut assign = assign.as_ref().clone();
            assign.values[0] = AstExpr::FunctionExpr(Box::new(function));
            Some(AstStmt::Assign(Box::new(assign)))
        }
        _ => None,
    }
}
