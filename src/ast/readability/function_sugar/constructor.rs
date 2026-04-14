//! 这个子模块负责把“构造器尾部立刻安装方法/字段函数”的模式收成更自然的函数 sugar。
//!
//! 它依赖前缀 local alias 证据和已经合法化的 AST，只吸收终端构造器链上的局部模式，
//! 不会在这里重写一般赋值语句。
//! 例如：
//! - `local t = {}; t.pick = function(...) end; return t`
//!   -> `local t = { pick = function(...) end }; return t`
//! - `local meta = {}; local methods = {}; function methods.bump(...) end; meta.__index = methods;
//!    local ctor = ffi.metatype("x", meta)`
//!   -> `local ctor = ffi.metatype("x", { __index = { bump = function(...) end } })`
//!
//! 这里不会去猜任意跨语句的数据流；只有“构造器 local -> 构造器字段接线 -> 终端返回/终端局部初始化”
//! 这一整段都还保持机械脚手架形状时，才会收回源码结构。

use std::collections::BTreeSet;

use super::super::binding_flow::{count_binding_uses_in_stmts_deep, name_matches_binding};
use crate::ast::common::{
    AstAssign, AstBindingRef, AstExpr, AstFieldAccess, AstFunctionExpr, AstFunctionName, AstLValue,
    AstLocalAttr, AstLocalDecl, AstReturn, AstStmt, AstTableField, AstTableKey,
};

pub(super) fn try_inline_terminal_constructor_fields(
    stmts: &[AstStmt],
) -> Option<(AstStmt, usize)> {
    let AstStmt::LocalDecl(local_decl) = stmts.first()? else {
        return None;
    };
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return None;
    }
    if local_decl.bindings[0].attr != AstLocalAttr::None {
        return None;
    }
    let binding = local_decl.bindings[0].id;
    let AstExpr::TableConstructor(_) = &local_decl.values[0] else {
        return None;
    };

    let mut rewritten = local_decl.as_ref().clone();
    let AstExpr::TableConstructor(table) = &mut rewritten.values[0] else {
        unreachable!("matched constructor value above")
    };

    let mut consumed = 1usize;
    let mut inlined_any = false;
    while let Some(stmt) = stmts.get(consumed) {
        let Some((field, func)) = inlineable_local_table_function_stmt(stmt, binding) else {
            break;
        };
        table
            .fields
            .push(AstTableField::Record(crate::ast::AstRecordField {
                key: AstTableKey::Name(field),
                value: AstExpr::FunctionExpr(Box::new(func)),
            }));
        consumed += 1;
        inlined_any = true;
    }
    if !inlined_any {
        return None;
    }

    let AstStmt::Return(ret) = stmts.get(consumed)? else {
        return None;
    };
    let [AstExpr::Var(name)] = ret.values.as_slice() else {
        return None;
    };
    if !name_matches_binding(name, binding) {
        return None;
    }

    Some((AstStmt::LocalDecl(Box::new(rewritten)), consumed))
}

pub(super) fn try_inline_terminal_constructor_call(
    stmts: &[AstStmt],
    _method_fields: &BTreeSet<String>,
) -> Option<(AstStmt, usize)> {
    let (callee_binding, callee_expr) = single_local_alias_decl(stmts.first()?)?;
    let mut consumed = 1usize;
    let mut arg_locals = Vec::<ConstructorArg>::new();

    while let Some(stmt) = stmts.get(consumed) {
        let Some((binding, value)) = single_local_alias_decl(stmt) else {
            break;
        };
        arg_locals.push(ConstructorArg {
            binding,
            value: value.clone(),
            pass_to_sink: true,
        });
        consumed += 1;
    }
    if arg_locals.is_empty() {
        return None;
    }

    while let Some(stmt) = stmts.get(consumed) {
        if inline_arg_local_table_function(stmt, &mut arg_locals) {
            consumed += 1;
            continue;
        }
        if inline_nested_arg_local_table(stmt, &mut arg_locals) {
            consumed += 1;
            continue;
        }
        break;
    }

    let sink = stmts.get(consumed)?;
    let rewritten_sink =
        rewrite_terminal_constructor_call_sink(sink, callee_binding, callee_expr, &arg_locals)?;
    if !matches!(sink, AstStmt::Return(_))
        && !removed_constructor_locals_are_dead_after_sink(
            stmts.get((consumed + 1)..).unwrap_or_default(),
            callee_binding,
            &arg_locals,
        )
    {
        return None;
    }
    Some((rewritten_sink, consumed + 1))
}

#[derive(Clone)]
struct ConstructorArg {
    binding: AstBindingRef,
    value: AstExpr,
    pass_to_sink: bool,
}

fn single_local_alias_decl(stmt: &AstStmt) -> Option<(AstBindingRef, &AstExpr)> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return None;
    }
    if local_decl.bindings[0].attr != AstLocalAttr::None {
        return None;
    }
    Some((local_decl.bindings[0].id, &local_decl.values[0]))
}

fn inlineable_local_table_function_stmt(
    stmt: &AstStmt,
    binding: AstBindingRef,
) -> Option<(String, AstFunctionExpr)> {
    match stmt {
        AstStmt::Assign(assign) => inlineable_local_table_function_assign(assign, binding),
        AstStmt::FunctionDecl(function_decl) => {
            let AstFunctionName::Plain(path) = &function_decl.target else {
                return None;
            };
            if path.fields.len() != 1 || !name_matches_binding(&path.root, binding) {
                return None;
            }
            // 同 assign 分支：闭包捕获了 constructor binding 时不能折入
            if function_decl.func.captured_bindings.contains(&binding) {
                return None;
            }
            Some((path.fields[0].clone(), function_decl.func.clone()))
        }
        _ => None,
    }
}

fn inlineable_local_table_function_assign(
    assign: &AstAssign,
    binding: AstBindingRef,
) -> Option<(String, AstFunctionExpr)> {
    if assign.targets.len() != 1 || assign.values.len() != 1 {
        return None;
    }
    let AstLValue::FieldAccess(access) = &assign.targets[0] else {
        return None;
    };
    let AstFieldAccess { base, field } = access.as_ref();
    let AstExpr::Var(name) = base else {
        return None;
    };
    if !name_matches_binding(name, binding) {
        return None;
    }
    let AstExpr::FunctionExpr(function) = &assign.values[0] else {
        return None;
    };
    // 如果闭包体捕获了 constructor binding 自身（如 `obj.inc = function() obj.count = ... end`），		
    // 折入 constructor 后 binding 可能因 return-handoff 被消除，导致闭包中引用悬空。
    if function.captured_bindings.contains(&binding) {
        return None;
    }
    Some((field.clone(), function.as_ref().clone()))
}

fn inline_arg_local_table_function(stmt: &AstStmt, arg_locals: &mut [ConstructorArg]) -> bool {
    for arg_local in arg_locals {
        let Some((field, func)) = inlineable_local_table_function_stmt(stmt, arg_local.binding)
        else {
            continue;
        };
        let AstExpr::TableConstructor(table) = &mut arg_local.value else {
            continue;
        };
        table
            .fields
            .push(AstTableField::Record(crate::ast::common::AstRecordField {
                key: AstTableKey::Name(field),
                value: AstExpr::FunctionExpr(Box::new(func)),
            }));
        return true;
    }
    false
}

fn inline_nested_arg_local_table(stmt: &AstStmt, arg_locals: &mut [ConstructorArg]) -> bool {
    let Some((outer_binding, field, inner_binding)) = inlineable_nested_table_assign(stmt) else {
        return false;
    };
    let Some(inner_index) = arg_locals
        .iter()
        .position(|arg| arg.binding == inner_binding)
    else {
        return false;
    };
    let Some(outer_index) = arg_locals
        .iter()
        .position(|arg| arg.binding == outer_binding)
    else {
        return false;
    };
    if inner_index == outer_index || !arg_locals[inner_index].pass_to_sink {
        return false;
    }

    let inner_value = arg_locals[inner_index].value.clone();
    let AstExpr::TableConstructor(_) = inner_value else {
        return false;
    };
    let AstExpr::TableConstructor(table) = &mut arg_locals[outer_index].value else {
        return false;
    };

    // 这里专门收回“先建内层 methods table，再接到外层 metadata 字段”的机械接线。
    // 它只在内层 table 仍是独立 constructor local 时触发，不会把任意普通变量赋值猜成
    // 嵌套表字面量。
    table
        .fields
        .push(AstTableField::Record(crate::ast::AstRecordField {
            key: AstTableKey::Name(field),
            value: inner_value,
        }));
    arg_locals[inner_index].pass_to_sink = false;
    true
}

fn inlineable_nested_table_assign(
    stmt: &AstStmt,
) -> Option<(AstBindingRef, String, AstBindingRef)> {
    let AstStmt::Assign(assign) = stmt else {
        return None;
    };
    if assign.targets.len() != 1 || assign.values.len() != 1 {
        return None;
    }
    let AstLValue::FieldAccess(access) = &assign.targets[0] else {
        return None;
    };
    let AstExpr::Var(outer_name) = &access.base else {
        return None;
    };
    let AstExpr::Var(inner_name) = &assign.values[0] else {
        return None;
    };
    Some((
        binding_from_name(outer_name)?,
        access.field.clone(),
        binding_from_name(inner_name)?,
    ))
}

fn binding_from_name(name: &crate::ast::common::AstNameRef) -> Option<AstBindingRef> {
    match name {
        crate::ast::common::AstNameRef::Local(local) => Some(AstBindingRef::Local(*local)),
        crate::ast::common::AstNameRef::SyntheticLocal(local) => {
            Some(AstBindingRef::SyntheticLocal(*local))
        }
        crate::ast::common::AstNameRef::Temp(temp) => Some(AstBindingRef::Temp(*temp)),
        crate::ast::common::AstNameRef::Param(_)
        | crate::ast::common::AstNameRef::Upvalue(_)
        | crate::ast::common::AstNameRef::Global(_) => None,
    }
}

fn rewrite_terminal_constructor_call_sink(
    stmt: &AstStmt,
    callee_binding: AstBindingRef,
    callee_expr: &AstExpr,
    arg_locals: &[ConstructorArg],
) -> Option<AstStmt> {
    match stmt {
        AstStmt::Return(ret) => {
            let mut rewritten: AstReturn = ret.as_ref().clone();
            rewritten.values[0] = rewrite_terminal_constructor_call_expr(
                ret.values.first()?,
                callee_binding,
                callee_expr,
                arg_locals,
            )?;
            Some(AstStmt::Return(Box::new(rewritten)))
        }
        AstStmt::LocalDecl(local_decl) => {
            let mut rewritten: AstLocalDecl = local_decl.as_ref().clone();
            rewritten.values[0] = rewrite_terminal_constructor_call_expr(
                local_decl.values.first()?,
                callee_binding,
                callee_expr,
                arg_locals,
            )?;
            Some(AstStmt::LocalDecl(Box::new(rewritten)))
        }
        _ => None,
    }
}

fn rewrite_terminal_constructor_call_expr(
    expr: &AstExpr,
    callee_binding: AstBindingRef,
    callee_expr: &AstExpr,
    arg_locals: &[ConstructorArg],
) -> Option<AstExpr> {
    let AstExpr::Call(call) = expr else {
        return None;
    };
    let AstExpr::Var(name) = &call.callee else {
        return None;
    };
    let active_args = arg_locals
        .iter()
        .filter(|arg| arg.pass_to_sink)
        .collect::<Vec<_>>();
    if !name_matches_binding(name, callee_binding) || call.args.len() != active_args.len() {
        return None;
    }
    for (arg, expected) in call.args.iter().zip(active_args.iter()) {
        let AstExpr::Var(name) = arg else {
            return None;
        };
        if !name_matches_binding(name, expected.binding) {
            return None;
        }
    }

    let mut rewritten = call.as_ref().clone();
    rewritten.callee = callee_expr.clone();
    rewritten.args = active_args
        .into_iter()
        .map(|arg| arg.value.clone())
        .collect();
    Some(AstExpr::Call(Box::new(rewritten)))
}

fn removed_constructor_locals_are_dead_after_sink(
    tail: &[AstStmt],
    callee_binding: AstBindingRef,
    arg_locals: &[ConstructorArg],
) -> bool {
    if count_binding_uses_in_stmts_deep(tail, callee_binding) != 0 {
        return false;
    }
    arg_locals
        .iter()
        .all(|arg| count_binding_uses_in_stmts_deep(tail, arg.binding) == 0)
}
