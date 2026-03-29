//! 这个子模块负责把“构造器尾部立刻安装方法”的模式收成更自然的函数 sugar。
//!
//! 它依赖 method field 收集和前缀 local alias 证据，只吸收终端构造器调用链，不会在这里
//! 重写一般赋值语句。
//! 例如：先建表再给字段塞函数、最后立刻调用的模式，会在这里折成更紧凑的写法。

use std::collections::BTreeSet;

use super::super::binding_flow::name_matches_binding;
use crate::ast::common::{
    AstBindingRef, AstExpr, AstFunctionDecl, AstFunctionExpr, AstFunctionName, AstLocalAttr,
    AstStmt, AstTableField, AstTableKey,
};

pub(super) fn try_inline_terminal_constructor_call(
    stmts: &[AstStmt],
    method_fields: &BTreeSet<String>,
) -> Option<(AstStmt, usize)> {
    let (callee_binding, callee_expr) = single_local_alias_decl(stmts.first()?)?;
    let mut consumed = 1usize;
    let mut arg_locals = Vec::<(AstBindingRef, AstExpr)>::new();

    while let Some(stmt) = stmts.get(consumed) {
        let Some((binding, value)) = single_local_alias_decl(stmt) else {
            break;
        };
        arg_locals.push((binding, value.clone()));
        consumed += 1;
    }
    if arg_locals.is_empty() {
        return None;
    }

    while let Some(stmt) = stmts.get(consumed) {
        let AstStmt::FunctionDecl(function_decl) = stmt else {
            break;
        };
        let Some((binding, field, func)) =
            inlineable_table_function_field(function_decl, method_fields)
        else {
            break;
        };
        let (_, table_expr) = arg_locals.iter_mut().find(|(id, _)| *id == binding)?;
        let AstExpr::TableConstructor(table) = table_expr else {
            return None;
        };
        table
            .fields
            .push(AstTableField::Record(crate::ast::common::AstRecordField {
                key: AstTableKey::Name(field),
                value: AstExpr::FunctionExpr(Box::new(func)),
            }));
        consumed += 1;
    }

    let AstStmt::Return(ret) = stmts.get(consumed)? else {
        return None;
    };
    let [AstExpr::Call(call)] = ret.values.as_slice() else {
        return None;
    };
    let AstExpr::Var(name) = &call.callee else {
        return None;
    };
    if !name_matches_binding(name, callee_binding) || call.args.len() != arg_locals.len() {
        return None;
    }
    for (arg, (binding, _)) in call.args.iter().zip(arg_locals.iter()) {
        let AstExpr::Var(name) = arg else {
            return None;
        };
        if !name_matches_binding(name, *binding) {
            return None;
        }
    }

    let mut lowered_return = ret.as_ref().clone();
    let AstExpr::Call(lowered_call) = &mut lowered_return.values[0] else {
        unreachable!("matched above")
    };
    lowered_call.callee = callee_expr.clone();
    lowered_call.args = arg_locals
        .into_iter()
        .map(|(_, value)| value)
        .collect::<Vec<_>>();
    Some((AstStmt::Return(Box::new(lowered_return)), consumed + 1))
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

fn inlineable_table_function_field(
    function_decl: &AstFunctionDecl,
    method_fields: &BTreeSet<String>,
) -> Option<(AstBindingRef, String, AstFunctionExpr)> {
    let AstFunctionName::Plain(path) = &function_decl.target else {
        return None;
    };
    if path.fields.len() != 1 || method_fields.contains(&path.fields[0]) {
        return None;
    }
    let binding = match &path.root {
        crate::ast::common::AstNameRef::Local(local) => AstBindingRef::Local(*local),
        crate::ast::common::AstNameRef::SyntheticLocal(local) => {
            AstBindingRef::SyntheticLocal(*local)
        }
        crate::ast::common::AstNameRef::Temp(temp) => AstBindingRef::Temp(*temp),
        crate::ast::common::AstNameRef::Param(_)
        | crate::ast::common::AstNameRef::Upvalue(_)
        | crate::ast::common::AstNameRef::Global(_) => return None,
    };
    Some((binding, path.fields[0].clone(), function_decl.func.clone()))
}
