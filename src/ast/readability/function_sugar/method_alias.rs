//! 收回 method-call 的局部别名脚手架。
//!
//! 这个 pass 只处理 AST build 明确留下来的机械壳：
//! - `local f = obj.method; f(obj, 1)` -> `obj:method(1)`
//! - `local r = expr; local f = r.method; local x = f(r)` -> `local x = expr:method()`
//!
//! 它不会去猜更模糊的任意等价调用，也不会越权给 AST build 没表达清楚的 call 形状兜底。

use super::super::binding_flow::{count_binding_uses_in_stmts_deep, name_matches_binding};
use crate::ast::common::{
    AstBindingRef, AstCallExpr, AstCallKind, AstCallStmt, AstExpr, AstGlobalDecl, AstLocalAttr,
    AstMethodCallExpr, AstReturn, AstStmt,
};

pub(super) fn try_recover_method_alias_stmt(stmts: &[AstStmt]) -> Option<(AstStmt, usize)> {
    try_recover_with_receiver_alias(stmts).or_else(|| try_recover_direct_receiver(stmts))
}

fn try_recover_with_receiver_alias(stmts: &[AstStmt]) -> Option<(AstStmt, usize)> {
    let [receiver_alias, field_alias, sink, ..] = stmts else {
        return None;
    };
    let (receiver_binding, receiver_expr) = single_local_alias_decl(receiver_alias)?;
    let (field_binding, field_access) = single_field_alias_decl(field_alias)?;
    let AstExpr::Var(receiver_name) = &field_access.base else {
        return None;
    };
    if !name_matches_binding(receiver_name, receiver_binding) {
        return None;
    }
    if count_binding_uses_in_stmts_deep(&stmts[1..], receiver_binding) != 2
        || count_binding_uses_in_stmts_deep(&stmts[2..], field_binding) != 1
    {
        return None;
    }

    Some((
        recover_method_call_sink(
            sink,
            field_binding,
            field_access.field.clone(),
            receiver_expr.clone(),
            |arg| matches!(arg, AstExpr::Var(name) if name_matches_binding(name, receiver_binding)),
        )?,
        3,
    ))
}

fn try_recover_direct_receiver(stmts: &[AstStmt]) -> Option<(AstStmt, usize)> {
    let [field_alias, sink, ..] = stmts else {
        return None;
    };
    let (field_binding, field_access) = single_field_alias_decl(field_alias)?;
    let AstExpr::Var(receiver_name) = &field_access.base else {
        return None;
    };
    if count_binding_uses_in_stmts_deep(&stmts[1..], field_binding) != 1 {
        return None;
    }

    Some((
        recover_method_call_sink(
            sink,
            field_binding,
            field_access.field.clone(),
            field_access.base.clone(),
            |arg| matches!(arg, AstExpr::Var(name) if name == receiver_name),
        )?,
        2,
    ))
}

fn single_local_alias_decl(stmt: &AstStmt) -> Option<(AstBindingRef, &AstExpr)> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    if local_decl.bindings.len() != 1
        || local_decl.values.len() != 1
        || local_decl.bindings[0].attr != AstLocalAttr::None
    {
        return None;
    }
    Some((local_decl.bindings[0].id, &local_decl.values[0]))
}

fn single_field_alias_decl(
    stmt: &AstStmt,
) -> Option<(AstBindingRef, &crate::ast::common::AstFieldAccess)> {
    let (binding, value) = single_local_alias_decl(stmt)?;
    let AstExpr::FieldAccess(access) = value else {
        return None;
    };
    Some((binding, access))
}

fn recover_method_call_sink(
    stmt: &AstStmt,
    callee_binding: AstBindingRef,
    method: String,
    receiver: AstExpr,
    receiver_matches: impl Fn(&AstExpr) -> bool,
) -> Option<AstStmt> {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            let [value] = local_decl.values.as_slice() else {
                return None;
            };
            let mut rewritten = (**local_decl).clone();
            rewritten.values[0] = recover_method_call_expr(
                value,
                callee_binding,
                &method,
                &receiver,
                receiver_matches,
            )?;
            Some(AstStmt::LocalDecl(Box::new(rewritten)))
        }
        AstStmt::GlobalDecl(global_decl) => {
            let [value] = global_decl.values.as_slice() else {
                return None;
            };
            let mut rewritten: AstGlobalDecl = (**global_decl).clone();
            rewritten.values[0] = recover_method_call_expr(
                value,
                callee_binding,
                &method,
                &receiver,
                receiver_matches,
            )?;
            Some(AstStmt::GlobalDecl(Box::new(rewritten)))
        }
        AstStmt::Assign(assign) => {
            let [value] = assign.values.as_slice() else {
                return None;
            };
            let mut rewritten = (**assign).clone();
            rewritten.values[0] = recover_method_call_expr(
                value,
                callee_binding,
                &method,
                &receiver,
                receiver_matches,
            )?;
            Some(AstStmt::Assign(Box::new(rewritten)))
        }
        AstStmt::Return(ret) => {
            let [value] = ret.values.as_slice() else {
                return None;
            };
            let mut rewritten: AstReturn = (**ret).clone();
            rewritten.values[0] = recover_method_call_expr(
                value,
                callee_binding,
                &method,
                &receiver,
                receiver_matches,
            )?;
            Some(AstStmt::Return(Box::new(rewritten)))
        }
        AstStmt::CallStmt(call_stmt) => {
            let AstCallKind::Call(call) = &call_stmt.call else {
                return None;
            };
            Some(AstStmt::CallStmt(Box::new(AstCallStmt {
                call: AstCallKind::MethodCall(Box::new(recover_method_call(
                    call,
                    callee_binding,
                    method,
                    receiver,
                    receiver_matches,
                )?)),
            })))
        }
        AstStmt::If(_)
        | AstStmt::While(_)
        | AstStmt::Repeat(_)
        | AstStmt::NumericFor(_)
        | AstStmt::GenericFor(_)
        | AstStmt::DoBlock(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_) => None,
    }
}

fn recover_method_call_expr(
    expr: &AstExpr,
    callee_binding: AstBindingRef,
    method: &str,
    receiver: &AstExpr,
    receiver_matches: impl Fn(&AstExpr) -> bool,
) -> Option<AstExpr> {
    let AstExpr::Call(call) = expr else {
        return None;
    };
    Some(AstExpr::MethodCall(Box::new(recover_method_call(
        call,
        callee_binding,
        method.to_owned(),
        receiver.clone(),
        receiver_matches,
    )?)))
}

fn recover_method_call(
    call: &AstCallExpr,
    callee_binding: AstBindingRef,
    method: String,
    receiver: AstExpr,
    receiver_matches: impl Fn(&AstExpr) -> bool,
) -> Option<AstMethodCallExpr> {
    let AstExpr::Var(callee_name) = &call.callee else {
        return None;
    };
    if !name_matches_binding(callee_name, callee_binding) {
        return None;
    }
    let [receiver_arg, args @ ..] = call.args.as_slice() else {
        return None;
    };
    if !receiver_matches(receiver_arg) {
        return None;
    }
    Some(AstMethodCallExpr {
        receiver,
        method,
        args: args.to_vec(),
    })
}
