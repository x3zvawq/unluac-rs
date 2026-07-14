//! 收回 method-call 的局部别名脚手架。
//!
//! 这个 pass 只处理 AST build 明确留下来的机械壳：
//! - `local r = expr; local f = r.method; local x = f(r)` -> `local x = expr:method()`
//! - `local r = expr; local f = r.method; local x = wrap(f(r))` -> `local x = wrap(expr:method())`
//! - `local r = expr; local x = r.method(r)` -> `local x = expr:method()`
//!
//! 普通 `obj.method(obj)` 不足以证明 method call：字段查询可能通过 `__index` 改写
//! `obj`，而冒号调用只会求值一次 receiver。没有独立 receiver 快照的形状必须保留。

use super::super::binding_flow::BindingUseIndex;
use super::super::binding_ref::name_matches_binding;
use super::super::expr_analysis::is_context_safe_expr;
use crate::ast::common::{
    AstBindingRef, AstCallExpr, AstCallKind, AstCallStmt, AstExpr, AstFieldAccess, AstGlobalDecl,
    AstIf, AstIndexAccess, AstLocalAttr, AstLogicalExpr, AstMethodCallExpr, AstRepeat, AstReturn,
    AstStmt, AstTableConstructor, AstTableField, AstTableKey, AstUnaryExpr, AstWhile,
};

pub(super) fn try_recover_method_alias_stmt(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    stmt_base: usize,
) -> Option<(AstStmt, usize)> {
    try_recover_with_receiver_alias(stmts, use_index, stmt_base)
        .or_else(|| try_recover_receiver_alias_direct_method_call(stmts, use_index, stmt_base))
}

pub(in crate::ast::readability) fn run_belongs_to_method_alias_owner(
    stmts: &[AstStmt],
    index: usize,
    sink_index: usize,
    use_index: &BindingUseIndex,
) -> bool {
    let Some(sink) = stmts.get(sink_index) else {
        return false;
    };
    if matches!(sink, AstStmt::GenericFor(_)) {
        return false;
    }
    let run = &stmts[index..];
    match sink_index.checked_sub(index) {
        Some(1) => try_recover_receiver_alias_direct_method_call(run, use_index, index).is_some(),
        Some(2) => try_recover_with_receiver_alias(run, use_index, index).is_some(),
        _ => false,
    }
}

fn try_recover_with_receiver_alias(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    stmt_base: usize,
) -> Option<(AstStmt, usize)> {
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
    if use_index.count_uses_in_suffix(stmt_base + 1, receiver_binding) != 2
        || use_index.count_uses_in_suffix(stmt_base + 2, field_binding) != 1
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

fn try_recover_receiver_alias_direct_method_call(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    stmt_base: usize,
) -> Option<(AstStmt, usize)> {
    let [receiver_alias, sink, ..] = stmts else {
        return None;
    };
    let (receiver_binding, receiver_expr) = single_local_alias_decl(receiver_alias)?;
    if use_index.count_uses_in_suffix(stmt_base + 1, receiver_binding) != 1 {
        return None;
    }
    if !is_context_safe_expr(receiver_expr) {
        return None;
    }

    Some((
        rewrite_single_expr_sink_stmt(sink, |value| {
            rewrite_method_call_expr_nested(value, |expr| {
                recover_direct_method_call_with_receiver_alias_expr(
                    expr,
                    receiver_binding,
                    receiver_expr,
                )
            })
        })?,
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
    rewrite_single_expr_sink_stmt(stmt, |value| {
        recover_method_call_expr(value, callee_binding, &method, &receiver, &receiver_matches)
    })
    .or_else(|| match stmt {
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
        | AstStmt::Label(_)
        | AstStmt::LocalDecl(_)
        | AstStmt::GlobalDecl(_)
        | AstStmt::Assign(_)
        | AstStmt::Return(_)
        | AstStmt::Error(_) => None,
    })
}

fn recover_method_call_expr(
    expr: &AstExpr,
    callee_binding: AstBindingRef,
    method: &str,
    receiver: &AstExpr,
    receiver_matches: &dyn Fn(&AstExpr) -> bool,
) -> Option<AstExpr> {
    rewrite_method_call_expr_nested(expr, |expr| {
        if let AstExpr::Call(call) = expr
            && let Some(method_call) = recover_method_call(
                call,
                callee_binding,
                method.to_owned(),
                receiver.clone(),
                receiver_matches,
            )
        {
            return Some(AstExpr::MethodCall(Box::new(method_call)));
        }

        None
    })
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

fn rewrite_method_call_expr_nested<F>(expr: &AstExpr, try_rewrite_here: F) -> Option<AstExpr>
where
    F: Fn(&AstExpr) -> Option<AstExpr> + Copy,
{
    if let Some(rewritten) = try_rewrite_here(expr) {
        return Some(rewritten);
    }

    match expr {
        AstExpr::Unary(unary) => {
            let (expr, changed) = rewrite_child_expr(&unary.expr, try_rewrite_here);
            changed.then_some(AstExpr::Unary(Box::new(AstUnaryExpr {
                op: unary.op,
                expr,
            })))
        }
        AstExpr::Binary(binary) => {
            let (lhs, lhs_changed) = rewrite_child_expr(&binary.lhs, try_rewrite_here);
            let (rhs, rhs_changed) = rewrite_child_expr(&binary.rhs, try_rewrite_here);
            (lhs_changed || rhs_changed).then_some(AstExpr::Binary(Box::new(
                crate::ast::common::AstBinaryExpr {
                    op: binary.op,
                    lhs,
                    rhs,
                },
            )))
        }
        AstExpr::LogicalAnd(logical) => {
            let (lhs, lhs_changed) = rewrite_child_expr(&logical.lhs, try_rewrite_here);
            let (rhs, rhs_changed) = rewrite_child_expr(&logical.rhs, try_rewrite_here);
            (lhs_changed || rhs_changed)
                .then_some(AstExpr::LogicalAnd(Box::new(AstLogicalExpr { lhs, rhs })))
        }
        AstExpr::LogicalOr(logical) => {
            let (lhs, lhs_changed) = rewrite_child_expr(&logical.lhs, try_rewrite_here);
            let (rhs, rhs_changed) = rewrite_child_expr(&logical.rhs, try_rewrite_here);
            (lhs_changed || rhs_changed)
                .then_some(AstExpr::LogicalOr(Box::new(AstLogicalExpr { lhs, rhs })))
        }
        AstExpr::Call(call) => {
            let (callee, callee_changed) = rewrite_child_expr(&call.callee, try_rewrite_here);
            let (args, args_changed) = rewrite_child_exprs(&call.args, try_rewrite_here);
            (callee_changed || args_changed)
                .then_some(AstExpr::Call(Box::new(AstCallExpr { callee, args })))
        }
        AstExpr::MethodCall(call) => {
            let (receiver, receiver_changed) = rewrite_child_expr(&call.receiver, try_rewrite_here);
            let (args, args_changed) = rewrite_child_exprs(&call.args, try_rewrite_here);
            (receiver_changed || args_changed).then_some(AstExpr::MethodCall(Box::new(
                AstMethodCallExpr {
                    receiver,
                    method: call.method.clone(),
                    args,
                },
            )))
        }
        AstExpr::FieldAccess(access) => {
            let (base, changed) = rewrite_child_expr(&access.base, try_rewrite_here);
            changed.then_some(AstExpr::FieldAccess(Box::new(AstFieldAccess {
                base,
                field: access.field.clone(),
            })))
        }
        AstExpr::IndexAccess(access) => {
            let (base, base_changed) = rewrite_child_expr(&access.base, try_rewrite_here);
            let (index, index_changed) = rewrite_child_expr(&access.index, try_rewrite_here);
            (base_changed || index_changed).then_some(AstExpr::IndexAccess(Box::new(
                AstIndexAccess { base, index },
            )))
        }
        AstExpr::SingleValue(inner) => {
            let (expr, changed) = rewrite_child_expr(inner, try_rewrite_here);
            changed.then_some(AstExpr::SingleValue(Box::new(expr)))
        }
        AstExpr::TableConstructor(table) => {
            let mut changed = false;
            let fields = table
                .fields
                .iter()
                .map(|field| {
                    let (rewritten, field_changed) = rewrite_table_field(field, try_rewrite_here);
                    changed |= field_changed;
                    rewritten
                })
                .collect::<Vec<_>>();
            changed.then_some(AstExpr::TableConstructor(Box::new(AstTableConstructor {
                fields,
            })))
        }
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::VarArg
        | AstExpr::FunctionExpr(_)
        | AstExpr::Error(_) => None,
    }
}

fn rewrite_child_expr<F>(expr: &AstExpr, try_rewrite_here: F) -> (AstExpr, bool)
where
    F: Fn(&AstExpr) -> Option<AstExpr> + Copy,
{
    match rewrite_method_call_expr_nested(expr, try_rewrite_here) {
        Some(rewritten) => (rewritten, true),
        None => (expr.clone(), false),
    }
}

fn rewrite_child_exprs<F>(exprs: &[AstExpr], try_rewrite_here: F) -> (Vec<AstExpr>, bool)
where
    F: Fn(&AstExpr) -> Option<AstExpr> + Copy,
{
    let mut changed = false;
    let rewritten = exprs
        .iter()
        .map(|expr| {
            let (rewritten, expr_changed) = rewrite_child_expr(expr, try_rewrite_here);
            changed |= expr_changed;
            rewritten
        })
        .collect();
    (rewritten, changed)
}

fn rewrite_table_field<F>(field: &AstTableField, try_rewrite_here: F) -> (AstTableField, bool)
where
    F: Fn(&AstExpr) -> Option<AstExpr> + Copy,
{
    match field {
        AstTableField::Array(value) => {
            let (value, changed) = rewrite_child_expr(value, try_rewrite_here);
            (AstTableField::Array(value), changed)
        }
        AstTableField::Record(field) => {
            let (key, key_changed) = match &field.key {
                AstTableKey::Expr(key) => {
                    let (key, changed) = rewrite_child_expr(key, try_rewrite_here);
                    (AstTableKey::Expr(key), changed)
                }
                AstTableKey::Name(name) => (AstTableKey::Name(name.clone()), false),
            };
            let (value, value_changed) = rewrite_child_expr(&field.value, try_rewrite_here);
            (
                AstTableField::Record(crate::ast::common::AstRecordField { key, value }),
                key_changed || value_changed,
            )
        }
    }
}

fn recover_direct_method_call_with_receiver_alias_expr(
    expr: &AstExpr,
    receiver_binding: AstBindingRef,
    receiver_expr: &AstExpr,
) -> Option<AstExpr> {
    let AstExpr::Call(call) = expr else {
        return None;
    };
    let AstExpr::FieldAccess(access) = &call.callee else {
        return None;
    };
    if &access.base != receiver_expr {
        return None;
    }
    let [receiver_arg, args @ ..] = call.args.as_slice() else {
        return None;
    };
    let AstExpr::Var(receiver_arg_name) = receiver_arg else {
        return None;
    };
    if !name_matches_binding(receiver_arg_name, receiver_binding) {
        return None;
    }

    Some(AstExpr::MethodCall(Box::new(AstMethodCallExpr {
        receiver: receiver_expr.clone(),
        method: access.field.clone(),
        args: args.to_vec(),
    })))
}

fn rewrite_single_expr_sink_stmt(
    stmt: &AstStmt,
    mut rewrite_expr: impl FnMut(&AstExpr) -> Option<AstExpr>,
) -> Option<AstStmt> {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            let [value] = local_decl.values.as_slice() else {
                return None;
            };
            let mut rewritten = (**local_decl).clone();
            rewritten.values[0] = rewrite_expr(value)?;
            Some(AstStmt::LocalDecl(Box::new(rewritten)))
        }
        AstStmt::GlobalDecl(global_decl) => {
            let [value] = global_decl.values.as_slice() else {
                return None;
            };
            let mut rewritten: AstGlobalDecl = (**global_decl).clone();
            rewritten.values[0] = rewrite_expr(value)?;
            Some(AstStmt::GlobalDecl(Box::new(rewritten)))
        }
        AstStmt::Assign(assign) => {
            let [value] = assign.values.as_slice() else {
                return None;
            };
            let mut rewritten = (**assign).clone();
            rewritten.values[0] = rewrite_expr(value)?;
            Some(AstStmt::Assign(Box::new(rewritten)))
        }
        AstStmt::Return(ret) => {
            let [value] = ret.values.as_slice() else {
                return None;
            };
            let mut rewritten: AstReturn = (**ret).clone();
            rewritten.values[0] = rewrite_expr(value)?;
            Some(AstStmt::Return(Box::new(rewritten)))
        }
        AstStmt::If(if_stmt) => Some(AstStmt::If(Box::new(AstIf {
            cond: rewrite_expr(&if_stmt.cond)?,
            then_block: if_stmt.then_block.clone(),
            else_block: if_stmt.else_block.clone(),
        }))),
        AstStmt::While(while_stmt) => Some(AstStmt::While(Box::new(AstWhile {
            cond: rewrite_expr(&while_stmt.cond)?,
            body: while_stmt.body.clone(),
        }))),
        AstStmt::Repeat(repeat_stmt) => Some(AstStmt::Repeat(Box::new(AstRepeat {
            body: repeat_stmt.body.clone(),
            cond: rewrite_expr(&repeat_stmt.cond)?,
        }))),
        AstStmt::CallStmt(_)
        | AstStmt::NumericFor(_)
        | AstStmt::GenericFor(_)
        | AstStmt::DoBlock(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => None,
    }
}
