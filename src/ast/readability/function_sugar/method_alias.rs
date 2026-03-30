//! 收回 method-call 的局部别名脚手架。
//!
//! 这个 pass 只处理 AST build 明确留下来的机械壳：
//! - `local f = obj.method; f(obj, 1)` -> `obj:method(1)`
//! - `local r = expr; local f = r.method; local x = f(r)` -> `local x = expr:method()`
//! - `local f = obj.method; local x = wrap(f(obj))` -> `local x = wrap(obj:method())`
//! - `local sign = obj.method(obj, 1) and "a" or "b"` -> `local sign = obj:method(1) and "a" or "b"`
//!
//! 它不会去猜更模糊的任意等价调用，也不会越权给 AST build 没表达清楚的 call 形状兜底。

use super::super::binding_flow::{count_binding_uses_in_stmts_deep, name_matches_binding};
use crate::ast::common::{
    AstBindingRef, AstCallExpr, AstCallKind, AstCallStmt, AstExpr, AstFieldAccess, AstGlobalDecl,
    AstIndexAccess, AstLocalAttr, AstLogicalExpr, AstMethodCallExpr, AstReturn, AstStmt,
    AstTableConstructor, AstTableField, AstTableKey, AstUnaryExpr,
};

pub(super) fn try_recover_method_alias_stmt(stmts: &[AstStmt]) -> Option<(AstStmt, usize)> {
    try_recover_with_receiver_alias(stmts)
        .or_else(|| try_recover_receiver_alias_direct_method_call(stmts))
        .or_else(|| try_recover_direct_receiver(stmts))
        .or_else(|| try_recover_direct_method_call_stmt(stmts))
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

fn try_recover_receiver_alias_direct_method_call(stmts: &[AstStmt]) -> Option<(AstStmt, usize)> {
    let [receiver_alias, sink, ..] = stmts else {
        return None;
    };
    let (receiver_binding, receiver_expr) = single_local_alias_decl(receiver_alias)?;
    if count_binding_uses_in_stmts_deep(&stmts[1..], receiver_binding) != 1 {
        return None;
    }

    Some((
        rewrite_single_value_sink_stmt(sink, |value| {
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
    rewrite_single_value_sink_stmt(stmt, |value| {
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
        | AstStmt::Return(_) => None,
    })
}

fn recover_method_call_expr(
    expr: &AstExpr,
    callee_binding: AstBindingRef,
    method: &str,
    receiver: &AstExpr,
    receiver_matches: &dyn Fn(&AstExpr) -> bool,
) -> Option<AstExpr> {
    rewrite_single_method_alias_use(expr, callee_binding, method, receiver, receiver_matches)
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

fn rewrite_single_method_alias_use(
    expr: &AstExpr,
    callee_binding: AstBindingRef,
    method: &str,
    receiver: &AstExpr,
    receiver_matches: &dyn Fn(&AstExpr) -> bool,
) -> Option<AstExpr> {
    match expr {
        AstExpr::Call(call) => {
            if let Some(method_call) = recover_method_call(
                call,
                callee_binding,
                method.to_owned(),
                receiver.clone(),
                receiver_matches,
            ) {
                return Some(AstExpr::MethodCall(Box::new(method_call)));
            }

            if let Some(callee) = rewrite_single_method_alias_use(
                &call.callee,
                callee_binding,
                method,
                receiver,
                receiver_matches,
            ) {
                return Some(AstExpr::Call(Box::new(AstCallExpr {
                    callee,
                    args: call.args.clone(),
                })));
            }

            for (index, arg) in call.args.iter().enumerate() {
                let Some(rewritten_arg) = rewrite_single_method_alias_use(
                    arg,
                    callee_binding,
                    method,
                    receiver,
                    receiver_matches,
                ) else {
                    continue;
                };
                let mut args = call.args.clone();
                args[index] = rewritten_arg;
                return Some(AstExpr::Call(Box::new(AstCallExpr {
                    callee: call.callee.clone(),
                    args,
                })));
            }

            None
        }
        AstExpr::MethodCall(call) => {
            if let Some(rewritten_receiver) = rewrite_single_method_alias_use(
                &call.receiver,
                callee_binding,
                method,
                receiver,
                receiver_matches,
            ) {
                return Some(AstExpr::MethodCall(Box::new(AstMethodCallExpr {
                    receiver: rewritten_receiver,
                    method: call.method.clone(),
                    args: call.args.clone(),
                })));
            }

            for (index, arg) in call.args.iter().enumerate() {
                let Some(rewritten_arg) = rewrite_single_method_alias_use(
                    arg,
                    callee_binding,
                    method,
                    receiver,
                    receiver_matches,
                ) else {
                    continue;
                };
                let mut args = call.args.clone();
                args[index] = rewritten_arg;
                return Some(AstExpr::MethodCall(Box::new(AstMethodCallExpr {
                    receiver: call.receiver.clone(),
                    method: call.method.clone(),
                    args,
                })));
            }

            None
        }
        AstExpr::Unary(unary) => Some(AstExpr::Unary(Box::new(AstUnaryExpr {
            op: unary.op,
            expr: rewrite_single_method_alias_use(
                &unary.expr,
                callee_binding,
                method,
                receiver,
                receiver_matches,
            )?,
        }))),
        AstExpr::Binary(binary) => rewrite_binary_like_expr(
            &binary.lhs,
            &binary.rhs,
            callee_binding,
            method,
            receiver,
            receiver_matches,
            |lhs, rhs| {
                AstExpr::Binary(Box::new(crate::ast::common::AstBinaryExpr {
                    op: binary.op,
                    lhs,
                    rhs,
                }))
            },
        ),
        AstExpr::LogicalAnd(logical) => rewrite_binary_like_expr(
            &logical.lhs,
            &logical.rhs,
            callee_binding,
            method,
            receiver,
            receiver_matches,
            |lhs, rhs| AstExpr::LogicalAnd(Box::new(AstLogicalExpr { lhs, rhs })),
        ),
        AstExpr::LogicalOr(logical) => rewrite_binary_like_expr(
            &logical.lhs,
            &logical.rhs,
            callee_binding,
            method,
            receiver,
            receiver_matches,
            |lhs, rhs| AstExpr::LogicalOr(Box::new(AstLogicalExpr { lhs, rhs })),
        ),
        AstExpr::FieldAccess(access) => Some(AstExpr::FieldAccess(Box::new(AstFieldAccess {
            base: rewrite_single_method_alias_use(
                &access.base,
                callee_binding,
                method,
                receiver,
                receiver_matches,
            )?,
            field: access.field.clone(),
        }))),
        AstExpr::IndexAccess(access) => {
            if let Some(base) = rewrite_single_method_alias_use(
                &access.base,
                callee_binding,
                method,
                receiver,
                receiver_matches,
            ) {
                return Some(AstExpr::IndexAccess(Box::new(AstIndexAccess {
                    base,
                    index: access.index.clone(),
                })));
            }
            Some(AstExpr::IndexAccess(Box::new(AstIndexAccess {
                base: access.base.clone(),
                index: rewrite_single_method_alias_use(
                    &access.index,
                    callee_binding,
                    method,
                    receiver,
                    receiver_matches,
                )?,
            })))
        }
        AstExpr::SingleValue(inner) => Some(AstExpr::SingleValue(Box::new(
            rewrite_single_method_alias_use(
                inner,
                callee_binding,
                method,
                receiver,
                receiver_matches,
            )?,
        ))),
        AstExpr::TableConstructor(table) => rewrite_table_constructor_expr(
            table,
            callee_binding,
            method,
            receiver,
            receiver_matches,
        ),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::VarArg
        | AstExpr::FunctionExpr(_) => None,
    }
}

fn rewrite_binary_like_expr(
    lhs: &AstExpr,
    rhs: &AstExpr,
    callee_binding: AstBindingRef,
    method: &str,
    receiver: &AstExpr,
    receiver_matches: &dyn Fn(&AstExpr) -> bool,
    make_expr: impl FnOnce(AstExpr, AstExpr) -> AstExpr,
) -> Option<AstExpr> {
    if let Some(rewritten_lhs) =
        rewrite_single_method_alias_use(lhs, callee_binding, method, receiver, receiver_matches)
    {
        return Some(make_expr(rewritten_lhs, rhs.clone()));
    }

    Some(make_expr(
        lhs.clone(),
        rewrite_single_method_alias_use(rhs, callee_binding, method, receiver, receiver_matches)?,
    ))
}

fn rewrite_table_constructor_expr(
    table: &AstTableConstructor,
    callee_binding: AstBindingRef,
    method: &str,
    receiver: &AstExpr,
    receiver_matches: &dyn Fn(&AstExpr) -> bool,
) -> Option<AstExpr> {
    table
        .fields
        .iter()
        .enumerate()
        .find_map(|(index, field)| match field {
            AstTableField::Array(value) => rewrite_single_method_alias_use(
                value,
                callee_binding,
                method,
                receiver,
                receiver_matches,
            )
            .map(|rewritten_value| {
                rebuild_table_with_field(table, index, AstTableField::Array(rewritten_value))
            }),
            AstTableField::Record(field) => {
                if let AstTableKey::Expr(key) = &field.key
                    && let Some(rewritten_key) = rewrite_single_method_alias_use(
                        key,
                        callee_binding,
                        method,
                        receiver,
                        receiver_matches,
                    )
                {
                    return Some(rebuild_table_with_field(
                        table,
                        index,
                        AstTableField::Record(crate::ast::common::AstRecordField {
                            key: AstTableKey::Expr(rewritten_key),
                            value: field.value.clone(),
                        }),
                    ));
                }

                rewrite_single_method_alias_use(
                    &field.value,
                    callee_binding,
                    method,
                    receiver,
                    receiver_matches,
                )
                .map(|rewritten_value| {
                    rebuild_table_with_field(
                        table,
                        index,
                        AstTableField::Record(crate::ast::common::AstRecordField {
                            key: field.key.clone(),
                            value: rewritten_value,
                        }),
                    )
                })
            }
        })
}

fn try_recover_direct_method_call_stmt(stmts: &[AstStmt]) -> Option<(AstStmt, usize)> {
    let [stmt, ..] = stmts else {
        return None;
    };
    Some((rewrite_direct_method_call_stmt(stmt)?, 1))
}

fn rewrite_direct_method_call_stmt(stmt: &AstStmt) -> Option<AstStmt> {
    rewrite_single_value_sink_stmt(stmt, rewrite_direct_method_call_expr_nested)
}

fn rewrite_direct_method_call_expr_nested(expr: &AstExpr) -> Option<AstExpr> {
    rewrite_method_call_expr_nested(expr, recover_direct_method_call_expr)
}

fn rewrite_method_call_expr_nested<F>(expr: &AstExpr, try_rewrite_here: F) -> Option<AstExpr>
where
    F: Fn(&AstExpr) -> Option<AstExpr> + Copy,
{
    if let Some(rewritten) = try_rewrite_here(expr) {
        return Some(rewritten);
    }

    match expr {
        AstExpr::Unary(unary) => Some(AstExpr::Unary(Box::new(AstUnaryExpr {
            op: unary.op,
            expr: rewrite_method_call_expr_nested(&unary.expr, try_rewrite_here)?,
        }))),
        AstExpr::Binary(binary) => {
            let lhs =
                rewrite_method_call_expr_nested(&binary.lhs, try_rewrite_here).unwrap_or(binary.lhs.clone());
            let rhs =
                rewrite_method_call_expr_nested(&binary.rhs, try_rewrite_here).unwrap_or(binary.rhs.clone());
            if lhs == binary.lhs && rhs == binary.rhs {
                None
            } else {
                Some(AstExpr::Binary(Box::new(
                    crate::ast::common::AstBinaryExpr {
                        op: binary.op,
                        lhs,
                        rhs,
                    },
                )))
            }
        }
        AstExpr::LogicalAnd(logical) => {
            let lhs = rewrite_method_call_expr_nested(&logical.lhs, try_rewrite_here)
                .unwrap_or(logical.lhs.clone());
            let rhs = rewrite_method_call_expr_nested(&logical.rhs, try_rewrite_here)
                .unwrap_or(logical.rhs.clone());
            if lhs == logical.lhs && rhs == logical.rhs {
                None
            } else {
                Some(AstExpr::LogicalAnd(Box::new(AstLogicalExpr { lhs, rhs })))
            }
        }
        AstExpr::LogicalOr(logical) => {
            let lhs = rewrite_method_call_expr_nested(&logical.lhs, try_rewrite_here)
                .unwrap_or(logical.lhs.clone());
            let rhs = rewrite_method_call_expr_nested(&logical.rhs, try_rewrite_here)
                .unwrap_or(logical.rhs.clone());
            if lhs == logical.lhs && rhs == logical.rhs {
                None
            } else {
                Some(AstExpr::LogicalOr(Box::new(AstLogicalExpr { lhs, rhs })))
            }
        }
        AstExpr::Call(call) => {
            if let Some(callee) = rewrite_method_call_expr_nested(&call.callee, try_rewrite_here) {
                return Some(AstExpr::Call(Box::new(AstCallExpr {
                    callee,
                    args: call.args.clone(),
                })));
            }
            for (index, arg) in call.args.iter().enumerate() {
                let Some(rewritten_arg) = rewrite_method_call_expr_nested(arg, try_rewrite_here) else {
                    continue;
                };
                let mut args = call.args.clone();
                args[index] = rewritten_arg;
                return Some(AstExpr::Call(Box::new(AstCallExpr {
                    callee: call.callee.clone(),
                    args,
                })));
            }
            None
        }
        AstExpr::MethodCall(call) => {
            if let Some(receiver) = rewrite_method_call_expr_nested(&call.receiver, try_rewrite_here)
            {
                return Some(AstExpr::MethodCall(Box::new(AstMethodCallExpr {
                    receiver,
                    method: call.method.clone(),
                    args: call.args.clone(),
                })));
            }
            for (index, arg) in call.args.iter().enumerate() {
                let Some(rewritten_arg) = rewrite_method_call_expr_nested(arg, try_rewrite_here) else {
                    continue;
                };
                let mut args = call.args.clone();
                args[index] = rewritten_arg;
                return Some(AstExpr::MethodCall(Box::new(AstMethodCallExpr {
                    receiver: call.receiver.clone(),
                    method: call.method.clone(),
                    args,
                })));
            }
            None
        }
        AstExpr::FieldAccess(access) => Some(AstExpr::FieldAccess(Box::new(AstFieldAccess {
            base: rewrite_method_call_expr_nested(&access.base, try_rewrite_here)?,
            field: access.field.clone(),
        }))),
        AstExpr::IndexAccess(access) => {
            if let Some(base) = rewrite_method_call_expr_nested(&access.base, try_rewrite_here) {
                return Some(AstExpr::IndexAccess(Box::new(AstIndexAccess {
                    base,
                    index: access.index.clone(),
                })));
            }
            Some(AstExpr::IndexAccess(Box::new(AstIndexAccess {
                base: access.base.clone(),
                index: rewrite_method_call_expr_nested(&access.index, try_rewrite_here)?,
            })))
        }
        AstExpr::SingleValue(inner) => Some(AstExpr::SingleValue(Box::new(
            rewrite_method_call_expr_nested(inner, try_rewrite_here)?,
        ))),
        AstExpr::TableConstructor(table) => {
            table
                .fields
                .iter()
                .enumerate()
                .find_map(|(index, field)| match field {
                    AstTableField::Array(value) => rewrite_method_call_expr_nested(value, try_rewrite_here)
                        .map(|rewritten_value| {
                            rebuild_table_with_field(
                                table,
                                index,
                                AstTableField::Array(rewritten_value),
                            )
                        }),
                    AstTableField::Record(field) => {
                        if let AstTableKey::Expr(key) = &field.key
                            && let Some(rewritten_key) =
                                rewrite_method_call_expr_nested(key, try_rewrite_here)
                        {
                            return Some(rebuild_table_with_field(
                                table,
                                index,
                                AstTableField::Record(crate::ast::common::AstRecordField {
                                    key: AstTableKey::Expr(rewritten_key),
                                    value: field.value.clone(),
                                }),
                            ));
                        }
                        rewrite_method_call_expr_nested(&field.value, try_rewrite_here).map(
                            |rewritten_value| {
                                rebuild_table_with_field(
                                    table,
                                    index,
                                    AstTableField::Record(crate::ast::common::AstRecordField {
                                        key: field.key.clone(),
                                        value: rewritten_value,
                                    }),
                                )
                            },
                        )
                    }
                })
        }
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::VarArg
        | AstExpr::FunctionExpr(_) => None,
    }
}

fn recover_direct_method_call_expr(expr: &AstExpr) -> Option<AstExpr> {
    let AstExpr::Call(call) = expr else {
        return None;
    };
    let AstExpr::FieldAccess(access) = &call.callee else {
        return None;
    };
    let AstExpr::Var(receiver_name) = &access.base else {
        return None;
    };
    let [receiver_arg, args @ ..] = call.args.as_slice() else {
        return None;
    };
    let AstExpr::Var(receiver_arg_name) = receiver_arg else {
        return None;
    };
    if receiver_arg_name != receiver_name {
        return None;
    }

    Some(AstExpr::MethodCall(Box::new(AstMethodCallExpr {
        receiver: access.base.clone(),
        method: access.field.clone(),
        args: args.to_vec(),
    })))
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

fn rewrite_single_value_sink_stmt(
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
        AstStmt::CallStmt(_)
        | AstStmt::If(_)
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

fn rebuild_table_with_field(
    table: &AstTableConstructor,
    index: usize,
    rewritten_field: AstTableField,
) -> AstExpr {
    let mut fields = table.fields.clone();
    fields[index] = rewritten_field;
    AstExpr::TableConstructor(Box::new(AstTableConstructor { fields }))
}
