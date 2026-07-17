//! 收回 method-call 的局部别名脚手架。
//!
//! 这个 pass 只处理 AST build 明确留下来的机械壳：
//! - `local r = expr; local f = r.method; local x = f(r)` -> `local x = expr:method()`
//! - `local r = expr; local f = r.method; local x = wrap(f(r))` 在外层前缀稳定时收回嵌套调用
//! - `local r = expr; local x = r.method(r)` -> `local x = expr:method()`
//!
//! 普通 `obj.method(obj)` 不足以证明 method call：字段查询可能通过 `__index` 改写
//! `obj`，而冒号调用只会求值一次 receiver。没有独立 receiver 快照的形状必须保留。
//! alias 原本只求值一次，因此也不能搬入 while/repeat，或越过外层调用、左侧操作数、
//! 复杂赋值目标等可观察前缀。

use super::super::binding_flow::{BindingUseIndex, MutableSnapshotNames};
use super::super::binding_ref::name_matches_binding;
use super::super::expr_analysis::{expr_requires_ordered_snapshot, is_context_safe_expr};
use crate::ast::common::{
    AstBindingRef, AstCallExpr, AstCallKind, AstCallStmt, AstExpr, AstGlobalDecl, AstIf,
    AstLocalAttr, AstMethodCallExpr, AstReturn, AstStmt,
};

pub(super) fn try_recover_method_alias_stmt(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    stmt_base: usize,
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<(AstStmt, usize)> {
    try_recover_with_receiver_alias(stmts, use_index, stmt_base, mutable_snapshots).or_else(|| {
        try_recover_receiver_alias_direct_method_call(
            stmts,
            use_index,
            stmt_base,
            mutable_snapshots,
        )
    })
}

pub(in crate::ast::readability) fn run_belongs_to_method_alias_owner(
    stmts: &[AstStmt],
    index: usize,
    sink_index: usize,
    use_index: &BindingUseIndex,
    mutable_snapshots: &MutableSnapshotNames,
) -> bool {
    let Some(sink) = stmts.get(sink_index) else {
        return false;
    };
    if matches!(sink, AstStmt::GenericFor(_)) {
        return false;
    }
    let run = &stmts[index..];
    match sink_index.checked_sub(index) {
        Some(1) => {
            try_recover_receiver_alias_direct_method_call(run, use_index, index, mutable_snapshots)
                .is_some()
        }
        Some(2) => {
            try_recover_with_receiver_alias(run, use_index, index, mutable_snapshots).is_some()
        }
        _ => false,
    }
}

fn try_recover_with_receiver_alias(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    stmt_base: usize,
    mutable_snapshots: &MutableSnapshotNames,
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
            mutable_snapshots,
            |arg| matches!(arg, AstExpr::Var(name) if name_matches_binding(name, receiver_binding)),
        )?,
        3,
    ))
}

fn try_recover_receiver_alias_direct_method_call(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    stmt_base: usize,
    mutable_snapshots: &MutableSnapshotNames,
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
            rewrite_method_call_expr_in_order(value, mutable_snapshots, |expr| {
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
    mutable_snapshots: &MutableSnapshotNames,
    receiver_matches: impl Fn(&AstExpr) -> bool,
) -> Option<AstStmt> {
    rewrite_single_expr_sink_stmt(stmt, |value| {
        recover_method_call_expr(
            value,
            callee_binding,
            &method,
            &receiver,
            mutable_snapshots,
            &receiver_matches,
        )
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
    mutable_snapshots: &MutableSnapshotNames,
    receiver_matches: &dyn Fn(&AstExpr) -> bool,
) -> Option<AstExpr> {
    rewrite_method_call_expr_in_order(expr, mutable_snapshots, |expr| {
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

fn rewrite_method_call_expr_in_order<F>(
    expr: &AstExpr,
    mutable_snapshots: &MutableSnapshotNames,
    try_rewrite_here: F,
) -> Option<AstExpr>
where
    F: Fn(&AstExpr) -> Option<AstExpr> + Copy,
{
    if let Some(rewritten) = try_rewrite_here(expr) {
        return Some(rewritten);
    }

    let mut rewritten = expr.clone();
    match &mut rewritten {
        AstExpr::Unary(unary) => {
            unary.expr = rewrite_method_call_expr_in_order(
                &unary.expr,
                mutable_snapshots,
                try_rewrite_here,
            )?;
            Some(rewritten)
        }
        AstExpr::Binary(binary) => {
            if let Some(lhs) =
                rewrite_method_call_expr_in_order(&binary.lhs, mutable_snapshots, try_rewrite_here)
            {
                binary.lhs = lhs;
                return Some(rewritten);
            }
            if !expr_prefix_is_stable(&binary.lhs, mutable_snapshots) {
                return None;
            }
            binary.rhs = rewrite_method_call_expr_in_order(
                &binary.rhs,
                mutable_snapshots,
                try_rewrite_here,
            )?;
            Some(rewritten)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            logical.lhs = rewrite_method_call_expr_in_order(
                &logical.lhs,
                mutable_snapshots,
                try_rewrite_here,
            )?;
            Some(rewritten)
        }
        AstExpr::Call(call) => {
            if let Some(callee) =
                rewrite_method_call_expr_in_order(&call.callee, mutable_snapshots, try_rewrite_here)
            {
                call.callee = callee;
                return Some(rewritten);
            }
            if !expr_prefix_is_stable(&call.callee, mutable_snapshots) {
                return None;
            }
            for arg in &mut call.args {
                if let Some(value) =
                    rewrite_method_call_expr_in_order(arg, mutable_snapshots, try_rewrite_here)
                {
                    *arg = value;
                    return Some(rewritten);
                }
                if !expr_prefix_is_stable(arg, mutable_snapshots) {
                    return None;
                }
            }
            None
        }
        AstExpr::MethodCall(call) => {
            call.receiver = rewrite_method_call_expr_in_order(
                &call.receiver,
                mutable_snapshots,
                try_rewrite_here,
            )?;
            Some(rewritten)
        }
        AstExpr::FieldAccess(access) => {
            access.base = rewrite_method_call_expr_in_order(
                &access.base,
                mutable_snapshots,
                try_rewrite_here,
            )?;
            Some(rewritten)
        }
        AstExpr::IndexAccess(access) => {
            if let Some(base) =
                rewrite_method_call_expr_in_order(&access.base, mutable_snapshots, try_rewrite_here)
            {
                access.base = base;
                return Some(rewritten);
            }
            if !expr_prefix_is_stable(&access.base, mutable_snapshots) {
                return None;
            }
            access.index = rewrite_method_call_expr_in_order(
                &access.index,
                mutable_snapshots,
                try_rewrite_here,
            )?;
            Some(rewritten)
        }
        AstExpr::SingleValue(inner) => {
            **inner =
                rewrite_method_call_expr_in_order(inner, mutable_snapshots, try_rewrite_here)?;
            Some(rewritten)
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
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_)
        | AstExpr::Error(_) => None,
    }
}

fn expr_prefix_is_stable(expr: &AstExpr, mutable_snapshots: &MutableSnapshotNames) -> bool {
    !expr_requires_ordered_snapshot(expr, mutable_snapshots)
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
            if assign
                .targets
                .iter()
                .any(|target| !matches!(target, crate::ast::common::AstLValue::Name(_)))
            {
                return None;
            }
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
        AstStmt::CallStmt(_)
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
        | AstStmt::Error(_) => None,
    }
}
