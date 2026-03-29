//! 这个子模块负责 table-constructor pass 里的 binding 识别与字段键翻译。
//!
//! 它依赖 HIR 已经分好的 lvalue/expr 形状，只回答“这个读写是不是同一个构造器绑定”，
//! 不会在这里扫描 region 或重建字段序列。
//! 例如：`t.x = v` 会在这里把键翻成 `Name(\"x\")` 并识别 `t` 的绑定身份。

use std::collections::BTreeSet;

use crate::hir::common::{
    HirCallExpr, HirDecisionTarget, HirExpr, HirLValue, HirStmt, HirTableField, HirTableKey,
};

use super::TableBinding;

pub(super) fn binding_from_lvalue(lvalue: &HirLValue) -> Option<TableBinding> {
    match lvalue {
        HirLValue::Temp(temp) => Some(TableBinding::Temp(*temp)),
        HirLValue::Local(local) => Some(TableBinding::Local(*local)),
        HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => None,
    }
}

pub(super) fn binding_from_expr(expr: &HirExpr) -> Option<TableBinding> {
    match expr {
        HirExpr::TempRef(temp) => Some(TableBinding::Temp(*temp)),
        HirExpr::LocalRef(local) => Some(TableBinding::Local(*local)),
        _ => None,
    }
}

pub(super) fn matches_binding_ref(expr: &HirExpr, binding: TableBinding) -> bool {
    binding_from_expr(expr) == Some(binding)
}

pub(super) fn table_key_from_expr(expr: &HirExpr) -> HirTableKey {
    if let HirExpr::String(name) = expr
        && is_identifier_name(name)
    {
        return HirTableKey::Name(name.clone());
    }
    HirTableKey::Expr(expr.clone())
}

pub(super) fn collect_stmt_slice_bindings(stmts: &[HirStmt]) -> BTreeSet<TableBinding> {
    let mut bindings = BTreeSet::new();
    for stmt in stmts {
        collect_stmt_bindings(stmt, &mut bindings);
    }
    bindings
}

pub(super) fn expr_depends_on_any_binding(expr: &HirExpr, bindings: &[TableBinding]) -> bool {
    bindings
        .iter()
        .any(|binding| expr_uses_binding(expr, *binding))
}

pub(super) fn expr_uses_binding(expr: &HirExpr, binding: TableBinding) -> bool {
    if matches_binding_ref(expr, binding) {
        return true;
    }

    match expr {
        HirExpr::TableAccess(access) => {
            expr_uses_binding(&access.base, binding) || expr_uses_binding(&access.key, binding)
        }
        HirExpr::Unary(unary) => expr_uses_binding(&unary.expr, binding),
        HirExpr::Binary(binary) => {
            expr_uses_binding(&binary.lhs, binding) || expr_uses_binding(&binary.rhs, binding)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_uses_binding(&logical.lhs, binding) || expr_uses_binding(&logical.rhs, binding)
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_uses_binding(&node.test, binding)
                || decision_target_uses_binding(&node.truthy, binding)
                || decision_target_uses_binding(&node.falsy, binding)
        }),
        HirExpr::Call(call) => call_expr_uses_binding(call, binding),
        HirExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                HirTableField::Array(expr) => expr_uses_binding(expr, binding),
                HirTableField::Record(field) => {
                    table_key_uses_binding(&field.key, binding)
                        || expr_uses_binding(&field.value, binding)
                }
            }) || table
                .trailing_multivalue
                .as_ref()
                .is_some_and(|expr| expr_uses_binding(expr, binding))
        }
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_uses_binding(&capture.value, binding)),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
        HirExpr::TempRef(_) | HirExpr::LocalRef(_) => false,
    }
}

fn is_identifier_name(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

fn collect_stmt_bindings(stmt: &HirStmt, bindings: &mut BTreeSet<TableBinding>) {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_expr_bindings(value, bindings);
            }
        }
        HirStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_lvalue_bindings(target, bindings);
            }
            for value in &assign.values {
                collect_expr_bindings(value, bindings);
            }
        }
        HirStmt::TableSetList(set_list) => {
            collect_expr_bindings(&set_list.base, bindings);
            for value in &set_list.values {
                collect_expr_bindings(value, bindings);
            }
            if let Some(trailing) = &set_list.trailing_multivalue {
                collect_expr_bindings(trailing, bindings);
            }
        }
        HirStmt::ErrNil(err_nil) => collect_expr_bindings(&err_nil.value, bindings),
        HirStmt::ToBeClosed(to_be_closed) => collect_expr_bindings(&to_be_closed.value, bindings),
        HirStmt::CallStmt(call_stmt) => collect_call_bindings(&call_stmt.call, bindings),
        HirStmt::Return(ret) => {
            for value in &ret.values {
                collect_expr_bindings(value, bindings);
            }
        }
        HirStmt::If(if_stmt) => {
            collect_expr_bindings(&if_stmt.cond, bindings);
            collect_stmt_slice_bindings_into(&if_stmt.then_block.stmts, bindings);
            if let Some(else_block) = &if_stmt.else_block {
                collect_stmt_slice_bindings_into(&else_block.stmts, bindings);
            }
        }
        HirStmt::While(while_stmt) => {
            collect_expr_bindings(&while_stmt.cond, bindings);
            collect_stmt_slice_bindings_into(&while_stmt.body.stmts, bindings);
        }
        HirStmt::Repeat(repeat_stmt) => {
            collect_stmt_slice_bindings_into(&repeat_stmt.body.stmts, bindings);
            collect_expr_bindings(&repeat_stmt.cond, bindings);
        }
        HirStmt::NumericFor(numeric_for) => {
            collect_expr_bindings(&numeric_for.start, bindings);
            collect_expr_bindings(&numeric_for.limit, bindings);
            collect_expr_bindings(&numeric_for.step, bindings);
            collect_stmt_slice_bindings_into(&numeric_for.body.stmts, bindings);
        }
        HirStmt::GenericFor(generic_for) => {
            for value in &generic_for.iterator {
                collect_expr_bindings(value, bindings);
            }
            collect_stmt_slice_bindings_into(&generic_for.body.stmts, bindings);
        }
        HirStmt::Block(block) => collect_stmt_slice_bindings_into(&block.stmts, bindings),
        HirStmt::Unstructured(unstructured) => {
            collect_stmt_slice_bindings_into(&unstructured.body.stmts, bindings);
        }
        HirStmt::Break
        | HirStmt::Close(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
    }
}

fn collect_stmt_slice_bindings_into(stmts: &[HirStmt], bindings: &mut BTreeSet<TableBinding>) {
    for stmt in stmts {
        collect_stmt_bindings(stmt, bindings);
    }
}

fn collect_lvalue_bindings(lvalue: &HirLValue, bindings: &mut BTreeSet<TableBinding>) {
    match lvalue {
        HirLValue::Temp(temp) => {
            bindings.insert(TableBinding::Temp(*temp));
        }
        HirLValue::Local(local) => {
            bindings.insert(TableBinding::Local(*local));
        }
        HirLValue::TableAccess(access) => {
            collect_expr_bindings(&access.base, bindings);
            collect_expr_bindings(&access.key, bindings);
        }
        HirLValue::Upvalue(_) | HirLValue::Global(_) => {}
    }
}

fn collect_call_bindings(call: &HirCallExpr, bindings: &mut BTreeSet<TableBinding>) {
    collect_expr_bindings(&call.callee, bindings);
    for arg in &call.args {
        collect_expr_bindings(arg, bindings);
    }
}

fn collect_expr_bindings(expr: &HirExpr, bindings: &mut BTreeSet<TableBinding>) {
    if let Some(binding) = binding_from_expr(expr) {
        bindings.insert(binding);
        return;
    }

    match expr {
        HirExpr::TableAccess(access) => {
            collect_expr_bindings(&access.base, bindings);
            collect_expr_bindings(&access.key, bindings);
        }
        HirExpr::Unary(unary) => collect_expr_bindings(&unary.expr, bindings),
        HirExpr::Binary(binary) => {
            collect_expr_bindings(&binary.lhs, bindings);
            collect_expr_bindings(&binary.rhs, bindings);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_expr_bindings(&logical.lhs, bindings);
            collect_expr_bindings(&logical.rhs, bindings);
        }
        HirExpr::Decision(decision) => {
            for node in &decision.nodes {
                collect_expr_bindings(&node.test, bindings);
                collect_decision_target_bindings(&node.truthy, bindings);
                collect_decision_target_bindings(&node.falsy, bindings);
            }
        }
        HirExpr::Call(call) => collect_call_bindings(call, bindings),
        HirExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    HirTableField::Array(expr) => collect_expr_bindings(expr, bindings),
                    HirTableField::Record(field) => {
                        collect_table_key_bindings(&field.key, bindings);
                        collect_expr_bindings(&field.value, bindings);
                    }
                }
            }
            if let Some(trailing) = &table.trailing_multivalue {
                collect_expr_bindings(trailing, bindings);
            }
        }
        HirExpr::Closure(closure) => {
            for capture in &closure.captures {
                collect_expr_bindings(&capture.value, bindings);
            }
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_)
        | HirExpr::LocalRef(_)
        | HirExpr::TempRef(_) => {}
    }
}

fn collect_decision_target_bindings(
    target: &HirDecisionTarget,
    bindings: &mut BTreeSet<TableBinding>,
) {
    match target {
        HirDecisionTarget::Expr(expr) => collect_expr_bindings(expr, bindings),
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => {}
    }
}

fn collect_table_key_bindings(key: &HirTableKey, bindings: &mut BTreeSet<TableBinding>) {
    if let HirTableKey::Expr(expr) = key {
        collect_expr_bindings(expr, bindings);
    }
}

fn call_expr_uses_binding(call: &HirCallExpr, binding: TableBinding) -> bool {
    expr_uses_binding(&call.callee, binding)
        || call.args.iter().any(|arg| expr_uses_binding(arg, binding))
}

fn decision_target_uses_binding(target: &HirDecisionTarget, binding: TableBinding) -> bool {
    match target {
        HirDecisionTarget::Expr(expr) => expr_uses_binding(expr, binding),
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => false,
    }
}

fn table_key_uses_binding(key: &HirTableKey, binding: TableBinding) -> bool {
    match key {
        HirTableKey::Name(_) => false,
        HirTableKey::Expr(expr) => expr_uses_binding(expr, binding),
    }
}
