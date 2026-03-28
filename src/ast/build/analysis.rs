//! AST build：局部分析和小型统计 helper。

use std::collections::BTreeSet;

use crate::hir::{
    HirBlock, HirCallExpr, HirDecisionTarget, HirExpr, HirLValue, HirModule, HirStmt,
    HirTableField, HirTableKey, LocalId, TempId,
};

pub(super) fn max_hir_label_id(module: &HirModule) -> usize {
    module
        .protos
        .iter()
        .map(|proto| max_hir_label_id_in_block(&proto.body))
        .max()
        .unwrap_or(0)
}

fn max_hir_label_id_in_block(block: &HirBlock) -> usize {
    block
        .stmts
        .iter()
        .map(|stmt| match stmt {
            HirStmt::If(if_stmt) => {
                let then_max = max_hir_label_id_in_block(&if_stmt.then_block);
                let else_max = if_stmt
                    .else_block
                    .as_ref()
                    .map(max_hir_label_id_in_block)
                    .unwrap_or(0);
                then_max.max(else_max)
            }
            HirStmt::While(while_stmt) => max_hir_label_id_in_block(&while_stmt.body),
            HirStmt::Repeat(repeat_stmt) => max_hir_label_id_in_block(&repeat_stmt.body),
            HirStmt::NumericFor(numeric_for) => max_hir_label_id_in_block(&numeric_for.body),
            HirStmt::GenericFor(generic_for) => max_hir_label_id_in_block(&generic_for.body),
            HirStmt::Block(block) => max_hir_label_id_in_block(block),
            HirStmt::Unstructured(unstructured) => max_hir_label_id_in_block(&unstructured.body),
            HirStmt::Goto(goto_stmt) => goto_stmt.target.index(),
            HirStmt::Label(label) => label.id.index(),
            _ => 0,
        })
        .max()
        .unwrap_or(0)
}

pub(super) fn collect_close_temps(block: &HirBlock) -> BTreeSet<TempId> {
    let mut temps = BTreeSet::new();
    collect_close_temps_in_block(block, &mut temps);
    temps
}

pub(super) fn collect_referenced_temps(block: &HirBlock) -> BTreeSet<TempId> {
    let mut temps = BTreeSet::new();
    collect_referenced_temps_in_block(block, &mut temps);
    temps
}

fn collect_referenced_temps_in_block(block: &HirBlock, temps: &mut BTreeSet<TempId>) {
    for stmt in &block.stmts {
        collect_referenced_temps_in_stmt(stmt, temps);
    }
}

fn collect_referenced_temps_in_stmt(stmt: &HirStmt, temps: &mut BTreeSet<TempId>) {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_referenced_temps_in_expr(value, temps);
            }
        }
        HirStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_referenced_temps_in_lvalue(target, temps);
            }
            for value in &assign.values {
                collect_referenced_temps_in_expr(value, temps);
            }
        }
        HirStmt::TableSetList(set_list) => {
            collect_referenced_temps_in_expr(&set_list.base, temps);
            for value in &set_list.values {
                collect_referenced_temps_in_expr(value, temps);
            }
            if let Some(value) = &set_list.trailing_multivalue {
                collect_referenced_temps_in_expr(value, temps);
            }
        }
        HirStmt::ErrNil(err_nnil) => collect_referenced_temps_in_expr(&err_nnil.value, temps),
        HirStmt::ToBeClosed(to_be_closed) => {
            collect_referenced_temps_in_expr(&to_be_closed.value, temps);
        }
        HirStmt::Close(_) => {}
        HirStmt::CallStmt(call_stmt) => collect_referenced_temps_in_call(&call_stmt.call, temps),
        HirStmt::Return(ret) => {
            for value in &ret.values {
                collect_referenced_temps_in_expr(value, temps);
            }
        }
        HirStmt::If(if_stmt) => {
            collect_referenced_temps_in_expr(&if_stmt.cond, temps);
            collect_referenced_temps_in_block(&if_stmt.then_block, temps);
            if let Some(else_block) = &if_stmt.else_block {
                collect_referenced_temps_in_block(else_block, temps);
            }
        }
        HirStmt::While(while_stmt) => {
            collect_referenced_temps_in_expr(&while_stmt.cond, temps);
            collect_referenced_temps_in_block(&while_stmt.body, temps);
        }
        HirStmt::Repeat(repeat_stmt) => {
            collect_referenced_temps_in_block(&repeat_stmt.body, temps);
            collect_referenced_temps_in_expr(&repeat_stmt.cond, temps);
        }
        HirStmt::NumericFor(numeric_for) => {
            collect_referenced_temps_in_expr(&numeric_for.start, temps);
            collect_referenced_temps_in_expr(&numeric_for.limit, temps);
            collect_referenced_temps_in_expr(&numeric_for.step, temps);
            collect_referenced_temps_in_block(&numeric_for.body, temps);
        }
        HirStmt::GenericFor(generic_for) => {
            for expr in &generic_for.iterator {
                collect_referenced_temps_in_expr(expr, temps);
            }
            collect_referenced_temps_in_block(&generic_for.body, temps);
        }
        HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_) | HirStmt::Label(_) => {}
        HirStmt::Block(block) => collect_referenced_temps_in_block(block, temps),
        HirStmt::Unstructured(unstructured) => {
            collect_referenced_temps_in_block(&unstructured.body, temps)
        }
    }
}

fn collect_referenced_temps_in_lvalue(target: &HirLValue, temps: &mut BTreeSet<TempId>) {
    match target {
        HirLValue::Temp(temp) => {
            temps.insert(*temp);
        }
        HirLValue::TableAccess(access) => {
            collect_referenced_temps_in_expr(&access.base, temps);
            collect_referenced_temps_in_expr(&access.key, temps);
        }
        HirLValue::Local(_) | HirLValue::Upvalue(_) | HirLValue::Global(_) => {}
    }
}

fn collect_referenced_temps_in_call(call: &HirCallExpr, temps: &mut BTreeSet<TempId>) {
    collect_referenced_temps_in_expr(&call.callee, temps);
    for arg in &call.args {
        collect_referenced_temps_in_expr(arg, temps);
    }
}

fn collect_referenced_temps_in_expr(expr: &HirExpr, temps: &mut BTreeSet<TempId>) {
    match expr {
        HirExpr::TempRef(temp) => {
            temps.insert(*temp);
        }
        HirExpr::TableAccess(access) => {
            collect_referenced_temps_in_expr(&access.base, temps);
            collect_referenced_temps_in_expr(&access.key, temps);
        }
        HirExpr::Unary(unary) => collect_referenced_temps_in_expr(&unary.expr, temps),
        HirExpr::Binary(binary) => {
            collect_referenced_temps_in_expr(&binary.lhs, temps);
            collect_referenced_temps_in_expr(&binary.rhs, temps);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_referenced_temps_in_expr(&logical.lhs, temps);
            collect_referenced_temps_in_expr(&logical.rhs, temps);
        }
        HirExpr::Decision(decision) => {
            for node in &decision.nodes {
                collect_referenced_temps_in_expr(&node.test, temps);
                collect_referenced_temps_in_target(&node.truthy, temps);
                collect_referenced_temps_in_target(&node.falsy, temps);
            }
        }
        HirExpr::Call(call) => collect_referenced_temps_in_call(call, temps),
        HirExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    HirTableField::Array(value) => collect_referenced_temps_in_expr(value, temps),
                    HirTableField::Record(record) => {
                        if let HirTableKey::Expr(expr) = &record.key {
                            collect_referenced_temps_in_expr(expr, temps);
                        }
                        collect_referenced_temps_in_expr(&record.value, temps);
                    }
                }
            }
            if let Some(value) = &table.trailing_multivalue {
                collect_referenced_temps_in_expr(value, temps);
            }
        }
        HirExpr::Closure(closure) => {
            for capture in &closure.captures {
                collect_referenced_temps_in_expr(&capture.value, temps);
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
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => {}
    }
}

fn collect_referenced_temps_in_target(target: &HirDecisionTarget, temps: &mut BTreeSet<TempId>) {
    if let HirDecisionTarget::Expr(expr) = target {
        collect_referenced_temps_in_expr(expr, temps);
    }
}

fn collect_close_temps_in_block(block: &HirBlock, temps: &mut BTreeSet<TempId>) {
    for stmt in &block.stmts {
        match stmt {
            HirStmt::ToBeClosed(to_be_closed) => {
                if let HirExpr::TempRef(temp) = &to_be_closed.value {
                    temps.insert(*temp);
                }
            }
            HirStmt::If(if_stmt) => {
                collect_close_temps_in_block(&if_stmt.then_block, temps);
                if let Some(else_block) = &if_stmt.else_block {
                    collect_close_temps_in_block(else_block, temps);
                }
            }
            HirStmt::While(while_stmt) => collect_close_temps_in_block(&while_stmt.body, temps),
            HirStmt::Repeat(repeat_stmt) => collect_close_temps_in_block(&repeat_stmt.body, temps),
            HirStmt::NumericFor(numeric_for) => {
                collect_close_temps_in_block(&numeric_for.body, temps)
            }
            HirStmt::GenericFor(generic_for) => {
                collect_close_temps_in_block(&generic_for.body, temps)
            }
            HirStmt::Block(block) => collect_close_temps_in_block(block, temps),
            HirStmt::Unstructured(unstructured) => {
                collect_close_temps_in_block(&unstructured.body, temps)
            }
            _ => {}
        }
    }
}

pub(super) fn block_has_continue(block: &HirBlock) -> bool {
    block.stmts.iter().any(stmt_has_continue)
}

fn stmt_has_continue(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::Continue => true,
        HirStmt::If(if_stmt) => {
            block_has_continue(&if_stmt.then_block)
                || if_stmt.else_block.as_ref().is_some_and(block_has_continue)
        }
        HirStmt::While(while_stmt) => block_has_continue(&while_stmt.body),
        HirStmt::Repeat(repeat_stmt) => block_has_continue(&repeat_stmt.body),
        HirStmt::NumericFor(numeric_for) => block_has_continue(&numeric_for.body),
        HirStmt::GenericFor(generic_for) => block_has_continue(&generic_for.body),
        HirStmt::Block(block) => block_has_continue(block),
        HirStmt::Unstructured(unstructured) => block_has_continue(&unstructured.body),
        _ => false,
    }
}

pub(super) fn count_local_uses_in_stmts(stmts: &[HirStmt], local: LocalId) -> usize {
    stmts
        .iter()
        .map(|stmt| count_local_uses_in_stmt(stmt, local))
        .sum()
}

fn count_local_uses_in_stmt(stmt: &HirStmt, local: LocalId) -> usize {
    match stmt {
        HirStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .map(|value| count_local_uses_in_expr(value, local))
            .sum(),
        HirStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .map(|target| count_local_uses_in_lvalue(target, local))
                .sum::<usize>()
                + assign
                    .values
                    .iter()
                    .map(|value| count_local_uses_in_expr(value, local))
                    .sum::<usize>()
        }
        HirStmt::TableSetList(set_list) => {
            count_local_uses_in_expr(&set_list.base, local)
                + set_list
                    .values
                    .iter()
                    .map(|value| count_local_uses_in_expr(value, local))
                    .sum::<usize>()
                + set_list
                    .trailing_multivalue
                    .as_ref()
                    .map(|value| count_local_uses_in_expr(value, local))
                    .unwrap_or(0)
        }
        HirStmt::ErrNil(err_nnil) => count_local_uses_in_expr(&err_nnil.value, local),
        HirStmt::ToBeClosed(to_be_closed) => count_local_uses_in_expr(&to_be_closed.value, local),
        HirStmt::Close(_) => 0,
        HirStmt::CallStmt(call_stmt) => count_local_uses_in_call(&call_stmt.call, local),
        HirStmt::Return(ret) => ret
            .values
            .iter()
            .map(|value| count_local_uses_in_expr(value, local))
            .sum(),
        HirStmt::If(if_stmt) => {
            count_local_uses_in_expr(&if_stmt.cond, local)
                + count_local_uses_in_block(&if_stmt.then_block, local)
                + if_stmt
                    .else_block
                    .as_ref()
                    .map(|else_block| count_local_uses_in_block(else_block, local))
                    .unwrap_or(0)
        }
        HirStmt::While(while_stmt) => {
            count_local_uses_in_expr(&while_stmt.cond, local)
                + count_local_uses_in_block(&while_stmt.body, local)
        }
        HirStmt::Repeat(repeat_stmt) => {
            count_local_uses_in_block(&repeat_stmt.body, local)
                + count_local_uses_in_expr(&repeat_stmt.cond, local)
        }
        HirStmt::NumericFor(numeric_for) => {
            count_local_uses_in_expr(&numeric_for.start, local)
                + count_local_uses_in_expr(&numeric_for.limit, local)
                + count_local_uses_in_expr(&numeric_for.step, local)
                + count_local_uses_in_block(&numeric_for.body, local)
        }
        HirStmt::GenericFor(generic_for) => {
            generic_for
                .iterator
                .iter()
                .map(|expr| count_local_uses_in_expr(expr, local))
                .sum::<usize>()
                + count_local_uses_in_block(&generic_for.body, local)
        }
        HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_) | HirStmt::Label(_) => 0,
        HirStmt::Block(block) => count_local_uses_in_block(block, local),
        HirStmt::Unstructured(unstructured) => count_local_uses_in_block(&unstructured.body, local),
    }
}

fn count_local_uses_in_block(block: &HirBlock, local: LocalId) -> usize {
    block
        .stmts
        .iter()
        .map(|stmt| count_local_uses_in_stmt(stmt, local))
        .sum()
}

fn count_local_uses_in_lvalue(target: &HirLValue, local: LocalId) -> usize {
    match target {
        HirLValue::TableAccess(access) => {
            count_local_uses_in_expr(&access.base, local)
                + count_local_uses_in_expr(&access.key, local)
        }
        HirLValue::Local(target_local) if *target_local == local => 1,
        _ => 0,
    }
}

pub(super) fn count_local_uses_in_call(call: &HirCallExpr, local: LocalId) -> usize {
    count_local_uses_in_expr(&call.callee, local)
        + call
            .args
            .iter()
            .map(|arg| count_local_uses_in_expr(arg, local))
            .sum::<usize>()
}

fn count_local_uses_in_expr(expr: &HirExpr, local: LocalId) -> usize {
    match expr {
        HirExpr::LocalRef(expr_local) if *expr_local == local => 1,
        HirExpr::TableAccess(access) => {
            count_local_uses_in_expr(&access.base, local)
                + count_local_uses_in_expr(&access.key, local)
        }
        HirExpr::Unary(unary) => count_local_uses_in_expr(&unary.expr, local),
        HirExpr::Binary(binary) => {
            count_local_uses_in_expr(&binary.lhs, local)
                + count_local_uses_in_expr(&binary.rhs, local)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            count_local_uses_in_expr(&logical.lhs, local)
                + count_local_uses_in_expr(&logical.rhs, local)
        }
        HirExpr::Decision(decision) => decision
            .nodes
            .iter()
            .map(|node| {
                count_local_uses_in_expr(&node.test, local)
                    + count_local_uses_in_target(&node.truthy, local)
                    + count_local_uses_in_target(&node.falsy, local)
            })
            .sum(),
        HirExpr::Call(call) => count_local_uses_in_call(call, local),
        HirExpr::TableConstructor(table) => table
            .fields
            .iter()
            .map(|field| match field {
                HirTableField::Array(expr) => count_local_uses_in_expr(expr, local),
                HirTableField::Record(record) => match &record.key {
                    HirTableKey::Name(_) => count_local_uses_in_expr(&record.value, local),
                    HirTableKey::Expr(expr) => {
                        count_local_uses_in_expr(expr, local)
                            + count_local_uses_in_expr(&record.value, local)
                    }
                },
            })
            .sum(),
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .map(|capture| count_local_uses_in_expr(&capture.value, local))
            .sum(),
        _ => 0,
    }
}

fn count_local_uses_in_target(target: &HirDecisionTarget, local: LocalId) -> usize {
    match target {
        HirDecisionTarget::Expr(expr) => count_local_uses_in_expr(expr, local),
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => 0,
    }
}
