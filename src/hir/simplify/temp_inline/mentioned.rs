//! 这个子模块负责 temp-inline pass 里的“已提及 temp”保护集。
//!
//! 它依赖 HIR 语句树当前形状，只回答进入嵌套循环/分支前哪些 temp 不能继续往里内联，
//! 不会在这里真正执行替换。
//! 例如：前缀语句和循环体都提到同一个 temp 时，这里会把它列入保护集。

use super::*;

pub(super) fn protected_temps_for_nested_stmt(
    stmts: &[HirStmt],
    stmt_index: usize,
    inherited: &BTreeSet<TempId>,
) -> BTreeSet<TempId> {
    let mut protected = inherited.clone();
    let Some(stmt) = stmts.get(stmt_index) else {
        return protected;
    };
    if !matches!(
        stmt,
        HirStmt::While(_) | HirStmt::Repeat(_) | HirStmt::NumericFor(_) | HirStmt::GenericFor(_)
    ) {
        return protected;
    }

    let prefix_temps = mentioned_temp_set_for_stmt_slice(&stmts[..stmt_index]);
    if prefix_temps.is_empty() {
        return protected;
    }

    let nested_temps = mentioned_temp_set_for_stmt(stmt);
    protected.extend(prefix_temps.intersection(&nested_temps).copied());
    protected
}

fn mentioned_temp_set_for_stmt_slice(stmts: &[HirStmt]) -> BTreeSet<TempId> {
    let mut temps = BTreeSet::new();
    for stmt in stmts {
        collect_stmt_mentioned_temps(stmt, &mut temps);
    }
    temps
}

fn mentioned_temp_set_for_stmt(stmt: &HirStmt) -> BTreeSet<TempId> {
    let mut temps = BTreeSet::new();
    collect_stmt_mentioned_temps(stmt, &mut temps);
    temps
}

fn collect_stmt_mentioned_temps(stmt: &HirStmt, temps: &mut BTreeSet<TempId>) {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_expr_mentioned_temps(value, temps);
            }
        }
        HirStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_lvalue_mentioned_temps(target, temps);
            }
            for value in &assign.values {
                collect_expr_mentioned_temps(value, temps);
            }
        }
        HirStmt::TableSetList(set_list) => {
            collect_expr_mentioned_temps(&set_list.base, temps);
            for value in &set_list.values {
                collect_expr_mentioned_temps(value, temps);
            }
            if let Some(trailing) = &set_list.trailing_multivalue {
                collect_expr_mentioned_temps(trailing, temps);
            }
        }
        HirStmt::ErrNil(err_nil) => collect_expr_mentioned_temps(&err_nil.value, temps),
        HirStmt::ToBeClosed(to_be_closed) => {
            collect_expr_mentioned_temps(&to_be_closed.value, temps);
        }
        HirStmt::CallStmt(call_stmt) => collect_call_mentioned_temps(&call_stmt.call, temps),
        HirStmt::Return(ret) => {
            for value in &ret.values {
                collect_expr_mentioned_temps(value, temps);
            }
        }
        HirStmt::If(if_stmt) => {
            collect_expr_mentioned_temps(&if_stmt.cond, temps);
            collect_block_mentioned_temps(&if_stmt.then_block, temps);
            if let Some(else_block) = &if_stmt.else_block {
                collect_block_mentioned_temps(else_block, temps);
            }
        }
        HirStmt::While(while_stmt) => {
            collect_expr_mentioned_temps(&while_stmt.cond, temps);
            collect_block_mentioned_temps(&while_stmt.body, temps);
        }
        HirStmt::Repeat(repeat_stmt) => {
            collect_block_mentioned_temps(&repeat_stmt.body, temps);
            collect_expr_mentioned_temps(&repeat_stmt.cond, temps);
        }
        HirStmt::NumericFor(numeric_for) => {
            collect_expr_mentioned_temps(&numeric_for.start, temps);
            collect_expr_mentioned_temps(&numeric_for.limit, temps);
            collect_expr_mentioned_temps(&numeric_for.step, temps);
            collect_block_mentioned_temps(&numeric_for.body, temps);
        }
        HirStmt::GenericFor(generic_for) => {
            for value in &generic_for.iterator {
                collect_expr_mentioned_temps(value, temps);
            }
            collect_block_mentioned_temps(&generic_for.body, temps);
        }
        HirStmt::Block(block) => collect_block_mentioned_temps(block, temps),
        HirStmt::Unstructured(unstructured) => {
            collect_block_mentioned_temps(&unstructured.body, temps)
        }
        HirStmt::Break
        | HirStmt::Close(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
    }
}

fn collect_block_mentioned_temps(block: &HirBlock, temps: &mut BTreeSet<TempId>) {
    for stmt in &block.stmts {
        collect_stmt_mentioned_temps(stmt, temps);
    }
}

fn collect_call_mentioned_temps(call: &HirCallExpr, temps: &mut BTreeSet<TempId>) {
    collect_expr_mentioned_temps(&call.callee, temps);
    for arg in &call.args {
        collect_expr_mentioned_temps(arg, temps);
    }
}

fn collect_lvalue_mentioned_temps(lvalue: &HirLValue, temps: &mut BTreeSet<TempId>) {
    match lvalue {
        HirLValue::Temp(temp) => {
            temps.insert(*temp);
        }
        HirLValue::TableAccess(access) => {
            collect_expr_mentioned_temps(&access.base, temps);
            collect_expr_mentioned_temps(&access.key, temps);
        }
        HirLValue::Local(_) | HirLValue::Upvalue(_) | HirLValue::Global(_) => {}
    }
}

pub(super) fn collect_expr_mentioned_temps(expr: &HirExpr, temps: &mut BTreeSet<TempId>) {
    match expr {
        HirExpr::TempRef(temp) => {
            temps.insert(*temp);
        }
        HirExpr::TableAccess(access) => {
            collect_expr_mentioned_temps(&access.base, temps);
            collect_expr_mentioned_temps(&access.key, temps);
        }
        HirExpr::Unary(unary) => collect_expr_mentioned_temps(&unary.expr, temps),
        HirExpr::Binary(binary) => {
            collect_expr_mentioned_temps(&binary.lhs, temps);
            collect_expr_mentioned_temps(&binary.rhs, temps);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_expr_mentioned_temps(&logical.lhs, temps);
            collect_expr_mentioned_temps(&logical.rhs, temps);
        }
        HirExpr::Decision(decision) => {
            for node in &decision.nodes {
                collect_expr_mentioned_temps(&node.test, temps);
                collect_decision_target_mentioned_temps(&node.truthy, temps);
                collect_decision_target_mentioned_temps(&node.falsy, temps);
            }
        }
        HirExpr::Call(call) => collect_call_mentioned_temps(call, temps),
        HirExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    HirTableField::Array(value) => collect_expr_mentioned_temps(value, temps),
                    HirTableField::Record(field) => {
                        if let HirTableKey::Expr(key) = &field.key {
                            collect_expr_mentioned_temps(key, temps);
                        }
                        collect_expr_mentioned_temps(&field.value, temps);
                    }
                }
            }
            if let Some(trailing) = &table.trailing_multivalue {
                collect_expr_mentioned_temps(trailing, temps);
            }
        }
        HirExpr::Closure(closure) => {
            for capture in &closure.captures {
                collect_expr_mentioned_temps(&capture.value, temps);
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

fn collect_decision_target_mentioned_temps(
    target: &crate::hir::common::HirDecisionTarget,
    temps: &mut BTreeSet<TempId>,
) {
    if let crate::hir::common::HirDecisionTarget::Expr(expr) = target {
        collect_expr_mentioned_temps(expr, temps);
    }
}
