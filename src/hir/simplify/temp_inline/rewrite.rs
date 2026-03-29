//! 这个子模块负责 temp-inline pass 的实际替换动作。
//!
//! 它依赖 `site` 已确认的内联位置和上层给好的 replacement，只做语法树内的定点替换，
//! 不会在这里重新判断这个 temp 应不应该内联。
//! 例如：`local r0 = print; r0(1)` 选定站点后，会在这里把 `r0` 改成 `print`。

use super::*;

pub(super) fn replace_temp_in_stmt(stmt: &mut HirStmt, temp: TempId, replacement: &HirExpr) {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            for value in &mut local_decl.values {
                replace_temp_in_expr(value, temp, replacement);
            }
        }
        HirStmt::Assign(assign) => {
            for target in &mut assign.targets {
                replace_temp_in_lvalue(target, temp, replacement);
            }
            for value in &mut assign.values {
                replace_temp_in_expr(value, temp, replacement);
            }
        }
        HirStmt::TableSetList(set_list) => {
            replace_temp_in_expr(&mut set_list.base, temp, replacement);
            for value in &mut set_list.values {
                replace_temp_in_expr(value, temp, replacement);
            }
            if let Some(expr) = &mut set_list.trailing_multivalue {
                replace_temp_in_expr(expr, temp, replacement);
            }
        }
        HirStmt::ErrNil(err_nil) => {
            replace_temp_in_expr(&mut err_nil.value, temp, replacement);
        }
        HirStmt::ToBeClosed(to_be_closed) => {
            replace_temp_in_expr(&mut to_be_closed.value, temp, replacement);
        }
        HirStmt::CallStmt(call_stmt) => {
            replace_temp_in_call_expr(&mut call_stmt.call, temp, replacement)
        }
        HirStmt::Return(ret) => {
            for value in &mut ret.values {
                replace_temp_in_expr(value, temp, replacement);
            }
        }
        HirStmt::If(if_stmt) => {
            replace_temp_in_expr(&mut if_stmt.cond, temp, replacement);
            replace_temp_in_block(&mut if_stmt.then_block, temp, replacement);
            if let Some(else_block) = &mut if_stmt.else_block {
                replace_temp_in_block(else_block, temp, replacement);
            }
        }
        HirStmt::While(while_stmt) => {
            replace_temp_in_expr(&mut while_stmt.cond, temp, replacement);
            replace_temp_in_block(&mut while_stmt.body, temp, replacement);
        }
        HirStmt::Repeat(repeat_stmt) => {
            replace_temp_in_block(&mut repeat_stmt.body, temp, replacement);
            replace_temp_in_expr(&mut repeat_stmt.cond, temp, replacement);
        }
        HirStmt::NumericFor(numeric_for) => {
            replace_temp_in_expr(&mut numeric_for.start, temp, replacement);
            replace_temp_in_expr(&mut numeric_for.limit, temp, replacement);
            replace_temp_in_expr(&mut numeric_for.step, temp, replacement);
            replace_temp_in_block(&mut numeric_for.body, temp, replacement);
        }
        HirStmt::GenericFor(generic_for) => {
            for expr in &mut generic_for.iterator {
                replace_temp_in_expr(expr, temp, replacement);
            }
            replace_temp_in_block(&mut generic_for.body, temp, replacement);
        }
        HirStmt::Close(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
        HirStmt::Block(block) => replace_temp_in_block(block, temp, replacement),
        HirStmt::Unstructured(unstructured) => {
            replace_temp_in_block(&mut unstructured.body, temp, replacement);
        }
    }
}

fn replace_temp_in_block(block: &mut HirBlock, temp: TempId, replacement: &HirExpr) {
    for stmt in &mut block.stmts {
        replace_temp_in_stmt(stmt, temp, replacement);
    }
}

fn replace_temp_in_call_expr(call: &mut HirCallExpr, temp: TempId, replacement: &HirExpr) {
    replace_temp_in_expr(&mut call.callee, temp, replacement);
    for arg in &mut call.args {
        replace_temp_in_expr(arg, temp, replacement);
    }
}

fn replace_temp_in_lvalue(lvalue: &mut HirLValue, temp: TempId, replacement: &HirExpr) {
    if let HirLValue::TableAccess(access) = lvalue {
        replace_temp_in_expr(&mut access.base, temp, replacement);
        replace_temp_in_expr(&mut access.key, temp, replacement);
    }
}

fn replace_temp_in_expr(expr: &mut HirExpr, temp: TempId, replacement: &HirExpr) {
    match expr {
        HirExpr::TempRef(other) if *other == temp => {
            *expr = replacement.clone();
        }
        HirExpr::TableAccess(access) => {
            replace_temp_in_expr(&mut access.base, temp, replacement);
            replace_temp_in_expr(&mut access.key, temp, replacement);
        }
        HirExpr::Unary(unary) => replace_temp_in_expr(&mut unary.expr, temp, replacement),
        HirExpr::Binary(binary) => {
            replace_temp_in_expr(&mut binary.lhs, temp, replacement);
            replace_temp_in_expr(&mut binary.rhs, temp, replacement);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            replace_temp_in_expr(&mut logical.lhs, temp, replacement);
            replace_temp_in_expr(&mut logical.rhs, temp, replacement);
        }
        HirExpr::Decision(decision) => {
            for node in &mut decision.nodes {
                replace_temp_in_expr(&mut node.test, temp, replacement);
                replace_temp_in_decision_target(&mut node.truthy, temp, replacement);
                replace_temp_in_decision_target(&mut node.falsy, temp, replacement);
            }
        }
        HirExpr::Call(call) => replace_temp_in_call_expr(call, temp, replacement),
        HirExpr::TableConstructor(table) => {
            for field in &mut table.fields {
                match field {
                    HirTableField::Array(expr) => replace_temp_in_expr(expr, temp, replacement),
                    HirTableField::Record(field) => {
                        replace_temp_in_table_key(&mut field.key, temp, replacement);
                        replace_temp_in_expr(&mut field.value, temp, replacement);
                    }
                }
            }
            if let Some(expr) = &mut table.trailing_multivalue {
                replace_temp_in_expr(expr, temp, replacement);
            }
        }
        HirExpr::Closure(closure) => {
            for capture in &mut closure.captures {
                replace_temp_in_expr(&mut capture.value, temp, replacement);
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
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => {}
    }
}

fn replace_temp_in_decision_target(
    target: &mut crate::hir::common::HirDecisionTarget,
    temp: TempId,
    replacement: &HirExpr,
) {
    if let crate::hir::common::HirDecisionTarget::Expr(expr) = target {
        replace_temp_in_expr(expr, temp, replacement);
    }
}

fn replace_temp_in_table_key(
    key: &mut crate::hir::common::HirTableKey,
    temp: TempId,
    replacement: &HirExpr,
) {
    if let crate::hir::common::HirTableKey::Expr(expr) = key {
        replace_temp_in_expr(expr, temp, replacement);
    }
}
