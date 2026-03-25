//! 这个文件集中放结构化 lowering 里的局部重写 helper。
//!
//! `structure.rs` 主体更适合表达“什么时候能结构化恢复”，而这些函数只负责在
//! 结构已经确定之后，把 loop state/temp 身份同步改写到同一批 HIR 语句里。
//! 单独拆出来之后，主流程文件更容易看出控制流决策，重写细节也更容易局部维护。

use std::collections::BTreeMap;

use crate::hir::common::{HirExpr, HirLValue, HirStmt, TempId};

pub(super) fn apply_loop_rewrites(
    stmts: &mut [HirStmt],
    target_overrides: &BTreeMap<TempId, HirLValue>,
) {
    if target_overrides.is_empty() {
        return;
    }

    // loop body 里某个 def 一旦被我们收成“稳定状态变量写回”，同 block 后面的 use
    // 也必须同步看到这个新身份；否则就会出现“target 已经是 l0，但后续读取还是 t2”
    // 这种半 SSA、半命令式的错误形状。
    let expr_overrides = temp_expr_overrides(target_overrides);
    for stmt in stmts {
        rewrite_stmt_exprs(stmt, &expr_overrides);
        rewrite_stmt_targets(stmt, target_overrides);
    }
}

pub(super) fn temp_expr_overrides(
    target_overrides: &BTreeMap<TempId, HirLValue>,
) -> BTreeMap<TempId, HirExpr> {
    target_overrides
        .iter()
        .filter_map(|(temp, lvalue)| lvalue_as_expr(lvalue).map(|expr| (*temp, expr)))
        .collect()
}

pub(super) fn lvalue_as_expr(lvalue: &HirLValue) -> Option<HirExpr> {
    match lvalue {
        HirLValue::Temp(temp) => Some(HirExpr::TempRef(*temp)),
        HirLValue::Local(local) => Some(HirExpr::LocalRef(*local)),
        HirLValue::Upvalue(upvalue) => Some(HirExpr::UpvalueRef(*upvalue)),
        HirLValue::Global(global) => Some(HirExpr::GlobalRef(global.clone())),
        HirLValue::TableAccess(_) => None,
    }
}

pub(super) fn rewrite_stmt_targets(
    stmt: &mut HirStmt,
    target_overrides: &BTreeMap<TempId, HirLValue>,
) {
    let HirStmt::Assign(assign) = stmt else {
        return;
    };
    for target in &mut assign.targets {
        let HirLValue::Temp(temp) = target else {
            continue;
        };
        if let Some(replacement) = target_overrides.get(temp) {
            *target = replacement.clone();
        }
    }
}

pub(super) fn rewrite_stmt_exprs(stmt: &mut HirStmt, expr_overrides: &BTreeMap<TempId, HirExpr>) {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            for value in &mut local_decl.values {
                rewrite_expr_temps(value, expr_overrides);
            }
        }
        HirStmt::Assign(assign) => {
            for target in &mut assign.targets {
                rewrite_lvalue_exprs(target, expr_overrides);
            }
            for value in &mut assign.values {
                rewrite_expr_temps(value, expr_overrides);
            }
        }
        HirStmt::TableSetList(set_list) => {
            rewrite_expr_temps(&mut set_list.base, expr_overrides);
            for value in &mut set_list.values {
                rewrite_expr_temps(value, expr_overrides);
            }
            if let Some(trailing) = &mut set_list.trailing_multivalue {
                rewrite_expr_temps(trailing, expr_overrides);
            }
        }
        HirStmt::CallStmt(call_stmt) => {
            rewrite_call_expr_temps(&mut call_stmt.call, expr_overrides)
        }
        HirStmt::Return(ret) => {
            for value in &mut ret.values {
                rewrite_expr_temps(value, expr_overrides);
            }
        }
        HirStmt::If(if_stmt) => {
            rewrite_expr_temps(&mut if_stmt.cond, expr_overrides);
        }
        HirStmt::While(while_stmt) => {
            rewrite_expr_temps(&mut while_stmt.cond, expr_overrides);
        }
        HirStmt::Repeat(repeat_stmt) => {
            rewrite_expr_temps(&mut repeat_stmt.cond, expr_overrides);
        }
        HirStmt::NumericFor(numeric_for) => {
            rewrite_expr_temps(&mut numeric_for.start, expr_overrides);
            rewrite_expr_temps(&mut numeric_for.limit, expr_overrides);
            rewrite_expr_temps(&mut numeric_for.step, expr_overrides);
        }
        HirStmt::GenericFor(generic_for) => {
            for value in &mut generic_for.iterator {
                rewrite_expr_temps(value, expr_overrides);
            }
        }
        HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_)
        | HirStmt::Block(_)
        | HirStmt::Unstructured(_) => {}
    }
}

fn rewrite_call_expr_temps(
    call: &mut crate::hir::common::HirCallExpr,
    expr_overrides: &BTreeMap<TempId, HirExpr>,
) {
    rewrite_expr_temps(&mut call.callee, expr_overrides);
    for arg in &mut call.args {
        rewrite_expr_temps(arg, expr_overrides);
    }
}

fn rewrite_lvalue_exprs(lvalue: &mut HirLValue, expr_overrides: &BTreeMap<TempId, HirExpr>) {
    if let HirLValue::TableAccess(access) = lvalue {
        rewrite_expr_temps(&mut access.base, expr_overrides);
        rewrite_expr_temps(&mut access.key, expr_overrides);
    }
}

pub(super) fn rewrite_expr_temps(expr: &mut HirExpr, expr_overrides: &BTreeMap<TempId, HirExpr>) {
    match expr {
        HirExpr::TempRef(temp) => {
            if let Some(replacement) = expr_overrides.get(temp) {
                *expr = replacement.clone();
            }
        }
        HirExpr::TableAccess(access) => {
            rewrite_expr_temps(&mut access.base, expr_overrides);
            rewrite_expr_temps(&mut access.key, expr_overrides);
        }
        HirExpr::Unary(unary) => rewrite_expr_temps(&mut unary.expr, expr_overrides),
        HirExpr::Binary(binary) => {
            rewrite_expr_temps(&mut binary.lhs, expr_overrides);
            rewrite_expr_temps(&mut binary.rhs, expr_overrides);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            rewrite_expr_temps(&mut logical.lhs, expr_overrides);
            rewrite_expr_temps(&mut logical.rhs, expr_overrides);
        }
        HirExpr::Decision(decision) => {
            for node in &mut decision.nodes {
                rewrite_expr_temps(&mut node.test, expr_overrides);
                rewrite_decision_target_temps(&mut node.truthy, expr_overrides);
                rewrite_decision_target_temps(&mut node.falsy, expr_overrides);
            }
        }
        HirExpr::Call(call) => rewrite_call_expr_temps(call, expr_overrides),
        HirExpr::TableConstructor(table) => {
            for field in &mut table.fields {
                match field {
                    crate::hir::common::HirTableField::Array(expr) => {
                        rewrite_expr_temps(expr, expr_overrides);
                    }
                    crate::hir::common::HirTableField::Record(field) => {
                        if let crate::hir::common::HirTableKey::Expr(expr) = &mut field.key {
                            rewrite_expr_temps(expr, expr_overrides);
                        }
                        rewrite_expr_temps(&mut field.value, expr_overrides);
                    }
                }
            }
            if let Some(trailing) = &mut table.trailing_multivalue {
                rewrite_expr_temps(trailing, expr_overrides);
            }
        }
        HirExpr::Closure(closure) => {
            for capture in &mut closure.captures {
                rewrite_expr_temps(&mut capture.value, expr_overrides);
            }
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => {}
    }
}

fn rewrite_decision_target_temps(
    target: &mut crate::hir::common::HirDecisionTarget,
    expr_overrides: &BTreeMap<TempId, HirExpr>,
) {
    if let crate::hir::common::HirDecisionTarget::Expr(expr) = target {
        rewrite_expr_temps(expr, expr_overrides);
    }
}
