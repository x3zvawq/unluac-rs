//! 这个文件负责 `locals` pass 内部的 temp -> local 引用改写。
//!
//! `locals` 的主文件决定哪些 temp 可以提升、何时复用已经被 closure 捕获的 local；
//! 本文件只消费已经确定的 `TempId -> LocalId` 映射，把表达式、左值、table 构造器和
//! closure capture 里的引用改成对应 local。它不会重新判断某个 temp 是否应该提升，
//! 也不会跨语句寻找新的绑定关系。
//!
//! 输入形状：`t2 = t1 + 1`，且主 pass 已确认 `t1 -> l0`。
//! 输出形状：`t2 = l0 + 1`。

use std::collections::BTreeMap;

use crate::hir::common::{
    HirCallExpr, HirDecisionTarget, HirExpr, HirLValue, HirStmt, HirTableConstructor,
    HirTableField, HirTableKey, LocalId, TempId,
};

pub(super) fn call_expr(call: &mut HirCallExpr, mapping: &BTreeMap<TempId, LocalId>) -> bool {
    let callee_changed = expr(&mut call.callee, mapping);
    let mut args_changed = false;
    for arg in &mut call.args {
        args_changed |= expr(arg, mapping);
    }
    callee_changed || args_changed
}

pub(super) fn expr(node: &mut HirExpr, mapping: &BTreeMap<TempId, LocalId>) -> bool {
    match node {
        HirExpr::TempRef(temp) => {
            if let Some(local) = mapping.get(temp) {
                *node = HirExpr::LocalRef(*local);
                true
            } else {
                false
            }
        }
        HirExpr::TableAccess(access) => {
            let base_changed = expr(&mut access.base, mapping);
            let key_changed = expr(&mut access.key, mapping);
            base_changed || key_changed
        }
        HirExpr::Unary(unary) => expr(&mut unary.expr, mapping),
        HirExpr::Binary(binary) => {
            let lhs_changed = expr(&mut binary.lhs, mapping);
            let rhs_changed = expr(&mut binary.rhs, mapping);
            lhs_changed || rhs_changed
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            let lhs_changed = expr(&mut logical.lhs, mapping);
            let rhs_changed = expr(&mut logical.rhs, mapping);
            lhs_changed || rhs_changed
        }
        HirExpr::Decision(decision) => {
            let mut changed = false;
            for node in &mut decision.nodes {
                let test_changed = expr(&mut node.test, mapping);
                let truthy_changed = decision_target(&mut node.truthy, mapping);
                let falsy_changed = decision_target(&mut node.falsy, mapping);
                changed |= test_changed || truthy_changed || falsy_changed;
            }
            changed
        }
        HirExpr::Call(call) => call_expr(call, mapping),
        HirExpr::TableConstructor(table) => table_constructor(table, mapping),
        HirExpr::Closure(closure) => {
            let mut changed = false;
            for capture in &mut closure.captures {
                changed |= expr(&mut capture.value, mapping);
            }
            changed
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
        | HirExpr::Unresolved(_) => false,
    }
}

fn decision_target(target: &mut HirDecisionTarget, mapping: &BTreeMap<TempId, LocalId>) -> bool {
    match target {
        HirDecisionTarget::Expr(expr) => self::expr(expr, mapping),
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => false,
    }
}

fn table_constructor(table: &mut HirTableConstructor, mapping: &BTreeMap<TempId, LocalId>) -> bool {
    let mut fields_changed = false;
    for field in &mut table.fields {
        let field_changed = match field {
            HirTableField::Array(expr) => self::expr(expr, mapping),
            HirTableField::Record(field) => {
                let key_changed = match &mut field.key {
                    HirTableKey::Name(_) => false,
                    HirTableKey::Expr(expr) => self::expr(expr, mapping),
                };
                let value_changed = self::expr(&mut field.value, mapping);
                key_changed || value_changed
            }
        };
        fields_changed |= field_changed;
    }
    let trailing_changed = table
        .trailing_multivalue
        .as_mut()
        .is_some_and(|expr| self::expr(expr, mapping));

    fields_changed || trailing_changed
}

pub(super) fn lvalue(lvalue: &mut HirLValue, mapping: &BTreeMap<TempId, LocalId>) -> bool {
    match lvalue {
        HirLValue::Temp(temp) => {
            if let Some(local) = mapping.get(temp) {
                *lvalue = HirLValue::Local(*local);
                true
            } else {
                false
            }
        }
        HirLValue::TableAccess(access) => {
            let base_changed = expr(&mut access.base, mapping);
            let key_changed = expr(&mut access.key, mapping);
            base_changed || key_changed
        }
        HirLValue::Param(_)
        | HirLValue::Local(_)
        | HirLValue::Upvalue(_)
        | HirLValue::Global(_) => false,
    }
}

/// 对语句中 closure capture 里残留的 TempRef 做定向重写。
///
/// 互递归/前向声明模式下（`local a, b; a = function() b()… end; b = function() a()… end`），
/// 第一次遍历 promote_block 时 b 的 temp 尚未加入 mapping，导致 a 的 capture 仍是
/// TempRef。这里用最终 mapping 补一次定向重写，只处理 closure capture 这一种残留，
/// 避免做全量二次遍历。
pub(super) fn forward_capture_refs(stmt: &mut HirStmt, mapping: &BTreeMap<TempId, LocalId>) {
    match stmt {
        HirStmt::Assign(assign) => {
            for expr in &mut assign.values {
                closure_capture_temps(expr, mapping);
            }
        }
        HirStmt::LocalDecl(local_decl) => {
            for expr in &mut local_decl.values {
                closure_capture_temps(expr, mapping);
            }
        }
        _ => {}
    }
}

fn closure_capture_temps(expr: &mut HirExpr, mapping: &BTreeMap<TempId, LocalId>) {
    if let HirExpr::Closure(closure) = expr {
        for capture in &mut closure.captures {
            self::expr(&mut capture.value, mapping);
        }
    }
}
