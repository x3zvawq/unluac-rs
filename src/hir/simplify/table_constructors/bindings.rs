//! 这个子模块负责 table-constructor pass 里的 binding 识别与字段键翻译。
//!
//! 它依赖 HIR 已经分好的 lvalue/expr 形状，只回答“这个读写是不是同一个构造器绑定”，
//! 不会在这里扫描 region 或重建字段序列。
//! 例如：`t.x = v` 会在这里把键翻成 `Name(\"x\")` 并识别 `t` 的绑定身份。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirCallExpr, HirDecisionTarget, HirExpr, HirLValue, HirStmt, HirTableField, HirTableKey,
};

use super::TableBinding;
use crate::hir::simplify::visit::{HirVisitor, visit_block, visit_stmts};

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
    let mut collector = BindingUseCollector::default();
    visit_stmts(stmts, &mut collector);
    collector.bindings
}

pub(super) fn collect_materialized_binding_counts(
    block: &crate::hir::common::HirBlock,
) -> BTreeMap<TableBinding, usize> {
    let mut collector = MaterializedBindingCollector::default();
    visit_block(block, &mut collector);
    collector.counts
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

#[derive(Default)]
struct BindingUseCollector {
    bindings: BTreeSet<TableBinding>,
}

impl HirVisitor for BindingUseCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let Some(binding) = binding_from_expr(expr) {
            self.bindings.insert(binding);
        }
    }
}

#[derive(Default)]
struct MaterializedBindingCollector {
    counts: BTreeMap<TableBinding, usize>,
}

impl HirVisitor for MaterializedBindingCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::LocalDecl(local_decl) => {
                for binding in &local_decl.bindings {
                    *self
                        .counts
                        .entry(TableBinding::Local(*binding))
                        .or_default() += 1;
                }
            }
            HirStmt::Assign(assign) => {
                for target in &assign.targets {
                    if let Some(binding) = binding_from_lvalue(target) {
                        *self.counts.entry(binding).or_default() += 1;
                    }
                }
            }
            HirStmt::NumericFor(numeric_for) => {
                *self
                    .counts
                    .entry(TableBinding::Local(numeric_for.binding))
                    .or_default() += 1;
            }
            HirStmt::GenericFor(generic_for) => {
                for binding in &generic_for.bindings {
                    *self
                        .counts
                        .entry(TableBinding::Local(*binding))
                        .or_default() += 1;
                }
            }
            HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Return(_)
            | HirStmt::If(_)
            | HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::Block(_)
            | HirStmt::Unstructured(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => {}
        }
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
