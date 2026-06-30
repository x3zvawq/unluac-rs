//! 这个子模块负责 temp-inline pass 里的“已提及 temp”保护集。
//!
//! 它依赖 HIR 语句树当前形状，只回答进入嵌套循环/分支前哪些 temp 不能继续往里内联，
//! 不会在这里真正执行替换。
//! 例如：前缀语句和循环体都提到同一个 temp 时，这里会把它列入保护集。

use super::*;
use crate::hir::traverse::{
    traverse_hir_call_children, traverse_hir_decision_children, traverse_hir_expr_children,
    traverse_hir_lvalue_children, traverse_hir_stmt_children,
    traverse_hir_table_constructor_children,
};

pub(super) struct NestedTempProtection {
    stmt_temps: Vec<BTreeSet<TempId>>,
    stmt_capture_temps: Vec<BTreeSet<TempId>>,
    scope_kinds: Vec<NestedScopeKind>,
    prefix_temps: BTreeSet<TempId>,
    suffix_temp_counts: BTreeMap<TempId, usize>,
    suffix_capture_counts: BTreeMap<TempId, usize>,
}

impl NestedTempProtection {
    pub(super) fn new(stmts: &[HirStmt]) -> Self {
        let stmt_temps = super::super::temp_touch::collect_temp_refs_by_stmt(stmts);
        let stmt_capture_temps = stmts
            .iter()
            .map(closure_capture_temp_set_for_stmt)
            .collect::<Vec<_>>();
        let suffix_temp_counts = temp_counts(&stmt_temps);
        let suffix_capture_counts = temp_counts(&stmt_capture_temps);
        let scope_kinds = stmts.iter().map(nested_scope_kind).collect();

        Self {
            stmt_temps,
            stmt_capture_temps,
            scope_kinds,
            prefix_temps: BTreeSet::new(),
            suffix_temp_counts,
            suffix_capture_counts,
        }
    }

    pub(super) fn begin_stmt(
        &mut self,
        stmt_index: usize,
        inherited: &BTreeSet<TempId>,
    ) -> BTreeSet<TempId> {
        decrement_counts(&mut self.suffix_temp_counts, &self.stmt_temps[stmt_index]);
        decrement_counts(
            &mut self.suffix_capture_counts,
            &self.stmt_capture_temps[stmt_index],
        );

        let mut protected = inherited.clone();
        match self.scope_kinds[stmt_index] {
            NestedScopeKind::None => {}
            NestedScopeKind::ClosureCaptureOnly => {
                // if/block 本身不会改变求值次数；这里不套用 loop 的完整前后缀保护，
                // 只保护会成为子 proto upvalue provenance 的 closure capture。
                protected.extend(
                    self.stmt_temps[stmt_index]
                        .iter()
                        .filter(|temp| self.suffix_capture_counts.contains_key(temp))
                        .copied(),
                );
            }
            NestedScopeKind::Full => {
                // 前缀保护求值点，后缀保护外层继续消费的 temp，二者都只对当前
                // nested stmt 中实际出现的 temp 生效。
                protected.extend(
                    self.stmt_temps[stmt_index]
                        .iter()
                        .filter(|temp| {
                            self.prefix_temps.contains(temp)
                                || self.suffix_temp_counts.contains_key(temp)
                        })
                        .copied(),
                );
            }
        }

        protected
    }

    pub(super) fn finish_stmt(&mut self, stmt: &HirStmt) {
        self.prefix_temps
            .extend(super::super::temp_touch::collect_temp_refs_in_stmts(
                std::slice::from_ref(stmt),
            ));
    }
}

#[derive(Debug, Clone, Copy)]
enum NestedScopeKind {
    None,
    ClosureCaptureOnly,
    Full,
}

fn nested_scope_kind(stmt: &HirStmt) -> NestedScopeKind {
    if stmt_needs_full_nested_scope_protection(stmt) {
        NestedScopeKind::Full
    } else if stmt_has_nested_inline_scope(stmt) {
        NestedScopeKind::ClosureCaptureOnly
    } else {
        NestedScopeKind::None
    }
}

fn stmt_has_nested_inline_scope(stmt: &HirStmt) -> bool {
    matches!(
        stmt,
        HirStmt::If(_)
            | HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::NumericFor(_)
            | HirStmt::GenericFor(_)
            | HirStmt::Block(_)
            | HirStmt::Unstructured(_)
    )
}

fn stmt_needs_full_nested_scope_protection(stmt: &HirStmt) -> bool {
    matches!(
        stmt,
        HirStmt::While(_) | HirStmt::Repeat(_) | HirStmt::NumericFor(_) | HirStmt::GenericFor(_)
    )
}

fn temp_counts(temp_sets: &[BTreeSet<TempId>]) -> BTreeMap<TempId, usize> {
    let mut counts = BTreeMap::new();
    for temps in temp_sets {
        for temp in temps {
            *counts.entry(*temp).or_insert(0) += 1;
        }
    }
    counts
}

fn decrement_counts(counts: &mut BTreeMap<TempId, usize>, temps: &BTreeSet<TempId>) {
    for temp in temps {
        let count = counts
            .get_mut(temp)
            .expect("stmt temp sets must be reflected in suffix counts");
        *count -= 1;
        if *count == 0 {
            counts.remove(temp);
        }
    }
}

fn closure_capture_temp_set_for_stmt(stmt: &HirStmt) -> BTreeSet<TempId> {
    let mut temps = BTreeSet::new();
    collect_stmt_closure_capture_temps(stmt, &mut temps);
    temps
}

fn collect_stmt_closure_capture_temps(stmt: &HirStmt, temps: &mut BTreeSet<TempId>) {
    traverse_hir_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(expr) => { collect_expr_closure_capture_temps(expr, temps); },
        lvalue(lvalue) => {
            traverse_hir_lvalue_children!(
                lvalue,
                borrow = [&],
                expr(expr) => { collect_expr_closure_capture_temps(expr, temps); }
            );
        },
        block(block) => { collect_block_closure_capture_temps(block, temps); },
        call(call) => { collect_call_closure_capture_temps(call, temps); },
        condition(cond) => { collect_expr_closure_capture_temps(cond, temps); }
    );
}

fn collect_block_closure_capture_temps(block: &HirBlock, temps: &mut BTreeSet<TempId>) {
    for stmt in &block.stmts {
        collect_stmt_closure_capture_temps(stmt, temps);
    }
}

fn collect_call_mentioned_temps(call: &HirCallExpr, temps: &mut BTreeSet<TempId>) {
    collect_expr_mentioned_temps(&call.callee, temps);
    for arg in &call.args {
        collect_expr_mentioned_temps(arg, temps);
    }
}

fn collect_call_closure_capture_temps(call: &HirCallExpr, temps: &mut BTreeSet<TempId>) {
    traverse_hir_call_children!(
        call,
        iter = iter,
        borrow = [&],
        expr(expr) => { collect_expr_closure_capture_temps(expr, temps); }
    );
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

fn collect_expr_closure_capture_temps(expr: &HirExpr, temps: &mut BTreeSet<TempId>) {
    if let HirExpr::Closure(closure) = expr {
        for capture in &closure.captures {
            collect_expr_mentioned_temps(&capture.value, temps);
        }
    }

    traverse_hir_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(child) => { collect_expr_closure_capture_temps(child, temps); },
        call(call) => { collect_call_closure_capture_temps(call, temps); },
        decision(decision) => {
            traverse_hir_decision_children!(
                decision,
                iter = iter,
                borrow = [&],
                expr(child) => { collect_expr_closure_capture_temps(child, temps); },
                condition(cond) => { collect_expr_closure_capture_temps(cond, temps); }
            );
        },
        table_constructor(table) => {
            traverse_hir_table_constructor_children!(
                table,
                iter = iter,
                opt = as_ref,
                borrow = [&],
                expr(child) => { collect_expr_closure_capture_temps(child, temps); }
            );
        }
    );
}

fn collect_decision_target_mentioned_temps(
    target: &crate::hir::common::HirDecisionTarget,
    temps: &mut BTreeSet<TempId>,
) {
    if let crate::hir::common::HirDecisionTarget::Expr(expr) = target {
        collect_expr_mentioned_temps(expr, temps);
    }
}
