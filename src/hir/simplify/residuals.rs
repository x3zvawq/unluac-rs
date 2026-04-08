//! HIR 退出残差统计。
//!
//! 统计一个 HirModule 中剩余未结构化的 Decision / Unresolved / Unstructured 节点数量，
//! 用来在 simplify 主循环里判断是否还需要继续收敛。

use crate::hir::traverse::{
    traverse_hir_call_children, traverse_hir_decision_children, traverse_hir_expr_children,
    traverse_hir_lvalue_children, traverse_hir_stmt_children, traverse_hir_table_constructor_children,
};
use crate::hir::{HirBlock, HirExpr, HirModule, HirStmt};

#[derive(Default)]
pub(super) struct HirExitResiduals {
    pub decisions: usize,
    pub unresolved: usize,
    pub fallback_unstructured: usize,
    pub other_unstructured: usize,
}

impl HirExitResiduals {
    pub fn has_soft_residuals(&self) -> bool {
        self.decisions != 0
            || self.unresolved != 0
            || self.fallback_unstructured != 0
            || self.other_unstructured != 0
    }
}

pub(super) fn collect_hir_exit_residuals(module: &HirModule) -> HirExitResiduals {
    let mut residuals = HirExitResiduals::default();
    for proto in &module.protos {
        collect_block_residuals(&proto.body, &mut residuals);
    }
    residuals
}

fn collect_block_residuals(block: &HirBlock, residuals: &mut HirExitResiduals) {
    for stmt in &block.stmts {
        collect_stmt_residuals(stmt, residuals);
    }
}

fn collect_stmt_residuals(stmt: &HirStmt, residuals: &mut HirExitResiduals) {
    // Unstructured 需要在递归前统计残差类型。
    if let HirStmt::Unstructured(unstructured) = stmt {
        if unstructured
            .summary
            .as_deref()
            .is_some_and(|summary| summary.contains("fallback"))
        {
            residuals.fallback_unstructured += 1;
        } else {
            residuals.other_unstructured += 1;
        }
    }

    traverse_hir_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(e) => { collect_expr_residuals(e, residuals); },
        lvalue(lv) => {
            traverse_hir_lvalue_children!(
                lv,
                borrow = [&],
                expr(e) => { collect_expr_residuals(e, residuals); }
            );
        },
        block(b) => { collect_block_residuals(b, residuals); },
        call(c) => {
            traverse_hir_call_children!(
                c,
                iter = iter,
                borrow = [&],
                expr(e) => { collect_expr_residuals(e, residuals); }
            );
        },
        condition(cond) => { collect_expr_residuals(cond, residuals); }
    );
}

fn collect_expr_residuals(expr: &HirExpr, residuals: &mut HirExitResiduals) {
    // Decision / Unresolved 需要在结构递归前统计。
    match expr {
        HirExpr::Decision(_) => residuals.decisions += 1,
        HirExpr::Unresolved(_) => residuals.unresolved += 1,
        _ => {}
    }

    traverse_hir_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(e) => { collect_expr_residuals(e, residuals); },
        call(c) => {
            traverse_hir_call_children!(
                c,
                iter = iter,
                borrow = [&],
                expr(e) => { collect_expr_residuals(e, residuals); }
            );
        },
        decision(d) => {
            traverse_hir_decision_children!(
                d,
                iter = iter,
                borrow = [&],
                expr(e) => { collect_expr_residuals(e, residuals); },
                condition(cond) => { collect_expr_residuals(cond, residuals); }
            );
        },
        table_constructor(t) => {
            traverse_hir_table_constructor_children!(
                t,
                iter = iter,
                opt = as_ref,
                borrow = [&],
                expr(e) => { collect_expr_residuals(e, residuals); }
            );
        }
    );
}

pub(super) fn emit_hir_warning(message: String) {
    eprintln!("[unluac][hir-warning] {message}");
}
