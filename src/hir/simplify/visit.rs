//! 这个文件提供 HIR simplify 共享的只读 visitor。
//!
//! 很多 simplify pass 在真正改写前，只是想先遍历 HIR 收集一批事实，例如：
//! - 哪些 label 仍然被 `goto` 引用
//! - 哪些 temp 在当前 proto 里有显式定义
//! - 某段 stmt 切片里还会读到哪些 local/temp
//!
//! 过去这些分析各自复制了一整套 `block/stmt/lvalue/call/expr` 递归骨架。这里把只读
//! 遍历收成共享设施，让 collector 更专注在"看到某个节点时记录什么"。
//!
//! 它不会跨层补事实，也不会主动进入子 proto 的 body 重新扫描整棵模块树；这里的
//! 作用域就是"当前正在 simplify 的这一个 proto"。例如 closure 只会访问 capture
//! 表达式，因为那正是当前 proto 能直接消费的事实边界。

use crate::hir::common::{
    HirBlock, HirCallExpr, HirDecisionExpr, HirExpr, HirLValue, HirProto, HirStmt,
    HirTableConstructor,
};

use super::traverse::{
    traverse_hir_call_children, traverse_hir_decision_children, traverse_hir_expr_children,
    traverse_hir_lvalue_children, traverse_hir_stmt_children,
    traverse_hir_table_constructor_children,
};

pub(super) trait HirVisitor {
    fn visit_block(&mut self, _block: &HirBlock) {}

    fn visit_stmt(&mut self, _stmt: &HirStmt) {}

    fn visit_expr(&mut self, _expr: &HirExpr) {}

    fn visit_lvalue(&mut self, _lvalue: &HirLValue) {}

    fn visit_call(&mut self, _call: &HirCallExpr) {}
}

pub(super) fn visit_proto(proto: &HirProto, visitor: &mut impl HirVisitor) {
    visit_block(&proto.body, visitor);
}

pub(super) fn visit_block(block: &HirBlock, visitor: &mut impl HirVisitor) {
    visitor.visit_block(block);
    visit_stmts(&block.stmts, visitor);
}

pub(super) fn visit_stmts(stmts: &[HirStmt], visitor: &mut impl HirVisitor) {
    for stmt in stmts {
        visit_stmt(stmt, visitor);
    }
}

fn visit_stmt(stmt: &HirStmt, visitor: &mut impl HirVisitor) {
    visitor.visit_stmt(stmt);
    traverse_hir_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(expr) => {
            visit_expr(expr, visitor);
        },
        lvalue(lvalue) => {
            visit_lvalue(lvalue, visitor);
        },
        block(block) => {
            visit_block(block, visitor);
        },
        call(call) => {
            visit_call(call, visitor);
        },
        condition(cond) => {
            visit_expr(cond, visitor);
        }
    );
}

pub(super) fn visit_call(call: &HirCallExpr, visitor: &mut impl HirVisitor) {
    visitor.visit_call(call);
    traverse_hir_call_children!(call, iter = iter, borrow = [&], expr(expr) => {
        visit_expr(expr, visitor);
    });
}

pub(super) fn visit_lvalue(lvalue: &HirLValue, visitor: &mut impl HirVisitor) {
    visitor.visit_lvalue(lvalue);
    traverse_hir_lvalue_children!(lvalue, borrow = [&], expr(expr) => {
        visit_expr(expr, visitor);
    });
}

pub(super) fn visit_expr(expr: &HirExpr, visitor: &mut impl HirVisitor) {
    visitor.visit_expr(expr);
    traverse_hir_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(e) => {
            visit_expr(e, visitor);
        },
        call(c) => {
            visit_call(c, visitor);
        },
        decision(d) => {
            visit_decision_expr(d, visitor);
        },
        table_constructor(t) => {
            visit_table_constructor(t, visitor);
        }
    );
}

fn visit_decision_expr(decision: &HirDecisionExpr, visitor: &mut impl HirVisitor) {
    traverse_hir_decision_children!(
        decision,
        iter = iter,
        borrow = [&],
        expr(e) => {
            visit_expr(e, visitor);
        },
        condition(cond) => {
            visit_expr(cond, visitor);
        }
    );
}

fn visit_table_constructor(table: &HirTableConstructor, visitor: &mut impl HirVisitor) {
    traverse_hir_table_constructor_children!(
        table,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(e) => {
            visit_expr(e, visitor);
        }
    );
}
