//! 这个文件提供 AST readability 共享的只读 visitor。
//!
//! 很多 readability pass 只是想“遍历 AST 收集一批事实”，例如统计 method 名、
//! 扫描 temp、寻找 synthetic local。过去这些分析各自复制了一整套
//! `block/stmt/lvalue/call/expr` 递归骨架；这里把只读遍历收成共享设施，让分析代码
//! 更专注在“看到某个节点时记录什么”，而不是重复维护递归。

use crate::ast::common::{
    AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstModule, AstStmt,
};

use super::traverse::{
    BlockKind, traverse_call_children, traverse_expr_children, traverse_lvalue_children,
    traverse_stmt_children,
};

pub(super) trait AstVisitor {
    fn visit_block(&mut self, _block: &AstBlock, _kind: BlockKind) {}

    fn visit_stmt(&mut self, _stmt: &AstStmt) {}

    fn visit_expr(&mut self, _expr: &AstExpr) {}

    fn visit_lvalue(&mut self, _lvalue: &AstLValue) {}

    fn visit_call(&mut self, _call: &AstCallKind) {}

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        true
    }

    fn leave_function_expr(&mut self, _function: &AstFunctionExpr) {}

    fn visit_condition_expr(&mut self, expr: &AstExpr) {
        self.visit_expr(expr);
    }
}

pub(super) fn visit_module(module: &AstModule, visitor: &mut impl AstVisitor) {
    visit_block_with_kind(&module.body, BlockKind::ModuleBody, visitor);
}

pub(super) fn visit_block(block: &AstBlock, visitor: &mut impl AstVisitor) {
    visit_block_with_kind(block, BlockKind::Regular, visitor);
}

fn visit_block_with_kind(block: &AstBlock, kind: BlockKind, visitor: &mut impl AstVisitor) {
    visitor.visit_block(block, kind);
    for stmt in &block.stmts {
        visit_stmt(stmt, visitor);
    }
}

fn visit_stmt(stmt: &AstStmt, visitor: &mut impl AstVisitor) {
    visitor.visit_stmt(stmt);
    traverse_stmt_children!(
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
        block(block, block_kind) => {
            visit_block_with_kind(block, block_kind, visitor);
        },
        function(function, function_kind) => {
            visit_function_expr(function, function_kind, visitor);
        },
        condition(condition) => {
            visit_condition_expr(condition, visitor);
        },
        call(call) => {
            visit_call(call, visitor);
        }
    );
}

fn visit_call(call: &AstCallKind, visitor: &mut impl AstVisitor) {
    visitor.visit_call(call);
    traverse_call_children!(call, iter = iter, borrow = [&], expr(expr) => {
        visit_expr(expr, visitor);
    });
}

fn visit_lvalue(lvalue: &AstLValue, visitor: &mut impl AstVisitor) {
    visitor.visit_lvalue(lvalue);
    traverse_lvalue_children!(lvalue, borrow = [&], expr(expr) => {
        visit_expr(expr, visitor);
    });
}

fn visit_expr(expr: &AstExpr, visitor: &mut impl AstVisitor) {
    visitor.visit_expr(expr);
    traverse_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(expr) => {
            visit_expr(expr, visitor);
        },
        function(function, function_kind) => {
            visit_function_expr(function, function_kind, visitor);
        }
    );
}

fn visit_condition_expr(expr: &AstExpr, visitor: &mut impl AstVisitor) {
    visitor.visit_condition_expr(expr);
    visit_expr(expr, visitor);
}

fn visit_function_expr(function: &AstFunctionExpr, kind: BlockKind, visitor: &mut impl AstVisitor) {
    if visitor.visit_function_expr(function) {
        visit_block_with_kind(&function.body, kind, visitor);
    }
    visitor.leave_function_expr(function);
}
