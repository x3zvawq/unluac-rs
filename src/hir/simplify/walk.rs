//! 这个文件提供 HIR simplify pass 共享的递归 walker。
//!
//! 很多 simplify pass 都只是"后序遍历整棵 HIR，然后在局部 block/stmt/expr 上做保守
//! 重写"。如果每个 pass 都各自维护一套 `block/stmt/lvalue/call/expr` 骨架，后面一旦
//! 新增 HIR 节点或调整遍历顺序，就得在多处同步返工。
//!
//! 这里把公共遍历样板收成两层接口：
//! - `HirRewritePass` 负责通用 block/stmt/expr 级重写
//! - `ExprRewritePass` 作为兼容层，继续服务"只关心表达式"的现有 pass
//!
//! 它不会替具体 pass 决定"哪些节点该改、哪些事实可信"；这些语义仍然由各个 pass
//! 自己负责。这个文件只统一递归顺序和进入子节点的边界，避免不同 pass 各自长出
//! 一套不一致的 walker。
//!
//! 例子：
//! - `logical_simplify` 只需要实现 `ExprRewritePass`
//! - `dead_labels` 这类要在整段 block 上做删改的 pass，则实现 `HirRewritePass`
//! - `close_scopes / decision-eliminate` 这类自带 block rebuild 的 pass，则可以只复用
//!   下面的 `for_each_nested_block_mut / rewrite_nested_blocks_in_stmt`

use crate::hir::common::{
    HirBlock, HirCallExpr, HirDecisionExpr, HirExpr, HirLValue, HirProto, HirStmt,
    HirTableConstructor,
};

use super::traverse::{
    traverse_hir_call_children, traverse_hir_decision_children, traverse_hir_expr_children,
    traverse_hir_lvalue_children, traverse_hir_stmt_children,
    traverse_hir_table_constructor_children,
};

pub(super) trait HirRewritePass {
    fn rewrite_block(&mut self, _block: &mut HirBlock) -> bool {
        false
    }

    fn rewrite_stmt(&mut self, _stmt: &mut HirStmt) -> bool {
        false
    }

    fn rewrite_expr(&mut self, _expr: &mut HirExpr) -> bool {
        false
    }

    fn rewrite_lvalue(&mut self, _lvalue: &mut HirLValue) -> bool {
        false
    }

    fn rewrite_call(&mut self, _call: &mut HirCallExpr) -> bool {
        false
    }

    fn rewrite_condition_expr(&mut self, expr: &mut HirExpr) -> bool {
        self.rewrite_expr(expr)
    }
}

pub(super) fn rewrite_proto(proto: &mut HirProto, pass: &mut impl HirRewritePass) -> bool {
    rewrite_block(&mut proto.body, pass)
}

pub(super) fn rewrite_stmts(stmts: &mut [HirStmt], pass: &mut impl HirRewritePass) -> bool {
    stmts.iter_mut().fold(false, |changed, stmt| {
        rewrite_stmt(stmt, pass) || changed
    })
}

pub(super) trait ExprRewritePass {
    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool;

    fn rewrite_condition_expr(&mut self, expr: &mut HirExpr) -> bool {
        self.rewrite_expr(expr)
    }
}

pub(super) fn rewrite_proto_exprs(proto: &mut HirProto, pass: &mut impl ExprRewritePass) -> bool {
    let mut adapter = ExprRewritePassAdapter { pass };
    rewrite_proto(proto, &mut adapter)
}

pub(super) fn for_each_nested_block_mut(stmt: &mut HirStmt, visit: &mut impl FnMut(&mut HirBlock)) {
    match stmt {
        HirStmt::If(if_stmt) => {
            visit(&mut if_stmt.then_block);
            if let Some(else_block) = &mut if_stmt.else_block {
                visit(else_block);
            }
        }
        HirStmt::While(while_stmt) => visit(&mut while_stmt.body),
        HirStmt::Repeat(repeat_stmt) => visit(&mut repeat_stmt.body),
        HirStmt::NumericFor(numeric_for) => visit(&mut numeric_for.body),
        HirStmt::GenericFor(generic_for) => visit(&mut generic_for.body),
        HirStmt::Block(block) => visit(block),
        HirStmt::Unstructured(unstructured) => visit(&mut unstructured.body),
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
    }
}

pub(super) fn rewrite_nested_blocks_in_stmt(
    stmt: &mut HirStmt,
    rewrite_block: &mut impl FnMut(&mut HirBlock) -> bool,
) -> bool {
    let mut changed = false;
    for_each_nested_block_mut(stmt, &mut |block| {
        changed |= rewrite_block(block);
    });
    changed
}

struct ExprRewritePassAdapter<'a, P> {
    pass: &'a mut P,
}

impl<P: ExprRewritePass> HirRewritePass for ExprRewritePassAdapter<'_, P> {
    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        self.pass.rewrite_expr(expr)
    }

    fn rewrite_condition_expr(&mut self, expr: &mut HirExpr) -> bool {
        self.pass.rewrite_condition_expr(expr)
    }
}

fn rewrite_block(block: &mut HirBlock, pass: &mut impl HirRewritePass) -> bool {
    let nested_changed = block
        .stmts
        .iter_mut()
        .fold(false, |changed, stmt| rewrite_stmt(stmt, pass) || changed);
    let block_changed = pass.rewrite_block(block);
    block_changed || nested_changed
}

fn rewrite_stmt(stmt: &mut HirStmt, pass: &mut impl HirRewritePass) -> bool {
    let mut nested_changed = false;
    traverse_hir_stmt_children!(
        stmt,
        iter = iter_mut,
        opt = as_mut,
        borrow = [&mut],
        expr(expr) => {
            nested_changed |= rewrite_expr(expr, pass);
        },
        lvalue(lvalue) => {
            nested_changed |= rewrite_lvalue(lvalue, pass);
        },
        block(block) => {
            nested_changed |= rewrite_block(block, pass);
        },
        call(call) => {
            nested_changed |= rewrite_call_expr(call, pass);
        },
        condition(cond) => {
            nested_changed |= rewrite_condition_expr(cond, pass);
        }
    );

    let stmt_changed = pass.rewrite_stmt(stmt);
    stmt_changed || nested_changed
}

fn rewrite_lvalue(lvalue: &mut HirLValue, pass: &mut impl HirRewritePass) -> bool {
    let mut nested_changed = false;
    traverse_hir_lvalue_children!(lvalue, borrow = [&mut], expr(expr) => {
        nested_changed |= rewrite_expr(expr, pass);
    });

    let lvalue_changed = pass.rewrite_lvalue(lvalue);
    lvalue_changed || nested_changed
}

fn rewrite_call_expr(call: &mut HirCallExpr, pass: &mut impl HirRewritePass) -> bool {
    let mut nested_changed = false;
    traverse_hir_call_children!(call, iter = iter_mut, borrow = [&mut], expr(expr) => {
        nested_changed |= rewrite_expr(expr, pass);
    });
    let call_changed = pass.rewrite_call(call);
    call_changed || nested_changed
}

fn rewrite_expr(expr: &mut HirExpr, pass: &mut impl HirRewritePass) -> bool {
    let mut nested_changed = false;
    traverse_hir_expr_children!(
        expr,
        iter = iter_mut,
        borrow = [&mut],
        expr(e) => {
            nested_changed |= rewrite_expr(e, pass);
        },
        call(c) => {
            nested_changed |= rewrite_call_expr(c, pass);
        },
        decision(d) => {
            nested_changed |= rewrite_decision_expr(d, pass);
        },
        table_constructor(t) => {
            nested_changed |= rewrite_table_constructor(t, pass);
        }
    );

    let expr_changed = pass.rewrite_expr(expr);
    expr_changed || nested_changed
}

fn rewrite_decision_expr(
    decision: &mut HirDecisionExpr,
    pass: &mut impl HirRewritePass,
) -> bool {
    let mut changed = false;
    traverse_hir_decision_children!(
        decision,
        iter = iter_mut,
        borrow = [&mut],
        expr(e) => {
            changed |= rewrite_expr(e, pass);
        },
        condition(cond) => {
            changed |= rewrite_condition_expr(cond, pass);
        }
    );
    changed
}

fn rewrite_table_constructor(
    table: &mut HirTableConstructor,
    pass: &mut impl HirRewritePass,
) -> bool {
    let mut changed = false;
    traverse_hir_table_constructor_children!(
        table,
        iter = iter_mut,
        opt = as_mut,
        borrow = [&mut],
        expr(e) => {
            changed |= rewrite_expr(e, pass);
        }
    );
    changed
}

fn rewrite_condition_expr(expr: &mut HirExpr, pass: &mut impl HirRewritePass) -> bool {
    let nested_changed = rewrite_expr(expr, pass);
    pass.rewrite_condition_expr(expr) || nested_changed
}
