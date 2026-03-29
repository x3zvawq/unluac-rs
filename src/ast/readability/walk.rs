//! 这个文件提供 AST readability pass 共享的递归 walker。
//!
//! 很多 readability pass 只是“递归遍历整棵 AST，然后在局部 block/stmt/expr 上做
//! 保守重写”。如果每个 pass 都各自维护一套 `block/stmt/lvalue/call/expr` 骨架，
//! 新 AST 节点一加，或者遍历边界一改，就要在一堆文件里同步返工。这里把纯遍历
//! 样板收成共享设施，让 pass 更专注在“当前节点要不要改写”。

use crate::ast::common::{
    AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstModule, AstStmt,
};

pub(super) use super::traverse::BlockKind;
use super::traverse::{
    traverse_call_children, traverse_expr_children, traverse_lvalue_children,
    traverse_stmt_children,
};

pub(super) trait AstRewritePass {
    fn rewrite_block(&mut self, _block: &mut AstBlock, _kind: BlockKind) -> bool {
        false
    }

    fn rewrite_stmt(&mut self, _stmt: &mut AstStmt) -> bool {
        false
    }

    fn rewrite_expr(&mut self, _expr: &mut AstExpr) -> bool {
        false
    }

    fn rewrite_lvalue(&mut self, _lvalue: &mut AstLValue) -> bool {
        false
    }

    fn rewrite_condition_expr(&mut self, expr: &mut AstExpr) -> bool {
        self.rewrite_expr(expr)
    }
}

/// 某些 readability pass 需要沿 block 树向下携带一份显式状态，
/// 例如“当前作用域已经可见哪些 global 名称”。
///
/// 这类 pass 以前只能各自复制整套递归 walker；这里把“进入 block 时产出子作用域状态”
/// 也收成共享设施，让 pass 只关心如何更新状态，不再重复维护遍历骨架。
pub(super) trait ScopedAstRewritePass {
    type Scope: Clone;

    fn enter_block(
        &mut self,
        _block: &mut AstBlock,
        _kind: BlockKind,
        outer_scope: &Self::Scope,
    ) -> (bool, Self::Scope) {
        (false, outer_scope.clone())
    }

    fn rewrite_stmt(&mut self, _stmt: &mut AstStmt, _scope: &Self::Scope) -> bool {
        false
    }

    fn rewrite_expr(&mut self, _expr: &mut AstExpr, _scope: &Self::Scope) -> bool {
        false
    }

    fn rewrite_lvalue(&mut self, _lvalue: &mut AstLValue, _scope: &Self::Scope) -> bool {
        false
    }

    fn rewrite_condition_expr(&mut self, expr: &mut AstExpr, scope: &Self::Scope) -> bool {
        self.rewrite_expr(expr, scope)
    }
}

pub(super) fn rewrite_module(module: &mut AstModule, pass: &mut impl AstRewritePass) -> bool {
    rewrite_block_with_kind(&mut module.body, BlockKind::ModuleBody, pass)
}

fn rewrite_block_with_kind(
    block: &mut AstBlock,
    kind: BlockKind,
    pass: &mut impl AstRewritePass,
) -> bool {
    let nested_changed = block
        .stmts
        .iter_mut()
        .fold(false, |changed, stmt| rewrite_stmt(stmt, pass) || changed);
    pass.rewrite_block(block, kind) || nested_changed
}

pub(super) fn rewrite_module_scoped<P: ScopedAstRewritePass>(
    module: &mut AstModule,
    scope: &P::Scope,
    pass: &mut P,
) -> bool {
    rewrite_block_with_kind_scoped(&mut module.body, BlockKind::ModuleBody, scope, pass)
}

fn rewrite_block_with_kind_scoped<P: ScopedAstRewritePass>(
    block: &mut AstBlock,
    kind: BlockKind,
    outer_scope: &P::Scope,
    pass: &mut P,
) -> bool {
    let (block_changed, scope) = pass.enter_block(block, kind, outer_scope);
    let nested_changed = block.stmts.iter_mut().fold(false, |changed, stmt| {
        rewrite_stmt_scoped(stmt, &scope, pass) || changed
    });
    block_changed || nested_changed
}

pub(super) fn rewrite_stmt(stmt: &mut AstStmt, pass: &mut impl AstRewritePass) -> bool {
    let mut nested_changed = false;
    traverse_stmt_children!(
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
        block(block, block_kind) => {
            nested_changed |= rewrite_block_with_kind(block, block_kind, pass);
        },
        function(function, function_kind) => {
            nested_changed |= rewrite_function_expr(function, function_kind, pass);
        },
        condition(condition) => {
            nested_changed |= rewrite_condition_expr(condition, pass);
        },
        call(call) => {
            nested_changed |= rewrite_call(call, pass);
        }
    );

    pass.rewrite_stmt(stmt) || nested_changed
}

fn rewrite_stmt_scoped<P: ScopedAstRewritePass>(
    stmt: &mut AstStmt,
    scope: &P::Scope,
    pass: &mut P,
) -> bool {
    let mut nested_changed = false;
    traverse_stmt_children!(
        stmt,
        iter = iter_mut,
        opt = as_mut,
        borrow = [&mut],
        expr(expr) => {
            nested_changed |= rewrite_expr_scoped(expr, scope, pass);
        },
        lvalue(lvalue) => {
            nested_changed |= rewrite_lvalue_scoped(lvalue, scope, pass);
        },
        block(block, block_kind) => {
            nested_changed |= rewrite_block_with_kind_scoped(block, block_kind, scope, pass);
        },
        function(function, function_kind) => {
            nested_changed |= rewrite_function_expr_scoped(function, function_kind, scope, pass);
        },
        condition(condition) => {
            nested_changed |= rewrite_condition_expr_scoped(condition, scope, pass);
        },
        call(call) => {
            nested_changed |= rewrite_call_scoped(call, scope, pass);
        }
    );

    pass.rewrite_stmt(stmt, scope) || nested_changed
}

pub(super) fn rewrite_expr(expr: &mut AstExpr, pass: &mut impl AstRewritePass) -> bool {
    let mut nested_changed = false;
    traverse_expr_children!(
        expr,
        iter = iter_mut,
        borrow = [&mut],
        expr(expr) => {
            nested_changed |= rewrite_expr(expr, pass);
        },
        function(function, function_kind) => {
            nested_changed |= rewrite_function_expr(function, function_kind, pass);
        }
    );

    pass.rewrite_expr(expr) || nested_changed
}

fn rewrite_expr_scoped<P: ScopedAstRewritePass>(
    expr: &mut AstExpr,
    scope: &P::Scope,
    pass: &mut P,
) -> bool {
    let mut nested_changed = false;
    traverse_expr_children!(
        expr,
        iter = iter_mut,
        borrow = [&mut],
        expr(expr) => {
            nested_changed |= rewrite_expr_scoped(expr, scope, pass);
        },
        function(function, function_kind) => {
            nested_changed |= rewrite_function_expr_scoped(function, function_kind, scope, pass);
        }
    );

    pass.rewrite_expr(expr, scope) || nested_changed
}

pub(super) fn rewrite_lvalue(lvalue: &mut AstLValue, pass: &mut impl AstRewritePass) -> bool {
    let mut nested_changed = false;
    traverse_lvalue_children!(lvalue, borrow = [&mut], expr(expr) => {
        nested_changed |= rewrite_expr(expr, pass);
    });

    pass.rewrite_lvalue(lvalue) || nested_changed
}

fn rewrite_lvalue_scoped<P: ScopedAstRewritePass>(
    lvalue: &mut AstLValue,
    scope: &P::Scope,
    pass: &mut P,
) -> bool {
    let mut nested_changed = false;
    traverse_lvalue_children!(lvalue, borrow = [&mut], expr(expr) => {
        nested_changed |= rewrite_expr_scoped(expr, scope, pass);
    });

    pass.rewrite_lvalue(lvalue, scope) || nested_changed
}

fn rewrite_condition_expr(expr: &mut AstExpr, pass: &mut impl AstRewritePass) -> bool {
    let nested_changed = rewrite_expr(expr, pass);
    pass.rewrite_condition_expr(expr) || nested_changed
}

fn rewrite_condition_expr_scoped<P: ScopedAstRewritePass>(
    expr: &mut AstExpr,
    scope: &P::Scope,
    pass: &mut P,
) -> bool {
    let nested_changed = rewrite_expr_scoped(expr, scope, pass);
    pass.rewrite_condition_expr(expr, scope) || nested_changed
}

fn rewrite_call(call: &mut AstCallKind, pass: &mut impl AstRewritePass) -> bool {
    let mut nested_changed = false;
    traverse_call_children!(call, iter = iter_mut, borrow = [&mut], expr(expr) => {
        nested_changed |= rewrite_expr(expr, pass);
    });
    nested_changed
}

fn rewrite_call_scoped<P: ScopedAstRewritePass>(
    call: &mut AstCallKind,
    scope: &P::Scope,
    pass: &mut P,
) -> bool {
    let mut nested_changed = false;
    traverse_call_children!(call, iter = iter_mut, borrow = [&mut], expr(expr) => {
        nested_changed |= rewrite_expr_scoped(expr, scope, pass);
    });
    nested_changed
}

fn rewrite_function_expr(
    function: &mut AstFunctionExpr,
    kind: BlockKind,
    pass: &mut impl AstRewritePass,
) -> bool {
    rewrite_block_with_kind(&mut function.body, kind, pass)
}

fn rewrite_function_expr_scoped<P: ScopedAstRewritePass>(
    function: &mut AstFunctionExpr,
    kind: BlockKind,
    scope: &P::Scope,
    pass: &mut P,
) -> bool {
    rewrite_block_with_kind_scoped(&mut function.body, kind, scope, pass)
}
