//! AST Readability 共用的递归改写骨架。
//!
//! 统一节点顺序、词法状态和 repeat 条件边界，候选证明由各 pass 负责。

use crate::ast::common::{
    AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstModule, AstStmt,
};

use crate::ast::traverse::BlockKind;
use crate::ast::traverse::{
    traverse_call_children, traverse_expr_children, traverse_lvalue_children,
    traverse_stmt_children,
};

pub(super) trait AstRewritePass {
    fn enter_function(&mut self, _function: &AstFunctionExpr) {}

    fn leave_function(&mut self, _function: &AstFunctionExpr) {}

    fn rewrite_block(&mut self, _block: &mut AstBlock, _kind: BlockKind) -> bool {
        false
    }

    fn rewrite_repeat_body(&mut self, block: &mut AstBlock, _condition: &AstExpr) -> bool {
        self.rewrite_block(block, BlockKind::Regular)
    }

    fn rewrite_repeat_body_and_condition(
        &mut self,
        block: &mut AstBlock,
        condition: &mut AstExpr,
    ) -> bool {
        self.rewrite_repeat_body(block, condition)
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

/// 词法状态由自身保存回退位置；子域只撤销新增变化，不复制祖先事实。
pub(super) trait RewriteScope {
    type Checkpoint;
    fn checkpoint(&self) -> Self::Checkpoint;
    fn restore(&mut self, checkpoint: Self::Checkpoint);
}

impl RewriteScope for usize {
    type Checkpoint = usize;
    fn checkpoint(&self) -> usize {
        *self
    }
    fn restore(&mut self, checkpoint: usize) {
        *self = checkpoint;
    }
}

/// 共享带状态的遍历顺序；entry 更新当前域，子域退出由 walker 恢复，后继消费最终语句。
pub(super) trait ScopedAstRewritePass {
    type Scope: RewriteScope;

    fn enter_function(&mut self, _function: &mut AstFunctionExpr, _scope: &mut Self::Scope) {}

    fn enter_block(
        &mut self,
        _block: &mut AstBlock,
        _kind: BlockKind,
        _scope: &mut Self::Scope,
    ) -> bool {
        false
    }

    fn enter_repeat_body(
        &mut self,
        block: &mut AstBlock,
        _condition: &AstExpr,
        _lifetime: &crate::hir::HirRepeatConditionLifetimeFacts,
        scope: &mut Self::Scope,
    ) -> bool {
        self.enter_block(block, BlockKind::Regular, scope)
    }

    fn enter_stmt_children(&mut self, _stmt: &AstStmt, _scope: &mut Self::Scope) {}
    fn after_stmt(&mut self, _stmt: &AstStmt, _scope: &mut Self::Scope) {}

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
    let mut nested_changed = false;
    for stmt in &mut block.stmts {
        nested_changed |= rewrite_stmt(stmt, pass);
    }
    let block_changed = pass.rewrite_block(block, kind);
    block_changed || nested_changed
}

pub(super) fn rewrite_module_scoped<P: ScopedAstRewritePass>(
    module: &mut AstModule,
    mut scope: P::Scope,
    pass: &mut P,
) -> bool {
    rewrite_block_with_kind_scoped(&mut module.body, BlockKind::ModuleBody, &mut scope, pass)
}

fn rewrite_block_with_kind_scoped<P: ScopedAstRewritePass>(
    block: &mut AstBlock,
    kind: BlockKind,
    scope: &mut P::Scope,
    pass: &mut P,
) -> bool {
    let checkpoint = scope.checkpoint();
    let mut changed = pass.enter_block(block, kind, scope);
    for stmt in &mut block.stmts {
        changed |= rewrite_stmt_scoped(stmt, scope, pass);
    }
    scope.restore(checkpoint);
    changed
}

pub(super) fn rewrite_stmt(stmt: &mut AstStmt, pass: &mut impl AstRewritePass) -> bool {
    if let AstStmt::Repeat(repeat_stmt) = stmt {
        let mut nested_changed = false;
        for stmt in &mut repeat_stmt.body.stmts {
            nested_changed |= rewrite_stmt(stmt, pass);
        }
        nested_changed |=
            pass.rewrite_repeat_body_and_condition(&mut repeat_stmt.body, &mut repeat_stmt.cond);
        nested_changed |= rewrite_condition_expr(&mut repeat_stmt.cond, pass);
        return pass.rewrite_stmt(stmt) || nested_changed;
    }

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
        block(block) => {
            nested_changed |= rewrite_block_with_kind(block, BlockKind::Regular, pass);
        },
        function(function) => {
            nested_changed |= rewrite_function_expr(function, BlockKind::FunctionBody, pass);
        },
        condition(condition) => {
            nested_changed |= rewrite_condition_expr(condition, pass);
        },
        call(call) => {
            nested_changed |= rewrite_call(call, pass);
        }
    );

    let stmt_changed = pass.rewrite_stmt(stmt);
    stmt_changed || nested_changed
}

fn rewrite_stmt_scoped<P: ScopedAstRewritePass>(
    stmt: &mut AstStmt,
    scope: &mut P::Scope,
    pass: &mut P,
) -> bool {
    let checkpoint = scope.checkpoint();
    pass.enter_stmt_children(stmt, scope);
    let changed = rewrite_stmt_children_scoped(stmt, scope, pass);
    scope.restore(checkpoint);
    // children 的临时许可覆盖 rewrite_stmt；后继状态消费最终语句，不能把新子域声明泄露出去。
    pass.after_stmt(stmt, scope);
    changed
}

fn rewrite_stmt_children_scoped<P: ScopedAstRewritePass>(
    stmt: &mut AstStmt,
    scope: &mut P::Scope,
    pass: &mut P,
) -> bool {
    if let AstStmt::Repeat(repeat_stmt) = stmt {
        let checkpoint = scope.checkpoint();
        let block_changed = pass.enter_repeat_body(
            &mut repeat_stmt.body,
            &repeat_stmt.cond,
            &repeat_stmt.lifetime,
            scope,
        );
        let mut nested_changed = false;
        // repeat body 与 until 条件共享词法作用域；逐句推进后，条件必须看到
        // body 末尾已经生效的声明，而不能退回 repeat 外层 scope。
        for stmt in &mut repeat_stmt.body.stmts {
            nested_changed |= rewrite_stmt_scoped(stmt, scope, pass);
        }
        nested_changed |= rewrite_condition_expr_scoped(&mut repeat_stmt.cond, scope, pass);
        scope.restore(checkpoint);
        return pass.rewrite_stmt(stmt, scope) || block_changed || nested_changed;
    }

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
        block(block) => {
            nested_changed |= rewrite_block_with_kind_scoped(block, BlockKind::Regular, scope, pass);
        },
        function(function) => {
            nested_changed |= rewrite_function_expr_scoped(function, BlockKind::FunctionBody, scope, pass);
        },
        condition(condition) => {
            nested_changed |= rewrite_condition_expr_scoped(condition, scope, pass);
        },
        call(call) => {
            nested_changed |= rewrite_call_scoped(call, scope, pass);
        }
    );

    let stmt_changed = pass.rewrite_stmt(stmt, scope);
    stmt_changed || nested_changed
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
        function(function) => {
            nested_changed |= rewrite_function_expr(function, BlockKind::FunctionBody, pass);
        }
    );

    let expr_changed = pass.rewrite_expr(expr);
    expr_changed || nested_changed
}

fn rewrite_expr_scoped<P: ScopedAstRewritePass>(
    expr: &mut AstExpr,
    scope: &mut P::Scope,
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
        function(function) => {
            nested_changed |= rewrite_function_expr_scoped(function, BlockKind::FunctionBody, scope, pass);
        }
    );

    let expr_changed = pass.rewrite_expr(expr, scope);
    expr_changed || nested_changed
}

pub(super) fn rewrite_lvalue(lvalue: &mut AstLValue, pass: &mut impl AstRewritePass) -> bool {
    let mut nested_changed = false;
    traverse_lvalue_children!(lvalue, borrow = [&mut], expr(expr) => {
        nested_changed |= rewrite_expr(expr, pass);
    });

    let lvalue_changed = pass.rewrite_lvalue(lvalue);
    lvalue_changed || nested_changed
}

fn rewrite_lvalue_scoped<P: ScopedAstRewritePass>(
    lvalue: &mut AstLValue,
    scope: &mut P::Scope,
    pass: &mut P,
) -> bool {
    let mut nested_changed = false;
    traverse_lvalue_children!(lvalue, borrow = [&mut], expr(expr) => {
        nested_changed |= rewrite_expr_scoped(expr, scope, pass);
    });

    let lvalue_changed = pass.rewrite_lvalue(lvalue, scope);
    lvalue_changed || nested_changed
}

fn rewrite_condition_expr(expr: &mut AstExpr, pass: &mut impl AstRewritePass) -> bool {
    let nested_changed = rewrite_expr(expr, pass);
    let expr_changed = pass.rewrite_condition_expr(expr);
    expr_changed || nested_changed
}

fn rewrite_condition_expr_scoped<P: ScopedAstRewritePass>(
    expr: &mut AstExpr,
    scope: &mut P::Scope,
    pass: &mut P,
) -> bool {
    let nested_changed = rewrite_expr_scoped(expr, scope, pass);
    let expr_changed = pass.rewrite_condition_expr(expr, scope);
    expr_changed || nested_changed
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
    scope: &mut P::Scope,
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
    pass.enter_function(function);
    let changed = rewrite_block_with_kind(&mut function.body, kind, pass);
    pass.leave_function(function);
    changed
}

fn rewrite_function_expr_scoped<P: ScopedAstRewritePass>(
    function: &mut AstFunctionExpr,
    kind: BlockKind,
    scope: &mut P::Scope,
    pass: &mut P,
) -> bool {
    let checkpoint = scope.checkpoint();
    pass.enter_function(function, scope);
    let changed = rewrite_block_with_kind_scoped(&mut function.body, kind, scope, pass);
    scope.restore(checkpoint);
    changed
}
