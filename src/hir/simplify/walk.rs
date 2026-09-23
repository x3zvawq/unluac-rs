//! 提供 HIR simplify 共用的递归改写骨架。
//!
//! HirRewritePass 提供 block/stmt/expr 等回调，统一子节点顺序和遍历边界；具体
//! 候选、语义证明与事实有效性仍由各 pass 负责。自带 block rebuild 的 pass 可只用
//! nested-block helper，不必复制整套递归。
//! 例如 logical_simplify 使用表达式及条件回调，dead_labels 在 block 回调中删标签。

use crate::hir::common::{
    HirBlock, HirCallExpr, HirDecisionExpr, HirExpr, HirLValue, HirProto, HirStmt,
    HirTableConstructor,
};

use crate::hir::traverse::{
    traverse_hir_call_children, traverse_hir_decision_children, traverse_hir_expr_children,
    traverse_hir_lvalue_children, traverse_hir_stmt_children,
    traverse_hir_table_constructor_children,
};

pub(crate) trait HirRewritePass {
    fn rewrite_block(&mut self, _block: &mut HirBlock) -> bool {
        false
    }

    fn rewrite_stmt(&mut self, _stmt: &mut HirStmt) -> bool {
        false
    }

    /// 先恢复父语句拥有的控制结构，避免子块改写先消除其结构证据。
    fn rewrite_stmt_before_children(&mut self, _stmt: &mut HirStmt) -> bool {
        false
    }

    fn rewrite_expr(&mut self, _expr: &mut HirExpr) -> bool {
        false
    }

    /// 先归一会影响遍历深度的表达式外壳，再沿改写后的子节点执行普通后序回调。
    fn rewrite_expr_before_children(&mut self, _expr: &mut HirExpr) -> bool {
        false
    }

    /// 捕获只允许身份改写；表达式 pass 不会进入或替换父级 cell。
    fn rewrite_capture(&mut self, _capture: &mut crate::hir::HirCapture) -> bool {
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

    /// 条件 owner 先消费控制图，避免普通值改写先物化真假结果或复制共享 guard。
    fn rewrite_condition_expr_before_children(&mut self, _expr: &mut HirExpr) -> bool {
        false
    }

    /// Generic-for 自身可以裁掉已由 transaction 宽度独立保存的 trailing nil；其它
    /// iterator rewrite 默认逐段校验并撤销变化区间，不抹掉其它 producer 的证明。
    /// 这是 pass 的固定能力；保留事务时不构建不会被消费的 iterator 快照。
    const PRESERVES_GENERIC_FOR_INITIALIZER_TRANSACTION: bool = false;
}

pub(crate) fn rewrite_proto(proto: &mut HirProto, pass: &mut impl HirRewritePass) -> bool {
    rewrite_block(&mut proto.body, pass)
}

pub(super) fn rewrite_stmts(stmts: &mut [HirStmt], pass: &mut impl HirRewritePass) -> bool {
    let mut changed = false;
    for stmt in stmts {
        changed |= rewrite_stmt(stmt, pass);
    }
    changed
}

pub(super) fn for_each_nested_block_mut(stmt: &mut HirStmt, visit: &mut impl FnMut(&mut HirBlock)) {
    traverse_hir_stmt_children!(
        stmt,
        iter = iter_mut,
        opt = as_mut,
        borrow = [&mut],
        expr(_expr) => {},
        tail_call(_call) => {},
        lvalue(_lvalue) => {},
        release(_local) => {},
        block(block) => { visit(block); },
        call(_call) => {},
        condition(_cond) => {}
    );
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

pub(super) fn rewrite_block(block: &mut HirBlock, pass: &mut impl HirRewritePass) -> bool {
    let mut nested_changed = false;
    for stmt in &mut block.stmts {
        nested_changed |= rewrite_stmt(stmt, pass);
    }
    let block_changed = pass.rewrite_block(block);
    block_changed || nested_changed
}

fn rewrite_stmt<P: HirRewritePass>(stmt: &mut HirStmt, pass: &mut P) -> bool {
    let original_assign_targets = match stmt {
        HirStmt::Assign(assign) if assign.generic_for_initializer_producer.is_some() => {
            Some(assign.targets.clone())
        }
        _ => None,
    };
    let original_generic_for_iterator = match stmt {
        HirStmt::GenericFor(generic_for)
            if generic_for.initializer_transaction.is_some()
                && !P::PRESERVES_GENERIC_FOR_INITIALIZER_TRANSACTION =>
        {
            Some(generic_for.iterator.clone())
        }
        _ => None,
    };
    let prefix_changed = pass.rewrite_stmt_before_children(stmt);
    let mut nested_changed = false;
    traverse_hir_stmt_children!(
        stmt,
        iter = iter_mut,
        opt = as_mut,
        borrow = [&mut],
        expr(expr) => {
            nested_changed |= rewrite_expr(expr, pass);
        },
        tail_call(call) => {
            nested_changed |= rewrite_call_expr(call, pass);
        },
        lvalue(lvalue) => {
            nested_changed |= rewrite_lvalue(lvalue, pass);
        },
        release(local) => {
            let mut target = HirLValue::Local(*local);
            nested_changed |= pass.rewrite_lvalue(&mut target);
            let HirLValue::Local(rewritten) = target else {
                panic!("a protected local root release must retain local binding identity");
            };
            *local = rewritten;
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
    let mut metadata_changed = false;
    if let (Some(original_targets), HirStmt::Assign(assign)) = (original_assign_targets, &mut *stmt)
        && assign.targets != original_targets
    {
        assign.generic_for_initializer_producer = None;
        metadata_changed = true;
    }
    if let (Some(original_iterator), HirStmt::GenericFor(generic_for)) =
        (original_generic_for_iterator, &mut *stmt)
        && generic_for.iterator != original_iterator
    {
        metadata_changed |= generic_for.retain_unchanged_initializer_spans(&original_iterator);
    }
    stmt_changed || nested_changed || metadata_changed || prefix_changed
}

pub(super) fn rewrite_lvalue(lvalue: &mut HirLValue, pass: &mut impl HirRewritePass) -> bool {
    let mut nested_changed = false;
    traverse_hir_lvalue_children!(lvalue, borrow = [&mut], expr(expr) => {
        nested_changed |= rewrite_expr(expr, pass);
    });

    let lvalue_changed = pass.rewrite_lvalue(lvalue);
    lvalue_changed || nested_changed
}

fn rewrite_call_expr(call: &mut HirCallExpr, pass: &mut impl HirRewritePass) -> bool {
    let mut nested_changed = false;
    traverse_hir_call_children!(
        call,
        iter = iter_mut,
        borrow = [&mut],
        expr(expr) => {
            nested_changed |= rewrite_expr(expr, pass);
        },
        tail_call(call) => {
            nested_changed |= rewrite_call_expr(call, pass);
        }
    );
    let call_changed = pass.rewrite_call(call);
    call_changed || nested_changed
}

pub(super) fn rewrite_expr(expr: &mut HirExpr, pass: &mut impl HirRewritePass) -> bool {
    let prefix_changed = pass.rewrite_expr_before_children(expr);
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
        },
        capture(capture) => {
            nested_changed |= pass.rewrite_capture(capture);
        }
    );

    let expr_changed = pass.rewrite_expr(expr);
    expr_changed || nested_changed || prefix_changed
}

fn rewrite_decision_expr(decision: &mut HirDecisionExpr, pass: &mut impl HirRewritePass) -> bool {
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
        },
        tail_call(call) => {
            changed |= rewrite_call_expr(call, pass);
        }
    );
    changed
}

fn rewrite_condition_expr(expr: &mut HirExpr, pass: &mut impl HirRewritePass) -> bool {
    let prefix_changed = pass.rewrite_condition_expr_before_children(expr);
    let nested_changed = rewrite_expr(expr, pass);
    pass.rewrite_condition_expr(expr) || nested_changed || prefix_changed
}
