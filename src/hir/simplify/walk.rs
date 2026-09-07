//! 这个文件提供 HIR simplify pass 共享的递归 walker。
//!
//! 很多 simplify pass 都只是"后序遍历整棵 HIR，然后在局部 block/stmt/expr 上做保守
//! 重写"。如果每个 pass 都各自维护一套 `block/stmt/lvalue/call/expr` 骨架，后面一旦
//! 新增 HIR 节点或调整遍历顺序，就得在多处同步返工。
//!
//! `HirRewritePass` 统一提供 block/stmt/expr 等回调，pass 只实现自己负责的改写。
//! block 入口允许直接借用 proto 的只读事实并独立修改 body，不为可变借用复制元数据。
//!
//! 它不会替具体 pass 决定"哪些节点该改、哪些事实可信"；这些语义仍然由各个 pass
//! 自己负责。这个文件只统一递归顺序和进入子节点的边界，避免不同 pass 各自长出
//! 一套不一致的 walker。generic-for operand 改写只撤销对应 producer span，未变的区间
//! 继续保留 lowering 证明；例如替换 callee 不会抹掉另一段 nil initializer 的身份。
//!
//! 例子：
//! - `logical_simplify` 实现表达式与条件回调，区分值语境与 truthiness 语境
//! - `dead_labels` 这类要在整段 block 上做删改的 pass，则实现 `HirRewritePass`
//! - `close_scopes / decision-eliminate` 这类自带 block rebuild 的 pass，则可以只复用
//!   下面的 `for_each_nested_block_mut / rewrite_nested_blocks_in_stmt`

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

    fn rewrite_expr(&mut self, _expr: &mut HirExpr) -> bool {
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
    stmt_changed || nested_changed || metadata_changed
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
    expr_changed || nested_changed
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
    let nested_changed = rewrite_expr(expr, pass);
    pass.rewrite_condition_expr(expr) || nested_changed
}
