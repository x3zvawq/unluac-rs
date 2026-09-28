//! HIR 共用的只读 visitor 与短路查询。
//!
//! 子节点由 traverse 统一定义，closure 只投影父级 capture，不进入 child body。

use crate::hir::common::{
    HirBlock, HirCallExpr, HirCapture, HirClosureExpr, HirDecisionExpr, HirExpr, HirLValue,
    HirProto, HirStmt, HirTableConstructor, LocalId,
};

use crate::hir::traverse::{
    traverse_hir_call_children, traverse_hir_decision_children, traverse_hir_expr_children,
    traverse_hir_lvalue_children, traverse_hir_stmt_children,
    traverse_hir_table_constructor_children,
};

pub(crate) trait HirVisitor<'hir> {
    /// 本次查询已完成；返回 true 后不再接收节点，完整事实收集器保持默认 false。
    fn is_complete(&self) -> bool {
        false
    }

    fn visit_block(&mut self, _block: &HirBlock) {}

    fn visit_stmt(&mut self, _stmt: &HirStmt) {}

    fn visit_expr(&mut self, _expr: &HirExpr) {}

    /// 真实 HIR 节点的稳定借用；capture 的临时 binding 叶子不经过此 hook。
    /// expr/lvalue 默认投影可产生临时叶子，只有这里的真实 closure 可被保存为树节点引用。
    fn visit_closure(&mut self, _closure: &'hir HirClosureExpr) {}

    fn visit_lvalue(&mut self, _lvalue: &HirLValue) {}

    /// 释放源码 local 的额外根，保持逻辑写入与 VM home 覆盖的区别。
    fn visit_local_root_release(&mut self, local: LocalId) {
        self.visit_lvalue(&HirLValue::Local(local));
    }

    fn visit_call(&mut self, _call: &HirCallExpr) {}

    /// capture 是带模式的父级绑定事件；重载者负责决定是否观察这次引用。
    fn visit_capture(&mut self, capture: &HirCapture)
    where
        Self: Sized,
    {
        self.visit_expr(&capture.binding.expr());
    }
}

// 同一 hook 只委派给仍在收集的分量，避免各事件的完成规则漂移。
macro_rules! visit_active_pair {
    ($($method:ident($arg:ident: $ty:ty)),* $(,)?) => {
        $(fn $method(&mut self, $arg: $ty) {
            if !self.0.is_complete() { self.0.$method($arg); }
            if !self.1.is_complete() { self.1.$method($arg); }
        })*
    };
}

/// 独立事实收集器共用一次遍历；每个 hook 都交给原收集器，保留各自的 capture/release 语义。
/// 已完成的分量停止接收事件，但必须等全部完成才结束遍历；例如 effects 已命中时，
/// 写集合仍需收齐后续节点。
impl<'hir, A: HirVisitor<'hir>, B: HirVisitor<'hir>> HirVisitor<'hir> for (A, B) {
    fn is_complete(&self) -> bool {
        self.0.is_complete() && self.1.is_complete()
    }

    visit_active_pair!(
        visit_block(block: &HirBlock),
        visit_stmt(stmt: &HirStmt),
        visit_expr(expr: &HirExpr),
        visit_closure(closure: &'hir HirClosureExpr),
        visit_lvalue(lvalue: &HirLValue),
        visit_local_root_release(local: LocalId),
        visit_call(call: &HirCallExpr),
        visit_capture(capture: &HirCapture),
    );
}

// 子节点宏中的 return 退出当前 walker，避免命中后仍枚举宽表或 value-pack 的剩余成员。
macro_rules! visit_next {
    ($visitor:ident, $visit:expr) => {
        if $visitor.is_complete() {
            return;
        }
        $visit;
        if $visitor.is_complete() {
            return;
        }
    };
}

pub(crate) fn visit_proto<'hir>(proto: &'hir HirProto, visitor: &mut impl HirVisitor<'hir>) {
    visit_next!(visitor, visit_block(&proto.body, visitor));
}

pub(crate) fn visit_block<'hir>(block: &'hir HirBlock, visitor: &mut impl HirVisitor<'hir>) {
    visit_next!(visitor, visitor.visit_block(block));
    visit_next!(visitor, visit_stmts(&block.stmts, visitor));
}

pub(crate) fn visit_stmts<'hir>(stmts: &'hir [HirStmt], visitor: &mut impl HirVisitor<'hir>) {
    for stmt in stmts {
        visit_next!(visitor, visit_stmt(stmt, visitor));
    }
}

/// 只枚举直属控制块，与可变 walker 共享子节点顺序；不进入表达式或孙级 block。
pub(crate) fn for_each_nested_block<'hir>(
    stmt: &'hir HirStmt,
    visit: &mut impl FnMut(&'hir HirBlock),
) {
    traverse_hir_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(_expr) => {},
        lvalue(_lvalue) => {},
        release(_local) => {},
        block(block) => { visit(block); },
        call(_call) => {},
        condition(_cond) => {}
    );
}

/// 只遍历语句及嵌套控制块；label 等词法事实不需要扫描求值表达式。
pub(crate) fn visit_stmt_structure(stmt: &HirStmt, visitor: &mut impl FnMut(&HirStmt)) {
    any_stmt_structure(stmt, &mut |stmt| {
        visitor(stmt);
        false
    });
}

/// 在当前 proto 的语句骨架中先序短路查询，不进入表达式或 child proto。
pub(crate) fn any_stmt_structure(
    stmt: &HirStmt,
    predicate: &mut impl FnMut(&HirStmt) -> bool,
) -> bool {
    if predicate(stmt) {
        return true;
    }
    let mut found = false;
    for_each_nested_block(stmt, &mut |block| {
        found = found
            || block
                .stmts
                .iter()
                .any(|stmt| any_stmt_structure(stmt, predicate));
    });
    found
}

fn visit_stmt<'hir>(stmt: &'hir HirStmt, visitor: &mut impl HirVisitor<'hir>) {
    visit_next!(visitor, visitor.visit_stmt(stmt));
    traverse_hir_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(expr) => {
            visit_next!(visitor, visit_expr(expr, visitor));
        },
        lvalue(lvalue) => {
            visit_next!(visitor, visit_lvalue(lvalue, visitor));
        },
        release(local) => { visit_next!(visitor, visitor.visit_local_root_release(*local)); },
        block(block) => {
            visit_next!(visitor, visit_block(block, visitor));
        },
        call(call) => {
            visit_next!(visitor, visit_call(call, visitor));
        },
        condition(cond) => {
            visit_next!(visitor, visit_expr(cond, visitor));
        }
    );
}

/// 只访问本语句的求值部分；嵌套 block 由控制流图在各自的节点访问。
pub(crate) fn visit_stmt_header<'hir>(stmt: &'hir HirStmt, visitor: &mut impl HirVisitor<'hir>) {
    visit_next!(visitor, visitor.visit_stmt(stmt));
    traverse_hir_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(expr) => { visit_next!(visitor, visit_expr(expr, visitor)); },
        lvalue(lvalue) => { visit_next!(visitor, visit_lvalue(lvalue, visitor)); },
        release(local) => { visit_next!(visitor, visitor.visit_local_root_release(*local)); },
        block(_block) => {},
        call(call) => { visit_next!(visitor, visit_call(call, visitor)); },
        condition(cond) => { visit_next!(visitor, visit_expr(cond, visitor)); }
    );
}

pub(crate) fn visit_call<'hir>(call: &'hir HirCallExpr, visitor: &mut impl HirVisitor<'hir>) {
    visit_next!(visitor, visitor.visit_call(call));
    traverse_hir_call_children!(call, iter = iter, borrow = [&], expr(expr) => {
        visit_next!(visitor, visit_expr(expr, visitor));
    });
}

pub(crate) fn visit_lvalue<'hir>(lvalue: &'hir HirLValue, visitor: &mut impl HirVisitor<'hir>) {
    visit_next!(visitor, visitor.visit_lvalue(lvalue));
    traverse_hir_lvalue_children!(lvalue, borrow = [&], expr(expr) => {
        visit_next!(visitor, visit_expr(expr, visitor));
    });
}

pub(crate) fn visit_expr<'hir>(expr: &'hir HirExpr, visitor: &mut impl HirVisitor<'hir>) {
    visit_next!(visitor, visitor.visit_expr(expr));
    if let HirExpr::Closure(closure) = expr {
        visit_next!(visitor, visitor.visit_closure(closure));
    }
    traverse_hir_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(e) => {
            visit_next!(visitor, visit_expr(e, visitor));
        },
        call(c) => {
            visit_next!(visitor, visit_call(c, visitor));
        },
        decision(d) => {
            visit_next!(visitor, visit_decision_expr(d, visitor));
        },
        table_constructor(t) => {
            visit_next!(visitor, visit_table_constructor(t, visitor));
        },
        capture(capture) => {
            visit_next!(visitor, visitor.visit_capture(capture));
        }
    );
}

/// 查询当前表达式及其语法子表达式；不沿 Decision 的 Node 引用重复展开共享节点。
pub(crate) fn any_expr(expr: &HirExpr, predicate: &mut impl FnMut(&HirExpr) -> bool) -> bool {
    struct AnyExpr<'a, F> {
        predicate: &'a mut F,
        found: bool,
    }

    impl<F: FnMut(&HirExpr) -> bool> HirVisitor<'_> for AnyExpr<'_, F> {
        fn is_complete(&self) -> bool {
            self.found
        }

        fn visit_expr(&mut self, expr: &HirExpr) {
            self.found = (self.predicate)(expr);
        }
    }

    let mut visitor = AnyExpr {
        predicate,
        found: false,
    };
    visit_expr(expr, &mut visitor);
    visitor.found
}

fn visit_decision_expr<'hir>(decision: &'hir HirDecisionExpr, visitor: &mut impl HirVisitor<'hir>) {
    traverse_hir_decision_children!(
        decision,
        iter = iter,
        borrow = [&],
        expr(e) => {
            visit_next!(visitor, visit_expr(e, visitor));
        },
        condition(cond) => {
            visit_next!(visitor, visit_expr(cond, visitor));
        }
    );
}

pub(crate) fn visit_table_constructor<'hir>(
    table: &'hir HirTableConstructor,
    visitor: &mut impl HirVisitor<'hir>,
) {
    traverse_hir_table_constructor_children!(
        table,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(e) => {
            visit_next!(visitor, visit_expr(e, visitor));
        }
    );
}
