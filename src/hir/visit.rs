//! 这个文件提供 HIR 及其消费者共享的只读 visitor。
//!
//! HIR pass 和 AST lowering 在真正改写前，需要遍历当前 HIR 快照收集事实，例如：
//! - 哪些 label 仍然被 `goto` 引用
//! - 哪些 temp 在当前 proto 里有显式定义
//! - 某段 stmt 切片里还会读到哪些 local/temp
//!
//! `block/stmt/lvalue/call/expr` 子节点关系只由 HIR traverse 宏定义，collector 只声明
//! "看到某个节点时记录什么"。例如 `x = f(t); return t` 可收集到一次 callee 和两次 temp
//! 引用；不得在 AST 另写一套 HIR 遍历并重新解释 pack 或 closure 子节点。
//!
//! 它不会跨层补事实，也不会主动进入子 proto 的 body 重新扫描整棵模块树；这里的
//! 作用域就是当前这一个 proto。closure 仅投影 capture 的父级绑定引用。
//! capture hook 持有 mode 与 binding，默认访问一次引用叶子；读取分析可以只进入 ByValue，
//! 例如 `f(x, function() return x end)` 的直接 x 读取不会被 ByReference capture 抵消。
//! `any_expr` 按同一子节点骨架进行先序短路查询，命中后不访问剩余子树；包含所有
//! Decision 节点和 capture binding，不把语法引用查询解释为运行可达性或子 proto 扫描。
//! local root release 默认作为逻辑 local 写暴露；分析 VM home 的 collector 必须单独
//! 消费该事件，不得从旧 local 的来源槽位推导一次物理覆盖。
//! 独立 collector 可组成 tuple 共用遍历；如读集合和写事件一次收集，capture 与 release
//! 仍逐个交给原 hook，不能由组合器统一解释其语义。

use crate::hir::common::{
    HirBlock, HirCallExpr, HirCapture, HirDecisionExpr, HirExpr, HirLValue, HirProto, HirStmt,
    HirTableConstructor, LocalId,
};

use crate::hir::traverse::{
    traverse_hir_call_children, traverse_hir_decision_children, traverse_hir_expr_children,
    traverse_hir_lvalue_children, traverse_hir_stmt_children,
    traverse_hir_table_constructor_children,
};

pub(crate) trait HirVisitor {
    fn visit_block(&mut self, _block: &HirBlock) {}

    fn visit_stmt(&mut self, _stmt: &HirStmt) {}

    fn visit_expr(&mut self, _expr: &HirExpr) {}

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

/// 独立事实收集器共用一次遍历；每个 hook 都交给原收集器，保留各自的 capture/release 语义。
impl<A: HirVisitor, B: HirVisitor> HirVisitor for (A, B) {
    fn visit_block(&mut self, block: &HirBlock) {
        self.0.visit_block(block);
        self.1.visit_block(block);
    }

    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.0.visit_stmt(stmt);
        self.1.visit_stmt(stmt);
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        self.0.visit_expr(expr);
        self.1.visit_expr(expr);
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.0.visit_lvalue(lvalue);
        self.1.visit_lvalue(lvalue);
    }

    fn visit_local_root_release(&mut self, local: LocalId) {
        self.0.visit_local_root_release(local);
        self.1.visit_local_root_release(local);
    }

    fn visit_call(&mut self, call: &HirCallExpr) {
        self.0.visit_call(call);
        self.1.visit_call(call);
    }

    fn visit_capture(&mut self, capture: &HirCapture) {
        self.0.visit_capture(capture);
        self.1.visit_capture(capture);
    }
}

pub(crate) fn visit_proto(proto: &HirProto, visitor: &mut impl HirVisitor) {
    visit_block(&proto.body, visitor);
}

pub(crate) fn visit_block(block: &HirBlock, visitor: &mut impl HirVisitor) {
    visitor.visit_block(block);
    visit_stmts(&block.stmts, visitor);
}

pub(crate) fn visit_stmts(stmts: &[HirStmt], visitor: &mut impl HirVisitor) {
    for stmt in stmts {
        visit_stmt(stmt, visitor);
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
        release(local) => { visitor.visit_local_root_release(*local); },
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

/// 只访问本语句的求值部分；嵌套 block 由控制流图在各自的节点访问。
pub(crate) fn visit_stmt_header(stmt: &HirStmt, visitor: &mut impl HirVisitor) {
    visitor.visit_stmt(stmt);
    traverse_hir_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(expr) => { visit_expr(expr, visitor); },
        lvalue(lvalue) => { visit_lvalue(lvalue, visitor); },
        release(local) => { visitor.visit_local_root_release(*local); },
        block(_block) => {},
        call(call) => { visit_call(call, visitor); },
        condition(cond) => { visit_expr(cond, visitor); }
    );
}

pub(crate) fn visit_call(call: &HirCallExpr, visitor: &mut impl HirVisitor) {
    visitor.visit_call(call);
    traverse_hir_call_children!(call, iter = iter, borrow = [&], expr(expr) => {
        visit_expr(expr, visitor);
    });
}

pub(crate) fn visit_lvalue(lvalue: &HirLValue, visitor: &mut impl HirVisitor) {
    visitor.visit_lvalue(lvalue);
    traverse_hir_lvalue_children!(lvalue, borrow = [&], expr(expr) => {
        visit_expr(expr, visitor);
    });
}

pub(crate) fn visit_expr(expr: &HirExpr, visitor: &mut impl HirVisitor) {
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
        },
        capture(capture) => {
            visitor.visit_capture(capture);
        }
    );
}

/// 查询当前表达式及其语法子表达式；不沿 Decision 的 Node 引用重复展开共享节点。
pub(crate) fn any_expr(expr: &HirExpr, predicate: &mut impl FnMut(&HirExpr) -> bool) -> bool {
    if predicate(expr) {
        return true;
    }
    traverse_hir_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(child) => {
            if any_expr(child, predicate) { return true; }
        },
        call(call) => {
            traverse_hir_call_children!(call, iter = iter, borrow = [&], expr(child) => {
                if any_expr(child, predicate) { return true; }
            });
        },
        decision(decision) => {
            traverse_hir_decision_children!(
                decision, iter = iter, borrow = [&],
                expr(child) => { if any_expr(child, predicate) { return true; } },
                condition(child) => { if any_expr(child, predicate) { return true; } }
            );
        },
        table_constructor(table) => {
            traverse_hir_table_constructor_children!(
                table, iter = iter, opt = as_ref, borrow = [&],
                expr(child) => { if any_expr(child, predicate) { return true; } }
            );
        },
        capture(capture) => {
            if predicate(&capture.binding.expr()) { return true; }
        }
    );
    false
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
