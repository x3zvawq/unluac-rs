//! 这个文件承载 temp 引用检测相关的纯查询工具。
//!
//! `locals` pass 在构建提升计划时需要回答一系列关于 temp 引用的问题：
//! - 一段语句中是否存在对某个/某些 temp 的引用？
//! - 某条语句是否只在控制头部（条件表达式）处消费了 temp，body 内不再引用？
//! - 某条语句的子树中是否包含 goto/label/continue 等非局部控制流？
//!
//! 这些查询都是只读的，不会修改 HIR 结构，因此独立提取出来
//! 既方便复用，也让 `locals.rs` 的主体逻辑更聚焦于提升决策本身。

use std::collections::BTreeSet;

use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirStmt, TempId};

use super::visit::{HirVisitor, visit_expr, visit_stmts};

pub(super) fn stmts_touch_temp(stmts: &[HirStmt], temp: TempId) -> bool {
    TempTouchCollector::touches_in_stmts(stmts, TempTouchQuery::One(temp))
}

pub(super) fn stmts_touch_any_temp(stmts: &[HirStmt], temps: &BTreeSet<TempId>) -> bool {
    TempTouchCollector::touches_in_stmts(stmts, TempTouchQuery::Many(temps))
}

pub(super) fn stmt_touches_any_temp(stmt: &HirStmt, temps: &BTreeSet<TempId>) -> bool {
    TempTouchCollector::touches_in_stmts(std::slice::from_ref(stmt), TempTouchQuery::Many(temps))
}

pub(super) fn expr_touches_any_temp(expr: &HirExpr, temps: &BTreeSet<TempId>) -> bool {
    TempTouchCollector::touches_in_expr(expr, TempTouchQuery::Many(temps))
}

/// 判断该语句是否 **只在控制头部** 消费了某些 temp，而 body 内不再引用。
///
/// 用于提升计划构建时识别 temp 的消费边界：如果 temp 只出现在 if/while/for
/// 的条件表达式中，提升后不需要担心 body 内的引用问题。
pub(super) fn stmt_consumes_temps_only_in_control_head(
    stmt: &HirStmt,
    temps: &BTreeSet<TempId>,
) -> bool {
    match stmt {
        HirStmt::If(if_stmt) => {
            expr_touches_any_temp(&if_stmt.cond, temps)
                && !stmts_touch_any_temp(&if_stmt.then_block.stmts, temps)
                && if_stmt
                    .else_block
                    .as_ref()
                    .is_none_or(|else_block| !stmts_touch_any_temp(&else_block.stmts, temps))
        }
        HirStmt::While(while_stmt) => {
            expr_touches_any_temp(&while_stmt.cond, temps)
                && !stmts_touch_any_temp(&while_stmt.body.stmts, temps)
        }
        HirStmt::Repeat(repeat_stmt) => {
            expr_touches_any_temp(&repeat_stmt.cond, temps)
                && !stmts_touch_any_temp(&repeat_stmt.body.stmts, temps)
        }
        HirStmt::NumericFor(numeric_for) => {
            (expr_touches_any_temp(&numeric_for.start, temps)
                || expr_touches_any_temp(&numeric_for.limit, temps)
                || expr_touches_any_temp(&numeric_for.step, temps))
                && !stmts_touch_any_temp(&numeric_for.body.stmts, temps)
        }
        HirStmt::GenericFor(generic_for) => {
            generic_for
                .iterator
                .iter()
                .any(|expr| expr_touches_any_temp(expr, temps))
                && !stmts_touch_any_temp(&generic_for.body.stmts, temps)
        }
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
        | HirStmt::Label(_)
        | HirStmt::Block(_)
        | HirStmt::Unstructured(_) => false,
    }
}

pub(super) fn stmt_contains_nested_nonlocal_control(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::If(if_stmt) => {
            block_contains_nonlocal_control(&if_stmt.then_block)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(block_contains_nonlocal_control)
        }
        HirStmt::While(while_stmt) => block_contains_nonlocal_control(&while_stmt.body),
        HirStmt::Repeat(repeat_stmt) => block_contains_nonlocal_control(&repeat_stmt.body),
        HirStmt::NumericFor(numeric_for) => block_contains_nonlocal_control(&numeric_for.body),
        HirStmt::GenericFor(generic_for) => block_contains_nonlocal_control(&generic_for.body),
        HirStmt::Block(block) => block_contains_nonlocal_control(block),
        HirStmt::Unstructured(_) => true,
        HirStmt::Continue | HirStmt::Goto(_) | HirStmt::Label(_) => true,
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break => false,
    }
}

fn block_contains_nonlocal_control(block: &HirBlock) -> bool {
    block
        .stmts
        .iter()
        .any(stmt_contains_nested_nonlocal_control)
}

#[derive(Clone, Copy)]
enum TempTouchQuery<'a> {
    One(TempId),
    Many(&'a BTreeSet<TempId>),
}

impl TempTouchQuery<'_> {
    fn matches(self, temp: TempId) -> bool {
        match self {
            Self::One(expected) => expected == temp,
            Self::Many(temps) => temps.contains(&temp),
        }
    }
}

struct TempTouchCollector<'a> {
    query: TempTouchQuery<'a>,
    touched: bool,
}

impl<'a> TempTouchCollector<'a> {
    fn touches_in_stmts(stmts: &[HirStmt], query: TempTouchQuery<'a>) -> bool {
        let mut collector = Self {
            query,
            touched: false,
        };
        visit_stmts(stmts, &mut collector);
        collector.touched
    }

    fn touches_in_expr(expr: &HirExpr, query: TempTouchQuery<'a>) -> bool {
        let mut collector = Self {
            query,
            touched: false,
        };
        visit_expr(expr, &mut collector);
        collector.touched
    }
}

impl HirVisitor for TempTouchCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::TempRef(temp) = expr {
            self.touched |= self.query.matches(*temp);
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let HirLValue::Temp(temp) = lvalue {
            self.touched |= self.query.matches(*temp);
        }
    }
}
