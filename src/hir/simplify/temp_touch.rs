//! 这个文件承载 temp 引用检测相关的纯查询工具。
//!
//! `locals` pass 在构建提升计划时需要回答一系列关于 temp 引用的问题：
//! - 一段语句中是否存在对某个/某些 temp 的引用？
//! - 某条语句是否只在控制头部（条件表达式）处消费了 temp，body 内不再引用？
//! - 某条语句的子树中是否包含 goto/label/continue 等非局部控制流？
//! - 递归进入子作用域时，外层前缀/后缀还保护着哪些 temp？
//!
//! 这些查询都是只读的，不会修改 HIR 结构，因此独立提取出来
//! 既方便复用，也让 `locals.rs` 的主体逻辑更聚焦于提升决策本身。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirStmt, TempId};

use super::visit::{HirVisitor, visit_expr, visit_stmts};

pub(super) fn stmts_touch_any_temp(stmts: &[HirStmt], temps: &BTreeSet<TempId>) -> bool {
    TempTouchCollector::touches_in_stmts(stmts, temps)
}

pub(super) fn expr_touches_any_temp(expr: &HirExpr, temps: &BTreeSet<TempId>) -> bool {
    TempTouchCollector::touches_in_expr(expr, temps)
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

struct TempTouchCollector<'a> {
    temps: &'a BTreeSet<TempId>,
    touched: bool,
}

impl<'a> TempTouchCollector<'a> {
    fn touches_in_stmts(stmts: &[HirStmt], temps: &'a BTreeSet<TempId>) -> bool {
        let mut collector = Self {
            temps,
            touched: false,
        };
        visit_stmts(stmts, &mut collector);
        collector.touched
    }

    fn touches_in_expr(expr: &HirExpr, temps: &'a BTreeSet<TempId>) -> bool {
        let mut collector = Self {
            temps,
            touched: false,
        };
        visit_expr(expr, &mut collector);
        collector.touched
    }
}

impl HirVisitor for TempTouchCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::TempRef(temp) = expr {
            self.touched |= self.temps.contains(temp);
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let HirLValue::Temp(temp) = lvalue {
            self.touched |= self.temps.contains(temp);
        }
    }
}

// ── temp 引用收集 ────────────────────────────────────────────────────

/// 收集一段语句中所有被引用的 TempId（含读和写，深入子作用域）。
///
/// 用于 locals pass 计算"外层仍然在用的 temp 集合"，防止子作用域
/// 错误地将跨作用域存活的 temp 提升为块级局部变量。
pub(super) fn collect_temp_refs_in_stmts(stmts: &[HirStmt]) -> BTreeSet<TempId> {
    let mut collector = TempRefCollector {
        temps: BTreeSet::new(),
    };
    visit_stmts(stmts, &mut collector);
    collector.temps
}

pub(super) fn collect_temp_refs_by_stmt(stmts: &[HirStmt]) -> Vec<BTreeSet<TempId>> {
    stmts
        .iter()
        .map(|stmt| collect_temp_refs_in_stmts(std::slice::from_ref(stmt)))
        .collect()
}

pub(super) struct TempTouchIndex<'a> {
    stmt_refs: &'a [BTreeSet<TempId>],
    indices_by_temp: BTreeMap<TempId, Vec<usize>>,
}

impl<'a> TempTouchIndex<'a> {
    pub(super) fn new(stmt_refs: &'a [BTreeSet<TempId>]) -> Self {
        let mut indices_by_temp = BTreeMap::<TempId, Vec<usize>>::new();
        for (index, refs) in stmt_refs.iter().enumerate() {
            for temp in refs {
                indices_by_temp.entry(*temp).or_default().push(index);
            }
        }

        Self {
            stmt_refs,
            indices_by_temp,
        }
    }

    pub(super) fn touches_before(&self, end: usize, temp: TempId) -> bool {
        self.touches_in_range(0, end, temp)
    }

    pub(super) fn touches_after(&self, start: usize, temp: TempId) -> bool {
        self.touches_in_range(start, self.stmt_refs.len(), temp)
    }

    pub(super) fn touches_in_range(&self, start: usize, end: usize, temp: TempId) -> bool {
        let Some(indices) = self.indices_by_temp.get(&temp) else {
            return false;
        };
        let offset = indices.partition_point(|index| *index < start);
        indices.get(offset).is_some_and(|index| *index < end)
    }

    pub(super) fn stmt_touches_any(&self, index: usize, temps: &BTreeSet<TempId>) -> bool {
        self.stmt_refs[index]
            .iter()
            .any(|temp| temps.contains(temp))
    }
}

pub(super) struct TempRefScopeTracker<'a> {
    stmt_refs: &'a [BTreeSet<TempId>],
    suffix_ref_counts: BTreeMap<TempId, usize>,
    prefix_refs: BTreeSet<TempId>,
}

impl<'a> TempRefScopeTracker<'a> {
    pub(super) fn new(stmt_refs: &'a [BTreeSet<TempId>]) -> Self {
        let mut suffix_ref_counts = BTreeMap::new();
        for refs in stmt_refs {
            for temp in refs {
                *suffix_ref_counts.entry(*temp).or_insert(0) += 1;
            }
        }

        Self {
            stmt_refs,
            suffix_ref_counts,
            prefix_refs: BTreeSet::new(),
        }
    }

    pub(super) fn len(&self) -> usize {
        self.stmt_refs.len()
    }

    pub(super) fn enter_stmt(&mut self, index: usize) {
        for temp in &self.stmt_refs[index] {
            let count = self
                .suffix_ref_counts
                .get_mut(temp)
                .expect("stmt temp refs must be counted in suffix");
            *count -= 1;
            if *count == 0 {
                self.suffix_ref_counts.remove(temp);
            }
        }
    }

    pub(super) fn leave_stmt(&mut self, index: usize) {
        self.prefix_refs
            .extend(self.stmt_refs[index].iter().copied());
    }

    pub(super) fn outer_with_suffix(&self, inherited: &BTreeSet<TempId>) -> BTreeSet<TempId> {
        inherited
            .iter()
            .copied()
            .chain(self.suffix_ref_counts.keys().copied())
            .collect()
    }

    pub(super) fn outer_with_prefix_and_suffix(
        &self,
        inherited: &BTreeSet<TempId>,
    ) -> BTreeSet<TempId> {
        inherited
            .iter()
            .copied()
            .chain(self.prefix_refs.iter().copied())
            .chain(self.suffix_ref_counts.keys().copied())
            .collect()
    }
}

struct TempRefCollector {
    temps: BTreeSet<TempId>,
}

impl HirVisitor for TempRefCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::TempRef(temp) = expr {
            self.temps.insert(*temp);
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let HirLValue::Temp(temp) = lvalue {
            self.temps.insert(*temp);
        }
    }
}
