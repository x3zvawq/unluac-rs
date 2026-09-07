//! 这个文件承载 temp 引用检测相关的纯查询工具。
//!
//! `locals` pass 在构建提升计划时需要回答一系列关于 temp 引用的问题：
//! - 一段语句中是否存在对某个/某些 temp 的引用？
//! - 某个 temp 在当前位置之后只出现于哪些语句？
//! - 某条语句是否只在控制头部（条件表达式）处消费了 temp，body 内不再引用？
//! - 某条语句的子树中是否包含 goto/label/continue 等非局部控制流？
//! - 递归进入子作用域时，外层前缀/后缀还保护着哪些 temp？
//!
//! 这些查询都是只读的，不会修改 HIR 结构。按 temp 建立的 occurrence index 让候选扩张
//! 只访问真实 touch 语句，不必为每个定义重复扫描完整后缀；独立提取也让 `locals.rs`
//! 的主体逻辑更聚焦于提升决策本身。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirProto, HirStmt, TempId};

use crate::hir::visit::{HirVisitor, visit_expr, visit_proto, visit_stmts};

pub(super) fn stmts_touch_any_temp(stmts: &[HirStmt], temps: &BTreeSet<TempId>) -> bool {
    TempTouchCollector::touches_in_stmts(stmts, temps)
}

pub(super) fn expr_touches_any_temp(expr: &HirExpr, temps: &BTreeSet<TempId>) -> bool {
    crate::hir::visit::any_expr(
        expr,
        &mut |expr| matches!(expr, HirExpr::TempRef(temp) if temps.contains(temp)),
    )
}

pub(super) fn collect_temp_refs_in_expr(expr: &HirExpr) -> BTreeSet<TempId> {
    let mut collector = TempRefCollector {
        temps: BTreeSet::new(),
    };
    visit_expr(expr, &mut collector);
    collector.temps
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
        HirStmt::LocalRootRelease(_) => false,
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
        | HirStmt::GlobalDecl(_)
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
        | HirStmt::Block(_) => false,
    }
}

pub(super) fn stmt_contains_nested_nonlocal_control(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::LocalRootRelease(_) => false,
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
        HirStmt::Goto(_) | HirStmt::Label(_) => true,
        HirStmt::LocalDecl(_)
        | HirStmt::GlobalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue => false,
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

pub(super) fn collect_temp_reads_by_stmt(stmts: &[HirStmt]) -> Vec<BTreeSet<TempId>> {
    stmts
        .iter()
        .map(|stmt| collect_temp_reads_in_stmts(std::slice::from_ref(stmt)))
        .collect()
}

pub(super) fn collect_temp_reads_in_proto(proto: &HirProto) -> BTreeSet<TempId> {
    let mut collector = TempReadCollector::default();
    visit_proto(proto, &mut collector);
    collector.temps
}

fn collect_temp_reads_in_stmts(stmts: &[HirStmt]) -> BTreeSet<TempId> {
    let mut collector = TempReadCollector::default();
    visit_stmts(stmts, &mut collector);
    collector.temps
}

/// temp 的语句位置；读或提及的角色由输入集合定义。
pub(super) type TempTouchIndex = crate::graph::PositionIndex<TempId>;

/// 以每条语句的引用集合增量维护当前语句之外仍需保护的身份。
///
/// locals 在本次声明规划期间冻结语句引用，按进入/离开当前语句维护外部 temp 保护。
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

    pub(super) fn suffix_contains(&self, reference: TempId) -> bool {
        self.suffix_ref_counts.contains_key(&reference)
    }

    pub(super) fn prefix_contains(&self, reference: TempId) -> bool {
        self.prefix_refs.contains(&reference)
    }
}

struct TempRefCollector {
    temps: BTreeSet<TempId>,
}

#[derive(Default)]
struct TempReadCollector {
    temps: BTreeSet<TempId>,
}

impl HirVisitor for TempReadCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::TempRef(temp) = expr {
            self.temps.insert(*temp);
        }
    }
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
