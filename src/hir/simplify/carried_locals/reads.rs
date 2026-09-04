//! carried binding 读取与 mention 事实的只读收集器。
//!
//! 读取事实用于判断 handoff seed 是否只依赖单个 carried 状态、suffix 是否仍观察旧
//! binding；mention 事实同时覆盖直接左值，用于保护子块之外仍存活的 source/target。
//! 它不判断写入安全性，也不执行 rewrite。
//! 存在性查询复用这些身份集合，不统计出现次数；只声明 binding 的字段不属于读取或
//! 直接左值。capture 值遵循共享 HIR visitor 的遍历边界，仍计入对应身份集合。
//!
//! 例子：
//! - 输入表达式：`state + 1`
//! - 输出事实：读取了唯一 carried binding `state`

use std::collections::BTreeSet;

use crate::hir::common::{HirExpr, HirLValue, HirStmt};

use super::binding::{CarryBinding, carry_binding_from_expr, carry_binding_from_lvalue};
use crate::hir::visit::{HirVisitor, visit_expr, visit_stmts};

pub(super) fn collect_binding_mentions_by_stmt(stmts: &[HirStmt]) -> Vec<BTreeSet<CarryBinding>> {
    stmts
        .iter()
        .map(|stmt| collect_binding_mentions_in_stmts(std::slice::from_ref(stmt)))
        .collect()
}

fn collect_binding_mentions_in_stmts(stmts: &[HirStmt]) -> BTreeSet<CarryBinding> {
    let mut collector = BindingMentionCollector::default();
    visit_stmts(stmts, &mut collector);
    collector.mentions
}

pub(super) fn binding_is_mentioned_in_stmts(stmts: &[HirStmt], binding: CarryBinding) -> bool {
    collect_binding_mentions_in_stmts(stmts).contains(&binding)
}

pub(super) fn bindings_are_mentioned_in_stmts(
    stmts: &[HirStmt],
    bindings: &[CarryBinding],
) -> bool {
    let mentions = collect_binding_mentions_in_stmts(stmts);
    bindings.iter().any(|binding| mentions.contains(binding))
}

pub(super) fn bindings_are_mentioned_in_exprs<'a>(
    exprs: impl IntoIterator<Item = &'a HirExpr>,
    bindings: &[CarryBinding],
) -> bool {
    let mut collector = BindingReadCollector::default();
    for expr in exprs {
        collector.collect_expr(expr);
    }
    bindings
        .iter()
        .any(|binding| collector.reads.contains(binding))
}

pub(super) fn collect_binding_mentions_in_expr(expr: &HirExpr) -> BTreeSet<CarryBinding> {
    let mut collector = BindingMentionCollector::default();
    visit_expr(expr, &mut collector);
    collector.mentions
}

#[derive(Default)]
pub(super) struct BindingReadCollector {
    pub(super) reads: BTreeSet<CarryBinding>,
}

impl BindingReadCollector {
    pub(super) fn collect_stmts(&mut self, stmts: &[HirStmt]) {
        visit_stmts(stmts, self);
    }

    pub(super) fn collect_expr(&mut self, expr: &HirExpr) {
        visit_expr(expr, self);
    }

    pub(super) fn single_read(&self) -> Option<CarryBinding> {
        let mut reads = self.reads.iter();
        let read = *reads.next()?;
        reads.next().is_none().then_some(read)
    }
}

impl HirVisitor for BindingReadCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let Some(binding) = carry_binding_from_expr(expr) {
            self.reads.insert(binding);
        }
    }
}

#[derive(Default)]
struct BindingMentionCollector {
    mentions: BTreeSet<CarryBinding>,
}

impl HirVisitor for BindingMentionCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let Some(binding) = carry_binding_from_expr(expr) {
            self.mentions.insert(binding);
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let Some(binding) = carry_binding_from_lvalue(lvalue) {
            self.mentions.insert(binding);
        }
    }
}
