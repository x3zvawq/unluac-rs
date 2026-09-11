//! carried binding 读取与 mention 事实的只读收集器。
//!
//! 读取事实用于判断 handoff seed 是否只依赖单个 carried 状态、suffix 是否仍观察旧
//! binding；mention 事实同时覆盖直接左值，用于保护子块之外仍存活的 source/target。
//! 它不判断写入安全性，也不执行 rewrite。
//! 存在性查询复用这些身份集合，不统计出现次数；只声明 binding 的字段不属于读取或
//! 直接左值。capture 值遵循共享 HIR visitor 的遍历边界，仍计入对应身份集合。
//! 递归保护使用一次快照中的语句先序区间：每个 header 只收集一次，父语句的区间包含
//! 全部子块；它不表示执行顺序。后序 owner 只在子块未改写时复用该快照，否则重建。
//! 例如 `do use(x) end; use(x)` 的两条语句均提及 x，查询第一条之外仍能找到 x。
//!
//! 例子：
//! - 输入表达式：`state + 1`
//! - 输出事实：读取了唯一 carried binding `state`

use std::{collections::BTreeSet, ops::Range};

use crate::graph::PositionIndex;
use crate::hir::common::{HirExpr, HirLValue, HirStmt};

use super::binding::{CarryBinding, carry_binding_from_expr, carry_binding_from_lvalue};
use crate::hir::visit::{
    HirVisitor, for_each_nested_block, visit_expr, visit_stmt_header, visit_stmts,
};

#[derive(Default)]
pub(super) struct BindingMentionIndex {
    occurrences: PositionIndex<CarryBinding>,
    blocks: Vec<BlockMentionRanges>,
}

#[derive(Default)]
struct BlockMentionRanges {
    range: Range<usize>,
    stmts: Vec<Range<usize>>,
}

impl BindingMentionIndex {
    pub(super) fn new(stmts: &[HirStmt]) -> Self {
        let mut index = Self::default();
        index.collect_block(stmts, &mut 0);
        index
    }

    fn collect_block(&mut self, stmts: &[HirStmt], next_position: &mut usize) {
        let block = self.blocks.len();
        let start = *next_position;
        self.blocks.push(BlockMentionRanges::default());
        for stmt in stmts {
            let position = *next_position;
            *next_position += 1;
            let mut collector = BindingMentionCollector::default();
            visit_stmt_header(stmt, &mut collector);
            for binding in collector.mentions {
                self.occurrences.record(binding, position);
            }
            for_each_nested_block(stmt, &mut |nested| {
                self.collect_block(&nested.stmts, next_position);
            });
            self.blocks[block].stmts.push(position..*next_position);
        }
        self.blocks[block].range = start..*next_position;
    }

    pub(super) fn blocks(&self) -> impl Iterator<Item = BlockMentions<'_>> {
        self.blocks.iter().map(|block| BlockMentions {
            occurrences: &self.occurrences,
            block,
        })
    }

    pub(super) fn root(&self) -> BlockMentions<'_> {
        BlockMentions {
            occurrences: &self.occurrences,
            block: &self.blocks[0],
        }
    }
}

/// 只借用快照，不借用可变 HIR；仅服务本次 owner 的候选批次，不跨后续 owner 复用。
#[derive(Clone, Copy)]
pub(super) struct BlockMentions<'a> {
    occurrences: &'a PositionIndex<CarryBinding>,
    block: &'a BlockMentionRanges,
}

impl BlockMentions<'_> {
    pub(super) fn outside_stmt(self, index: usize, binding: CarryBinding) -> bool {
        let stmt = &self.block.stmts[index];
        self.contains(binding, self.block.range.start..stmt.start)
            || self.contains(binding, stmt.end..self.block.range.end)
    }

    pub(super) fn first_is(self, index: usize, binding: CarryBinding) -> bool {
        let stmt = &self.block.stmts[index];
        self.contains(binding, stmt.clone())
            && !self.contains(binding, self.block.range.start..stmt.start)
    }

    pub(super) fn last_is(self, index: usize, binding: CarryBinding) -> bool {
        self.occurrences
            .last_in(&binding, self.block.range.clone())
            .is_some_and(|position| self.block.stmts[index].contains(&position))
    }

    fn contains(self, binding: CarryBinding, range: Range<usize>) -> bool {
        self.occurrences.last_in(&binding, range).is_some()
    }
}

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

impl HirVisitor<'_> for BindingReadCollector {
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

impl HirVisitor<'_> for BindingMentionCollector {
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
