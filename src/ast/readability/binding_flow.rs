//! 这个文件集中承载 AST readability 里的局部 binding 流分析工具。
//!
//! 这些 pass 经常需要回答同一类问题：
//! - 某个 binding 在一段语句里还会不会再被读取？
//! - 某个语句实际提到了哪些 binding（包括赋值目标这种 mention，而不只是读取）？
//! - 某个语句/块会不会提前引用一组待下沉的 hoisted local？
//! - 某个 binding 在当前函数体里一共被用了几次？
//! - repeat body 之后的 until 条件会不会继续读取正文 local？
//!
//! 这里故意把“当前函数体”作为边界，不继续钻进嵌套函数体。
//! 原因是 HIR-origin LocalId 与已物化 HirTemp 仍按函数局部编号，跨闭包继续统计
//! 很容易把不同函数里碰巧同号的 binding 错算成同一个变量。
//! 但 `FunctionExpr.captured_bindings` 是闭包创建时对当前词法 binding 的显式引用，
//! 必须按当前语句的一次使用统计，否则后续 pass 可能误删仍被闭包持有的局部。

mod refs;
mod writes;

pub(super) use writes::BindingWriteIndex;

use std::collections::{BTreeMap, BTreeSet};
use std::ops::ControlFlow;

use super::super::common::{
    AstBindingRef, AstBlock, AstExpr, AstFunctionExpr, AstNameRef, AstStmt,
};
use crate::ast::visit::{self, AstVisitor, NameAccess};

pub(super) use refs::{
    BindingRefSet, block_references_binding_set, expr_has_binding_read, expr_reads_binding,
    expr_references_any_binding, expr_references_binding_set, expr_uses_binding,
    stmt_references_binding_set, stmt_uses_binding, stmt_writes_name,
};

pub(super) type MutableSnapshotNames = BTreeSet<AstNameRef>;

pub(super) fn mutable_snapshot_names_in_block(block: &AstBlock) -> MutableSnapshotNames {
    #[derive(Default)]
    struct CaptureWriteCollector(MutableSnapshotNames);

    impl crate::ast::visit::AstVisitor for CaptureWriteCollector {
        fn visit_function_expr(&mut self, function: &AstFunctionExpr) -> bool {
            self.0.extend(function.capture_write_names.iter().cloned());
            false
        }
    }

    let mut collector = CaptureWriteCollector::default();
    crate::ast::visit::visit_block(block, &mut collector);
    collector.0
}

#[derive(Debug, Default, Clone)]
pub(super) struct BindingUseIndex {
    stmt_len: usize,
    stmt_counts: Vec<BTreeMap<AstBindingRef, usize>>,
    suffix_counts: BTreeMap<AstBindingRef, BindingUseSuffixCounts>,
}

#[derive(Debug, Clone)]
struct BindingUseSuffixCounts {
    stmt_indices: Vec<usize>,
    suffix_totals: Vec<usize>,
}

impl BindingUseIndex {
    pub(super) fn for_stmts(stmts: &[AstStmt]) -> Self {
        Self::for_stmts_with_trailing_expr(stmts, None)
    }

    pub(super) fn for_stmts_with_trailing_expr(
        stmts: &[AstStmt],
        trailing_expr: Option<&AstExpr>,
    ) -> Self {
        let stmt_len = stmts.len() + usize::from(trailing_expr.is_some());
        let mut stmt_counts = Vec::with_capacity(stmt_len);
        let mut occurrences = BTreeMap::<AstBindingRef, Vec<(usize, usize)>>::new();

        for (stmt_index, stmt) in stmts.iter().enumerate() {
            let mut counts = BTreeMap::new();
            visit::visit_stmt(stmt, &mut use_collector(&mut counts));
            for (&binding, &count) in &counts {
                occurrences
                    .entry(binding)
                    .or_default()
                    .push((stmt_index, count));
            }
            stmt_counts.push(counts);
        }

        if let Some(expr) = trailing_expr {
            let stmt_index = stmts.len();
            let mut counts = BTreeMap::new();
            visit::visit_expr(expr, &mut use_collector(&mut counts));
            for (&binding, &count) in &counts {
                occurrences
                    .entry(binding)
                    .or_default()
                    .push((stmt_index, count));
            }
            stmt_counts.push(counts);
        }

        let suffix_counts = occurrences
            .into_iter()
            .map(|(binding, entries)| {
                let mut stmt_indices = Vec::with_capacity(entries.len());
                let mut suffix_totals = Vec::with_capacity(entries.len());
                let mut running_total = 0usize;

                for (stmt_index, count) in entries.iter().rev() {
                    running_total += *count;
                    stmt_indices.push(*stmt_index);
                    suffix_totals.push(running_total);
                }

                stmt_indices.reverse();
                suffix_totals.reverse();

                (
                    binding,
                    BindingUseSuffixCounts {
                        stmt_indices,
                        suffix_totals,
                    },
                )
            })
            .collect();

        Self {
            stmt_len,
            stmt_counts,
            suffix_counts,
        }
    }

    pub(super) fn count_uses_in_suffix(&self, start: usize, binding: AstBindingRef) -> usize {
        if start >= self.stmt_len {
            return 0;
        }

        let Some(counts) = self.suffix_counts.get(&binding) else {
            return 0;
        };
        let first_suffix_stmt = counts
            .stmt_indices
            .partition_point(|stmt_index| *stmt_index < start);
        counts
            .suffix_totals
            .get(first_suffix_stmt)
            .copied()
            .unwrap_or(0)
    }

    /// 返回 suffix 中所有承载该 binding 读取的顶层语句索引。
    ///
    /// 同一语句内的多次读取只出现一个索引；trailing expression 仍以末尾虚拟语句表示。
    pub(super) fn use_stmt_indices_in_suffix(
        &self,
        start: usize,
        binding: AstBindingRef,
    ) -> &[usize] {
        let Some(counts) = self.suffix_counts.get(&binding) else {
            return &[];
        };
        let index = counts
            .stmt_indices
            .partition_point(|stmt_index| *stmt_index < start);
        &counts.stmt_indices[index..]
    }

    pub(super) fn count_uses_in_range(
        &self,
        start: usize,
        end: usize,
        binding: AstBindingRef,
    ) -> usize {
        if start >= end {
            return 0;
        }
        self.count_uses_in_suffix(start, binding) - self.count_uses_in_suffix(end, binding)
    }

    pub(super) fn uses_in_stmt_index(
        &self,
        stmt_index: usize,
    ) -> impl Iterator<Item = (AstBindingRef, usize)> + '_ {
        self.stmt_counts
            .get(stmt_index)
            .into_iter()
            .flat_map(|counts| counts.iter().map(|(binding, count)| (*binding, *count)))
    }
}

pub(super) fn binding_mentions_in_stmt(stmt: &AstStmt) -> BTreeSet<AstBindingRef> {
    let mut mentions = BTreeSet::new();
    visit::visit_stmt(
        stmt,
        &mut BindingCollector(|binding, _| {
            mentions.insert(binding);
        }),
    );
    mentions
}

pub(super) fn binding_mentions_in_block(block: &AstBlock) -> BTreeSet<AstBindingRef> {
    let mut mentions = BTreeSet::new();
    visit::visit_block(
        block,
        &mut BindingCollector(|binding, _| {
            mentions.insert(binding);
        }),
    );
    mentions
}

pub(super) fn binding_mentions_in_expr(expr: &AstExpr) -> BTreeSet<AstBindingRef> {
    let mut mentions = BTreeSet::new();
    visit::visit_expr(
        expr,
        &mut BindingCollector(|binding, _| {
            mentions.insert(binding);
        }),
    );
    mentions
}

struct BindingCollector<F>(F);

impl<F: FnMut(AstBindingRef, NameAccess)> AstVisitor for BindingCollector<F> {
    fn visit_name(&mut self, name: &AstNameRef, access: NameAccess) -> ControlFlow<()> {
        if let Some(binding) = AstBindingRef::from_name_ref(name) {
            self.0(binding, access);
        }
        ControlFlow::Continue(())
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        false
    }
}

fn use_collector(counts: &mut BTreeMap<AstBindingRef, usize>) -> impl AstVisitor + '_ {
    BindingCollector(|binding, access| {
        if matches!(access, NameAccess::Read | NameAccess::Capture) {
            *counts.entry(binding).or_default() += 1;
        }
    })
}
