//! 当前 AST 函数体的共享 binding 读取、提及与使用查询。
//!
//! 消费共享 visitor 的名字角色及显式 capture，供 Readability 判断词法依赖；
//! 不进入使用独立编号的 child function。

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
    BindingRefSet, block_captures_direct_local, block_references_binding_set,
    expr_has_binding_read, expr_reads_binding, expr_reads_name, expr_references_any_binding,
    expr_references_binding_set, expr_uses_binding, stmt_references_binding_set, stmt_uses_binding,
    stmt_writes_name,
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
        Self::collect(stmts, trailing_expr, None, None)
    }

    /// 同一快照只分派一次名字事件；尾条件只参与读取，不成为语句写入位置。
    pub(super) fn with_writes(
        stmts: &[AstStmt],
        trailing_expr: Option<&AstExpr>,
    ) -> (Self, BindingWriteIndex) {
        let mut writes = BindingWriteIndex::default();
        let uses = Self::collect(stmts, trailing_expr, Some(&mut writes), None);
        (uses, writes)
    }

    pub(super) fn with_mentions(
        stmts: &[AstStmt],
        trailing_expr: Option<&AstExpr>,
    ) -> (Self, BTreeMap<AstBindingRef, usize>) {
        let mut mentions = BTreeMap::<AstBindingRef, (usize, usize)>::new();
        let uses = Self::collect(stmts, trailing_expr, None, Some(&mut mentions));
        (
            uses,
            mentions
                .into_iter()
                .map(|(id, (_, count))| (id, count))
                .collect(),
        )
    }

    fn collect(
        stmts: &[AstStmt],
        trailing_expr: Option<&AstExpr>,
        mut writes: Option<&mut BindingWriteIndex>,
        mut mentions: Option<&mut BTreeMap<AstBindingRef, (usize, usize)>>,
    ) -> Self {
        let stmt_len = stmts.len() + usize::from(trailing_expr.is_some());
        let mut stmt_counts = vec![BTreeMap::new(); stmt_len];
        let mut occurrences = BTreeMap::<AstBindingRef, Vec<(usize, usize)>>::new();

        for (index, stmt) in stmts.iter().enumerate() {
            visit::visit_stmt(
                stmt,
                &mut IndexCollector {
                    index,
                    counts: Some(&mut stmt_counts[index]),
                    writes: writes.as_deref_mut(),
                    mentions: mentions.as_deref_mut(),
                },
            );
        }
        if let Some(expr) = trailing_expr {
            visit::visit_expr(
                expr,
                &mut IndexCollector {
                    index: stmts.len(),
                    counts: Some(&mut stmt_counts[stmts.len()]),
                    writes: None,
                    mentions,
                },
            );
        }
        for (stmt_index, counts) in stmt_counts.iter().enumerate() {
            for (&binding, &count) in counts {
                occurrences
                    .entry(binding)
                    .or_default()
                    .push((stmt_index, count));
            }
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

/// 当前函数内每个 binding 最后出现的顶层语句位置，包含声明、读写与显式捕获。
pub(super) fn last_binding_mentions(stmts: &[AstStmt]) -> BTreeMap<AstBindingRef, usize> {
    let mut last_mentions = BTreeMap::new();
    for (index, stmt) in stmts.iter().enumerate() {
        visit::visit_stmt(
            stmt,
            &mut BindingCollector(|binding, _| {
                last_mentions.insert(binding, index);
            }),
        );
    }
    last_mentions
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

/// 各查询组合共用一个遍历器实例类型，只填充调用方实际消费的索引。
struct IndexCollector<'a> {
    index: usize,
    counts: Option<&'a mut BTreeMap<AstBindingRef, usize>>,
    writes: Option<&'a mut BindingWriteIndex>,
    mentions: Option<&'a mut BTreeMap<AstBindingRef, (usize, usize)>>,
}

impl AstVisitor for IndexCollector<'_> {
    fn visit_name(&mut self, name: &AstNameRef, access: NameAccess) -> ControlFlow<()> {
        if let Some(writes) = &mut self.writes {
            writes.record(self.index, name, access);
        }
        if let Some(binding) = AstBindingRef::from_name_ref(name) {
            if matches!(access, NameAccess::Read | NameAccess::Capture)
                && let Some(counts) = &mut self.counts
            {
                *counts.entry(binding).or_default() += 1;
            }
            if let Some(mentions) = &mut self.mentions {
                let (last, count) = mentions.entry(binding).or_insert((self.index, 0));
                if *count == 0 || *last != self.index {
                    *count += 1;
                    *last = self.index;
                }
            }
        }
        ControlFlow::Continue(())
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        false
    }
}
