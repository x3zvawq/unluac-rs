//! 索引当前 HIR 块直属 cleanup 的位置与覆盖范围。
//!
//! 消费 Close 和原终结身份，供资源作用域 owner 查询，不推断嵌套词法域。

use std::{
    collections::{BTreeSet, BinaryHeap},
    ops::Range,
};

use crate::hir::common::HirStmt;

use super::frame_cleanup_end;

/// 只在当前未改写 block 快照内有效；范围可以包含词法作用域外的 goto cleanup。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct CloseSelection {
    range: Range<usize>,
    reg: usize,
    terminal: bool,
}

impl CloseSelection {
    pub(super) fn scope(range: Range<usize>, reg: usize) -> Self {
        Self {
            range,
            reg,
            terminal: true,
        }
    }

    pub(super) fn explicit(range: Range<usize>, reg: usize) -> Self {
        Self {
            range,
            reg,
            terminal: false,
        }
    }
}

#[derive(Clone, Copy, Default)]
struct CloseSummary {
    explicit: Option<usize>,
    terminal: bool,
    explicit_count: usize,
    maximum: usize,
}

impl CloseSummary {
    fn union(self, other: Self) -> Self {
        Self {
            explicit: self.explicit.into_iter().chain(other.explicit).min(),
            terminal: self.terminal || other.terminal,
            explicit_count: self.explicit_count + other.explicit_count,
            maximum: self.maximum.max(other.maximum),
        }
    }
}

pub(super) struct DirectCloseIndex<'a> {
    stmts: &'a [HirStmt],
    positions: Vec<usize>,
    tree: Vec<CloseSummary>,
    base: usize,
}

impl<'a> DirectCloseIndex<'a> {
    pub(super) fn new(stmts: &'a [HirStmt]) -> Self {
        let mut positions = Vec::new();
        let mut leaves = Vec::new();
        for (index, stmt) in stmts.iter().enumerate() {
            if let HirStmt::Close(close) = stmt {
                let explicit = (close.kind == crate::transformer::CloseKind::Explicit)
                    .then_some(close.from_reg);
                let terminal = frame_cleanup_end(stmts, index).is_some();
                if explicit.is_some() || terminal {
                    positions.push(index);
                    leaves.push(CloseSummary {
                        explicit,
                        terminal,
                        explicit_count: usize::from(explicit.is_some()),
                        maximum: close.from_reg,
                    });
                }
            }
        }
        let base = leaves.len().next_power_of_two();
        let mut tree = vec![CloseSummary::default(); 2 * base];
        tree[base..base + leaves.len()].copy_from_slice(&leaves);
        for node in (1..base).rev() {
            tree[node] = tree[2 * node].union(tree[2 * node + 1]);
        }
        Self {
            stmts,
            positions,
            tree,
            base,
        }
    }

    fn positions_in(&self, range: Range<usize>) -> Range<usize> {
        let start = self.positions.partition_point(|&index| index < range.start);
        let end = start + self.positions[start..].partition_point(|&index| index < range.end);
        start..end
    }

    pub(super) fn last(&self, selection: &CloseSelection) -> Option<usize> {
        self.last_in_node(
            1,
            0..self.base,
            &self.positions_in(selection.range.clone()),
            selection,
        )
    }

    fn last_in_node(
        &self,
        node: usize,
        span: Range<usize>,
        range: &Range<usize>,
        selection: &CloseSelection,
    ) -> Option<usize> {
        let summary = self.tree[node];
        if range.is_empty()
            || span.end <= range.start
            || span.start >= range.end
            || !(summary
                .explicit
                .is_some_and(|minimum| minimum <= selection.reg)
                || (selection.terminal && summary.terminal))
        {
            return None;
        }
        if span.end - span.start == 1 {
            return Some(self.positions[span.start]);
        }
        let middle = (span.start + span.end) / 2;
        self.last_in_node(2 * node + 1, middle..span.end, range, selection)
            .or_else(|| self.last_in_node(2 * node, span.start..middle, range, selection))
    }

    /// 成功的外部 label cleanup 必须是语句连续前缀；间隙或较高槽 close 都不能跳过。
    pub(super) fn contiguous_explicit(
        &self,
        range: Range<usize>,
        reg: usize,
    ) -> Result<Option<CloseSelection>, ()> {
        let mut selection = CloseSelection::explicit(range, reg);
        let Some(last) = self.last(&selection) else {
            return Ok(None);
        };
        selection.range.end = last + 1;
        let bounds = self.positions_in(selection.range.clone());
        let (mut left, mut right) = (self.base + bounds.start, self.base + bounds.end);
        let mut summary = CloseSummary::default();
        while left < right {
            if left % 2 == 1 {
                summary = summary.union(self.tree[left]);
                left += 1;
            }
            if right % 2 == 1 {
                right -= 1;
                summary = summary.union(self.tree[right]);
            }
            left /= 2;
            right /= 2;
        }
        if summary.explicit_count != selection.range.len() || summary.maximum > reg {
            return Err(());
        }
        Ok(Some(selection))
    }

    /// 只发布已接受候选的并集；最大活跃槽位足以判断独立 close 是否被任一 owner 覆盖。
    pub(super) fn owned_closes<'s>(
        &self,
        selections: impl Iterator<Item = &'s CloseSelection>,
    ) -> BTreeSet<usize> {
        let mut selections = selections.collect::<Vec<_>>();
        selections.sort_unstable_by_key(|selection| selection.range.start);
        let mut owned = BTreeSet::new();
        let mut pending = selections.into_iter().peekable();
        let mut active = BinaryHeap::<(usize, usize)>::new();
        let mut terminal_end = 0;
        for &index in &self.positions {
            while let Some(selection) = pending.next_if(|selection| selection.range.start <= index)
            {
                active.push((selection.reg, selection.range.end));
                if selection.terminal {
                    terminal_end = terminal_end.max(selection.range.end);
                }
            }
            while active.peek().is_some_and(|&(_, end)| end <= index) {
                active.pop();
            }
            let HirStmt::Close(close) = &self.stmts[index] else {
                unreachable!("direct close positions only contain cleanup statements")
            };
            let covered = if close.kind == crate::transformer::CloseKind::Explicit {
                active.peek().is_some_and(|&(reg, _)| close.from_reg <= reg)
            } else {
                index < terminal_end
            };
            if covered {
                owned.insert(index);
            }
        }
        owned
    }
}
