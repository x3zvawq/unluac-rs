//! 当前 HIR 块直属 cleanup 的位置与覆盖阈值，供资源边界消费者共享。
//!
//! 非零 Close(r) 覆盖不小于 r 的槽位；区间树保存最小阈值，跳过不覆盖候选的子区间。
//! 嵌套 cleanup 属于不同词法 owner，不进入这里。Close(0) 只有紧邻 Return 或处于
//! 当前 epoch 末尾才提供终结事实；外部 goto 的 cleanup 查询始终排除它。
//! 例如 `Close(0); side(); TBC` 中的零槽 close 对完整块不终结，但 epoch 若恰好
//! 截止在该 close 之后，它仍是合法终点。索引保留前一种事实，查询补充 epoch 边界。

use std::ops::Range;

use crate::hir::common::HirStmt;

use super::terminal_close_zero_end;

#[derive(Clone, Copy, Default)]
struct CloseSummary {
    nonzero: Option<usize>,
    terminal: bool,
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
                let nonzero = (close.from_reg != 0).then_some(close.from_reg);
                let terminal =
                    close.from_reg == 0 && terminal_close_zero_end(stmts, index).is_some();
                if nonzero.is_some() || terminal {
                    positions.push(index);
                    leaves.push(CloseSummary { nonzero, terminal });
                }
            }
        }
        let base = leaves.len().next_power_of_two();
        let mut tree = vec![CloseSummary::default(); 2 * base];
        tree[base..base + leaves.len()].copy_from_slice(&leaves);
        for node in (1..base).rev() {
            let left = tree[2 * node];
            let right = tree[2 * node + 1];
            tree[node] = CloseSummary {
                nonzero: left.nonzero.into_iter().chain(right.nonzero).min(),
                terminal: left.terminal || right.terminal,
            };
        }
        Self {
            stmts,
            positions,
            tree,
            base,
        }
    }

    pub(super) fn nonzero_closes(
        &self,
        range: Range<usize>,
        reg: usize,
    ) -> impl Iterator<Item = usize> + '_ {
        self.covering(range, reg, false)
    }

    pub(super) fn scope_closes(
        &self,
        range: Range<usize>,
        reg: usize,
    ) -> impl Iterator<Item = usize> + '_ {
        let terminal = range.end.checked_sub(1).filter(|&index| {
            index >= range.start
                && matches!(self.stmts[index], HirStmt::Close(ref close) if close.from_reg == 0)
        });
        // 末尾零槽 close 单独发布一次，包括未被完整块索引收录的 epoch 终点。
        self.covering(range.start..terminal.unwrap_or(range.end), reg, true)
            .chain(terminal)
    }

    fn covering(
        &self,
        range: Range<usize>,
        reg: usize,
        terminal: bool,
    ) -> impl Iterator<Item = usize> + '_ {
        let start = self.positions.partition_point(|&index| index < range.start);
        let end = start + self.positions[start..].partition_point(|&index| index < range.end);
        let mut next = Some((1, 0..self.base));
        let mut pending = Vec::new();
        std::iter::from_fn(move || {
            while let Some((node, span)) = next.take().or_else(|| pending.pop()) {
                let summary = self.tree[node];
                if start >= end
                    || span.end <= start
                    || span.start >= end
                    || !(summary.nonzero.is_some_and(|minimum| minimum <= reg)
                        || (terminal && summary.terminal))
                {
                    continue;
                }
                if span.end - span.start == 1 {
                    return Some(self.positions[span.start]);
                }
                let middle = (span.start + span.end) / 2;
                pending.push((2 * node + 1, middle..span.end));
                next = Some((2 * node, span.start..middle));
            }
            None
        })
    }
}
