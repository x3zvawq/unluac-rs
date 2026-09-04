//! 当前 HIR 块的直属 label 位置与资源活跃区间，不重建 CFG 或 TBC 数据流。
//!
//! HirLabel 携带 Structure 冻结的 active-set；索引用 label 序号保留每个 origin 的
//! 出现位置，供作用域候选验证连续性。嵌套 label 属于自己的词法 owner，不计入这里。
//! 例如 active、inactive、active 不能用单一 Lua 块表达；active、active、inactive
//! 的终点是第三个 label，全部 active 时则只证明到最后一个 label 后。

use std::{cell::OnceCell, ops::Range};

use crate::graph::PositionIndex;
use crate::hir::common::{HirLabel, HirStmt};
use crate::transformer::InstrRef;

pub(super) struct DirectLabelIndex<'a> {
    labels: Vec<(usize, &'a HirLabel)>,
    active: OnceCell<PositionIndex<InstrRef>>,
}

impl<'a> DirectLabelIndex<'a> {
    pub(super) fn new(stmts: &'a [HirStmt]) -> Self {
        Self {
            labels: stmts
                .iter()
                .enumerate()
                .filter_map(|(index, stmt)| match stmt {
                    HirStmt::Label(label) => Some((index, label.as_ref())),
                    _ => None,
                })
                .collect(),
            active: OnceCell::new(),
        }
    }

    fn ordinals(&self, range: Range<usize>) -> Range<usize> {
        let start = self
            .labels
            .partition_point(|(index, _)| *index < range.start);
        let end = start + self.labels[start..].partition_point(|(index, _)| *index < range.end);
        start..end
    }

    pub(super) fn in_range(&self, range: Range<usize>) -> &[(usize, &'a HirLabel)] {
        &self.labels[self.ordinals(range)]
    }

    pub(super) fn active_scope_end(
        &self,
        range: Range<usize>,
        origin: InstrRef,
    ) -> Result<Option<usize>, ()> {
        let range = self.ordinals(range);
        let active = self.active.get_or_init(|| {
            let mut positions = PositionIndex::default();
            for (ordinal, (_, label)) in self.labels.iter().enumerate() {
                for &origin in &label.tbc_barriers {
                    positions.record(origin, ordinal);
                }
            }
            positions
        });
        let suffix = active.positions_from(&origin, range.start);
        let active = &suffix[..suffix.partition_point(|&ordinal| ordinal < range.end)];
        let Some(&last) = active.last() else {
            return Ok(None);
        };
        if active[0] != range.start || active.len() != last - range.start + 1 {
            // 候选拒绝[SemanticBarrier:Scope]：inactive -> active 或 active 集中途断开，
            // 不能将 scope 外入口与同一 origin 的活跃片段包入单一 Lua block。
            return Err(());
        }
        // 无 inactive label 时只证明到最后 active label；后续终点仍由 cleanup 和
        // binding activity 决定，不能把无关尾语句扩进资源作用域。
        Ok(Some(if last + 1 < range.end {
            self.labels[last + 1].0
        } else {
            self.labels[last].0 + 1
        }))
    }
}
