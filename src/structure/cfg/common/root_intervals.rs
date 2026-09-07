//! 索引同一 low 快照内的开放覆写和物理根观察阈值，避免每个 producer 重扫指令后缀。
//!
//! 事实只来自 InstrEffect 与 RootObservation；不解码 opcode，也不证明控制流闭合或根释放。
//! 例如区间内两次观察分别保留前 5、3 个槽，则共同保活前缀为 3；从槽 4 开始的开放
//! 写入会覆盖 home 4，但不覆盖 home 3。调用方必须先找覆写，再查询覆写之前的观察。

use std::ops::Range;

use super::{InstrEffect, RootObservation, SideEffectSummary};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Thresholds {
    open_write: usize,
    rooted_prefix: usize,
}

impl Thresholds {
    // 支持的 VM 槽阈值都是有限寄存器范围；最大 usize 表示区间没有这种事件。
    const EMPTY: Self = Self {
        open_write: usize::MAX,
        rooted_prefix: usize::MAX,
    };

    fn merge(self, other: Self) -> Self {
        Self {
            open_write: self.open_write.min(other.open_write),
            rooted_prefix: self.rooted_prefix.min(other.rooted_prefix),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RootIntervalIndex {
    leaf_base: usize,
    nodes: Vec<Thresholds>,
}

impl RootIntervalIndex {
    pub(crate) fn new(effects: &[InstrEffect], summaries: &[SideEffectSummary]) -> Self {
        let leaf_base = effects.len().next_power_of_two();
        let mut nodes = vec![Thresholds::EMPTY; leaf_base * 2];
        for (index, effect) in effects.iter().enumerate() {
            nodes[leaf_base + index] = Thresholds {
                open_write: effect.open_must_def.map_or(usize::MAX, |reg| reg.index()),
                rooted_prefix: match summaries[index].root_observation {
                    RootObservation::Call { caller_end } => caller_end.index(),
                    RootObservation::PrefixLowerBound { end } => end,
                    RootObservation::None | RootObservation::Close | RootObservation::FrameExit => {
                        usize::MAX
                    }
                },
            };
        }
        for index in (1..leaf_base).rev() {
            nodes[index] = nodes[index * 2].merge(nodes[index * 2 + 1]);
        }
        Self { leaf_base, nodes }
    }

    pub(crate) fn minimum_rooted_prefix(&self, range: Range<usize>) -> Option<usize> {
        let mut left = self.leaf_base + range.start;
        let mut right = self.leaf_base + range.end;
        let mut prefix = usize::MAX;
        while left < right {
            if left % 2 == 1 {
                prefix = prefix.min(self.nodes[left].rooted_prefix);
                left += 1;
            }
            if right % 2 == 1 {
                right -= 1;
                prefix = prefix.min(self.nodes[right].rooted_prefix);
            }
            left /= 2;
            right /= 2;
        }
        (prefix != usize::MAX).then_some(prefix)
    }

    pub(crate) fn first_open_write(&self, range: Range<usize>, home: usize) -> Option<usize> {
        self.find_open_write(1, 0..self.leaf_base, &range, home)
    }

    fn find_open_write(
        &self,
        node: usize,
        span: Range<usize>,
        range: &Range<usize>,
        home: usize,
    ) -> Option<usize> {
        if span.end <= range.start || span.start >= range.end || self.nodes[node].open_write > home
        {
            return None;
        }
        if span.end - span.start == 1 {
            return Some(span.start);
        }
        let middle = span.start + (span.end - span.start) / 2;
        self.find_open_write(node * 2, span.start..middle, range, home)
            .or_else(|| self.find_open_write(node * 2 + 1, middle..span.end, range, home))
    }
}
