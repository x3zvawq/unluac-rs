//! 索引 Low-IR 快照的覆盖、关闭与物理根观察区间。
//!
//! 消费 InstrEffect 和 RootObservation，提供位置查询；控制闭合和根释放由消费者证明。

use std::ops::Range;

use super::{InstrEffect, RootObservation, SideEffectSummary};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Thresholds {
    open_write: usize,
    close: usize,
    rooted_prefix: usize,
}

impl Thresholds {
    // 支持的 VM 槽阈值都是有限寄存器范围；最大 usize 表示区间没有这种事件。
    const EMPTY: Self = Self {
        open_write: usize::MAX,
        close: usize::MAX,
        rooted_prefix: usize::MAX,
    };

    fn merge(self, other: Self) -> Self {
        Self {
            open_write: self.open_write.min(other.open_write),
            close: self.close.min(other.close),
            rooted_prefix: self.rooted_prefix.min(other.rooted_prefix),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RootIntervalIndex {
    leaf_base: usize,
    nodes: Vec<Thresholds>,
    observations: Vec<usize>,
}

impl RootIntervalIndex {
    pub(crate) fn new(effects: &[InstrEffect], summaries: &[SideEffectSummary]) -> Self {
        let leaf_base = effects.len().next_power_of_two();
        let mut nodes = vec![Thresholds::EMPTY; leaf_base * 2];
        let mut observations = Vec::new();
        for (index, effect) in effects.iter().enumerate() {
            let summary = &summaries[index];
            if summary.may_observe_gc_roots() || summary.root_observation != RootObservation::None {
                observations.push(index);
            }
            nodes[leaf_base + index] = Thresholds {
                open_write: effect.open_must_def.map_or(usize::MAX, |reg| reg.index()),
                close: match summary.root_observation {
                    RootObservation::Close { from } => from.index(),
                    _ => usize::MAX,
                },
                rooted_prefix: match summary.root_observation {
                    RootObservation::Call { caller_end } => caller_end.index(),
                    RootObservation::PrefixLowerBound { end } => end,
                    RootObservation::None
                    | RootObservation::Close { .. }
                    | RootObservation::FrameExit => usize::MAX,
                },
            };
        }
        for index in (1..leaf_base).rev() {
            nodes[index] = nodes[index * 2].merge(nodes[index * 2 + 1]);
        }
        Self {
            leaf_base,
            nodes,
            observations,
        }
    }

    /// 包含 GC 与清理事件，不要求观察提供普通 caller-frame 保活前缀。
    pub(crate) fn has_observation(&self, range: Range<usize>) -> bool {
        let first = self
            .observations
            .partition_point(|&index| index < range.start);
        self.observations
            .get(first)
            .is_some_and(|&index| index < range.end)
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
        self.find_threshold(1, 0..self.leaf_base, &range, home, |event| event.open_write)
    }

    pub(crate) fn first_close(&self, range: Range<usize>, home: usize) -> Option<usize> {
        self.find_threshold(1, 0..self.leaf_base, &range, home, |event| event.close)
    }

    fn find_threshold(
        &self,
        node: usize,
        span: Range<usize>,
        range: &Range<usize>,
        home: usize,
        threshold: impl Fn(Thresholds) -> usize + Copy,
    ) -> Option<usize> {
        if span.end <= range.start || span.start >= range.end || threshold(self.nodes[node]) > home
        {
            return None;
        }
        if span.end - span.start == 1 {
            return Some(span.start);
        }
        let middle = span.start + (span.end - span.start) / 2;
        self.find_threshold(node * 2, span.start..middle, range, home, threshold)
            .or_else(|| self.find_threshold(node * 2 + 1, middle..span.end, range, home, threshold))
    }
}
