//! 当前语句快照的词法 label 引用索引，不解释运行可达性或 Structured CFG。
//!
//! 各层提供顶层 owner 内的 label 与 goto 集合，索引保留每个 label 的有序来源位置，
//! 并用来源极值按目标 owner 建立区间树。区间内任一 label 的来源越出允许范围，即存在外部入边。
//! 例如 owner 0 的 goto 指向 owner 3 的 label，则目标区间 [2,4) 有来自前缀的入边。
//! 查询某个来源区间内是否存在 goto 时读取精确位置：来源 0、4 不能证明 [1,4) 有入边。
//! 同一 label 在多个 owner 中出现时，每个位置都保留该来源事实；不在这里猜词法合法性。

use std::collections::BTreeSet;
use std::ops::Range;

use super::PositionIndex;

pub(crate) struct LabelReferences<L> {
    pub(crate) labels: BTreeSet<L>,
    pub(crate) goto_targets: BTreeSet<L>,
}

impl<L> Default for LabelReferences<L> {
    fn default() -> Self {
        Self {
            labels: BTreeSet::new(),
            goto_targets: BTreeSet::new(),
        }
    }
}

type IncomingSpan = (usize, usize);

pub(crate) struct LabelReferenceIndex<L> {
    incoming: PositionIndex<L>,
    tree: Vec<Option<IncomingSpan>>,
    len: usize,
}

impl<L: Copy + Ord> LabelReferenceIndex<L> {
    pub(crate) fn new(stmts: &[LabelReferences<L>]) -> Self {
        let len = stmts.len();
        let mut incoming = PositionIndex::default();
        for (source, refs) in stmts.iter().enumerate() {
            for &label in &refs.goto_targets {
                incoming.record(label, source);
            }
        }
        let mut tree = vec![None; if incoming.is_empty() { 0 } else { 2 * len }];
        if !tree.is_empty() {
            for (target, refs) in stmts.iter().enumerate() {
                for label in &refs.labels {
                    tree[len + target] = merge(tree[len + target], incoming.span(label));
                }
            }
            for node in (1..len).rev() {
                tree[node] = merge(tree[2 * node], tree[2 * node + 1]);
            }
        }
        Self {
            incoming,
            tree,
            len,
        }
    }

    pub(crate) fn has_goto_before(&self, end: usize, label: L) -> bool {
        self.incoming.has_before(&label, end)
    }

    pub(crate) fn has_goto_at_or_after(&self, start: usize, label: L) -> bool {
        self.incoming.has_at_or_after(&label, start)
    }

    pub(crate) fn has_goto_in(&self, sources: Range<usize>, label: L) -> bool {
        assert!(sources.start <= sources.end && sources.end <= self.len);
        self.incoming.last_in(&label, sources).is_some()
    }

    /// 两个区间属于同一顶层语句快照；targets 内的来源是否越过 allowed_sources。
    pub(crate) fn has_incoming_outside(
        &self,
        targets: Range<usize>,
        allowed_sources: Range<usize>,
    ) -> bool {
        assert!(targets.start <= targets.end && targets.end <= self.len);
        assert!(allowed_sources.start <= allowed_sources.end && allowed_sources.end <= self.len);
        if self.tree.is_empty() {
            return false;
        }
        let outside = |span: Option<IncomingSpan>| {
            span.is_some_and(|(first, last)| {
                first < allowed_sources.start || last >= allowed_sources.end
            })
        };
        let mut left = self.len + targets.start;
        let mut right = self.len + targets.end;
        while left < right {
            if left % 2 == 1 {
                if outside(self.tree[left]) {
                    return true;
                }
                left += 1;
            }
            if right % 2 == 1 {
                right -= 1;
                if outside(self.tree[right]) {
                    return true;
                }
            }
            left /= 2;
            right /= 2;
        }
        false
    }
}

fn merge(left: Option<IncomingSpan>, right: Option<IncomingSpan>) -> Option<IncomingSpan> {
    match (left, right) {
        (Some((a, b)), Some((c, d))) => Some((a.min(c), b.max(d))),
        (left, right) => left.or(right),
    }
}
