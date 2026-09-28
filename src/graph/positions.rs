//! 按身份索引当前快照中的有序出现位置。
//!
//! 供各层查询词法与资源事件区间，不推断读取角色或生命周期。

use std::{borrow::Borrow, collections::BTreeMap, ops::Range};

pub(crate) struct PositionIndex<K>(BTreeMap<K, Vec<usize>>);

impl<K> Default for PositionIndex<K> {
    fn default() -> Self {
        Self(BTreeMap::new())
    }
}

impl<K: Ord> PositionIndex<K> {
    pub(crate) fn record(&mut self, key: K, position: usize) {
        let positions = self.0.entry(key).or_default();
        if positions.last() != Some(&position) {
            positions.push(position);
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn span(&self, key: &K) -> Option<(usize, usize)> {
        self.0
            .get(key)
            .map(|positions| (positions[0], positions[positions.len() - 1]))
    }

    pub(crate) fn has_before(&self, key: &K, end: usize) -> bool {
        self.span(key).is_some_and(|(first, _)| first < end)
    }

    pub(crate) fn has_at_or_after(&self, key: &K, start: usize) -> bool {
        self.span(key).is_some_and(|(_, last)| last >= start)
    }

    pub(crate) fn positions_from(&self, key: &K, start: usize) -> &[usize] {
        let Some(positions) = self.0.get(key) else {
            return &[];
        };
        &positions[positions.partition_point(|&position| position < start)..]
    }

    pub(crate) fn last_in<Q: Ord + ?Sized>(&self, key: &Q, range: Range<usize>) -> Option<usize>
    where
        K: Borrow<Q>,
    {
        let positions = self.0.get(key)?;
        let end = positions.partition_point(|&position| position < range.end);
        positions[..end]
            .last()
            .copied()
            .filter(|&position| position >= range.start)
    }
}
