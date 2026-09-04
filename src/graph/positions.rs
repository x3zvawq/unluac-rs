//! 按身份记录当前快照中的有序出现位置，供各层词法身份和资源活动查询共享。
//!
//! 生产者按位置递增发布事件；同一身份在一个 owner 中多次出现只保留一次。
//! 这里只解释位置区间，不推断可达性、读取角色或资源生命周期。例如位置 0、4
//! 不能证明 [1,4) 内有事件；搜索上界早于起点时也不存在活动。

use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Range,
};

pub(crate) struct PositionIndex<K>(BTreeMap<K, Vec<usize>>);

impl<K> Default for PositionIndex<K> {
    fn default() -> Self {
        Self(BTreeMap::new())
    }
}

impl<K: Ord> PositionIndex<K> {
    pub(crate) fn from_sets(sets: &[BTreeSet<K>]) -> Self
    where
        K: Copy,
    {
        let mut index = Self::default();
        for (position, keys) in sets.iter().enumerate() {
            for &key in keys {
                index.record(key, position);
            }
        }
        index
    }

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

    pub(crate) fn last_in(&self, key: &K, range: Range<usize>) -> Option<usize> {
        let positions = self.0.get(key)?;
        let end = positions.partition_point(|&position| position < range.end);
        positions[..end]
            .last()
            .copied()
            .filter(|&position| position >= range.start)
    }
}
