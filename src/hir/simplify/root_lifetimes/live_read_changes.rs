//! 调度活动 temp 的下一条语句读写边界。
//!
//! 消费同一快照的 TempUseEvents，供 Call/Lookup owner 按各自观察时序维护活读状态。

use super::{BTreeMap, BTreeSet, TempId, TempUseEvents};

#[derive(Default)]
pub(super) struct LiveReadChanges {
    pending: BTreeSet<(usize, TempId)>,
    by_temp: BTreeMap<TempId, usize>,
}

impl LiveReadChanges {
    pub(super) fn schedule(&mut self, uses: &TempUseEvents<'_>, temp: TempId, after: usize) {
        self.remove(temp);
        if let Some(at) = uses.next_read_write_boundary(temp, after) {
            self.pending.insert((at, temp));
            self.by_temp.insert(temp, at);
        }
    }

    pub(super) fn remove(&mut self, temp: TempId) {
        if let Some(at) = self.by_temp.remove(&temp) {
            self.pending.remove(&(at, temp));
        }
    }

    pub(super) fn clear(&mut self) {
        self.pending.clear();
        self.by_temp.clear();
    }

    pub(super) fn pop_through(
        &mut self,
        uses: &TempUseEvents<'_>,
        index: usize,
    ) -> Option<(usize, TempId, bool)> {
        while let Some(&(at, temp)) = self.pending.first() {
            if at > index {
                return None;
            }
            self.schedule(uses, temp, at);
            let live = uses.has_live_read_from(temp, at);
            if live != uses.has_live_read_from(temp, at - 1) {
                return Some((at, temp, live));
            }
        }
        None
    }
}
