//! 为当前仍绑定的 temp 调度下一条直属语句读写边界。
//!
//! 事件位置和活读判定来自同一不可变 HIR 快照的 TempUseEvents；本层不推导 VM home，
//! 也不保存每个 temp 的完整未来变化表。每个活动 alias 至多保留一个待处理边界，
//! 移除或重新绑定时撤销旧项，避免旧 value 的事件影响新 value。
//! 例如 `a = lookup; use(a); a = other` 只逐次查询 a 的下一读写位置；
//! 同一语句可能既读又写，必须比较该语句前后的既有活读结果，而不能把写入直接当死亡。
//! Call 与 Lookup 分别传入读取后和读取前的边界，本层不合并两种观察时序。

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
