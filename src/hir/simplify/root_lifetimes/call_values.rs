//! 按调用结果的值身份共享别名、活读与观察代表。
//!
//! 消费父层的 copy/overwrite 证明及共享语句事件，各物理 home 仍独立持有释放事务。

use super::live_read_changes::LiveReadChanges;
use super::{ActiveCallRoot, BTreeMap, BTreeSet, CallValueId, HomeSlotKey, TempId, TempUseEvents};

pub(super) struct CallValues<'a> {
    roots: BTreeMap<HomeSlotKey, ActiveCallRoot>,
    values: Vec<CallValue>,
    by_temp: BTreeMap<TempId, (CallValueId, HomeSlotKey)>,
    aliases_by_home: BTreeMap<HomeSlotKey, BTreeSet<TempId>>,
    pending_observation: BTreeSet<CallValueId>,
    pending_fence: BTreeSet<CallValueId>,
    changes: LiveReadChanges,
    uses: &'a TempUseEvents<'a>,
    index: usize,
}

#[derive(Default)]
struct CallValue {
    active_homes: usize,
    aliases: BTreeSet<TempId>,
    live_aliases_by_home: BTreeMap<HomeSlotKey, usize>,
    // false 排在前面，对应已经观察过的 home；第二关键字保持原最低 home 规则。
    representatives: BTreeSet<(bool, HomeSlotKey)>,
    ordinary_representatives: BTreeSet<(bool, HomeSlotKey)>,
}

impl CallValue {
    fn change_live(&mut self, home: HomeSlotKey, live: bool) {
        if live {
            *self.live_aliases_by_home.entry(home).or_default() += 1;
        } else {
            let count = self
                .live_aliases_by_home
                .get_mut(&home)
                .expect("live alias must retain its home count");
            *count -= 1;
            if *count == 0 {
                self.live_aliases_by_home.remove(&home);
            }
        }
    }
}

impl<'a> CallValues<'a> {
    /// 无活动根也无可继续传播的别名；历史 value arena 本身不受后续 home 写入影响。
    pub(super) fn is_empty(&self) -> bool {
        self.roots.is_empty() && self.by_temp.is_empty()
    }

    /// 两个索引可以重合；这个上界只选择较小的查询域，结果仍按 home 去重。
    pub(super) fn tracked_home_count_bound(&self) -> usize {
        self.roots.len() + self.aliases_by_home.len()
    }

    pub(super) fn tracked_homes(&self) -> impl Iterator<Item = super::HomeSlotKey> + '_ {
        self.roots
            .keys()
            .chain(self.aliases_by_home.keys())
            .copied()
    }

    pub(super) fn tracks_home(&self, home: HomeSlotKey) -> bool {
        self.roots.contains_key(&home) || self.aliases_by_home.contains_key(&home)
    }

    pub(super) fn tracked_temps(&self) -> impl Iterator<Item = TempId> + '_ {
        self.by_temp.keys().copied()
    }

    pub(super) fn tracked_temp_count(&self) -> usize {
        self.by_temp.len()
    }

    pub(super) fn read_values_at(&self, index: usize) -> BTreeSet<CallValueId> {
        let events = self.uses.events.block().reads(index);
        if events.len() < self.by_temp.len() {
            events
                .iter()
                .filter_map(|(_, temp)| self.value_for_temp(*temp))
                .collect()
        } else {
            self.tracked_temps()
                .filter(|temp| self.uses.has_read_at(*temp, index))
                .filter_map(|temp| self.value_for_temp(temp))
                .collect()
        }
    }

    pub(super) fn new(uses: &'a TempUseEvents<'a>) -> Self {
        Self {
            roots: BTreeMap::new(),
            values: Vec::new(),
            by_temp: BTreeMap::new(),
            aliases_by_home: BTreeMap::new(),
            pending_observation: BTreeSet::new(),
            pending_fence: BTreeSet::new(),
            changes: LiveReadChanges::default(),
            uses,
            index: 0,
        }
    }

    pub(super) fn advance(&mut self, index: usize) {
        self.index = index;
        // 释放配对查询的是本条语句读取完毕后的状态；新写入别名也从该点进入集合。
        while let Some((_, temp, live)) = self.changes.pop_through(self.uses, index + 1) {
            if let Some((value, home)) = self.by_temp.get(&temp) {
                self.values[value.0].change_live(*home, live);
            }
        }
    }

    pub(super) fn new_value(&mut self) -> CallValueId {
        let value = CallValueId(self.values.len());
        self.values.push(CallValue::default());
        value
    }

    pub(super) fn value_for_temp(&self, temp: TempId) -> Option<CallValueId> {
        self.by_temp
            .get(&temp)
            .map(|(value, _)| *value)
            .filter(|value| self.values[value.0].active_homes != 0)
    }

    pub(super) fn aliases(&self, value: CallValueId) -> &BTreeSet<TempId> {
        &self.values[value.0].aliases
    }

    pub(super) fn value_has_live_read_after(&self, value: CallValueId) -> bool {
        !self.values[value.0].live_aliases_by_home.is_empty()
    }

    pub(super) fn has_live_read_after(&self, value: CallValueId, home: HomeSlotKey) -> bool {
        self.values[value.0]
            .live_aliases_by_home
            .get(&home)
            .copied()
            .unwrap_or(0)
            != 0
    }

    pub(super) fn forget_temp(&mut self, temp: TempId) {
        self.changes.remove(temp);
        if let Some((value, home)) = self.by_temp.remove(&temp) {
            self.values[value.0].aliases.remove(&temp);
            if self.uses.has_live_read_after(temp, self.index) {
                self.values[value.0].change_live(home, false);
            }
            if let Some(aliases) = self.aliases_by_home.get_mut(&home) {
                aliases.remove(&temp);
                if aliases.is_empty() {
                    self.aliases_by_home.remove(&home);
                }
            }
        }
    }

    pub(super) fn bind(&mut self, temp: TempId, home: HomeSlotKey, value: CallValueId) {
        self.forget_temp(temp);
        self.by_temp.insert(temp, (value, home));
        self.aliases_by_home.entry(home).or_default().insert(temp);
        self.values[value.0].aliases.insert(temp);
        if self.uses.has_live_read_after(temp, self.index) {
            self.values[value.0].change_live(home, true);
        }
        self.changes.schedule(self.uses, temp, self.index + 1);
    }

    pub(super) fn forget_home_aliases(&mut self, home: HomeSlotKey) {
        if let Some(aliases) = self.aliases_by_home.remove(&home) {
            for temp in aliases {
                self.forget_temp(temp);
            }
        }
    }

    pub(super) fn get(&self, home: &HomeSlotKey) -> Option<&ActiveCallRoot> {
        self.roots.get(home)
    }

    pub(super) fn homes(&self, value: CallValueId) -> impl Iterator<Item = &HomeSlotKey> {
        self.values[value.0]
            .representatives
            .iter()
            .map(|(_, home)| home)
    }

    pub(super) fn insert(&mut self, home: HomeSlotKey, root: ActiveCallRoot) {
        assert!(
            !self.roots.contains_key(&home),
            "call root home must retire before reuse"
        );
        let value = root.value_id;
        let state = &mut self.values[value.0];
        state.active_homes += 1;
        if root.eligible && !root.transferred {
            state.representatives.insert((!root.observed, home));
        }
        if root.eligible && !root.transferred && !root.explicit_fence_only {
            state
                .ordinary_representatives
                .insert((!root.observed, home));
        }
        self.roots.insert(home, root);
        self.refresh_pending(value);
    }

    pub(super) fn remove(&mut self, home: &HomeSlotKey) -> Option<ActiveCallRoot> {
        let root = self.roots.remove(home)?;
        let state = &mut self.values[root.value_id.0];
        state.active_homes -= 1;
        state.representatives.remove(&(!root.observed, *home));
        state
            .ordinary_representatives
            .remove(&(!root.observed, *home));
        self.refresh_pending(root.value_id);
        Some(root)
    }

    /// 交接只撤销观察代表，精确固定覆写仍由同一 home 状态机处理；不再新增 caller 根。
    pub(super) fn transfer(&mut self, home: HomeSlotKey) {
        let mut root = self
            .remove(&home)
            .expect("transferred call root owns its home");
        root.transferred = true;
        self.insert(home, root);
    }

    pub(super) fn clear(&mut self) {
        self.changes.clear();
        self.roots.clear();
        self.values.clear();
        self.by_temp.clear();
        self.aliases_by_home.clear();
        self.pending_observation.clear();
        self.pending_fence.clear();
    }

    pub(super) fn representative(&self, value: CallValueId, fence: bool) -> Option<HomeSlotKey> {
        let state = &self.values[value.0];
        let representatives = if fence {
            &state.representatives
        } else {
            &state.ordinary_representatives
        };
        representatives.first().map(|(_, home)| *home)
    }

    pub(super) fn pending(&self, fence: bool) -> Vec<HomeSlotKey> {
        let values = if fence {
            &self.pending_fence
        } else {
            &self.pending_observation
        };
        values
            .iter()
            .filter_map(|value| self.representative(*value, fence))
            .collect()
    }

    pub(super) fn observe(&mut self, home: HomeSlotKey, fence: bool) {
        let root = self
            .roots
            .get_mut(&home)
            .expect("selected call root must remain active");
        root.observed = true;
        root.preserved |= fence;
        let value = root.value_id;
        let state = &mut self.values[value.0];
        state.representatives.remove(&(true, home));
        state.representatives.insert((false, home));
        if !root.explicit_fence_only {
            state.ordinary_representatives.remove(&(true, home));
            state.ordinary_representatives.insert((false, home));
        }
        self.refresh_pending(value);
    }

    fn refresh_pending(&mut self, value: CallValueId) {
        let ordinary = self
            .representative(value, false)
            .is_some_and(|home| !self.roots[&home].observed);
        let fence = self
            .representative(value, true)
            .is_some_and(|home| !self.roots[&home].preserved);
        if ordinary {
            self.pending_observation.insert(value);
        } else {
            self.pending_observation.remove(&value);
        }
        if fence {
            self.pending_fence.insert(value);
        } else {
            self.pending_fence.remove(&value);
        }
    }
}
