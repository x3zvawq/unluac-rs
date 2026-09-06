//! 按 call 值身份共享别名、活读和观察代表，物理 home 仍各自持有释放事务。
//!
//! 身份和 home 来自父层的 copy/overwrite 证明，活读变化消费共享语句事件，不重建 VM 协议。
//! 例如 `a = f(); b = a; c = b` 只保存一次三个别名；覆盖 a 只结束 a 的事务，
//! b、c 仍可选出另一个根。观察优先选择已观察的最低 home，否则选择最低可用 home。
//! 潜在事件排除仅由显式 GC 证明的 copy home；显式 fence 另记是否已物化当前代表。
//! 不符合根保护资格的 home 仍传播确值身份，但不参与观察代表选择或签发释放事务。

use super::{ActiveCallRoot, BTreeMap, BTreeSet, CallValueId, HomeSlotKey, TempId, TempUseEvents};

pub(super) struct CallValues<'a> {
    roots: BTreeMap<HomeSlotKey, ActiveCallRoot>,
    values: Vec<CallValue>,
    by_temp: BTreeMap<TempId, (CallValueId, HomeSlotKey)>,
    aliases_by_home: BTreeMap<HomeSlotKey, BTreeSet<TempId>>,
    pending_observation: BTreeSet<CallValueId>,
    pending_fence: BTreeSet<CallValueId>,
    changes: std::vec::IntoIter<(usize, TempId, bool)>,
    uses: &'a TempUseEvents,
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
    pub(super) fn new(uses: &'a TempUseEvents) -> Self {
        Self {
            roots: BTreeMap::new(),
            values: Vec::new(),
            by_temp: BTreeMap::new(),
            aliases_by_home: BTreeMap::new(),
            pending_observation: BTreeSet::new(),
            pending_fence: BTreeSet::new(),
            changes: uses.live_read_changes().into_iter(),
            uses,
            index: 0,
        }
    }

    pub(super) fn advance(&mut self, index: usize) {
        self.index = index;
        // 释放配对查询的是本条语句读取完毕后的状态；新写入别名也从该点进入集合。
        while self
            .changes
            .as_slice()
            .first()
            .is_some_and(|change| change.0 <= index + 1)
        {
            let (_, temp, live) = self.changes.next().unwrap();
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
        if root.eligible {
            state.representatives.insert((!root.observed, home));
        }
        if root.eligible && !root.explicit_fence_only {
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

    pub(super) fn clear(&mut self) {
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
