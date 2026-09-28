//! 维护 lookup 和动态运算结果的共享值身份、别名与观察窗口。
//!
//! 消费当前 RootLifetimeFacts 及父层身份证明，供独立 home 的根退休查询。

use super::live_read_changes::LiveReadChanges;
use super::{
    ActiveScalarGcHome, BTreeMap, BTreeSet, HomeSlotKey, ProtoPromotionFacts, ScalarValueId,
    TempId, TempUseEvents,
};

// 观察发生在本语句写入前；alias 的增删从 index + 1 生效，不能回溯改变当前观察。
pub(super) struct ScalarValues<'a> {
    pub(super) by_temp: BTreeMap<TempId, ScalarValueId>,
    states: Vec<ValueObservations>,
    changes: LiveReadChanges,
    uses: &'a TempUseEvents<'a>,
    observations: BTreeSet<usize>,
}

struct ValueObservations {
    aliases: BTreeSet<TempId>,
    // GlobalRef 建立 identity 时的唯一来源 home；copy 不改变来源，覆盖不重用 identity。
    global_home: Option<HomeSlotKey>,
    live_aliases: usize,
    dead_since: usize,
    last_fence: Option<usize>,
    last_observation: Option<usize>,
    exposed: bool,
}

impl<'a> ScalarValues<'a> {
    pub(super) fn new(uses: &'a TempUseEvents<'a>) -> Self {
        Self {
            by_temp: BTreeMap::new(),
            states: Vec::new(),
            changes: LiveReadChanges::default(),
            uses,
            observations: uses
                .events
                .block()
                .observation_indices()
                .union(&uses.gc_fence_indices)
                .copied()
                .collect(),
        }
    }

    pub(super) fn advance(&mut self, index: usize) {
        for (_, temp) in self.uses.events.block().exposed_values(index) {
            if let Some(value) = self.by_temp.get(temp) {
                self.states[value.0].exposed = true;
            }
        }
        while let Some((at, temp, live)) = self.changes.pop_through(self.uses, index) {
            if let Some(value) = self.by_temp.get(&temp) {
                self.states[value.0].change(
                    live,
                    at,
                    &self.observations,
                    &self.uses.gc_fence_indices,
                );
            }
        }
    }

    pub(super) fn new_value(
        &mut self,
        index: usize,
        global_home: Option<HomeSlotKey>,
    ) -> ScalarValueId {
        let value = ScalarValueId(self.states.len());
        self.states.push(ValueObservations {
            aliases: BTreeSet::new(),
            global_home,
            live_aliases: 0,
            dead_since: index + 1,
            last_fence: None,
            last_observation: None,
            exposed: false,
        });
        value
    }

    pub(super) fn global_home(&self, value: ScalarValueId) -> Option<HomeSlotKey> {
        self.states[value.0].global_home
    }

    pub(super) fn exposed(&self, value: ScalarValueId) -> bool {
        self.states[value.0].exposed
    }

    pub(super) fn insert(&mut self, temp: TempId, value: ScalarValueId, index: usize) {
        self.remove(&temp, index);
        self.by_temp.insert(temp, value);
        self.states[value.0].aliases.insert(temp);
        if self.uses.has_live_read_from(temp, index) {
            self.states[value.0].change(
                true,
                index + 1,
                &self.observations,
                &self.uses.gc_fence_indices,
            );
        }
        self.changes.schedule(self.uses, temp, index);
    }

    pub(super) fn remove(&mut self, temp: &TempId, index: usize) -> Option<ScalarValueId> {
        self.changes.remove(*temp);
        let value = self.by_temp.remove(temp)?;
        self.states[value.0].aliases.remove(temp);
        if self.uses.has_live_read_from(*temp, index) {
            self.states[value.0].change(
                false,
                index + 1,
                &self.observations,
                &self.uses.gc_fence_indices,
            );
        }
        Some(value)
    }

    pub(super) fn retire_value(
        &mut self,
        value: ScalarValueId,
        index: usize,
        active: &mut BTreeMap<HomeSlotKey, ActiveScalarGcHome>,
        facts: &ProtoPromotionFacts,
    ) {
        // collector 只在完整语句边界退役值；每个活动 home 都至少持有一个映射中的 alias。
        // 同 home 的多个 alias 会重复删除同一个键，但不会访问其它 value 的 home。
        for temp in std::mem::take(&mut self.states[value.0].aliases) {
            let home = facts
                .trusted_temp_home_slot(temp)
                .expect("tracked lookup alias must have a trusted home");
            active.remove(&home);
            self.remove(&temp, index);
        }
    }

    pub(super) fn clear(&mut self) {
        self.changes.clear();
        for value in self.by_temp.values() {
            self.states[value.0].aliases.clear();
        }
        self.by_temp.clear();
        // identity 编号与 global origin 由本次 collector 持有，不能在边界后重用编号。
        // 清空映射后这些 state 不再有可达 alias；后续新值继续分配独立 identity。
    }

    pub(super) fn crossed_observer_before(&self, root: usize, overwrite: usize) -> bool {
        self.observations
            .range(root + 1..overwrite)
            .next()
            .is_some()
    }

    pub(super) fn observed(
        &self,
        root: &ActiveScalarGcHome,
        end: usize,
        paired_overwrite: bool,
    ) -> bool {
        let state = &self.states[root.value_id.0];
        let (positions, last) = if root.pure_scope_end_copy_root || paired_overwrite {
            (&self.observations, state.last_observation)
        } else if state.global_home.is_none() {
            (&self.uses.gc_fence_indices, state.last_fence)
        } else {
            return false;
        };
        let latest = if state.live_aliases == 0 {
            last.max(positions.range(state.dead_since..end).next_back().copied())
        } else {
            last
        };
        latest.is_some_and(|index| index > root.root_index)
    }
}

impl ValueObservations {
    fn change(
        &mut self,
        live: bool,
        at: usize,
        observations: &BTreeSet<usize>,
        fences: &BTreeSet<usize>,
    ) {
        if live {
            if self.live_aliases == 0 {
                self.last_observation = self
                    .last_observation
                    .max(observations.range(self.dead_since..at).next_back().copied());
                self.last_fence = self
                    .last_fence
                    .max(fences.range(self.dead_since..at).next_back().copied());
            }
            self.live_aliases += 1;
        } else {
            self.live_aliases -= 1;
            if self.live_aliases == 0 {
                self.dead_since = at;
            }
        }
    }
}
