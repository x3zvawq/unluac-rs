//! 为 lookup 的共享值身份维护别名、全局来源与无后续活读的观察窗口。
//!
//! temp 的读写顺序消费当前 RootLifetimeFacts；identity 与 alias 的建立、退休仍由父层
//! collector 证明。本层记录其来源和反向别名，整值退休只访问这些别名已证明的 home，
//! 不推断 VM home，也不合并不同 home 的 root 生命周期。例如
//! `a = lookup; b = a; gc(); use(b)` 中两个 home 共享一次活读事实；覆盖 b 后的 GC 是否
//! 保护 a，则由 a 的建立位置与该 identity 的零活读窗口共同决定。
//! 观察只发生在语句写入前：读写事件的状态变化从下一语句生效，映射修改也从 index + 1
//! 生效。只保存已关闭零窗口中的最后观察，因为 collector 只向前查询当前 root 的后缀。

use super::{
    ActiveLookupGcHome, BTreeMap, BTreeSet, HirExprSafety, HirStmt, HomeSlotKey, LookupValueId,
    ProtoPromotionFacts, TempId, TempUseEvents, stmt_may_observe_gc_roots,
};

pub(super) struct LookupValues<'a> {
    pub(super) by_temp: BTreeMap<TempId, LookupValueId>,
    states: Vec<ValueObservations>,
    changes: std::vec::IntoIter<(usize, TempId, bool)>,
    uses: &'a TempUseEvents,
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
}

impl<'a> LookupValues<'a> {
    pub(super) fn new(uses: &'a TempUseEvents, stmts: &[HirStmt], safety: HirExprSafety) -> Self {
        Self {
            by_temp: BTreeMap::new(),
            states: Vec::new(),
            changes: uses.live_read_changes().into_iter(),
            uses,
            observations: stmts
                .iter()
                .enumerate()
                .filter_map(|(index, stmt)| {
                    (uses.is_gc_fence(index) || stmt_may_observe_gc_roots(stmt, safety))
                        .then_some(index)
                })
                .collect(),
        }
    }

    pub(super) fn advance(&mut self, index: usize) {
        while self
            .changes
            .as_slice()
            .first()
            .is_some_and(|event| event.0 <= index)
        {
            let (at, temp, live) = self.changes.next().unwrap();
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
    ) -> LookupValueId {
        let value = LookupValueId(self.states.len());
        self.states.push(ValueObservations {
            aliases: BTreeSet::new(),
            global_home,
            live_aliases: 0,
            dead_since: index + 1,
            last_fence: None,
            last_observation: None,
        });
        value
    }

    pub(super) fn global_home(&self, value: LookupValueId) -> Option<HomeSlotKey> {
        self.states[value.0].global_home
    }

    pub(super) fn insert(&mut self, temp: TempId, value: LookupValueId, index: usize) {
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
    }

    pub(super) fn remove(&mut self, temp: &TempId, index: usize) -> Option<LookupValueId> {
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
        value: LookupValueId,
        index: usize,
        active: &mut BTreeMap<HomeSlotKey, ActiveLookupGcHome>,
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

    pub(super) fn observed(&self, root: &ActiveLookupGcHome, end: usize) -> bool {
        let state = &self.states[root.value_id.0];
        let (positions, last) = if root.pure_scope_end_copy_root {
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
