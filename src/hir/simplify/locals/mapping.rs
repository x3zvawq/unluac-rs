//! 维护 locals 提升的词法映射和全部 SSA 版本的 home 摘要。
//! 子块只记录自身增量，退出时回滚；兄弟块不会继承彼此的绑定或冲突。

use super::{BTreeMap, HomeSlotKey, LocalId, PromotionCtx, TempId};

#[derive(Default)]
pub(super) struct LocalMapping {
    bindings: BTreeMap<TempId, LocalId>,
    homes: BTreeMap<LocalId, BTreeMap<Option<HomeSlotKey>, usize>>,
    undo: Vec<(TempId, Option<LocalId>, Option<HomeSlotKey>)>,
}

impl LocalMapping {
    pub(super) fn bindings(&self) -> &BTreeMap<TempId, LocalId> {
        &self.bindings
    }

    pub(super) fn checkpoint(&self) -> usize {
        self.undo.len()
    }

    pub(super) fn insert(&mut self, temp: TempId, local: LocalId, ctx: &PromotionCtx<'_>) {
        // Temp 的身份与 home 在本次提升中不可变；Local 的 debug/capture 资格在查询时检查。
        let home = ctx.facts.trusted_temp_home_slot(temp).filter(|_| {
            !ctx.identity_sensitive_temps.contains(&temp)
                && ctx
                    .temp_debug_locals
                    .get(temp.index())
                    .is_none_or(Option::is_none)
                && ctx
                    .temp_debug_scopes
                    .get(temp.index())
                    .is_none_or(Option::is_none)
        });
        let previous = self.bindings.insert(temp, local);
        if let Some(previous) = previous {
            self.remove_home(previous, home);
        }
        self.add_home(local, home);
        self.undo.push((temp, previous, home));
    }

    fn add_home(&mut self, local: LocalId, home: Option<HomeSlotKey>) {
        *self
            .homes
            .entry(local)
            .or_default()
            .entry(home)
            .or_default() += 1;
    }

    fn remove_home(&mut self, local: LocalId, home: Option<HomeSlotKey>) {
        let homes = self
            .homes
            .get_mut(&local)
            .expect("mapped local has home counts");
        let count = homes
            .get_mut(&home)
            .expect("mapped temp contributes its home");
        *count -= 1;
        if *count == 0 {
            homes.remove(&home);
        }
        if homes.is_empty() {
            self.homes.remove(&local);
        }
    }

    pub(super) fn rollback(&mut self, checkpoint: usize) {
        while self.undo.len() > checkpoint {
            let (temp, previous, home) = self.undo.pop().unwrap();
            let local = self
                .bindings
                .remove(&temp)
                .expect("inserted temp remains mapped");
            self.remove_home(local, home);
            if let Some(previous) = previous {
                self.bindings.insert(temp, previous);
                self.add_home(previous, home);
            }
        }
    }

    pub(super) fn reusable_home(
        &self,
        local: LocalId,
        ctx: &PromotionCtx<'_>,
    ) -> Option<HomeSlotKey> {
        if ctx.identity_sensitive_locals.contains(&local)
            || ctx
                .local_debug_hints
                .get(local.index())
                .is_some_and(Option::is_some)
            || ctx
                .local_debug_scopes
                .get(local.index())
                .is_some_and(Option::is_some)
        {
            return None;
        }
        let homes = self.homes.get(&local)?;
        // 缺失 home、受保护版本或不同 close epoch 都阻止复用，不能仅查询最新版本。
        (homes.len() == 1)
            .then(|| *homes.first_key_value().unwrap().0)
            .flatten()
    }
}
