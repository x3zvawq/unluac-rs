//! 维护 locals 提升的词法映射和全部 SSA 版本的 home 摘要。
//! 词法映射在子块退出时回滚；计划索引增量记录标量与子域输出的绑定和最后需求。

use super::{BTreeMap, BTreeSet, HomeSlotKey, LocalId, PromotionCtx, TempId};

#[derive(Default)]
pub(super) struct LocalMapping {
    bindings: BTreeMap<TempId, LocalId>,
    homes: BTreeMap<LocalId, BTreeMap<Option<HomeSlotKey>, usize>>,
    entry_nil_homes: BTreeMap<HomeSlotKey, BTreeMap<LocalId, usize>>,
    undo: Vec<(TempId, Option<LocalId>, Option<HomeSlotKey>, bool)>,
    declared_homes: BTreeMap<LocalId, HomeSlotKey>,
    declared_undo: Vec<LocalId>,
    /// 当前词法前缀的身份计数；多个 SSA 版本和已物化声明只占一个 local。
    visible_locals: BTreeMap<LocalId, usize>,
}

impl LocalMapping {
    pub(super) fn bindings(&self) -> &BTreeMap<TempId, LocalId> {
        &self.bindings
    }

    pub(super) fn visible_local_count(&self) -> usize {
        self.visible_locals.len()
    }

    pub(super) fn checkpoint(&self) -> (usize, usize) {
        (self.undo.len(), self.declared_undo.len())
    }

    /// 前轮已物化的声明仍有词法身份；不能因本轮没有 Temp 提升计划而丢失它。
    pub(super) fn declare(&mut self, local: LocalId, ctx: &PromotionCtx<'_>) {
        if let Some(home) = ctx.facts.trusted_local_home_slot(local) {
            assert!(self.declared_homes.insert(local, home).is_none());
        }
        self.declared_undo.push(local);
        *self.visible_locals.entry(local).or_default() += 1;
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
        let entry_nil =
            ctx.facts.is_entry_nil_phi_temp(temp) && !ctx.facts.is_loop_carrier_temp(temp);
        let previous = self.bindings.insert(temp, local);
        if let Some(previous) = previous {
            self.remove_home(previous, home, entry_nil);
        }
        self.add_home(local, home, entry_nil);
        self.undo.push((temp, previous, home, entry_nil));
    }

    fn add_home(&mut self, local: LocalId, home: Option<HomeSlotKey>, entry_nil: bool) {
        *self.visible_locals.entry(local).or_default() += 1;
        *self
            .homes
            .entry(local)
            .or_default()
            .entry(home)
            .or_default() += 1;
        if entry_nil && let Some(home) = home {
            *self
                .entry_nil_homes
                .entry(home)
                .or_default()
                .entry(local)
                .or_default() += 1;
        }
    }

    fn remove_visible_local(&mut self, local: LocalId) {
        let count = self
            .visible_locals
            .get_mut(&local)
            .expect("visible local has an owner");
        *count -= 1;
        if *count == 0 {
            self.visible_locals.remove(&local);
        }
    }

    fn remove_home(&mut self, local: LocalId, home: Option<HomeSlotKey>, entry_nil: bool) {
        self.remove_visible_local(local);
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
        if entry_nil && let Some(home) = home {
            let owners = self
                .entry_nil_homes
                .get_mut(&home)
                .expect("entry phi has home owner");
            let count = owners
                .get_mut(&local)
                .expect("mapped entry phi contributes owner");
            *count -= 1;
            if *count == 0 {
                owners.remove(&local);
            }
            if owners.is_empty() {
                self.entry_nil_homes.remove(&home);
            }
        }
    }

    pub(super) fn rollback(&mut self, checkpoint: (usize, usize)) {
        while self.declared_undo.len() > checkpoint.1 {
            let local = self.declared_undo.pop().unwrap();
            self.declared_homes.remove(&local);
            self.remove_visible_local(local);
        }
        while self.undo.len() > checkpoint.0 {
            let (temp, previous, home, entry_nil) = self.undo.pop().unwrap();
            let local = self
                .bindings
                .remove(&temp)
                .expect("inserted temp remains mapped");
            self.remove_home(local, home, entry_nil);
            if let Some(previous) = previous {
                self.bindings.insert(temp, previous);
                self.add_home(previous, home, entry_nil);
            }
        }
    }

    /// 已在父域声明的 Entry(nil) region result 拥有原槽；子域同 home 写仍属于这个物理根。
    pub(super) fn entry_nil_owner(
        &self,
        home: HomeSlotKey,
        ctx: &PromotionCtx<'_>,
    ) -> Option<LocalId> {
        let owners = self.entry_nil_homes.get(&home)?;
        if owners.len() != 1 {
            return None;
        }
        let local = *owners.first_key_value()?.0;
        (self.reusable_home(local, ctx) == Some(home)).then_some(local)
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
        let Some(homes) = self.homes.get(&local) else {
            return self.declared_homes.get(&local).copied();
        };
        // 缺失 home、受保护版本或不同 close epoch 都阻止复用，不能仅查询最新版本。
        (homes.len() == 1)
            .then(|| *homes.first_key_value().unwrap().0)
            .flatten()
    }
}

/// 本次提升计划的 SSA 映射和匿名绑定最后需求；标量与合流阶段共同增量维护。
#[derive(Default)]
pub(super) struct PlannedLocalUses {
    pub(super) bindings: BTreeMap<TempId, LocalId>,
    pub(super) homes: BTreeMap<TempId, Option<HomeSlotKey>>,
    pub(super) last_touches: BTreeMap<LocalId, usize>,
    /// 本轮提升已绑定 capture/debug 身份的 local；后续同槽写不能再借用它。
    pub(super) protected_locals: BTreeSet<LocalId>,
}

impl PlannedLocalUses {
    pub(super) fn record(
        &mut self,
        plan: &super::PromotionPlan,
        ctx: &PromotionCtx<'_>,
        events: super::RootEventBlock<'_>,
        trailing_reads: &BTreeMap<TempId, usize>,
        tail_index: usize,
    ) {
        self.bindings
            .extend(plan.temps.iter().map(|&temp| (temp, plan.local)));
        self.homes
            .extend(plan.temps.iter().map(|&temp| (temp, plan.home_slot)));
        // 所有版本共用最后需求；新增 capture/debug 身份撤销资格，不能只看最近 temp。
        let anonymous = ctx
            .local_debug_hints
            .get(plan.local.index())
            .is_none_or(Option::is_none)
            && ctx
                .local_debug_scopes
                .get(plan.local.index())
                .is_none_or(Option::is_none)
            && super::debug_hint_for_temp_group(ctx.temp_debug_locals, &plan.temps).is_none()
            && plan
                .temps
                .iter()
                .all(|temp| !ctx.identity_sensitive_temps.contains(temp));
        if !anonymous {
            self.protected_locals.insert(plan.local);
            self.last_touches.remove(&plan.local);
            return;
        }
        if matches!(plan.action, super::PromotionAction::AllocateLocal) {
            self.last_touches.insert(plan.local, plan.decl_index);
        }
        if let Some(last) = self.last_touches.get_mut(&plan.local) {
            for &temp in &plan.temps {
                let end = if trailing_reads.contains_key(&temp) {
                    tail_index
                } else {
                    events.last_touch(temp).unwrap_or(plan.decl_index)
                };
                *last = (*last).max(end);
            }
        }
    }
}

/// 新声明占用原 home，显式覆盖重新确认该 home 的当前 owner；较高旧窗口随之结束。
/// 继续借用更高的旧绑定会延长其词法窗口，破坏后续完整表达式帧的声明前缀。
/// 每个登记项至多移除一次，不为每个覆盖候选重扫其间声明。
pub(super) fn introduce_overwrite_owner(
    owners: &mut BTreeMap<usize, LocalId>,
    home: Option<HomeSlotKey>,
    local: LocalId,
) {
    if let Some(home) = home {
        let _ = owners.split_off(&home.slot());
        owners.insert(home.slot(), local);
    } else {
        owners.clear();
    }
}
