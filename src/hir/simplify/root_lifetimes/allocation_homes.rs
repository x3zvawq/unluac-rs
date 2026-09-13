//! 按物理 home 索引分配对象的独立根事务与该槽中的别名。
//!
//! 分配身份使用当前 block 快照中最初 constructor 的语句位置，home 来自 Promotion；
//! 本层只维护 collector 已证明的 copy/overwrite，不反查别名或重建 VM 协议。
//! 例如 a={}、b=a 后两个 home 共享 site；覆盖 a 只取走 a 的 owner 与别名，b 仍保留。
//! 同 site 再写回已有 home 延续原 producer，不能把一次 SSA copy 当成新的生命周期。
//! 该身份不跨改写发布，也不是表容量/模板 provenance 或可能重复赋值的 TempId。

use super::{AllocationHomeOwner, BTreeMap, BTreeSet, HomeSlotKey, TempId};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) struct AllocationSite(pub(super) usize);

#[derive(Default)]
pub(super) struct AllocationHomes {
    homes: BTreeMap<HomeSlotKey, ActiveAllocationHome>,
    by_temp: BTreeMap<TempId, HomeSlotKey>,
}

pub(super) struct ActiveAllocationHome {
    pub(super) aliases: BTreeSet<TempId>,
    pub(super) owner: AllocationHomeOwner,
    pub(super) allocation_site: AllocationSite,
}

impl AllocationHomes {
    pub(super) fn is_empty(&self) -> bool {
        self.homes.is_empty()
    }

    pub(super) fn len(&self) -> usize {
        self.homes.len()
    }

    pub(super) fn keys(&self) -> impl Iterator<Item = HomeSlotKey> + '_ {
        self.homes.keys().copied()
    }

    pub(super) fn temps(&self) -> impl Iterator<Item = TempId> + '_ {
        self.by_temp.keys().copied()
    }

    pub(super) fn temp_count(&self) -> usize {
        self.by_temp.len()
    }

    pub(super) fn get(&self, home: &HomeSlotKey) -> Option<&ActiveAllocationHome> {
        self.homes.get(home)
    }

    pub(super) fn site_for_temp(&self, temp: TempId) -> Option<AllocationSite> {
        self.by_temp
            .get(&temp)
            .map(|home| self.homes[home].allocation_site)
    }

    pub(super) fn forget_temp(&mut self, temp: TempId) {
        if let Some(home) = self.by_temp.remove(&temp) {
            self.homes.get_mut(&home).unwrap().aliases.remove(&temp);
        }
    }

    pub(super) fn bind(
        &mut self,
        home: HomeSlotKey,
        temp: TempId,
        allocation_site: AllocationSite,
        owner: AllocationHomeOwner,
    ) {
        // caller 已结束异值目标 home；同值写回保留原 owner，即使旧 SSA 别名已耗尽。
        let root = self
            .homes
            .entry(home)
            .or_insert_with(|| ActiveAllocationHome {
                aliases: BTreeSet::new(),
                owner,
                allocation_site,
            });
        root.aliases.insert(temp);
        self.by_temp.insert(temp, home);
    }

    pub(super) fn remove(&mut self, home: &HomeSlotKey) -> Option<ActiveAllocationHome> {
        let root = self.homes.remove(home)?;
        for temp in &root.aliases {
            self.by_temp.remove(temp);
        }
        // 返回旧别名供精确覆盖或 dispatch 判定使用，不能先清空被取走的 owner。
        Some(root)
    }

    pub(super) fn remove_homes(&mut self, homes: &BTreeSet<HomeSlotKey>) {
        for home in homes {
            self.remove(home);
        }
    }

    pub(super) fn clear(&mut self) {
        self.homes.clear();
        self.by_temp.clear();
    }
}
