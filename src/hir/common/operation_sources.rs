//! 保留互斥表达式合并后的全部原操作来源。
//!
//! 来源由原 NEWTABLE/GETTABLE/SETTABLE lowering 发布；改写 owner 先证明形状与求值轨迹，再合并来源。
//! 例如 `(a and {}) or (b and {})` 的共享尾仍须同时满足两处分配的物理许可。
//! 合并用持久 DAG，不逐次复制已有集合；查询和 proto remap 按共享节点去重，避免
//! 重复展开或递归栈。未知分支保留在域内，不能借其它已知分支取得原槽证明。

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use super::HirSourceSite;

#[derive(Debug, Clone, Default)]
pub(crate) enum HirOperationSources {
    #[default]
    Unknown,
    Single(HirSourceSite),
    Alternatives(Arc<(Self, Self)>),
}

/// 同一不可变事实快照内的来源归约缓存；缓存同时持有 DAG，防止地址被复用。
/// 例如逐层合并同布局读取时，每个旧来源只校验一次，不在每个父分支重扫历史来源。
pub(crate) struct HirSourceFactsCache<T> {
    sites: BTreeMap<HirSourceSite, Option<T>>,
    pairs: BTreeMap<
        *const (HirOperationSources, HirOperationSources),
        (HirOperationSources, Option<T>),
    >,
}

impl<T> Default for HirSourceFactsCache<T> {
    fn default() -> Self {
        Self {
            sites: BTreeMap::new(),
            pairs: BTreeMap::new(),
        }
    }
}

impl<T: Copy + Eq> HirSourceFactsCache<T> {
    /// 全部来源必须产生同一事实；未知来源或任一失败沿 DAG 传播，不能从部分来源签发许可。
    pub(crate) fn common_fact(
        &mut self,
        source: &HirOperationSources,
        mut query: impl FnMut(HirSourceSite) -> Option<T>,
    ) -> Option<T> {
        let mut pending = vec![(source, false)];
        while let Some((source, exiting)) = pending.pop() {
            match source {
                HirOperationSources::Unknown => {}
                HirOperationSources::Single(site) => {
                    self.sites.entry(*site).or_insert_with(|| query(*site));
                }
                HirOperationSources::Alternatives(pair) => {
                    let key = Arc::as_ptr(pair);
                    if self.pairs.contains_key(&key) {
                        continue;
                    }
                    if exiting {
                        let left = self.cached(&pair.0);
                        let right = self.cached(&pair.1);
                        let fact = left.filter(|_| left == right);
                        self.pairs.insert(key, (source.clone(), fact));
                    } else {
                        pending.extend([(source, true), (&pair.1, false), (&pair.0, false)]);
                    }
                }
            }
        }
        self.cached(source)
    }

    fn cached(&self, source: &HirOperationSources) -> Option<T> {
        match source {
            HirOperationSources::Unknown => None,
            HirOperationSources::Single(site) => self.sites[site],
            HirOperationSources::Alternatives(pair) => self.pairs[&Arc::as_ptr(pair)].1,
        }
    }
}

impl PartialEq for HirOperationSources {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Unknown, Self::Unknown) => true,
            (Self::Single(left), Self::Single(right)) => left == right,
            (Self::Alternatives(left), Self::Alternatives(right)) => Arc::ptr_eq(left, right),
            _ => false,
        }
    }
}

impl HirOperationSources {
    /// 只合并来源，不签发形状或互斥执行证明；调用者必须先完成对应事务验证。
    pub(crate) fn alternatives(&self, other: &Self) -> Self {
        if self == other {
            self.clone()
        } else {
            Self::Alternatives(Arc::new((self.clone(), other.clone())))
        }
    }

    pub(crate) fn try_for_each_known(
        &self,
        mut visit: impl FnMut(HirSourceSite) -> Option<()>,
    ) -> Option<()> {
        let mut pending = vec![self];
        let mut visited = BTreeSet::new();
        while let Some(source) = pending.pop() {
            match source {
                Self::Unknown => return None,
                Self::Single(site) => visit(*site)?,
                Self::Alternatives(pair) => {
                    if visited.insert(Arc::as_ptr(pair)) {
                        pending.extend([&pair.1, &pair.0]);
                    }
                }
            }
        }
        Some(())
    }

    /// 同一 DAG 中每个来源与共享节点只处理一次。原树在整个重建期间仍被借用，
    /// 指针只作本次遍历去重键，不作为跨快照或跨层身份。
    pub(crate) fn rewrite_sites(&mut self, mut rewrite: impl FnMut(&mut HirSourceSite)) -> bool {
        let mut pending = vec![(&*self, false)];
        let mut sites = BTreeMap::new();
        let mut pairs = BTreeMap::new();
        let mut changed = false;
        while let Some((source, exiting)) = pending.pop() {
            match source {
                Self::Unknown => {}
                Self::Single(site) => {
                    sites.entry(*site).or_insert_with(|| {
                        let mut mapped = *site;
                        rewrite(&mut mapped);
                        changed |= mapped != *site;
                        mapped
                    });
                }
                Self::Alternatives(pair) => {
                    let key = Arc::as_ptr(pair);
                    if pairs.contains_key(&key) {
                        continue;
                    }
                    if exiting {
                        let left = pair.0.mapped(&sites, &pairs);
                        let right = pair.1.mapped(&sites, &pairs);
                        let mapped = if left == pair.0 && right == pair.1 {
                            source.clone()
                        } else {
                            left.alternatives(&right)
                        };
                        pairs.insert(key, mapped);
                    } else {
                        pending.extend([(source, true), (&pair.1, false), (&pair.0, false)]);
                    }
                }
            }
        }
        if changed {
            *self = self.mapped(&sites, &pairs);
        }
        changed
    }

    fn mapped(
        &self,
        sites: &BTreeMap<HirSourceSite, HirSourceSite>,
        pairs: &BTreeMap<*const (Self, Self), Self>,
    ) -> Self {
        match self {
            Self::Unknown => Self::Unknown,
            Self::Single(site) => Self::Single(sites[site]),
            Self::Alternatives(pair) => pairs[&Arc::as_ptr(pair)].clone(),
        }
    }
}
