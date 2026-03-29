//! CFG/GraphFacts/Dataflow 共用的紧凑容器。
//!
//! 这些容器只表达“固定寄存器索引上的稀疏/小集合状态”，不承载 CFG 或 SSA 语义。
//! 把它们单独拆出来，是为了避免 Dataflow 相关实现细节继续把 `cfg/common` 撑成
//! 一个混合文件，同时也让 debug/structure 等消费方共享同一套紧凑表示。

use std::borrow::Borrow;
use std::collections::BTreeSet;
use std::ops::Index;

use crate::transformer::Reg;

/// 固定寄存器上的紧凑值集合。
///
/// 数据流里的大多数寄存器在任一点上要么没有 reaching 值，要么只有一个值；直接为每个
/// 单元素状态分配 `BTreeSet` 会把 materialize/snapshot 阶段的常数项放得很大。这里
/// 先把最常见的 0/1 元素情况内联进枚举，只在真正多定义时才退化到 `BTreeSet`。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum CompactSet<T> {
    #[default]
    Empty,
    One(T),
    Many(BTreeSet<T>),
}

impl<T> CompactSet<T>
where
    T: Copy + Ord,
{
    pub fn singleton(value: T) -> Self {
        Self::One(value)
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }

    pub fn len(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::One(_) => 1,
            Self::Many(values) => values.len(),
        }
    }

    pub fn contains(&self, value: &T) -> bool {
        match self {
            Self::Empty => false,
            Self::One(existing) => existing == value,
            Self::Many(values) => values.contains(value),
        }
    }

    pub fn clear(&mut self) {
        *self = Self::Empty;
    }

    pub fn insert(&mut self, value: T) -> bool {
        match self {
            Self::Empty => {
                *self = Self::One(value);
                true
            }
            Self::One(existing) => {
                if *existing == value {
                    false
                } else {
                    *self = Self::Many(BTreeSet::from([*existing, value]));
                    true
                }
            }
            Self::Many(values) => values.insert(value),
        }
    }

    pub fn extend<I>(&mut self, values: I)
    where
        I: IntoIterator<Item = T>,
    {
        for value in values {
            self.insert(value);
        }
    }

    pub fn iter(&self) -> CompactSetIter<'_, T> {
        match self {
            Self::Empty => CompactSetIter::Empty,
            Self::One(value) => CompactSetIter::One(std::iter::once(value)),
            Self::Many(values) => CompactSetIter::Many(values.iter()),
        }
    }
}

pub enum CompactSetIter<'a, T> {
    Empty,
    One(std::iter::Once<&'a T>),
    Many(std::collections::btree_set::Iter<'a, T>),
}

impl<'a, T> Iterator for CompactSetIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Empty => None,
            Self::One(iter) => iter.next(),
            Self::Many(iter) => iter.next(),
        }
    }
}

impl<'a, T> IntoIterator for &'a CompactSet<T>
where
    T: Copy + Ord,
{
    type Item = &'a T;
    type IntoIter = CompactSetIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// 一条指令在某个时点对固定寄存器的稀疏视图。
///
/// 数据流求解内部本来就是按寄存器索引保存状态；这里继续沿用这个布局，
/// 避免把每条指令的 snapshot 再重建成 `BTreeMap`。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegValueMap<T> {
    regs: Vec<CompactSet<T>>,
}

impl<T> RegValueMap<T>
where
    T: Copy + Ord,
{
    pub fn with_reg_count(reg_count: usize) -> Self {
        Self {
            regs: vec![CompactSet::Empty; reg_count],
        }
    }

    pub fn from_state(state: &[CompactSet<T>]) -> Self {
        Self {
            regs: state.to_vec(),
        }
    }

    pub fn get<Q>(&self, reg: Q) -> Option<&CompactSet<T>>
    where
        Q: Borrow<Reg>,
    {
        self.regs
            .get(reg.borrow().index())
            .filter(|values| !values.is_empty())
    }

    pub fn insert(&mut self, reg: Reg, values: CompactSet<T>) {
        if values.is_empty() {
            return;
        }
        let slot = self
            .regs
            .get_mut(reg.index())
            .expect("reg map should already be sized for every reachable register");
        *slot = values;
    }

    pub fn keys(&self) -> impl Iterator<Item = Reg> + '_ {
        self.iter().map(|(reg, _)| reg)
    }

    pub fn values(&self) -> impl Iterator<Item = &CompactSet<T>> + '_ {
        self.iter().map(|(_, values)| values)
    }

    pub fn iter(&self) -> impl Iterator<Item = (Reg, &CompactSet<T>)> + '_ {
        self.regs
            .iter()
            .enumerate()
            .filter_map(|(index, values)| (!values.is_empty()).then_some((Reg(index), values)))
    }
}

impl<T> Default for RegValueMap<T> {
    fn default() -> Self {
        Self { regs: Vec::new() }
    }
}

impl<T> Index<&Reg> for RegValueMap<T>
where
    T: Copy + Ord,
{
    type Output = CompactSet<T>;

    fn index(&self, index: &Reg) -> &Self::Output {
        self.get(*index)
            .expect("indexed register should exist and have a non-empty reaching set")
    }
}
