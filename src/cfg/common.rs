//! 这个文件集中声明 CFG、图分析和数据流层共享的公共类型。
//!
//! 这些层都不再带 dialect-specific 语义，所以这里直接把“稳定 id、图结构、
//! 数据流事实”收拢成一套共享契约，避免后续 `decompile` 壳和真实实现各维护一份。

use std::borrow::Borrow;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Index;

use crate::transformer::{InstrRef, LowInstr, Reg};

/// 一个 proto 的控制流图，以及它的子 proto 图。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CfgGraph {
    pub cfg: Cfg,
    pub children: Vec<CfgGraph>,
}

/// 单个 proto 的基础控制流图。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Cfg {
    pub blocks: Vec<BasicBlock>,
    pub edges: Vec<CfgEdge>,
    pub entry_block: BlockRef,
    pub exit_block: BlockRef,
    pub block_order: Vec<BlockRef>,
    pub instr_to_block: Vec<BlockRef>,
    pub preds: Vec<Vec<EdgeRef>>,
    pub succs: Vec<Vec<EdgeRef>>,
    pub reachable_blocks: BTreeSet<BlockRef>,
}

/// 边的稳定引用。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
pub struct EdgeRef(pub usize);

impl EdgeRef {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// block 的稳定引用。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
pub struct BlockRef(pub usize);

impl BlockRef {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 一个 basic block。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Default)]
pub struct BasicBlock {
    pub kind: BlockKind,
    pub instrs: InstrRange,
}

/// block 的类别。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Default)]
pub enum BlockKind {
    #[default]
    Normal,
    SyntheticExit,
}

/// 指令线性区间。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct InstrRange {
    pub start: InstrRef,
    pub len: usize,
}

impl InstrRange {
    pub const fn new(start: InstrRef, len: usize) -> Self {
        Self { start, len }
    }

    pub const fn end(self) -> usize {
        self.start.index() + self.len
    }

    pub const fn is_empty(self) -> bool {
        self.len == 0
    }

    pub const fn last(self) -> Option<InstrRef> {
        if self.len == 0 {
            None
        } else {
            Some(InstrRef(self.start.index() + self.len - 1))
        }
    }
}

impl Default for InstrRange {
    fn default() -> Self {
        Self::new(InstrRef(0), 0)
    }
}

/// CFG 边。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct CfgEdge {
    pub from: BlockRef,
    pub to: BlockRef,
    pub kind: EdgeKind,
}

/// CFG 原生边类别。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum EdgeKind {
    Fallthrough,
    Jump,
    BranchTrue,
    BranchFalse,
    LoopBody,
    LoopExit,
    Return,
    TailCall,
}

/// 一个 proto 的图分析事实，以及它的子 proto 事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GraphFacts {
    pub rpo: Vec<BlockRef>,
    pub dominator_tree: DominatorTree,
    pub post_dominator_tree: PostDominatorTree,
    pub dominance_frontier: Vec<BTreeSet<BlockRef>>,
    pub backedges: Vec<EdgeRef>,
    pub loop_headers: BTreeSet<BlockRef>,
    pub natural_loops: Vec<NaturalLoop>,
    pub children: Vec<GraphFacts>,
}

/// 支配树。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DominatorTree {
    pub parent: Vec<Option<BlockRef>>,
    pub children: Vec<Vec<BlockRef>>,
    pub order: Vec<BlockRef>,
}

/// 后支配树。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct PostDominatorTree {
    pub parent: Vec<Option<BlockRef>>,
    pub children: Vec<Vec<BlockRef>>,
    pub order: Vec<BlockRef>,
}

/// 一条 natural loop 事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NaturalLoop {
    pub header: BlockRef,
    pub backedge: EdgeRef,
    pub blocks: BTreeSet<BlockRef>,
}

/// 一个 proto 的数据流事实，以及它的子 proto 事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataflowFacts {
    pub instr_effects: Vec<InstrEffect>,
    pub effect_summaries: Vec<SideEffectSummary>,
    pub defs: Vec<Def>,
    pub open_defs: Vec<OpenDef>,
    pub reg_versions: BTreeMap<Reg, Vec<DefId>>,
    pub instr_defs: Vec<Vec<DefId>>,
    pub reaching_defs: Vec<InstrReachingDefs>,
    pub reaching_values: Vec<InstrReachingValues>,
    pub use_defs: Vec<InstrUseDefs>,
    pub use_values: Vec<InstrUseValues>,
    pub def_uses: Vec<Vec<UseSite>>,
    pub open_reaching_defs: Vec<BTreeSet<OpenDefId>>,
    pub open_use_defs: Vec<BTreeSet<OpenDefId>>,
    pub open_def_uses: Vec<Vec<OpenUseSite>>,
    pub live_in: Vec<BTreeSet<Reg>>,
    pub live_out: Vec<BTreeSet<Reg>>,
    pub open_live_in: Vec<bool>,
    pub open_live_out: Vec<bool>,
    pub phi_candidates: Vec<PhiCandidate>,
    pub children: Vec<DataflowFacts>,
}

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

/// 一条 low-IR 指令在数据流层的固定/开放读写摘要。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct InstrEffect {
    pub fixed_uses: BTreeSet<Reg>,
    pub fixed_must_defs: BTreeSet<Reg>,
    pub fixed_may_defs: BTreeSet<Reg>,
    pub open_use: Option<Reg>,
    pub open_must_def: Option<Reg>,
    pub open_may_def: Option<Reg>,
}

/// 一条指令的副作用摘要。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SideEffectSummary {
    pub tags: BTreeSet<EffectTag>,
}

/// 当前阶段关心的副作用标签。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum EffectTag {
    Alloc,
    ReadTable,
    WriteTable,
    ReadEnv,
    WriteEnv,
    ReadUpvalue,
    WriteUpvalue,
    Call,
    Close,
}

/// 一个固定寄存器定义的唯一身份。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct DefId(pub usize);

impl DefId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 一个开放结果包定义的唯一身份。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct OpenDefId(pub usize);

impl OpenDefId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 一个固定寄存器定义实例。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct Def {
    pub id: DefId,
    pub reg: Reg,
    pub instr: InstrRef,
    pub block: BlockRef,
}

/// 一个开放结果包定义实例。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct OpenDef {
    pub id: OpenDefId,
    pub start_reg: Reg,
    pub instr: InstrRef,
    pub block: BlockRef,
}

/// 一条指令在执行前可见的 reaching defs。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct InstrReachingDefs {
    pub fixed: RegValueMap<DefId>,
}

/// 一条指令真实 use 对应到哪些定义。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct InstrUseDefs {
    pub fixed: RegValueMap<DefId>,
    pub open: BTreeSet<OpenDefId>,
}

/// 一条指令在执行前可见的 SSA-like 值身份。
///
/// `reaching_defs` 保留底层真实 `DefId` 证据，这里则负责把 block 入口已经确认的
/// phi 合流替换成稳定的 `SsaValue::Phi`，供 HIR 之类的后续层直接消费。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct InstrReachingValues {
    pub fixed: RegValueMap<SsaValue>,
}

/// 一条指令真实 use 对应到哪些 SSA-like 值身份。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct InstrUseValues {
    pub fixed: RegValueMap<SsaValue>,
}

/// 一个固定定义被使用的位置。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct UseSite {
    pub instr: InstrRef,
    pub reg: Reg,
}

/// 一个开放定义被消费的位置。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct OpenUseSite {
    pub instr: InstrRef,
    pub start_reg: Reg,
}

/// 一个 SSA-like phi 候选。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PhiCandidate {
    pub id: PhiId,
    pub block: BlockRef,
    pub reg: Reg,
    pub incoming: Vec<PhiIncoming>,
}

/// 一个 phi 候选的稳定身份。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct PhiId(pub usize);

impl PhiId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 一个 predecessor 边给 phi 提供的候选版本。
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct PhiIncoming {
    pub pred: BlockRef,
    pub defs: BTreeSet<DefId>,
}

/// 一个寄存器值在 SSA-like 视图里的稳定身份。
///
/// 这里区分“真实 low-IR 定义”和“block 入口合流出的 phi 值”，是为了让后续层
/// 不用重复从 `use_defs = {def_a, def_b}` 里反推“其实这是同一个 merge 后的值”。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum SsaValue {
    Def(DefId),
    Phi(PhiId),
}

impl Cfg {
    /// block 末尾指令通常决定了边形态，所以这里提供统一入口避免各层重复取尾。
    pub fn terminator<'a>(&self, instrs: &'a [LowInstr], block: BlockRef) -> Option<&'a LowInstr> {
        self.blocks
            .get(block.index())
            .and_then(|basic_block| basic_block.instrs.last())
            .and_then(|instr| instrs.get(instr.index()))
    }
}
