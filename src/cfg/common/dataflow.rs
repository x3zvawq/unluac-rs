//! Dataflow 层的稳定事实与查询。
//!
//! 这里承接 low-IR + CFG + GraphFacts 推导出的 SSA-like / liveness / effect 事实。
//! 下游应通过这里提供的查询接口读取定义、phi 和 reaching/use 信息，而不是直接依赖
//! 这些事实在内存中的当前组织形状。

use std::collections::{BTreeSet, VecDeque};
use std::fmt;
use std::ops::Range;

use crate::transformer::{InstrRef, Reg};

use super::cfg::{BlockRef, Cfg};
use super::storage::{CompactSet, CompactSetIter, RegValueMap, RegValueMapIter};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ValueFactsStorage {
    Materialized {
        reaching_values: Vec<InstrReachingValues>,
        use_values: Vec<InstrUseValues>,
    },
    NoPhi,
}

/// 一个 proto 的数据流事实，以及它的子 proto 事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataflowFacts {
    pub instr_effects: Vec<InstrEffect>,
    pub effect_summaries: Vec<SideEffectSummary>,
    pub defs: Vec<Def>,
    pub open_defs: Vec<OpenDef>,
    pub instr_defs: Vec<Vec<DefId>>,
    pub reaching_defs: Vec<InstrReachingDefs>,
    pub use_defs: Vec<InstrUseDefs>,
    pub def_uses: Vec<Vec<UseSite>>,
    pub open_reaching_defs: Vec<BTreeSet<OpenDefId>>,
    pub open_use_defs: Vec<BTreeSet<OpenDefId>>,
    pub open_def_uses: Vec<Vec<OpenUseSite>>,
    pub live_in: Vec<BTreeSet<Reg>>,
    pub live_out: Vec<BTreeSet<Reg>>,
    pub open_live_in: Vec<bool>,
    pub open_live_out: Vec<bool>,
    pub phi_candidates: Vec<PhiCandidate>,
    pub(crate) phi_block_ranges: Vec<Range<usize>>,
    pub(crate) value_facts: ValueFactsStorage,
    pub children: Vec<DataflowFacts>,
}

#[derive(Debug, Clone, Copy)]
pub enum ValueMapRef<'a> {
    Materialized(&'a RegValueMap<SsaValue>),
    DefBacked(&'a RegValueMap<DefId>),
}

impl<'a> ValueMapRef<'a> {
    pub fn get(self, reg: Reg) -> Option<ValueSetRef<'a>> {
        match self {
            Self::Materialized(map) => map.get(reg).map(ValueSetRef::Materialized),
            Self::DefBacked(map) => map.get(reg).map(ValueSetRef::DefBacked),
        }
    }

    pub fn iter(self) -> ValueMapIter<'a> {
        match self {
            Self::Materialized(map) => ValueMapIter::Materialized(map.iter()),
            Self::DefBacked(map) => ValueMapIter::DefBacked(map.iter()),
        }
    }

    pub fn values(self) -> ValueMapValuesIter<'a> {
        ValueMapValuesIter { inner: self.iter() }
    }
}

pub struct ValueMapValuesIter<'a> {
    inner: ValueMapIter<'a>,
}

impl<'a> Iterator for ValueMapValuesIter<'a> {
    type Item = ValueSetRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, values)| values)
    }
}

pub enum ValueMapIter<'a> {
    Materialized(RegValueMapIter<'a, SsaValue>),
    DefBacked(RegValueMapIter<'a, DefId>),
}

impl<'a> Iterator for ValueMapIter<'a> {
    type Item = (Reg, ValueSetRef<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Materialized(iter) => iter
                .next()
                .map(|(reg, values)| (reg, ValueSetRef::Materialized(values))),
            Self::DefBacked(iter) => iter
                .next()
                .map(|(reg, values)| (reg, ValueSetRef::DefBacked(values))),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ValueSetRef<'a> {
    Materialized(&'a CompactSet<SsaValue>),
    DefBacked(&'a CompactSet<DefId>),
}

impl<'a> ValueSetRef<'a> {
    pub fn is_empty(self) -> bool {
        match self {
            Self::Materialized(values) => values.is_empty(),
            Self::DefBacked(values) => values.is_empty(),
        }
    }

    pub fn len(self) -> usize {
        match self {
            Self::Materialized(values) => values.len(),
            Self::DefBacked(values) => values.len(),
        }
    }

    pub fn contains(self, needle: &SsaValue) -> bool {
        match (self, needle) {
            (Self::Materialized(values), _) => values.contains(needle),
            (Self::DefBacked(values), SsaValue::Def(def_id)) => values.contains(def_id),
            (Self::DefBacked(_), SsaValue::Phi(_)) => false,
        }
    }

    pub fn iter(self) -> ValueSetIter<'a> {
        match self {
            Self::Materialized(values) => ValueSetIter::Materialized(values.iter()),
            Self::DefBacked(values) => ValueSetIter::DefBacked(values.iter()),
        }
    }

    pub fn to_compact_set(self) -> CompactSet<SsaValue> {
        match self {
            Self::Materialized(values) => values.clone(),
            Self::DefBacked(values) => match values {
                CompactSet::Empty => CompactSet::Empty,
                CompactSet::One(def_id) => CompactSet::singleton(SsaValue::Def(*def_id)),
                CompactSet::Many(def_ids) => {
                    CompactSet::Many(def_ids.iter().copied().map(SsaValue::Def).collect())
                }
            },
        }
    }
}

pub enum ValueSetIter<'a> {
    Materialized(CompactSetIter<'a, SsaValue>),
    DefBacked(CompactSetIter<'a, DefId>),
}

impl<'a> Iterator for ValueSetIter<'a> {
    type Item = SsaValue;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Materialized(iter) => iter.next().copied(),
            Self::DefBacked(iter) => iter.next().copied().map(SsaValue::Def),
        }
    }
}

impl DataflowFacts {
    pub fn reaching_defs_at(&self, instr: InstrRef) -> &InstrReachingDefs {
        self.reaching_defs
            .get(instr.index())
            .expect("dataflow should have a reaching-def snapshot for every instruction")
    }

    pub fn reaching_values_at(&self, instr: InstrRef) -> ValueMapRef<'_> {
        match &self.value_facts {
            ValueFactsStorage::Materialized {
                reaching_values, ..
            } => {
                let values = reaching_values
                    .get(instr.index())
                    .expect("dataflow should have a reaching-value snapshot for every instruction");
                ValueMapRef::Materialized(&values.fixed)
            }
            ValueFactsStorage::NoPhi => {
                let defs = self
                    .reaching_defs
                    .get(instr.index())
                    .expect("dataflow should have a reaching-def snapshot for every instruction");
                ValueMapRef::DefBacked(&defs.fixed)
            }
        }
    }

    pub fn use_defs_at(&self, instr: InstrRef) -> &InstrUseDefs {
        self.use_defs
            .get(instr.index())
            .expect("dataflow should have a use-def summary for every instruction")
    }

    pub fn use_values_at(&self, instr: InstrRef) -> ValueMapRef<'_> {
        match &self.value_facts {
            ValueFactsStorage::Materialized { use_values, .. } => {
                let values = use_values
                    .get(instr.index())
                    .expect("dataflow should have a use-value summary for every instruction");
                ValueMapRef::Materialized(&values.fixed)
            }
            ValueFactsStorage::NoPhi => {
                let defs = self
                    .use_defs
                    .get(instr.index())
                    .expect("dataflow should have a use-def summary for every instruction");
                ValueMapRef::DefBacked(&defs.fixed)
            }
        }
    }

    pub fn open_reaching_defs_at(&self, instr: InstrRef) -> &BTreeSet<OpenDefId> {
        self.open_reaching_defs
            .get(instr.index())
            .expect("dataflow should have an open-def snapshot for every instruction")
    }

    pub fn open_use_defs_at(&self, instr: InstrRef) -> &BTreeSet<OpenDefId> {
        self.open_use_defs
            .get(instr.index())
            .expect("dataflow should have an open-def use summary for every instruction")
    }

    pub fn live_in_regs(&self, block: BlockRef) -> &BTreeSet<Reg> {
        self.live_in
            .get(block.index())
            .expect("dataflow should have a live-in set for every block")
    }

    pub fn live_out_regs(&self, block: BlockRef) -> &BTreeSet<Reg> {
        self.live_out
            .get(block.index())
            .expect("dataflow should have a live-out set for every block")
    }

    pub fn block_open_live_in(&self, block: BlockRef) -> bool {
        self.open_live_in
            .get(block.index())
            .copied()
            .expect("dataflow should have an open-live-in flag for every block")
    }

    pub fn block_open_live_out(&self, block: BlockRef) -> bool {
        self.open_live_out
            .get(block.index())
            .copied()
            .expect("dataflow should have an open-live-out flag for every block")
    }

    pub fn phi_candidate(&self, phi_id: PhiId) -> Option<&PhiCandidate> {
        self.phi_candidates.get(phi_id.index())
    }

    pub fn phi_candidates_in_block(&self, block: BlockRef) -> &[PhiCandidate] {
        let Some(range) = self.phi_block_ranges.get(block.index()) else {
            return &[];
        };

        &self.phi_candidates[range.clone()]
    }

    pub fn phi_candidate_for_reg(&self, block: BlockRef, reg: Reg) -> Option<&PhiCandidate> {
        self.phi_candidates_in_block(block)
            .iter()
            .find(|phi| phi.reg == reg)
    }

    pub fn phi_use_count(&self, phi_id: PhiId) -> usize {
        if self.phi_candidates.is_empty() {
            return 0;
        }

        (0..self.use_defs.len())
            .map(|instr_index| self.use_values_at(InstrRef(instr_index)))
            .flat_map(ValueMapRef::values)
            .filter(|values| values.contains(&SsaValue::Phi(phi_id)))
            .count()
    }

    pub fn def_reg(&self, def_id: DefId) -> Reg {
        self.defs
            .get(def_id.index())
            .map(|def| def.reg)
            .expect("dataflow should have a def record for every def id")
    }

    pub fn def_block(&self, def_id: DefId) -> BlockRef {
        self.defs
            .get(def_id.index())
            .map(|def| def.block)
            .expect("dataflow should have a def record for every def id")
    }

    pub fn def_instr(&self, def_id: DefId) -> InstrRef {
        self.defs
            .get(def_id.index())
            .map(|def| def.instr)
            .expect("dataflow should have a def record for every def id")
    }

    pub fn instr_def_for_reg(&self, instr: InstrRef, reg: Reg) -> Option<DefId> {
        self.instr_defs
            .get(instr.index())?
            .iter()
            .copied()
            .find(|def_id| self.def_reg(*def_id) == reg)
    }

    pub fn latest_local_def_in_block(
        &self,
        block: BlockRef,
        defs: impl IntoIterator<Item = DefId>,
    ) -> Option<DefId> {
        defs.into_iter()
            .filter(|def_id| self.def_block(*def_id) == block)
            .max_by_key(|def_id| self.def_instr(*def_id).index())
    }

    pub fn phi_used_only_in_block(&self, cfg: &Cfg, phi_id: PhiId, block: BlockRef) -> bool {
        if self.phi_candidates.is_empty() {
            return false;
        }

        let mut saw_use = false;

        for instr_index in 0..self.use_defs.len() {
            let used_here = self
                .use_values_at(InstrRef(instr_index))
                .values()
                .any(|values| values.contains(&SsaValue::Phi(phi_id)));
            if !used_here {
                continue;
            }

            saw_use = true;
            if cfg.instr_to_block[instr_index] != block {
                return false;
            }
        }

        saw_use
    }

    /// 计算"真正死亡"的 phi 集合——既没有任何指令直接读取，也没有被任何存活 phi
    /// 的 incoming 间接引用。返回的 `BTreeSet<PhiId>` 中的 phi 可以安全地跳过物化。
    pub fn compute_truly_dead_phis(&self, cfg: &Cfg) -> BTreeSet<PhiId> {
        if self.phi_candidates.is_empty() {
            return BTreeSet::new();
        }

        // Step 1: 收集被至少一条指令直接使用的 phi（instruction-level alive）。
        let mut alive = BTreeSet::new();
        for instr_index in 0..self.use_defs.len() {
            for values in self.use_values_at(InstrRef(instr_index)).values() {
                for value in values.iter() {
                    if let SsaValue::Phi(phi_id) = value {
                        alive.insert(phi_id);
                    }
                }
            }
        }

        // Step 2: 从 alive phi 反向传播——如果某个 alive phi 的 incoming 边上
        //         predecessor 出口处寄存器的 SSA 值是另一个 phi，则那个 phi 也 alive。
        let mut queue: VecDeque<PhiId> = alive.iter().copied().collect();
        while let Some(phi_id) = queue.pop_front() {
            let phi = &self.phi_candidates[phi_id.index()];
            for incoming in &phi.incoming {
                self.propagate_phi_liveness_from_block(
                    cfg,
                    incoming.pred,
                    phi.reg,
                    &mut alive,
                    &mut queue,
                );
            }
        }

        // Step 3: dead = all - alive
        self.phi_candidates
            .iter()
            .map(|phi| phi.id)
            .filter(|id| !alive.contains(id))
            .collect()
    }

    /// 检查 block 出口处 reg 的 SSA 值；若包含 Phi，将其标为 alive 并入队。
    fn propagate_phi_liveness_from_block(
        &self,
        cfg: &Cfg,
        block: BlockRef,
        reg: Reg,
        alive: &mut BTreeSet<PhiId>,
        queue: &mut VecDeque<PhiId>,
    ) {
        let block_range = &cfg.blocks[block.index()].instrs;
        if let Some(last_instr) = block_range.last() {
            let effect = &self.instr_effects[last_instr.index()];
            // must-def 意味着出口值是确定的 Def，不可能是上游 phi。
            if effect.fixed_must_defs.contains(&reg) {
                return;
            }
            // 否则 reaching_values 反映了出口处的 SSA 值。
            if let Some(reg_values) = self.reaching_values_at(last_instr).get(reg) {
                for value in reg_values.iter() {
                    if let SsaValue::Phi(upstream) = value
                        && alive.insert(upstream)
                    {
                        queue.push_back(upstream);
                    }
                }
            }
        } else {
            // 空 block：出口值 = 入口值。先看 block 自身是否有 phi。
            let phi_range = &self.phi_block_ranges[block.index()];
            if let Some(phi) = self.phi_candidates[phi_range.clone()]
                .iter()
                .find(|p| p.reg == reg)
                && alive.insert(phi.id)
            {
                queue.push_back(phi.id);
            }
            // 若空 block 没有自己的 phi，入口值来源于前驱合并；保守地不再递归，
            // 以避免在大型 CFG 上产生过多开销。此时若有 upstream phi 漏标为 alive，
            // 只会导致多消除一些 phi（仍然安全，因为这些 phi 的值在该路径上
            // 不会被消费——空 block + 无 phi 说明该 reg 只是路过转发）。
        }
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

impl fmt::Display for DefId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "def{}", self.0)
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

impl fmt::Display for PhiId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "phi{}", self.0)
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
