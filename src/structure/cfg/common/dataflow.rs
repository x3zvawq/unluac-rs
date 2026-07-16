//! Dataflow 层的稳定事实与查询。
//!
//! 这里承接 low-IR + CFG + GraphFacts 推导出的 canonical SSA / liveness / effect 事实。
//! 下游应通过这里提供的查询接口读取定义、phi 和 reaching/use 信息，而不是直接依赖
//! 这些事实在内存中的当前组织形状。

use std::collections::{BTreeSet, VecDeque};
use std::fmt;
use std::ops::Range;

use crate::transformer::{InstrRef, Reg};

use super::cfg::EdgeRef;
use super::cfg::{BlockRef, Cfg};

/// SSA 只给真实活跃寄存器保存一份当前值，避免按指令复制整个寄存器状态。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SsaRegMap {
    entries: Vec<(Reg, SsaValue)>,
}

impl SsaRegMap {
    pub(crate) fn from_sorted_entries(entries: Vec<(Reg, SsaValue)>) -> Self {
        debug_assert!(entries.windows(2).all(|pair| pair[0].0 < pair[1].0));
        Self { entries }
    }

    pub fn get(&self, reg: Reg) -> Option<SsaValue> {
        self.entries
            .binary_search_by_key(&reg.index(), |(stored, _)| stored.index())
            .ok()
            .map(|index| self.entries[index].1)
    }

    pub fn iter(&self) -> impl Iterator<Item = (Reg, SsaValue)> + '_ {
        self.entries.iter().copied()
    }

    pub fn values(&self) -> impl Iterator<Item = SsaValue> + '_ {
        self.entries.iter().map(|(_, value)| *value)
    }

    pub(crate) fn map_values(&mut self, mut map: impl FnMut(SsaValue) -> SsaValue) {
        for (_, value) in &mut self.entries {
            *value = map(*value);
        }
    }
}

/// 一个 proto 的数据流事实，以及它的子 proto 事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataflowFacts {
    pub instr_effects: Vec<InstrEffect>,
    pub effect_summaries: Vec<SideEffectSummary>,
    pub defs: Vec<Def>,
    pub open_defs: Vec<OpenDef>,
    pub instr_defs: Vec<Vec<DefId>>,
    pub block_entry_values: Vec<SsaRegMap>,
    pub block_exit_values: Vec<SsaRegMap>,
    pub use_values: Vec<InstrUseValues>,
    pub(crate) def_uses: Vec<Vec<UseSite>>,
    pub(crate) def_phi_uses: Vec<Vec<PhiId>>,
    pub(crate) phi_uses: Vec<Vec<UseSite>>,
    pub(crate) phi_phi_uses: Vec<Vec<PhiId>>,
    pub open_use_sources: Vec<OpenUseSources>,
    pub live_in: Vec<BTreeSet<Reg>>,
    pub live_out: Vec<BTreeSet<Reg>>,
    pub open_live_in: Vec<bool>,
    pub open_live_out: Vec<bool>,
    pub phi_candidates: Vec<PhiCandidate>,
    pub(crate) phi_block_ranges: Vec<Range<usize>>,
    pub(crate) phi_use_blocks: Vec<Option<BlockRef>>,
    pub children: Vec<DataflowFacts>,
}

impl DataflowFacts {
    pub fn block_entry_value(&self, block: BlockRef, reg: Reg) -> SsaValue {
        self.block_entry_values
            .get(block.index())
            .and_then(|values| values.get(reg))
            .unwrap_or(SsaValue::Entry(reg))
    }

    pub fn block_exit_value(&self, block: BlockRef, reg: Reg) -> SsaValue {
        self.block_exit_values
            .get(block.index())
            .and_then(|values| values.get(reg))
            .unwrap_or(SsaValue::Entry(reg))
    }

    pub fn use_value(&self, instr: InstrRef, reg: Reg) -> SsaValue {
        self.use_values
            .get(instr.index())
            .and_then(|values| values.fixed.get(reg))
            .unwrap_or(SsaValue::Entry(reg))
    }

    pub fn use_values_at(&self, instr: InstrRef) -> &SsaRegMap {
        &self
            .use_values
            .get(instr.index())
            .expect("dataflow should have a use-value summary for every instruction")
            .fixed
    }

    pub fn open_use_sources_at(&self, instr: InstrRef) -> &OpenUseSources {
        self.open_use_sources
            .get(instr.index())
            .expect("dataflow should have an open-source use summary for every instruction")
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
        self.phi_uses.get(phi_id.index()).map_or(0, Vec::len)
    }

    pub fn phi_consumer_ids(&self, phi_id: PhiId) -> &[PhiId] {
        self.phi_phi_uses
            .get(phi_id.index())
            .map_or(&[], Vec::as_slice)
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

    pub fn phi_used_only_in_block(&self, phi_id: PhiId, block: BlockRef) -> bool {
        self.phi_use_count(phi_id) > 0
            && self.phi_use_blocks.get(phi_id.index()).copied().flatten() == Some(block)
    }

    /// SSA 值是否只被指定指令直接读取，且没有继续流入其他 phi。
    pub(crate) fn value_used_only_by(&self, value: SsaValue, instr: InstrRef, reg: Reg) -> bool {
        let is_only_site =
            |uses: &[UseSite]| matches!(uses, [site] if site.instr == instr && site.reg == reg);
        match value {
            SsaValue::Def(def) => {
                self.def_uses
                    .get(def.index())
                    .is_some_and(|uses| is_only_site(uses))
                    && self.def_phi_uses.get(def.index()).is_none_or(Vec::is_empty)
            }
            SsaValue::Phi(phi) => {
                self.phi_uses
                    .get(phi.index())
                    .is_some_and(|uses| is_only_site(uses))
                    && self.phi_phi_uses.get(phi.index()).is_none_or(Vec::is_empty)
            }
            SsaValue::Entry(_) => false,
        }
    }

    /// 计算"真正死亡"的 phi 集合——既没有任何指令直接读取，也没有被任何存活 phi
    /// 的 incoming 间接引用。返回的 `BTreeSet<PhiId>` 中的 phi 可以安全地跳过物化。
    pub fn compute_truly_dead_phis(&self) -> BTreeSet<PhiId> {
        if self.phi_candidates.is_empty() {
            return BTreeSet::new();
        }

        // Step 1: 收集被至少一条指令直接使用的 phi（instruction-level alive）。
        let mut alive = BTreeSet::new();
        for values in &self.use_values {
            for value in values.fixed.values() {
                if let SsaValue::Phi(phi_id) = value {
                    alive.insert(phi_id);
                }
            }
        }

        // Step 2: 从 alive phi 反向传播——如果某个 alive phi 的 incoming 边上
        //         predecessor 出口处寄存器的 SSA 值是另一个 phi，则那个 phi 也 alive。
        let mut queue: VecDeque<PhiId> = alive.iter().copied().collect();
        while let Some(phi_id) = queue.pop_front() {
            let phi = &self.phi_candidates[phi_id.index()];
            for incoming in &phi.incoming {
                if let SsaValue::Phi(upstream) = incoming.value
                    && alive.insert(upstream)
                {
                    queue.push_back(upstream);
                }
            }
        }

        // Step 3: dead = all - alive
        self.phi_candidates
            .iter()
            .map(|phi| phi.id)
            .filter(|id| !alive.contains(id))
            .collect()
    }

    pub fn leaf_defs(&self, root: SsaValue) -> BTreeSet<DefId> {
        let mut defs = BTreeSet::new();
        let mut seen = BTreeSet::new();
        let mut pending = vec![root];
        while let Some(value) = pending.pop() {
            match value {
                SsaValue::Entry(_) => {}
                SsaValue::Def(def) => {
                    defs.insert(def);
                }
                SsaValue::Phi(phi) if seen.insert(phi) => {
                    if let Some(candidate) = self.phi_candidate(phi) {
                        pending.extend(candidate.incoming.iter().map(|incoming| incoming.value));
                    }
                }
                SsaValue::Phi(_) => {}
            }
        }
        defs
    }

    pub fn value_contains(&self, root: SsaValue, target: SsaValue) -> bool {
        let mut pending = vec![root];
        let mut seen_phis = BTreeSet::new();
        while let Some(value) = pending.pop() {
            if value == target {
                return true;
            }
            let SsaValue::Phi(phi_id) = value else {
                continue;
            };
            if !seen_phis.insert(phi_id) {
                continue;
            }
            if let Some(phi) = self.phi_candidate(phi_id) {
                pending.extend(phi.incoming.iter().map(|incoming| incoming.value));
            }
        }
        false
    }

    /// 判断一个底层定义经任意 phi 传播后，是否在允许区域之外被真实指令读取。
    pub fn def_has_use_outside(
        &self,
        cfg: &Cfg,
        def: DefId,
        allowed_blocks: &BTreeSet<BlockRef>,
    ) -> bool {
        let mut seen = BTreeSet::new();
        let mut pending = self
            .def_phi_uses
            .get(def.index())
            .into_iter()
            .flatten()
            .copied()
            .collect::<Vec<_>>();
        if self.def_uses.get(def.index()).is_some_and(|uses| {
            uses.iter()
                .any(|site| !allowed_blocks.contains(&cfg.instr_to_block[site.instr.index()]))
        }) {
            return true;
        }
        while let Some(phi) = pending.pop() {
            if !seen.insert(phi) {
                continue;
            }
            if self.phi_uses.get(phi.index()).is_some_and(|uses| {
                uses.iter()
                    .any(|site| !allowed_blocks.contains(&cfg.instr_to_block[site.instr.index()]))
            }) {
                return true;
            }
            pending.extend(
                self.phi_phi_uses
                    .get(phi.index())
                    .into_iter()
                    .flatten()
                    .copied(),
            );
        }
        false
    }
}

/// 一条 low-IR 指令在数据流层的固定/开放读写摘要。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct InstrEffect {
    pub fixed_uses: BTreeSet<Reg>,
    pub fixed_must_defs: BTreeSet<Reg>,
    pub open_use: Option<Reg>,
    pub open_must_def: Option<Reg>,
}

impl InstrEffect {
    /// 指令是否必定覆盖该固定寄存器；open result 从起始槽一直覆盖到栈顶。
    pub fn must_define(&self, reg: Reg) -> bool {
        self.fixed_must_defs.contains(&reg)
            || self
                .open_must_def
                .is_some_and(|start| reg.index() >= start.index())
    }
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

/// 一个 open use 可能到达的函数入口尾包与真实 producer。
///
/// `has_entry` 不能折叠成空 def 集：在合流点它表示至少一条路径没有执行任何
/// open producer，HIR 只有在函数入口确为 vararg 尾包时才能解释它。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct OpenUseSources {
    pub(crate) has_entry: bool,
    pub(crate) defs: BTreeSet<OpenDefId>,
}

impl OpenUseSources {
    pub fn has_entry(&self) -> bool {
        self.has_entry
    }

    pub fn defs(&self) -> &BTreeSet<OpenDefId> {
        &self.defs
    }

    pub(crate) fn insert_entry(&mut self) -> bool {
        let changed = !self.has_entry;
        self.has_entry = true;
        changed
    }

    pub(crate) fn insert_def(&mut self, def: OpenDefId) -> bool {
        self.defs.insert(def)
    }

    pub(crate) fn merge(&mut self, other: &Self) -> bool {
        let old_len = self.defs.len();
        let entry_changed = other.has_entry && self.insert_entry();
        self.defs.extend(other.defs.iter().copied());
        entry_changed || self.defs.len() != old_len
    }
}

/// 一条指令真实读取的寄存器及其唯一 SSA 值。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct InstrUseValues {
    pub fixed: SsaRegMap,
}

/// 一个固定定义被使用的位置。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct UseSite {
    pub instr: InstrRef,
    pub reg: Reg,
}

/// 一个 SSA phi。
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
    /// `None` 表示函数入口的初始值；真实 CFG 输入按边记录，不能按 predecessor 去重。
    pub edge: Option<EdgeRef>,
    pub pred: Option<BlockRef>,
    pub value: SsaValue,
}

/// 一个固定寄存器值在 canonical SSA 里的稳定身份。
///
/// 这里区分“真实 low-IR 定义”和“block 入口合流出的 phi 值”，是为了让后续层
/// 不用重复从 `use_defs = {def_a, def_b}` 里反推“其实这是同一个 merge 后的值”。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum SsaValue {
    Entry(Reg),
    Def(DefId),
    Phi(PhiId),
}

impl fmt::Display for SsaValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Entry(reg) => write!(f, "entry({reg})"),
            Self::Def(def) => def.fmt(f),
            Self::Phi(phi) => phi.fmt(f),
        }
    }
}
