//! Dataflow 层的稳定事实与查询。
//!
//! 这里承接 low-IR + CFG + GraphFacts 推导出的 canonical SSA / liveness / effect 事实。
//! 下游应通过这里提供的查询接口读取定义、phi 和 reaching/use 信息，而不是直接依赖
//! 这些事实在内存中的当前组织形状。`RootObservation` 保留观察期间的物理栈合同，
//! 与 SSA 读写和副作用标签分别表达值依赖、可见事件及 root 存活边界。

use std::collections::BTreeSet;
use std::fmt;
use std::ops::Range;

use crate::transformer::{InstrRef, Reg};

use crate::structure::StructureError;

use super::cfg::EdgeRef;
use super::cfg::{BlockRef, Cfg};

/// SSA 只给真实活跃寄存器保存一份当前值，避免按指令复制整个寄存器状态。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SsaRegMap {
    entries: Vec<(Reg, SsaValue)>,
}

impl SsaRegMap {
    pub(crate) fn from_sorted_entries(
        entries: Vec<(Reg, SsaValue)>,
    ) -> Result<Self, StructureError> {
        if !entries.windows(2).all(|pair| pair[0].0 < pair[1].0) {
            return Err(StructureError::invalid(
                "SSA register map entries are not strictly sorted",
            ));
        }
        Ok(Self { entries })
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

    pub(crate) fn try_map_values<E>(
        &mut self,
        mut map: impl FnMut(SsaValue) -> Result<SsaValue, E>,
    ) -> Result<(), E> {
        for (_, value) in &mut self.entries {
            *value = map(*value)?;
        }
        Ok(())
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
    pub(crate) fixed_defs_by_reg: Vec<Vec<DefId>>,
    pub block_entry_values: Vec<SsaRegMap>,
    pub block_exit_values: Vec<SsaRegMap>,
    pub(crate) block_end_values: Vec<SsaRegMap>,
    pub use_values: Vec<InstrUseValues>,
    pub(crate) def_uses: Vec<Vec<UseSite>>,
    pub(crate) def_overwritten_values: Vec<Option<SsaValue>>,
    pub(crate) canonical_move_values: Vec<Option<SsaValue>>,
    pub(crate) def_phi_uses: Vec<Vec<PhiId>>,
    pub(crate) phi_uses: Vec<Vec<UseSite>>,
    pub(crate) phi_phi_uses: Vec<Vec<PhiId>>,
    pub(crate) phi_truly_dead: Vec<bool>,
    pub open_use_sources: Vec<OpenUseSources>,
    pub live_in: Vec<BTreeSet<Reg>>,
    pub live_out: Vec<BTreeSet<Reg>>,
    pub open_live_in: Vec<bool>,
    pub open_live_out: Vec<bool>,
    pub phi_candidates: Vec<PhiCandidate>,
    pub(crate) incoming_slots_by_edge: Vec<Option<usize>>,
    pub(crate) phi_block_ranges: Vec<Range<usize>>,
    pub(crate) phi_use_blocks: Vec<Option<BlockRef>>,
    pub children: Vec<DataflowFacts>,
}

impl DataflowFacts {
    /// 返回 exclusive low 区间内最后一次 fixed Def，包括不可达块中的定义。
    ///
    /// 索引在 Dataflow 产出时按指令顺序冻结；例如 debug local 入口不读取该槽，也能
    /// 查询初始化前缀。这里只回答线性区间内的 fixed 写入，不推断跨块 reaching value、
    /// open 覆盖或 Move 值根；调用方仍负责限定所属 block 与解释缺失定义。
    pub(crate) fn last_fixed_def_in_range(&self, reg: Reg, range: Range<usize>) -> Option<DefId> {
        let definitions = self.fixed_defs_by_reg.get(reg.index())?;
        let end = definitions.partition_point(|&def| self.def_instr(def).index() < range.end);
        let &def = definitions.get(end.checked_sub(1)?)?;
        (self.def_instr(def).index() >= range.start).then_some(def)
    }

    /// 最终 SSA 快照中的透明 Move 值根；Phi/Entry 保持原身份。
    ///
    /// None 表示该链没有可证明的源（例如不可达 Move 没有 use-value）。这里只证明
    /// 值恒等，不证明寄存器、close epoch 或物理根的生命周期，也不授权延后读取。
    pub(crate) fn canonical_move_value(&self, value: SsaValue) -> Option<SsaValue> {
        match value {
            SsaValue::Def(def) => self
                .canonical_move_values
                .get(def.index())
                .copied()
                .flatten(),
            _ => Some(value),
        }
    }

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

    /// 返回 basic block 末尾仍可由稀疏 SSA 证明的值。exit map 保存 live-out，end map
    /// 补充本块定义后已死的寄存器；只从前驱继承的槽再查询 entry，仍缺失则未知。
    pub(crate) fn block_end_value(&self, block: BlockRef, reg: Reg) -> Option<SsaValue> {
        self.block_exit_values
            .get(block.index())
            .and_then(|values| values.get(reg))
            .or_else(|| {
                self.block_end_values
                    .get(block.index())
                    .and_then(|values| values.get(reg))
            })
            .or_else(|| {
                self.block_entry_values
                    .get(block.index())
                    .and_then(|values| values.get(reg))
            })
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

    /// 按真实 CFG edge 读取同一 SSA snapshot 的 incoming；不包含合成 Entry 输入。
    ///
    /// SSA/open rename 共用的 slot 排列在 phi 压缩后不变。不同目标块的 edge 可以
    /// 占据同一 slot，因此仍须核对 edge 身份，不能把另一个 phi 的该槽误作结果。
    pub fn phi_incoming_for_edge(&self, phi: PhiId, edge: EdgeRef) -> Option<&PhiIncoming> {
        let slot = self
            .incoming_slots_by_edge
            .get(edge.index())
            .copied()
            .flatten()?;
        self.phi_candidate(phi)?
            .incoming
            .get(slot)
            .filter(|incoming| incoming.edge == Some(edge))
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

    pub fn phi_is_truly_dead(&self, phi_id: PhiId) -> bool {
        self.phi_truly_dead
            .get(phi_id.index())
            .copied()
            .expect("dataflow should have a dead/live flag for every phi")
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

    /// 当前写入覆盖的 canonical 值；不同路径身份不一致时返回未知。
    ///
    /// pruned SSA 的无读取槽可能没有入口 phi，不能直接采用支配树栈顶。Dataflow
    /// 用共享入口查询补齐稀疏快照间的覆盖关系；open result 覆盖表示未知。
    /// 这条物理覆盖关系不是值读取，不增加 SSA use，也不决定 HIR 绑定是否允许共址。
    pub fn def_overwritten_value(&self, def: DefId) -> Option<SsaValue> {
        self.def_overwritten_values[def.index()]
    }

    /// 最后一次值读取后、首个潜在 GC/cleanup 观察前的必定覆盖。
    ///
    /// 只证明同一 basic block 内、没有 phi use 的 canonical value epoch；返回覆盖 def
    /// 身份，不能把“未发现 root 保留事实”当作等价的释放证明。消费者还须验证当前唯一
    /// producer/use、捕获与求值顺序。例如 CALL r; SETLIST(..., r); MOVE r,callee
    /// 的结果不再跨后续调用独立保活，赋值给弱表且随后先 GC 的情况则没有此证明。
    pub fn unobserved_root_overwrite_after_last_use(&self, def: DefId, cfg: &Cfg) -> Option<DefId> {
        let block = self.def_block(def);
        let producer = self.def_instr(def).index();
        let home = self.def_reg(def);
        if !self.def_phi_uses[def.index()].is_empty() {
            return None;
        }
        let uses = &self.def_uses[def.index()];
        if uses.iter().any(|use_| {
            use_.instr.index() <= producer || cfg.instr_to_block[use_.instr.index()] != block
        }) {
            return None;
        }
        let last_use = uses.iter().map(|use_| use_.instr.index()).max()?;
        for index in last_use + 1..cfg.blocks[block.index()].instrs.end() {
            let summary = &self.effect_summaries[index];
            if summary.may_observe_gc_roots() || summary.root_observation != RootObservation::None {
                return None;
            }
            if self.instr_effects[index].must_define(home) {
                return self.instr_def_for_reg(InstrRef(index), home);
            }
        }
        None
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

    /// 展开 phi 链，返回最终可到达的 entry/def 身份。
    pub fn leaf_values(&self, root: SsaValue) -> BTreeSet<SsaValue> {
        let mut leaves = BTreeSet::new();
        let mut seen = BTreeSet::new();
        let mut pending = vec![root];
        while let Some(value) = pending.pop() {
            match value {
                SsaValue::Entry(_) | SsaValue::Def(_) => {
                    leaves.insert(value);
                }
                SsaValue::Phi(phi) if seen.insert(phi) => {
                    if let Some(candidate) = self.phi_candidate(phi) {
                        pending.extend(candidate.incoming.iter().map(|incoming| incoming.value));
                    }
                }
                SsaValue::Phi(_) => {}
            }
        }
        leaves
    }

    pub fn leaf_defs(&self, root: SsaValue) -> BTreeSet<DefId> {
        self.leaf_values(root)
            .into_iter()
            .filter_map(|value| match value {
                SsaValue::Def(def) => Some(def),
                SsaValue::Entry(_) | SsaValue::Phi(_) => None,
            })
            .collect()
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
    pub root_observation: RootObservation,
}

impl SideEffectSummary {
    /// 可能调用用户代码或触发分配的事件；不把 frame exit 或 cleanup 的专用协议混进来。
    pub fn may_observe_gc_roots(&self) -> bool {
        self.tags.iter().any(|tag| {
            matches!(
                tag,
                EffectTag::Alloc
                    | EffectTag::ReadTable
                    | EffectTag::WriteTable
                    | EffectTag::ReadEnv
                    | EffectTag::WriteEnv
                    | EffectTag::Call
                    | EffectTag::Metamethod
            )
        })
    }
}

/// 原始指令观察期间的物理 root 合同。只在同一 low-IR snapshot 内以 InstrRef 定位。
///
/// PrefixLowerBound 之外是未知，不能推出死亡；Call 的边界只描述 caller frame，
/// 被调用函数仍可通过自己的参数持有同一对象。这些事实不授权删除 producer 或延长词法 scope。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum RootObservation {
    #[default]
    None,
    FrameExit,
    /// Close 结束 open-upvalue/TBC 协议而不覆盖槽；不凭空证明此前未被观察的高槽存活。
    Close,
    PrefixLowerBound {
        end: usize,
    },
    Call {
        caller_end: Reg,
    },
}

impl RootObservation {
    pub fn keeps_home_rooted(self, home: Reg) -> bool {
        match self {
            Self::PrefixLowerBound { end } => home.index() < end,
            Self::Call { caller_end } => home.index() < caller_end.index(),
            Self::None | Self::FrameExit | Self::Close => false,
        }
    }

    /// 专用于普通调用的 collective 证明；不能把前缀下界当作排除上界。
    pub fn excludes_homes_from_caller(self, homes: &BTreeSet<Reg>) -> bool {
        matches!(self, Self::Call { caller_end }
            if homes.iter().all(|home| home.index() >= caller_end.index()))
    }
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
    Metamethod,
    MayThrow,
    Close,
    RegisterClose,
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
