//! Dataflow 层的稳定事实与查询。
//!
//! 这里承接 low-IR + CFG + GraphFacts 推导出的 SSA-like / liveness / effect 事实。
//! 下游应通过这里提供的查询接口读取定义、phi 和 reaching/use 信息，而不是直接依赖
//! 这些事实在内存中的当前组织形状。

use std::collections::BTreeSet;
use std::ops::Range;

use crate::transformer::{InstrRef, Reg};

use super::cfg::{BlockRef, Cfg};
use super::storage::RegValueMap;

/// 一个 proto 的数据流事实，以及它的子 proto 事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataflowFacts {
    pub instr_effects: Vec<InstrEffect>,
    pub effect_summaries: Vec<SideEffectSummary>,
    pub defs: Vec<Def>,
    pub open_defs: Vec<OpenDef>,
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
    pub(crate) phi_block_ranges: Vec<Range<usize>>,
    pub children: Vec<DataflowFacts>,
}

impl DataflowFacts {
    pub fn reaching_defs_at(&self, instr: InstrRef) -> &InstrReachingDefs {
        self.reaching_defs
            .get(instr.index())
            .expect("dataflow should have a reaching-def snapshot for every instruction")
    }

    pub fn reaching_values_at(&self, instr: InstrRef) -> &InstrReachingValues {
        self.reaching_values
            .get(instr.index())
            .expect("dataflow should have a reaching-value snapshot for every instruction")
    }

    pub fn use_defs_at(&self, instr: InstrRef) -> &InstrUseDefs {
        self.use_defs
            .get(instr.index())
            .expect("dataflow should have a use-def summary for every instruction")
    }

    pub fn use_values_at(&self, instr: InstrRef) -> &InstrUseValues {
        self.use_values
            .get(instr.index())
            .expect("dataflow should have a use-value summary for every instruction")
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
        self.use_values
            .iter()
            .flat_map(|uses| uses.fixed.values())
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
        let mut saw_use = false;

        for (instr_index, use_values) in self.use_values.iter().enumerate() {
            let used_here = use_values
                .fixed
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
