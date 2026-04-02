//! 这个文件实现基于 low-IR + CFG + GraphFacts 的基础数据流分析。
//!
//! 这里先把后续结构恢复必需的“读写、副作用、def-use、liveness、phi 候选”
//! 一次性统一算出来，避免 StructureFacts 再反向重复扫底层 low-IR。

mod effects;
mod fixed;
mod liveness;
mod phi;
mod values;

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use crate::transformer::{
    AccessBase, AccessKey, BranchOperands, CaptureSource, CondOperand, LowInstr, LoweredChunk,
    LoweredProto, Reg, RegRange, ResultPack, ValueOperand, ValuePack,
};

use self::effects::{compute_instr_effect, compute_reg_count, compute_side_effect_summary};
use self::fixed::{materialize_instruction_facts, solve_reaching_defs};
use self::liveness::solve_liveness;
use self::phi::compute_phi_candidates;
use self::values::materialize_value_facts;
use super::common::{
    BlockRef, Cfg, CfgGraph, CompactSet, DataflowFacts, Def, DefId, EffectTag, GraphFacts,
    InstrEffect, InstrReachingDefs, InstrReachingValues, InstrUseDefs, InstrUseValues, OpenDef,
    OpenDefId, OpenUseSite, PhiCandidate, PhiId, PhiIncoming, RegValueMap, SideEffectSummary,
    SsaValue, UseSite, ValueFactsStorage,
};

type FixedState = TrackedState<DefId>;
type ValueState = TrackedState<SsaValue>;

struct DefLookupTables {
    fixed: Vec<FixedDefLookup>,
    open_must: Vec<Option<OpenDefId>>,
    open_may: Vec<Option<OpenDefId>>,
}

#[derive(Debug, Clone, Default)]
struct FixedDefLookup {
    must: Vec<(Reg, DefId)>,
    may: Vec<(Reg, DefId)>,
}

impl FixedDefLookup {
    fn defines(&self, reg: Reg) -> bool {
        self.must
            .iter()
            .chain(self.may.iter())
            .any(|(candidate, _)| *candidate == reg)
    }
}

struct BlockReachingState {
    fixed_in: Vec<FixedState>,
    fixed_out: Vec<FixedState>,
    open_in: Vec<CompactSet<OpenDefId>>,
    open_out: Vec<CompactSet<OpenDefId>>,
}

struct InstructionFacts {
    reaching_defs: Vec<InstrReachingDefs>,
    use_defs: Vec<InstrUseDefs>,
    def_uses: Vec<Vec<UseSite>>,
    open_reaching_defs: Vec<CompactSet<OpenDefId>>,
    open_use_defs: Vec<CompactSet<OpenDefId>>,
    open_def_uses: Vec<Vec<OpenUseSite>>,
}

struct BlockValueState {
    fixed_in: Vec<ValueState>,
    fixed_out: Vec<ValueState>,
}

#[derive(Debug, Clone)]
struct TrackedState<T> {
    regs: Vec<CompactSet<T>>,
    active_regs: Vec<Reg>,
    active_marks: Vec<bool>,
    active_sorted: bool,
}

impl<T> TrackedState<T>
where
    T: Copy + Ord,
{
    fn new(reg_count: usize) -> Self {
        Self {
            regs: vec![CompactSet::Empty; reg_count],
            active_regs: Vec::new(),
            active_marks: vec![false; reg_count],
            active_sorted: true,
        }
    }

    fn get(&self, reg: Reg) -> &CompactSet<T> {
        self.regs
            .get(reg.index())
            .expect("tracked state should have a slot for every reachable register")
    }

    fn set_singleton(&mut self, reg: Reg, value: T) -> bool {
        self.set_compact(reg, CompactSet::singleton(value))
    }

    fn insert(&mut self, reg: Reg, value: T) -> bool {
        let index = reg.index();
        let changed = self.regs[index].insert(value);
        if changed {
            self.ensure_active(reg);
        }
        changed
    }

    fn extend_from(&mut self, other: &Self) -> bool {
        let mut changed = false;

        for reg in other.active_regs.iter().copied() {
            match other.get(reg) {
                CompactSet::Empty => {}
                CompactSet::One(value) => {
                    changed |= self.insert(reg, *value);
                }
                CompactSet::Many(values) => {
                    for value in values {
                        changed |= self.insert(reg, *value);
                    }
                }
            }
        }

        changed
    }

    fn snapshot_map(&mut self) -> RegValueMap<T> {
        if !self.active_sorted {
            self.active_regs.sort_unstable_by_key(|reg| reg.index());
            self.active_sorted = true;
        }
        let mut entries = Vec::with_capacity(self.active_regs.len());
        for &reg in &self.active_regs {
            let values = self
                .regs
                .get(reg.index())
                .cloned()
                .expect("tracked state should have a slot for every active register");
            if !values.is_empty() {
                entries.push((reg, values));
            }
        }
        RegValueMap::from_sparse_entries(entries)
    }

    fn set_compact(&mut self, reg: Reg, values: CompactSet<T>) -> bool {
        let index = reg.index();
        if self.regs[index] == values {
            return false;
        }
        self.regs[index] = values;
        if !self.regs[index].is_empty() {
            self.ensure_active(reg);
        }
        true
    }

    fn ensure_active(&mut self, reg: Reg) {
        let index = reg.index();
        if self.active_marks[index] {
            return;
        }

        if let Some(last_reg) = self.active_regs.last().copied()
            && last_reg.index() > index
        {
            self.active_sorted = false;
        }
        self.active_marks[index] = true;
        self.active_regs.push(reg);
    }
}

impl<T> PartialEq for TrackedState<T>
where
    T: Copy + Ord + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.regs == other.regs
    }
}

impl<T> Eq for TrackedState<T> where T: Copy + Ord + Eq {}

struct FixedUseScratch {
    regs: Vec<Reg>,
    seen: Vec<bool>,
}

impl FixedUseScratch {
    fn new(reg_count: usize) -> Self {
        Self {
            regs: Vec::new(),
            seen: vec![false; reg_count],
        }
    }

    fn resolve<'a>(
        &'a mut self,
        effect: &InstrEffect,
        current_open: &CompactSet<OpenDefId>,
        open_defs: &[OpenDef],
    ) -> &'a [Reg] {
        self.clear();

        for reg in effect.fixed_uses.iter().copied() {
            self.push(reg);
        }

        let Some(start_reg) = effect.open_use else {
            self.sort();
            return &self.regs;
        };

        if current_open.len() != 1 {
            self.sort();
            return &self.regs;
        }

        let open_def_id = current_open
            .iter()
            .next()
            .expect("len checked above, exactly one reaching open def exists");
        let Some(open_def) = open_defs.get(open_def_id.index()) else {
            self.sort();
            return &self.regs;
        };
        if open_def.start_reg.index() <= start_reg.index() {
            self.sort();
            return &self.regs;
        }

        for index in start_reg.index()..open_def.start_reg.index() {
            self.push(Reg(index));
        }
        self.sort();
        &self.regs
    }

    fn clear(&mut self) {
        for reg in self.regs.iter().copied() {
            self.seen[reg.index()] = false;
        }
        self.regs.clear();
    }

    fn push(&mut self, reg: Reg) {
        if self.seen[reg.index()] {
            return;
        }

        self.seen[reg.index()] = true;
        self.regs.push(reg);
    }

    fn sort(&mut self) {
        self.regs.sort_unstable_by_key(|reg| reg.index());
    }
}

struct MaterializeScratch {
    fixed_use_regs: FixedUseScratch,
}

impl MaterializeScratch {
    fn new(reg_count: usize) -> Self {
        Self {
            fixed_use_regs: FixedUseScratch::new(reg_count),
        }
    }
}

struct ValueMaterializeCtx<'a> {
    lookups: &'a DefLookupTables,
    open_defs: &'a [OpenDef],
    phi_candidates: &'a [PhiCandidate],
    phi_block_ranges: &'a [Range<usize>],
}

struct BlockLiveness {
    live_in: Vec<BTreeSet<Reg>>,
    live_out: Vec<BTreeSet<Reg>>,
    open_live_in: Vec<bool>,
    open_live_out: Vec<bool>,
}

/// 对整个 lowered chunk 递归计算数据流事实。
pub fn analyze_dataflow(
    chunk: &LoweredChunk,
    cfg: &CfgGraph,
    graph_facts: &GraphFacts,
) -> DataflowFacts {
    analyze_proto_dataflow(&chunk.main, &cfg.cfg, graph_facts, &cfg.children)
}

fn analyze_proto_dataflow(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    child_cfgs: &[CfgGraph],
) -> DataflowFacts {
    let instr_effects = proto
        .instrs
        .iter()
        .map(compute_instr_effect)
        .collect::<Vec<_>>();
    let effect_summaries = proto
        .instrs
        .iter()
        .map(compute_side_effect_summary)
        .collect::<Vec<_>>();
    let reg_count = compute_reg_count(proto, &instr_effects);

    let mut defs = Vec::new();
    let mut open_defs = Vec::new();
    let mut instr_defs = vec![Vec::new(); proto.instrs.len()];
    let mut lookups = DefLookupTables {
        fixed: vec![FixedDefLookup::default(); proto.instrs.len()],
        open_must: vec![None; proto.instrs.len()],
        open_may: vec![None; proto.instrs.len()],
    };

    for block in cfg.block_order.iter().copied() {
        let Some(instr_indices) = instr_indices(cfg, block) else {
            continue;
        };

        for instr_index in instr_indices {
            let effect = &instr_effects[instr_index];

            for reg in &effect.fixed_must_defs {
                let id = DefId(defs.len());
                let reg = *reg;
                let def = Def {
                    id,
                    reg,
                    instr: crate::transformer::InstrRef(instr_index),
                    block,
                };
                defs.push(def);
                instr_defs[instr_index].push(id);
                lookups.fixed[instr_index].must.push((reg, id));
            }

            for reg in &effect.fixed_may_defs {
                let id = DefId(defs.len());
                let reg = *reg;
                let def = Def {
                    id,
                    reg,
                    instr: crate::transformer::InstrRef(instr_index),
                    block,
                };
                defs.push(def);
                instr_defs[instr_index].push(id);
                lookups.fixed[instr_index].may.push((reg, id));
            }

            if let Some(start_reg) = effect.open_must_def {
                let id = OpenDefId(open_defs.len());
                open_defs.push(OpenDef {
                    id,
                    start_reg,
                    instr: crate::transformer::InstrRef(instr_index),
                    block,
                });
                lookups.open_must[instr_index] = Some(id);
            }

            if let Some(start_reg) = effect.open_may_def {
                let id = OpenDefId(open_defs.len());
                open_defs.push(OpenDef {
                    id,
                    start_reg,
                    instr: crate::transformer::InstrRef(instr_index),
                    block,
                });
                lookups.open_may[instr_index] = Some(id);
            }
        }
    }

    let mut block_state = BlockReachingState {
        fixed_in: vec![TrackedState::new(reg_count); cfg.blocks.len()],
        fixed_out: vec![TrackedState::new(reg_count); cfg.blocks.len()],
        open_in: vec![CompactSet::Empty; cfg.blocks.len()],
        open_out: vec![CompactSet::Empty; cfg.blocks.len()],
    };

    solve_reaching_defs(cfg, graph_facts, &instr_effects, &lookups, &mut block_state);

    let mut instruction_facts = InstructionFacts {
        reaching_defs: vec![InstrReachingDefs::default(); proto.instrs.len()],
        use_defs: vec![InstrUseDefs::default(); proto.instrs.len()],
        def_uses: vec![Vec::new(); defs.len()],
        open_reaching_defs: vec![CompactSet::Empty; proto.instrs.len()],
        open_use_defs: vec![CompactSet::Empty; proto.instrs.len()],
        open_def_uses: vec![Vec::new(); open_defs.len()],
    };

    let mut materialize_scratch = MaterializeScratch::new(reg_count);

    materialize_instruction_facts(
        cfg,
        &instr_effects,
        &lookups,
        &open_defs,
        &block_state,
        &mut materialize_scratch,
        &mut instruction_facts,
    );

    let liveness = solve_liveness(cfg, graph_facts, &instr_effects, &instruction_facts);

    let phi_candidates = compute_phi_candidates(
        cfg,
        graph_facts,
        &defs,
        &liveness.live_in,
        &block_state.fixed_out,
        &lookups.fixed,
    );
    let phi_block_ranges = index_phi_candidate_ranges(cfg, &phi_candidates);

    let value_facts = if phi_candidates.is_empty() {
        ValueFactsStorage::NoPhi
    } else {
        let materialized = materialize_value_facts(
            cfg,
            graph_facts,
            &instr_effects,
            ValueMaterializeCtx {
                lookups: &lookups,
                open_defs: &open_defs,
                phi_candidates: &phi_candidates,
                phi_block_ranges: &phi_block_ranges,
            },
            reg_count,
            &mut materialize_scratch,
            &instruction_facts,
        );
        ValueFactsStorage::Materialized {
            reaching_values: materialized.reaching_values,
            use_values: materialized.use_values,
        }
    };

    let children = proto
        .children
        .iter()
        .zip(child_cfgs.iter())
        .zip(graph_facts.children.iter())
        .map(|((child_proto, child_cfg), child_graph_facts)| {
            analyze_proto_dataflow(
                child_proto,
                &child_cfg.cfg,
                child_graph_facts,
                &child_cfg.children,
            )
        })
        .collect();

    DataflowFacts {
        instr_effects,
        effect_summaries,
        defs,
        open_defs,
        instr_defs,
        reaching_defs: instruction_facts.reaching_defs,
        use_defs: instruction_facts.use_defs,
        def_uses: instruction_facts.def_uses,
        open_reaching_defs: collect_open_sets(&instruction_facts.open_reaching_defs),
        open_use_defs: collect_open_sets(&instruction_facts.open_use_defs),
        open_def_uses: instruction_facts.open_def_uses,
        live_in: liveness.live_in,
        live_out: liveness.live_out,
        open_live_in: liveness.open_live_in,
        open_live_out: liveness.open_live_out,
        phi_candidates,
        phi_block_ranges,
        value_facts,
        children,
    }
}

/// `Open(start)` 表示“从 start 到当前 top 的连续值包”，而不是单个开放尾值。
///
/// 因此如果当前 reaching 的 open def 实际从更晚寄存器开始，那么 `start..tail_start-1`
/// 这一段仍然是被这条指令真实读取的固定寄存器前缀，必须进入 use/liveness。
fn resolved_fixed_use_regs<'a>(
    scratch: &'a mut MaterializeScratch,
    effect: &InstrEffect,
    current_open: &CompactSet<OpenDefId>,
    open_defs: &[OpenDef],
) -> &'a [Reg] {
    scratch.fixed_use_regs.resolve(effect, current_open, open_defs)
}

fn instr_indices(cfg: &Cfg, block: BlockRef) -> Option<impl Iterator<Item = usize>> {
    let range = cfg.blocks.get(block.index())?.instrs;
    if range.is_empty() {
        return None;
    }

    Some(range.start.index()..range.end())
}

fn index_phi_candidate_ranges(cfg: &Cfg, phi_candidates: &[PhiCandidate]) -> Vec<Range<usize>> {
    let mut ranges = vec![0..0; cfg.blocks.len()];
    let mut next_phi = 0;

    for (block_index, range) in ranges.iter_mut().enumerate() {
        let start = next_phi;
        while next_phi < phi_candidates.len()
            && phi_candidates[next_phi].block.index() == block_index
        {
            next_phi += 1;
        }
        *range = start..next_phi;
    }

    ranges
}

fn collect_open_sets(sets: &[CompactSet<OpenDefId>]) -> Vec<BTreeSet<OpenDefId>> {
    sets.iter()
        .map(|set| set.iter().copied().collect())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tracked_state_snapshot_preserves_sparse_contents() {
        let mut state = TrackedState::new(8);
        state.set_singleton(Reg(4), DefId(11));
        state.insert(Reg(4), DefId(12));
        state.set_singleton(Reg(1), DefId(3));

        let snapshot = state.snapshot_map();

        assert_eq!(snapshot.keys().collect::<Vec<_>>(), vec![Reg(1), Reg(4)]);
        assert_eq!(
            snapshot.get(Reg(1)).cloned(),
            Some(CompactSet::singleton(DefId(3)))
        );
        assert_eq!(
            snapshot.get(Reg(4)).cloned(),
            Some(CompactSet::Many(BTreeSet::from([DefId(11), DefId(12)])))
        );
        assert_eq!(snapshot.get(Reg(7)), None);
    }

    #[test]
    fn resolved_fixed_use_regs_should_include_open_gap_prefix() {
        let mut effect = InstrEffect::default();
        effect.fixed_uses.extend([Reg(1), Reg(5)]);
        effect.open_use = Some(Reg(2));

        let open_defs = vec![OpenDef {
            id: OpenDefId(0),
            start_reg: Reg(4),
            instr: crate::transformer::InstrRef(0),
            block: BlockRef(0),
        }];
        let current_open = CompactSet::singleton(OpenDefId(0));
        let mut scratch = MaterializeScratch::new(8);

        let regs = resolved_fixed_use_regs(&mut scratch, &effect, &current_open, &open_defs);

        assert_eq!(regs, &[Reg(1), Reg(2), Reg(3), Reg(5)]);
    }

    #[test]
    fn block_phi_values_should_override_reaching_defs_in_snapshot() {
        let mut state = ValueState::new(4);
        state.set_singleton(Reg(1), SsaValue::Def(DefId(7)));

        values::apply_block_phi_values(
            &mut state,
            &[PhiCandidate {
                id: PhiId(2),
                block: BlockRef(1),
                reg: Reg(1),
                incoming: Vec::new(),
            }],
        );

        let snapshot = state.snapshot_map();

        assert_eq!(
            snapshot.get(Reg(1)).cloned(),
            Some(CompactSet::singleton(SsaValue::Phi(PhiId(2))))
        );
    }

    #[test]
    fn no_phi_value_queries_should_wrap_defs_as_ssa_defs() {
        let reaching_defs = InstrReachingDefs {
            fixed: RegValueMap::from_sparse_entries(vec![
                (Reg(0), CompactSet::singleton(DefId(1))),
                (Reg(2), CompactSet::Many(BTreeSet::from([DefId(3), DefId(4)]))),
            ]),
        };
        let use_defs = InstrUseDefs {
            fixed: RegValueMap::from_sparse_entries(vec![(Reg(2), CompactSet::singleton(DefId(4)))]),
            open: BTreeSet::new(),
        };
        let dataflow = DataflowFacts {
            instr_effects: vec![InstrEffect::default()],
            effect_summaries: vec![SideEffectSummary::default()],
            defs: Vec::new(),
            open_defs: Vec::new(),
            instr_defs: vec![Vec::new()],
            reaching_defs: vec![reaching_defs],
            use_defs: vec![use_defs],
            def_uses: Vec::new(),
            open_reaching_defs: vec![BTreeSet::new()],
            open_use_defs: vec![BTreeSet::new()],
            open_def_uses: Vec::new(),
            live_in: Vec::new(),
            live_out: Vec::new(),
            open_live_in: Vec::new(),
            open_live_out: Vec::new(),
            phi_candidates: Vec::new(),
            phi_block_ranges: Vec::new(),
            value_facts: ValueFactsStorage::NoPhi,
            children: Vec::new(),
        };

        assert_eq!(
            dataflow
                .reaching_values_at(crate::transformer::InstrRef(0))
                .get(Reg(0))
                .map(|values| values.to_compact_set()),
            Some(CompactSet::singleton(SsaValue::Def(DefId(1))))
        );
        assert_eq!(
            dataflow
                .reaching_values_at(crate::transformer::InstrRef(0))
                .get(Reg(2))
                .map(|values| values.to_compact_set()),
            Some(CompactSet::Many(BTreeSet::from([
                SsaValue::Def(DefId(3)),
                SsaValue::Def(DefId(4)),
            ])))
        );
        assert_eq!(
            dataflow
                .use_values_at(crate::transformer::InstrRef(0))
                .get(Reg(2))
                .map(|values| values.to_compact_set()),
            Some(CompactSet::singleton(SsaValue::Def(DefId(4))))
        );
    }
}
