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
    SsaValue, UseSite,
};

type FixedState = Vec<CompactSet<DefId>>;
type ValueState = Vec<CompactSet<SsaValue>>;

struct DefLookupTables {
    fixed: Vec<BTreeMap<Reg, DefId>>,
    open_must: Vec<Option<OpenDefId>>,
    open_may: Vec<Option<OpenDefId>>,
}

struct BlockReachingState {
    fixed_in: Vec<FixedState>,
    fixed_out: Vec<FixedState>,
    open_in: Vec<CompactSet<OpenDefId>>,
    open_out: Vec<CompactSet<OpenDefId>>,
}

struct InstructionFacts {
    reaching_defs: Vec<InstrReachingDefs>,
    reaching_values: Vec<InstrReachingValues>,
    use_defs: Vec<InstrUseDefs>,
    use_values: Vec<InstrUseValues>,
    def_uses: Vec<Vec<UseSite>>,
    open_reaching_defs: Vec<CompactSet<OpenDefId>>,
    open_use_defs: Vec<CompactSet<OpenDefId>>,
    open_def_uses: Vec<Vec<OpenUseSite>>,
}

struct BlockValueState {
    fixed_in: Vec<ValueState>,
    fixed_out: Vec<ValueState>,
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
        fixed: vec![BTreeMap::<Reg, DefId>::new(); proto.instrs.len()],
        open_must: vec![None; proto.instrs.len()],
        open_may: vec![None; proto.instrs.len()],
    };

    for block in cfg.block_order.iter().copied() {
        let Some(instr_indices) = instr_indices(cfg, block) else {
            continue;
        };

        for instr_index in instr_indices {
            let effect = &instr_effects[instr_index];

            for reg in effect
                .fixed_must_defs
                .iter()
                .chain(effect.fixed_may_defs.iter())
            {
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
                lookups.fixed[instr_index].insert(reg, id);
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
        fixed_in: vec![vec![CompactSet::Empty; reg_count]; cfg.blocks.len()],
        fixed_out: vec![vec![CompactSet::Empty; reg_count]; cfg.blocks.len()],
        open_in: vec![CompactSet::Empty; cfg.blocks.len()],
        open_out: vec![CompactSet::Empty; cfg.blocks.len()],
    };

    solve_reaching_defs(cfg, graph_facts, &instr_effects, &lookups, &mut block_state);

    let mut instruction_facts = InstructionFacts {
        reaching_defs: vec![InstrReachingDefs::default(); proto.instrs.len()],
        reaching_values: vec![InstrReachingValues::default(); proto.instrs.len()],
        use_defs: vec![InstrUseDefs::default(); proto.instrs.len()],
        use_values: vec![InstrUseValues::default(); proto.instrs.len()],
        def_uses: vec![Vec::new(); defs.len()],
        open_reaching_defs: vec![CompactSet::Empty; proto.instrs.len()],
        open_use_defs: vec![CompactSet::Empty; proto.instrs.len()],
        open_def_uses: vec![Vec::new(); open_defs.len()],
    };

    materialize_instruction_facts(
        cfg,
        &instr_effects,
        &lookups,
        &open_defs,
        &block_state,
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

    materialize_value_facts(
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
        &mut instruction_facts,
    );

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
        reaching_values: instruction_facts.reaching_values,
        use_defs: instruction_facts.use_defs,
        use_values: instruction_facts.use_values,
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
        children,
    }
}

/// `Open(start)` 表示“从 start 到当前 top 的连续值包”，而不是单个开放尾值。
///
/// 因此如果当前 reaching 的 open def 实际从更晚寄存器开始，那么 `start..tail_start-1`
/// 这一段仍然是被这条指令真实读取的固定寄存器前缀，必须进入 use/liveness。
fn resolved_fixed_use_regs(
    effect: &InstrEffect,
    current_open: &CompactSet<OpenDefId>,
    open_defs: &[OpenDef],
) -> BTreeSet<Reg> {
    let mut regs = effect.fixed_uses.clone();

    let Some(start_reg) = effect.open_use else {
        return regs;
    };

    if current_open.len() != 1 {
        return regs;
    }

    let open_def_id = current_open
        .iter()
        .next()
        .expect("len checked above, exactly one reaching open def exists");
    let Some(open_def) = open_defs.get(open_def_id.index()) else {
        return regs;
    };
    if open_def.start_reg.index() <= start_reg.index() {
        return regs;
    }

    for index in start_reg.index()..open_def.start_reg.index() {
        regs.insert(Reg(index));
    }

    regs
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
