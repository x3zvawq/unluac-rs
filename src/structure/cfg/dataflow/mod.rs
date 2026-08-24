//! low-IR 到 canonical SSA、liveness 与副作用事实的统一入口。

mod effects;
mod liveness;
mod open;
mod ssa;

use std::collections::{BTreeSet, VecDeque};

use crate::decompile::{DecompileContext, DecompileError, DecompileState};
use crate::structure::StructureError;
use crate::transformer::{
    AccessBase, AccessKey, BranchSubject, CaptureSource, CondOperand, InstrRef, LowInstr,
    LoweredProto, Reg, RegRange, ResultPack, UnaryOpKind, ValueOperand, ValuePack,
};

use self::effects::{compute_instr_effect, compute_reg_count, compute_side_effect_summary};
use self::liveness::solve_liveness;
use self::open::analyze_open_values;
use self::ssa::build_ssa;
use super::common::{
    BlockRef, Cfg, CfgGraph, DataflowFacts, Def, DefId, EffectTag, GraphFacts, InstrEffect,
    PhiCandidate, SideEffectSummary, SsaValue,
};

struct BlockLiveness {
    live_in: Vec<BTreeSet<Reg>>,
    live_out: Vec<BTreeSet<Reg>>,
}

/// Dataflow 阶段入口：从 low-IR、CFG 和 GraphFacts 槽位读取事实，写回数据流事实。
pub(crate) fn analyze_dataflow(
    state: &mut DecompileState,
    _context: &DecompileContext<'_>,
) -> Result<(), DecompileError> {
    let lowered = state.require_lowered()?;
    let cfg = state.require_cfg()?;
    let graph_facts = state.require_graph_facts()?;
    state.dataflow = Some(compute_dataflow_facts(
        &lowered.main,
        &cfg.cfg,
        graph_facts,
        &cfg.children,
    )?);
    Ok(())
}

/// 对 proto 树计算数据流事实。
pub fn compute_dataflow_facts(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    child_cfgs: &[CfgGraph],
) -> Result<DataflowFacts, StructureError> {
    struct Frame<'a> {
        proto: &'a LoweredProto,
        cfg: &'a Cfg,
        graph_facts: &'a GraphFacts,
        child_cfgs: &'a [CfgGraph],
        next_child: usize,
        children: Vec<DataflowFacts>,
    }

    let mut stack = vec![Frame {
        proto,
        cfg,
        graph_facts,
        child_cfgs,
        next_child: 0,
        children: Vec::new(),
    }];
    loop {
        let child = {
            let frame = stack.last_mut().expect("dataflow proto frame is non-empty");
            if frame.proto.children.len() != frame.child_cfgs.len()
                || frame.proto.children.len() != frame.graph_facts.children.len()
            {
                return Err(StructureError::invalid(
                    "proto, CFG, and graph child counts disagree",
                ));
            }
            let index = frame.next_child;
            let child = frame.proto.children.get(index).map(|proto| {
                (
                    proto,
                    &frame.child_cfgs[index],
                    &frame.graph_facts.children[index],
                )
            });
            if child.is_some() {
                frame.next_child += 1;
            }
            child
        };
        if let Some((child_proto, child_cfg, child_graph)) = child {
            stack.push(Frame {
                proto: child_proto,
                cfg: &child_cfg.cfg,
                graph_facts: child_graph,
                child_cfgs: &child_cfg.children,
                next_child: 0,
                children: Vec::new(),
            });
            continue;
        }

        let frame = stack.pop().expect("dataflow proto frame is non-empty");
        let mut facts = compute_dataflow_proto(frame.proto, frame.cfg, frame.graph_facts)?;
        facts.children = frame.children;
        if let Some(parent) = stack.last_mut() {
            parent.children.push(facts);
        } else {
            return Ok(facts);
        }
    }
}

/// Compute one proto's block-local dataflow facts.  Proto scheduling is kept outside
/// this function so deep Luau child chains never recurse through the analysis stack.
fn compute_dataflow_proto(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
) -> Result<DataflowFacts, StructureError> {
    super::validate_cfg(cfg)?;
    if cfg.instr_to_block.len() != proto.instrs.len() {
        return Err(StructureError::invalid(format!(
            "CFG covers {} instructions, but the lowered proto contains {}",
            cfg.instr_to_block.len(),
            proto.instrs.len()
        )));
    }
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
    let reg_count = compute_reg_count(proto, &instr_effects)?;

    let entry_open_start = proto
        .signature
        .is_vararg
        .then_some(Reg(usize::from(proto.signature.num_params)));
    let incoming_slots = incoming_slots_by_edge(cfg);
    let open = analyze_open_values(
        cfg,
        graph_facts,
        &instr_effects,
        reg_count,
        entry_open_start,
        &incoming_slots,
    )?;
    let liveness = solve_liveness(
        cfg,
        graph_facts,
        &instr_effects,
        &open.fixed_liveness_use_regs,
        reg_count,
    )?;

    let mut defs = Vec::new();
    let mut instr_defs = vec![Vec::new(); proto.instrs.len()];
    let mut def_lookup = vec![Vec::new(); proto.instrs.len()];
    for block in cfg.block_order.iter().copied() {
        let Some(indices) = instr_indices(cfg, block) else {
            continue;
        };
        for instr_index in indices {
            for &reg in &instr_effects[instr_index].fixed_must_defs {
                let id = DefId(defs.len());
                defs.push(Def {
                    id,
                    reg,
                    instr: InstrRef(instr_index),
                    block,
                });
                instr_defs[instr_index].push(id);
                def_lookup[instr_index].push((reg, id));
            }
        }
    }

    let ssa = build_ssa(
        cfg,
        graph_facts,
        &defs,
        &def_lookup,
        &open.fixed_ssa_use_regs,
        &liveness.live_in,
        &liveness.live_out,
        reg_count,
        proto.instrs.len(),
        &incoming_slots,
    )?;
    Ok(DataflowFacts {
        instr_effects,
        effect_summaries,
        defs,
        open_defs: open.defs,
        instr_defs,
        block_entry_values: ssa.block_entry_values,
        block_exit_values: ssa.block_exit_values,
        block_end_values: ssa.block_end_values,
        use_values: ssa.use_values,
        def_uses: ssa.def_uses,
        def_phi_uses: ssa.def_phi_uses,
        phi_uses: ssa.phi_uses,
        phi_phi_uses: ssa.phi_phi_uses,
        phi_truly_dead: ssa.phi_truly_dead,
        open_use_sources: open.use_sources,
        live_in: liveness.live_in,
        live_out: liveness.live_out,
        open_live_in: open.live_in,
        open_live_out: open.live_out,
        phi_candidates: ssa.phis,
        phi_block_ranges: ssa.phi_block_ranges,
        phi_use_blocks: ssa.phi_use_blocks,
        children: Vec::new(),
    })
}

fn instr_indices(cfg: &Cfg, block: BlockRef) -> Option<impl Iterator<Item = usize>> {
    let range = cfg.blocks.get(block.index())?.instrs;
    (!range.is_empty()).then(|| range.start.index()..range.end())
}

fn index_phi_candidate_ranges(cfg: &Cfg, phis: &[PhiCandidate]) -> Vec<std::ops::Range<usize>> {
    let mut ranges = vec![0..0; cfg.blocks.len()];
    let mut next = 0;
    for (block_index, range) in ranges.iter_mut().enumerate() {
        let start = next;
        while next < phis.len() && phis[next].block.index() == block_index {
            next += 1;
        }
        *range = start..next;
    }
    ranges
}

fn incoming_slots_by_edge(cfg: &Cfg) -> Vec<Option<usize>> {
    let mut slots = vec![None; cfg.edges.len()];
    for block in &cfg.block_order {
        let mut next = usize::from(*block == cfg.entry_block);
        for edge in &cfg.preds[block.index()] {
            if cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from) {
                slots[edge.index()] = Some(next);
                next += 1;
            }
        }
    }
    slots
}

fn canonical_value(
    mut value: SsaValue,
    replacements: &[SsaValue],
) -> Result<SsaValue, StructureError> {
    let mut remaining = replacements.len() + 1;
    while let SsaValue::Phi(phi) = value {
        let Some(next) = replacements.get(phi.index()).copied() else {
            return Err(StructureError::invalid(format!(
                "SSA canonicalization references missing {phi}"
            )));
        };
        if next == value {
            break;
        }
        if remaining == 0 {
            return Err(StructureError::invalid(
                "SSA replacement graph contains a cycle",
            ));
        }
        value = next;
        remaining -= 1;
    }
    Ok(value)
}
