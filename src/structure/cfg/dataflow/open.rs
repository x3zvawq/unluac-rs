//! 多返回值尾包的 transient SSA 分析。
//!
//! open result pack 的实际宽度由后续消费点和所有可达来源共同决定，不能塞进固定寄存器
//! SSA。这里消费 CFG、支配事实和 instruction open-use/must-def，内部建立独立 pack phi，
//! 最终投影函数入口尾包、真实 `OpenDefId` 来源、分层 fixed-prefix uses 与 open
//! liveness；它不把 pack phi 暴露给 Structure/HIR，也不参与源码结构选择。
//!
//! 输入形状：两条路径分别产生 `call()` 的 open results，merge 后从 r3 起消费 open pack。
//! 输出形状：消费点保留两条 `OpenDefId` 与可能的 `Entry`；所有来源共同具有的 fixed
//! prefix 才进入 SSA use，路径条件下可能读取的更宽 prefix 只进入 liveness。

use super::*;
use crate::structure::{EdgeRef, OpenDef, OpenDefId, OpenUseSources};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub(super) enum OpenValue {
    Entry,
    Def(OpenDefId),
    Phi(OpenPhiId),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct OpenPhiId(usize);

impl OpenPhiId {
    pub(super) const fn index(self) -> usize {
        self.0
    }
}

pub(super) struct OpenIncoming {
    pub(super) edge: Option<EdgeRef>,
    pub(super) value: OpenValue,
}

pub(super) struct OpenPhi {
    pub(super) incoming: Vec<OpenIncoming>,
}

pub(super) struct OpenAnalysis {
    pub(super) defs: Vec<OpenDef>,
    pub(super) use_sources: Vec<OpenUseSources>,
    pub(super) fixed_ssa_use_regs: Vec<Vec<Reg>>,
    pub(super) fixed_liveness_use_regs: Vec<Vec<Reg>>,
    pub(super) live_in: Vec<bool>,
    pub(super) live_out: Vec<bool>,
}

pub(super) fn analyze_open_values(
    cfg: &Cfg,
    graph: &GraphFacts,
    effects: &[super::super::common::InstrEffect],
    reg_count: usize,
    entry_open_start: Option<Reg>,
    incoming_slots: &[Option<usize>],
) -> OpenAnalysis {
    let (live_in, live_out) = solve_open_liveness(cfg, graph, effects);
    let mut defs = Vec::new();
    let mut instr_defs = vec![None; effects.len()];
    let mut def_blocks = BTreeSet::new();
    for block in cfg.block_order.iter().copied() {
        let Some(indices) = super::instr_indices(cfg, block) else {
            continue;
        };
        for instr_index in indices {
            let Some(start_reg) = effects[instr_index].open_must_def else {
                continue;
            };
            let id = OpenDefId(defs.len());
            defs.push(OpenDef {
                id,
                start_reg,
                instr: InstrRef(instr_index),
                block,
            });
            instr_defs[instr_index] = Some(id);
            def_blocks.insert(block);
        }
    }

    let phi_blocks = place_open_phis(cfg, graph, &def_blocks, &live_in);
    let mut block_phi = vec![None; cfg.blocks.len()];
    let mut phis = Vec::with_capacity(phi_blocks.len());
    for block in phi_blocks {
        let id = OpenPhiId(phis.len());
        block_phi[block.index()] = Some(id);
        let mut incoming = Vec::new();
        if block == cfg.entry_block {
            incoming.push(OpenIncoming {
                edge: None,
                value: OpenValue::Entry,
            });
        }
        incoming.extend(
            cfg.preds[block.index()]
                .iter()
                .copied()
                .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
                .map(|edge| OpenIncoming {
                    edge: Some(edge),
                    value: OpenValue::Entry,
                }),
        );
        phis.push(OpenPhi { incoming });
    }

    let mut uses = vec![None; effects.len()];
    rename_open(
        cfg,
        graph,
        effects,
        &instr_defs,
        &block_phi,
        &mut phis,
        &mut uses,
        incoming_slots,
    );

    let phi_sources = index_open_phi_sources(&phis);
    let mut use_sources = vec![OpenUseSources::default(); effects.len()];
    let mut fixed_ssa_use_regs = Vec::with_capacity(effects.len());
    let mut fixed_liveness_use_regs = Vec::with_capacity(effects.len());
    for (instr_index, effect) in effects.iter().enumerate() {
        let sources = open_sources_for_value(uses[instr_index], &phi_sources);
        use_sources[instr_index] = sources.clone();

        let mut ssa_regs = effect.fixed_uses.iter().copied().collect::<Vec<_>>();
        let mut liveness_regs = ssa_regs.clone();
        if let Some(start_reg) = effect.open_use {
            let (must_end, may_end) =
                fixed_prefix_ends(&sources, &defs, entry_open_start, start_reg, reg_count);
            ssa_regs.extend((start_reg.index()..must_end).map(Reg));
            liveness_regs.extend((start_reg.index()..may_end).map(Reg));
        }
        for regs in [&mut ssa_regs, &mut liveness_regs] {
            regs.sort_unstable_by_key(|reg| reg.index());
            regs.dedup();
            debug_assert!(regs.iter().all(|reg| reg.index() < reg_count));
        }
        fixed_ssa_use_regs.push(ssa_regs);
        fixed_liveness_use_regs.push(liveness_regs);
    }

    OpenAnalysis {
        defs,
        use_sources,
        fixed_ssa_use_regs,
        fixed_liveness_use_regs,
        live_in,
        live_out,
    }
}

fn solve_open_liveness(
    cfg: &Cfg,
    graph: &GraphFacts,
    effects: &[super::super::common::InstrEffect],
) -> (Vec<bool>, Vec<bool>) {
    let mut block_use = vec![false; cfg.blocks.len()];
    let mut block_def = vec![false; cfg.blocks.len()];
    for block in cfg.block_order.iter().copied() {
        let Some(indices) = super::instr_indices(cfg, block) else {
            continue;
        };
        let mut defined = false;
        for index in indices {
            if effects[index].open_use.is_some() && !defined {
                block_use[block.index()] = true;
            }
            if effects[index].open_must_def.is_some() {
                defined = true;
                block_def[block.index()] = true;
            }
        }
    }

    let mut live_in = vec![false; cfg.blocks.len()];
    let mut live_out = vec![false; cfg.blocks.len()];
    let mut worklist = graph.rpo.iter().rev().copied().collect::<VecDeque<_>>();
    let mut queued = vec![false; cfg.blocks.len()];
    for block in &worklist {
        queued[block.index()] = true;
    }
    while let Some(block) = worklist.pop_front() {
        queued[block.index()] = false;
        let new_out = cfg.succs[block.index()].iter().any(|edge| {
            let succ = cfg.edges[edge.index()].to;
            cfg.reachable_blocks.contains(&succ) && live_in[succ.index()]
        });
        let new_in = block_use[block.index()] || (new_out && !block_def[block.index()]);
        let changed = new_in != live_in[block.index()];
        live_in[block.index()] = new_in;
        live_out[block.index()] = new_out;
        if changed {
            for edge in &cfg.preds[block.index()] {
                let pred = cfg.edges[edge.index()].from;
                if cfg.reachable_blocks.contains(&pred) && !queued[pred.index()] {
                    queued[pred.index()] = true;
                    worklist.push_back(pred);
                }
            }
        }
    }
    (live_in, live_out)
}

fn place_open_phis(
    cfg: &Cfg,
    graph: &GraphFacts,
    def_blocks: &BTreeSet<BlockRef>,
    live_in: &[bool],
) -> BTreeSet<BlockRef> {
    let mut placed = BTreeSet::new();
    let mut pending = def_blocks.iter().copied().collect::<VecDeque<_>>();
    while let Some(block) = pending.pop_front() {
        for frontier in graph.dominance_frontier_blocks(block) {
            if !live_in[frontier.index()] || !placed.insert(frontier) {
                continue;
            }
            if !def_blocks.contains(&frontier) {
                pending.push_back(frontier);
            }
        }
    }
    for natural_loop in &graph.natural_loops {
        if natural_loop.header == cfg.entry_block
            && live_in[cfg.entry_block.index()]
            && natural_loop
                .blocks
                .iter()
                .any(|block| def_blocks.contains(block))
        {
            placed.insert(cfg.entry_block);
        }
    }
    placed
}

#[allow(clippy::too_many_arguments)]
fn rename_open(
    cfg: &Cfg,
    graph: &GraphFacts,
    effects: &[super::super::common::InstrEffect],
    instr_defs: &[Option<OpenDefId>],
    block_phi: &[Option<OpenPhiId>],
    phis: &mut [OpenPhi],
    uses: &mut [Option<OpenValue>],
    incoming_slots: &[Option<usize>],
) {
    let mut pending = vec![(cfg.entry_block, OpenValue::Entry)];
    while let Some((block, inherited)) = pending.pop() {
        let mut current = block_phi[block.index()].map_or(inherited, OpenValue::Phi);
        if let Some(indices) = super::instr_indices(cfg, block) {
            for instr_index in indices {
                if effects[instr_index].open_use.is_some() {
                    uses[instr_index] = Some(current);
                }
                if let Some(def) = instr_defs[instr_index] {
                    current = OpenValue::Def(def);
                }
            }
        }

        for edge in &cfg.succs[block.index()] {
            let succ = cfg.edges[edge.index()].to;
            let Some(phi) = block_phi[succ.index()] else {
                continue;
            };
            let slot = incoming_slots[edge.index()]
                .expect("reachable CFG edge must have an incoming slot");
            let incoming = phis[phi.index()]
                .incoming
                .get_mut(slot)
                .expect("open phi incoming slots must match CFG predecessors");
            assert_eq!(incoming.edge, Some(*edge));
            incoming.value = current;
        }
        for child in graph.dominator_tree.children[block.index()].iter().rev() {
            pending.push((*child, current));
        }
    }
}

fn index_open_phi_sources(phis: &[OpenPhi]) -> Vec<OpenUseSources> {
    let mut sources = vec![OpenUseSources::default(); phis.len()];
    let mut dependents = vec![Vec::new(); phis.len()];
    for (phi_index, phi) in phis.iter().enumerate() {
        for incoming in &phi.incoming {
            match incoming.value {
                OpenValue::Entry => {
                    sources[phi_index].insert_entry();
                }
                OpenValue::Def(def) => {
                    sources[phi_index].insert_def(def);
                }
                OpenValue::Phi(source) => dependents[source.index()].push(phi_index),
            }
        }
    }

    let mut pending = (0..phis.len()).collect::<VecDeque<_>>();
    let mut queued = vec![true; phis.len()];
    while let Some(source) = pending.pop_front() {
        queued[source] = false;
        let source_values = sources[source].clone();
        for &dependent in &dependents[source] {
            if sources[dependent].merge(&source_values) && !queued[dependent] {
                queued[dependent] = true;
                pending.push_back(dependent);
            }
        }
    }
    sources
}

fn open_sources_for_value(
    value: Option<OpenValue>,
    phi_sources: &[OpenUseSources],
) -> OpenUseSources {
    let mut sources = OpenUseSources::default();
    match value {
        Some(OpenValue::Entry) => {
            sources.insert_entry();
        }
        Some(OpenValue::Def(def)) => {
            sources.insert_def(def);
        }
        Some(OpenValue::Phi(phi)) => {
            if let Some(phi_sources) = phi_sources.get(phi.index()) {
                sources.merge(phi_sources);
            }
        }
        None => {}
    }
    sources
}

fn fixed_prefix_ends(
    sources: &OpenUseSources,
    defs: &[OpenDef],
    entry_open_start: Option<Reg>,
    use_start: Reg,
    reg_count: usize,
) -> (usize, usize) {
    let start = use_start.index();
    let mut source_starts = sources
        .defs()
        .iter()
        .map(|def| defs[def.index()].start_reg.index())
        .collect::<Vec<_>>();
    if sources.has_entry() {
        let Some(entry_start) = entry_open_start else {
            return (start, reg_count);
        };
        source_starts.push(entry_start.index());
    }
    let Some(min_start) = source_starts.iter().copied().min() else {
        return (start, start);
    };
    let max_start = source_starts.iter().copied().max().unwrap_or(min_start);
    (
        min_start.clamp(start, reg_count),
        max_start.clamp(start, reg_count),
    )
}
