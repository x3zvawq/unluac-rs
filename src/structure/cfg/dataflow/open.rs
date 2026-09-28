//! 分析多返回值尾包的来源、固定前缀与活跃性。
//!
//! 消费 CFG、支配和 open-use/must-def，向 Dataflow 发布真实 OpenDefId 与入口尾包事实；
//! 内部 pack phi 不进入 Structure/HIR。

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

struct FixedUseBounds {
    ssa_end: usize,
    liveness_end: usize,
}

/// 固定读取直接借用 InstrEffect；这里只保存 open 来源证明的 must/may 前缀端点。
pub(super) struct FixedUseFacts<'a> {
    effects: &'a [InstrEffect],
    bounds: Vec<FixedUseBounds>,
}

impl FixedUseFacts<'_> {
    pub(super) fn ssa_regs(&self, instr: InstrRef) -> impl Iterator<Item = Reg> + '_ {
        self.uses_with_prefix(instr, self.bounds[instr.index()].ssa_end)
    }

    pub(super) fn liveness_regs(&self, instr: InstrRef) -> impl Iterator<Item = Reg> + '_ {
        self.uses_with_prefix(instr, self.bounds[instr.index()].liveness_end)
    }

    fn uses_with_prefix(&self, instr: InstrRef, end: usize) -> impl Iterator<Item = Reg> + '_ {
        let effect = &self.effects[instr.index()];
        let fixed = effect.fixed_uses();
        let start = effect.open_use.map_or(0, Reg::index);
        // 固定集合已升序唯一；范围覆盖的成员只从范围输出，避免重新展开、排序和去重。
        let (before, after): (&[Reg], &[Reg]) = if start == end {
            (fixed, &[])
        } else {
            let lo = fixed.partition_point(|reg| reg.index() < start);
            let hi = fixed.partition_point(|reg| reg.index() < end);
            (&fixed[..lo], &fixed[hi..])
        };
        before
            .iter()
            .copied()
            .chain((start..end).map(Reg))
            .chain(after.iter().copied())
    }
}

pub(super) struct OpenAnalysis<'a> {
    pub(super) defs: Vec<OpenDef>,
    pub(super) use_sources: Vec<OpenUseSources>,
    pub(super) fixed_uses: FixedUseFacts<'a>,
    pub(super) live_in: Vec<bool>,
    pub(super) live_out: Vec<bool>,
}

pub(super) fn analyze_open_values<'a>(
    cfg: &Cfg,
    graph: &GraphFacts,
    effects: &'a [InstrEffect],
    reg_count: usize,
    entry_open_start: Option<Reg>,
    incoming_slots: &[Option<usize>],
) -> Result<OpenAnalysis<'a>, StructureError> {
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
    )?;

    let phi_sources = index_open_phi_sources(&phis)?;
    let mut use_sources = Vec::with_capacity(effects.len());
    let mut bounds = Vec::with_capacity(effects.len());
    for (instr_index, effect) in effects.iter().enumerate() {
        let sources = open_sources_for_value(uses[instr_index], &phi_sources)?;

        // compute_reg_count 已覆盖全部固定读取；新增前缀由 fixed_prefix_ends 限定在 arena 内。
        let (ssa_end, liveness_end) = if let Some(start_reg) = effect.open_use {
            fixed_prefix_ends(&sources, &defs, entry_open_start, start_reg, reg_count)?
        } else {
            (0, 0)
        };
        bounds.push(FixedUseBounds {
            ssa_end,
            liveness_end,
        });
        use_sources.push(sources);
    }

    Ok(OpenAnalysis {
        defs,
        use_sources,
        fixed_uses: FixedUseFacts { effects, bounds },
        live_in,
        live_out,
    })
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
        for index in indices {
            if effects[index].open_use.is_some() && !block_def[block.index()] {
                block_use[block.index()] = true;
            }
            if effects[index].open_must_def.is_some() {
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
            super::liveness::enqueue_predecessors(cfg, block, &mut worklist, &mut queued);
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
    graph.extend_dominance_frontier(def_blocks, &mut placed, |block| live_in[block.index()]);
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
) -> Result<(), StructureError> {
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
            let Some(slot) = incoming_slots.get(edge.index()).copied().flatten() else {
                return Err(StructureError::invalid(format!(
                    "reachable CFG edge {edge} has no open-phi incoming slot"
                )));
            };
            let Some(phi) = phis.get_mut(phi.index()) else {
                return Err(StructureError::invalid(format!(
                    "open phi #{} is outside the phi arena",
                    phi.index()
                )));
            };
            let Some(incoming) = phi.incoming.get_mut(slot) else {
                return Err(StructureError::invalid(format!(
                    "open phi incoming slot #{slot} does not match CFG edge {edge}"
                )));
            };
            if incoming.edge != Some(*edge) {
                return Err(StructureError::invalid(format!(
                    "open phi incoming slot #{slot} references the wrong CFG edge"
                )));
            }
            incoming.value = current;
        }
        for child in graph.dominator_tree.children[block.index()].iter().rev() {
            pending.push((*child, current));
        }
    }
    Ok(())
}

fn index_open_phi_sources(phis: &[OpenPhi]) -> Result<Vec<OpenUseSources>, StructureError> {
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
                OpenValue::Phi(source) => {
                    let Some(source_dependents) = dependents.get_mut(source.index()) else {
                        return Err(StructureError::invalid(format!(
                            "open phi #{phi_index} references missing source phi #{}",
                            source.index()
                        )));
                    };
                    source_dependents.push(phi_index);
                }
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
    Ok(sources)
}

fn open_sources_for_value(
    value: Option<OpenValue>,
    phi_sources: &[OpenUseSources],
) -> Result<OpenUseSources, StructureError> {
    let mut sources = OpenUseSources::default();
    match value {
        Some(OpenValue::Entry) => {
            sources.insert_entry();
        }
        Some(OpenValue::Def(def)) => {
            sources.insert_def(def);
        }
        Some(OpenValue::Phi(phi)) => {
            let Some(phi_sources) = phi_sources.get(phi.index()) else {
                return Err(StructureError::invalid(format!(
                    "open use references missing phi #{}",
                    phi.index()
                )));
            };
            sources.merge(phi_sources);
        }
        None => {}
    }
    Ok(sources)
}

fn fixed_prefix_ends(
    sources: &OpenUseSources,
    defs: &[OpenDef],
    entry_open_start: Option<Reg>,
    use_start: Reg,
    reg_count: usize,
) -> Result<(usize, usize), StructureError> {
    let start = use_start.index();
    if start > reg_count {
        return Err(StructureError::invalid(format!(
            "open use starts at r{start}, outside the register arena"
        )));
    }
    let mut source_bounds: Option<(usize, usize)> = None;
    let mut include_start = |start| {
        let (minimum, maximum) = source_bounds.get_or_insert((start, start));
        *minimum = (*minimum).min(start);
        *maximum = (*maximum).max(start);
    };
    for def in sources.defs() {
        let Some(definition) = defs.get(def.index()) else {
            return Err(StructureError::invalid(format!(
                "open use references missing definition #{}",
                def.index()
            )));
        };
        let source_start = definition.start_reg.index();
        if source_start > reg_count {
            return Err(StructureError::invalid(format!(
                "open definition #{} starts at r{source_start}, outside the register arena",
                def.index()
            )));
        }
        include_start(source_start);
    }
    if sources.has_entry() {
        let Some(entry_start) = entry_open_start else {
            return Ok((start, reg_count));
        };
        let entry_start = entry_start.index();
        if entry_start > reg_count {
            return Err(StructureError::invalid(format!(
                "entry open value starts at r{entry_start}, outside the register arena"
            )));
        }
        include_start(entry_start);
    }
    let Some((min_start, max_start)) = source_bounds else {
        return Ok((start, start));
    };
    Ok((
        min_start.clamp(start, reg_count),
        max_start.clamp(start, reg_count),
    ))
}
