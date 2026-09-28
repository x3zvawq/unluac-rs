//! 求解 Dataflow 的寄存器活跃性。
//!
//! 真实 use/def 决定逻辑活性，物理观察另外约束 SSA 保留需求，两者独立发布。

use super::*;

pub(super) fn enqueue_predecessors(
    cfg: &Cfg,
    block: BlockRef,
    worklist: &mut VecDeque<BlockRef>,
    queued: &mut [bool],
) {
    for edge in &cfg.preds[block.index()] {
        let pred = cfg.edges[edge.index()].from;
        if cfg.reachable_blocks.contains(&pred) && !queued[pred.index()] {
            queued[pred.index()] = true;
            worklist.push_back(pred);
        }
    }
}

pub(super) fn solve_liveness(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    instr_effects: &[InstrEffect],
    fixed_uses: &FixedUseFacts<'_>,
    reg_count: usize,
    root_observations: Option<&[SideEffectSummary]>,
) -> Result<BlockLiveness, StructureError> {
    let mut block_uses = vec![DenseRegSet::new(reg_count); cfg.blocks.len()];
    let mut block_defs = vec![DenseRegSet::new(reg_count); cfg.blocks.len()];

    for block in cfg.block_order.iter().copied() {
        let Some(instr_indices) = super::instr_indices(cfg, block) else {
            continue;
        };

        let defs = &mut block_defs[block.index()];
        let uses = &mut block_uses[block.index()];
        let mut observed_prefix_end = 0;

        for instr_index in instr_indices {
            // root 观察是 SSA 保留需求，不是真实读取；独立求解，不能伪造 UseSite
            // 或改变对外发布的逻辑 live-in/live-out。
            if let Some(summaries) = root_observations {
                let end = match summaries[instr_index].root_observation {
                    RootObservation::PrefixLowerBound { end } => end,
                    RootObservation::Call { caller_end } => caller_end.index(),
                    _ => 0,
                };
                // uses/defs 在块内只增不减；每个观察前缀槽只检查一次。
                let end = end.min(reg_count);
                for reg in (observed_prefix_end..end).map(Reg) {
                    if !defs.contains(reg)? {
                        uses.insert(reg)?;
                    }
                }
                observed_prefix_end = observed_prefix_end.max(end);
            }
            for reg in fixed_uses.liveness_regs(InstrRef(instr_index)) {
                if !defs.contains(reg)? {
                    uses.insert(reg)?;
                }
            }

            for reg in instr_effects[instr_index].fixed_must_defs() {
                defs.insert(*reg)?;
            }
        }
    }

    let mut live_in = vec![DenseRegSet::new(reg_count); cfg.blocks.len()];
    let mut live_out = vec![DenseRegSet::new(reg_count); cfg.blocks.len()];

    let mut worklist = graph_facts
        .rpo
        .iter()
        .rev()
        .copied()
        .collect::<VecDeque<_>>();
    let mut queued = vec![false; cfg.blocks.len()];
    for block in &worklist {
        queued[block.index()] = true;
    }

    // 全部集合共享固定寄存器域；提交后回收旧结果缓冲区，回边重访不重复分配。
    let mut new_live_out = DenseRegSet::new(reg_count);
    let mut new_live_in = DenseRegSet::new(reg_count);
    while let Some(block) = worklist.pop_front() {
        queued[block.index()] = false;
        new_live_out.bits.fill(false);

        for edge_ref in &cfg.succs[block.index()] {
            let succ = cfg.edges[edge_ref.index()].to;
            if !cfg.reachable_blocks.contains(&succ) {
                continue;
            }
            new_live_out.extend_from(&live_in[succ.index()]);
        }

        new_live_in
            .bits
            .copy_from_slice(&block_uses[block.index()].bits);
        new_live_in.extend_without(&new_live_out, &block_defs[block.index()]);
        let entry_changed = live_in[block.index()] != new_live_in;

        std::mem::swap(&mut live_out[block.index()], &mut new_live_out);
        std::mem::swap(&mut live_in[block.index()], &mut new_live_in);
        if entry_changed {
            enqueue_predecessors(cfg, block, &mut worklist, &mut queued);
        }
    }

    Ok(BlockLiveness {
        live_in: live_in.into_iter().map(DenseRegSet::into_regs).collect(),
        live_out: live_out.into_iter().map(DenseRegSet::into_regs).collect(),
    })
}

#[derive(Clone, PartialEq, Eq)]
pub(super) struct DenseRegSet {
    pub(super) bits: Vec<bool>,
}

impl DenseRegSet {
    pub(super) fn new(reg_count: usize) -> Self {
        Self {
            bits: vec![false; reg_count],
        }
    }

    fn insert(&mut self, reg: Reg) -> Result<bool, StructureError> {
        let Some(slot) = self.bits.get_mut(reg.index()) else {
            return Err(StructureError::invalid(format!(
                "liveness register r{} exceeds register arena {}",
                reg.index(),
                self.bits.len()
            )));
        };
        let changed = !*slot;
        *slot = true;
        Ok(changed)
    }

    fn contains(&self, reg: Reg) -> Result<bool, StructureError> {
        self.bits.get(reg.index()).copied().ok_or_else(|| {
            StructureError::invalid(format!(
                "liveness register r{} exceeds register arena {}",
                reg.index(),
                self.bits.len()
            ))
        })
    }

    pub(super) fn extend_from(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (slot, incoming) in self.bits.iter_mut().zip(other.bits.iter()) {
            changed |= *incoming && !*slot;
            *slot |= *incoming;
        }
        changed
    }

    fn extend_without(&mut self, values: &Self, excluded: &Self) {
        for (index, incoming) in values.bits.iter().copied().enumerate() {
            if incoming && !excluded.bits[index] {
                self.bits[index] = true;
            }
        }
    }

    fn into_regs(self) -> BTreeSet<Reg> {
        self.bits
            .into_iter()
            .enumerate()
            .filter_map(|(index, live)| live.then_some(Reg(index)))
            .collect()
    }
}
