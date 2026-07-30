//! 这个文件实现 Dataflow 内部的寄存器活跃性固定点求解。
//!
//! 它只消费 CFG 后继关系与已经解析的真实寄存器 use/def，产出后续 phi
//! 与 StructureFacts 可复用的 live-in/live-out 集合；这里不判断 branch/loop/短路候选，
//! 也不把活跃性解释成源码级变量身份。
//!
//! 例子：某个 block 之后的后继仍读取 r3，则 r3 会进入当前 block 的 live_out；
//! 如果当前 block 先定义 r3 再读取后继值，固定点会把该定义挡在 live_in 之外。

use super::*;

fn enqueue_predecessors(
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
    fixed_use_regs: &[Vec<Reg>],
    reg_count: usize,
) -> Result<BlockLiveness, StructureError> {
    let mut block_uses = vec![DenseRegSet::new(reg_count); cfg.blocks.len()];
    let mut block_defs = vec![DenseRegSet::new(reg_count); cfg.blocks.len()];

    for block in cfg.block_order.iter().copied() {
        let Some(instr_indices) = super::instr_indices(cfg, block) else {
            continue;
        };

        let mut seen_defs = DenseRegSet::new(reg_count);

        for instr_index in instr_indices {
            for &reg in &fixed_use_regs[instr_index] {
                if !seen_defs.contains(reg)? {
                    block_uses[block.index()].insert(reg)?;
                }
            }

            for reg in &instr_effects[instr_index].fixed_must_defs {
                seen_defs.insert(*reg)?;
                block_defs[block.index()].insert(*reg)?;
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

    while let Some(block) = worklist.pop_front() {
        queued[block.index()] = false;
        let mut new_live_out = DenseRegSet::new(reg_count);

        for edge_ref in &cfg.succs[block.index()] {
            let succ = cfg.edges[edge_ref.index()].to;
            if !cfg.reachable_blocks.contains(&succ) {
                continue;
            }
            new_live_out.extend_from(&live_in[succ.index()]);
        }

        let mut new_live_in = block_uses[block.index()].clone();
        new_live_in.extend_without(&new_live_out, &block_defs[block.index()]);
        let entry_changed = live_in[block.index()] != new_live_in;

        live_out[block.index()] = new_live_out;
        live_in[block.index()] = new_live_in;
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
struct DenseRegSet {
    bits: Vec<bool>,
}

impl DenseRegSet {
    fn new(reg_count: usize) -> Self {
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

    fn extend_from(&mut self, other: &Self) {
        for (slot, incoming) in self.bits.iter_mut().zip(other.bits.iter()) {
            *slot |= *incoming;
        }
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
