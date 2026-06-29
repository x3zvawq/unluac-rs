//! 这个文件实现 Dataflow 内部的寄存器活跃性固定点求解。
//!
//! 它只消费 CFG 后继关系、指令 use/def 和 open vararg/use-def 事实，产出后续 phi
//! 与 StructureFacts 可复用的 live-in/live-out 集合；这里不判断 branch/loop/短路候选，
//! 也不把活跃性解释成源码级变量身份。
//!
//! 例子：某个 block 之后的后继仍读取 r3，则 r3 会进入当前 block 的 live_out；
//! 如果当前 block 先定义 r3 再读取后继值，固定点会把该定义挡在 live_in 之外。

use super::*;

pub(super) fn solve_liveness(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    instr_effects: &[InstrEffect],
    instruction_facts: &InstructionFacts,
    reg_count: usize,
) -> BlockLiveness {
    let mut block_uses = vec![DenseRegSet::new(reg_count); cfg.blocks.len()];
    let mut block_defs = vec![DenseRegSet::new(reg_count); cfg.blocks.len()];
    let mut block_open_use = vec![false; cfg.blocks.len()];
    let mut block_open_def = vec![false; cfg.blocks.len()];

    for block in cfg.block_order.iter().copied() {
        let Some(instr_indices) = super::instr_indices(cfg, block) else {
            continue;
        };

        let mut seen_defs = DenseRegSet::new(reg_count);
        let mut seen_open_def = false;

        for instr_index in instr_indices {
            let effect = &instr_effects[instr_index];

            for reg in instruction_facts.use_defs[instr_index].fixed.keys() {
                if !seen_defs.contains(reg) {
                    block_uses[block.index()].insert(reg);
                }
            }

            if effect.open_use.is_some() && !seen_open_def {
                block_open_use[block.index()] = true;
            }

            for reg in effect
                .fixed_must_defs
                .iter()
                .chain(effect.fixed_may_defs.iter())
            {
                seen_defs.insert(*reg);
                block_defs[block.index()].insert(*reg);
            }

            if effect.open_must_def.is_some() || effect.open_may_def.is_some() {
                seen_open_def = true;
                block_open_def[block.index()] = true;
            }
        }
    }

    let mut live_in = vec![DenseRegSet::new(reg_count); cfg.blocks.len()];
    let mut live_out = vec![DenseRegSet::new(reg_count); cfg.blocks.len()];
    let mut open_live_in = vec![false; cfg.blocks.len()];
    let mut open_live_out = vec![false; cfg.blocks.len()];

    let reverse_rpo = graph_facts.rpo.iter().rev().copied().collect::<Vec<_>>();
    let mut changed = true;
    while changed {
        changed = false;

        for block in &reverse_rpo {
            let block = *block;
            let mut new_live_out = DenseRegSet::new(reg_count);
            let mut new_open_live_out = false;

            for edge_ref in &cfg.succs[block.index()] {
                let succ = cfg.edges[edge_ref.index()].to;
                if !cfg.reachable_blocks.contains(&succ) {
                    continue;
                }
                new_live_out.extend_from(&live_in[succ.index()]);
                new_open_live_out |= open_live_in[succ.index()];
            }

            let mut new_live_in = block_uses[block.index()].clone();
            new_live_in.extend_without(&new_live_out, &block_defs[block.index()]);
            let new_open_live_in = block_open_use[block.index()]
                || (new_open_live_out && !block_open_def[block.index()]);

            if live_out[block.index()] != new_live_out {
                live_out[block.index()] = new_live_out;
                changed = true;
            }
            if live_in[block.index()] != new_live_in {
                live_in[block.index()] = new_live_in;
                changed = true;
            }
            if open_live_out[block.index()] != new_open_live_out {
                open_live_out[block.index()] = new_open_live_out;
                changed = true;
            }
            if open_live_in[block.index()] != new_open_live_in {
                open_live_in[block.index()] = new_open_live_in;
                changed = true;
            }
        }
    }

    BlockLiveness {
        live_in: live_in.into_iter().map(DenseRegSet::into_regs).collect(),
        live_out: live_out.into_iter().map(DenseRegSet::into_regs).collect(),
        open_live_in,
        open_live_out,
    }
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

    fn insert(&mut self, reg: Reg) -> bool {
        let slot = self
            .bits
            .get_mut(reg.index())
            .expect("liveness reg set should cover every reachable register");
        let changed = !*slot;
        *slot = true;
        changed
    }

    fn contains(&self, reg: Reg) -> bool {
        self.bits
            .get(reg.index())
            .copied()
            .expect("liveness reg set should cover every reachable register")
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
