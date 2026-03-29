use super::*;

pub(super) fn solve_liveness(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    instr_effects: &[InstrEffect],
    instruction_facts: &InstructionFacts,
) -> BlockLiveness {
    let mut block_uses = vec![BTreeSet::new(); cfg.blocks.len()];
    let mut block_defs = vec![BTreeSet::new(); cfg.blocks.len()];
    let mut block_open_use = vec![false; cfg.blocks.len()];
    let mut block_open_def = vec![false; cfg.blocks.len()];

    for block in cfg.block_order.iter().copied() {
        let Some(instr_indices) = super::instr_indices(cfg, block) else {
            continue;
        };

        let mut seen_defs = BTreeSet::new();
        let mut seen_open_def = false;

        for instr_index in instr_indices {
            let effect = &instr_effects[instr_index];

            for reg in instruction_facts.use_defs[instr_index].fixed.keys() {
                if !seen_defs.contains(&reg) {
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

    let mut live_in = vec![BTreeSet::new(); cfg.blocks.len()];
    let mut live_out = vec![BTreeSet::new(); cfg.blocks.len()];
    let mut open_live_in = vec![false; cfg.blocks.len()];
    let mut open_live_out = vec![false; cfg.blocks.len()];

    let reverse_rpo = graph_facts.rpo.iter().rev().copied().collect::<Vec<_>>();
    let mut changed = true;
    while changed {
        changed = false;

        for block in &reverse_rpo {
            let block = *block;
            let mut new_live_out = BTreeSet::new();
            let mut new_open_live_out = false;

            for edge_ref in &cfg.succs[block.index()] {
                let succ = cfg.edges[edge_ref.index()].to;
                if !cfg.reachable_blocks.contains(&succ) {
                    continue;
                }
                new_live_out.extend(live_in[succ.index()].iter().copied());
                new_open_live_out |= open_live_in[succ.index()];
            }

            let mut new_live_in = block_uses[block.index()].clone();
            new_live_in.extend(
                new_live_out
                    .iter()
                    .filter(|reg| !block_defs[block.index()].contains(reg))
                    .copied(),
            );
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
        live_in,
        live_out,
        open_live_in,
        open_live_out,
    }
}
