use super::*;

pub(super) fn solve_reaching_defs(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    instr_effects: &[InstrEffect],
    lookups: &DefLookupTables,
    block_state: &mut BlockReachingState,
) {
    let mut changed = true;
    while changed {
        changed = false;

        for block in &graph_facts.rpo {
            let block = *block;
            let (new_in, new_open_in) =
                merge_predecessor_state(cfg, block, &block_state.fixed_out, &block_state.open_out);

            if block_state.fixed_in[block.index()] != new_in {
                block_state.fixed_in[block.index()] = new_in.clone();
                changed = true;
            }
            if block_state.open_in[block.index()] != new_open_in {
                block_state.open_in[block.index()] = new_open_in.clone();
                changed = true;
            }

            let mut current_fixed = new_in;
            let mut current_open = new_open_in;

            if let Some(instr_indices) = super::instr_indices(cfg, block) {
                for instr_index in instr_indices {
                    apply_transfer(
                        &instr_effects[instr_index],
                        &lookups.fixed[instr_index],
                        lookups.open_must[instr_index],
                        lookups.open_may[instr_index],
                        &mut current_fixed,
                        &mut current_open,
                    );
                }
            }

            if block_state.fixed_out[block.index()] != current_fixed {
                block_state.fixed_out[block.index()] = current_fixed;
                changed = true;
            }
            if block_state.open_out[block.index()] != current_open {
                block_state.open_out[block.index()] = current_open;
                changed = true;
            }
        }
    }
}

pub(super) fn materialize_instruction_facts(
    cfg: &Cfg,
    instr_effects: &[InstrEffect],
    lookups: &DefLookupTables,
    open_defs: &[OpenDef],
    block_state: &BlockReachingState,
    scratch: &mut MaterializeScratch,
    instruction_facts: &mut InstructionFacts,
) {
    for block in cfg.block_order.iter().copied() {
        let Some(instr_indices) = super::instr_indices(cfg, block) else {
            continue;
        };

        let mut current_fixed = block_state.fixed_in[block.index()].clone();
        let mut current_open = block_state.open_in[block.index()].clone();

        for instr_index in instr_indices {
            let effect = &instr_effects[instr_index];
            instruction_facts.reaching_defs[instr_index] = snapshot_fixed_state(&mut current_fixed);
            instruction_facts.open_reaching_defs[instr_index] = current_open.clone();

            let fixed_use_regs =
                scratch.fixed_use_regs.resolve(effect, &current_open, open_defs);
            let mut fixed_use_entries = Vec::with_capacity(fixed_use_regs.len());
            for &reg in fixed_use_regs {
                let defs = current_fixed.get(reg).clone();
                for def in &defs {
                    instruction_facts.def_uses[def.index()].push(UseSite {
                        instr: crate::transformer::InstrRef(instr_index),
                        reg,
                    });
                }
                if !defs.is_empty() {
                    fixed_use_entries.push((reg, defs));
                }
            }

            if let Some(start_reg) = effect.open_use {
                instruction_facts.open_use_defs[instr_index] = current_open.clone();
                for open_def in &current_open {
                    instruction_facts.open_def_uses[open_def.index()].push(OpenUseSite {
                        instr: crate::transformer::InstrRef(instr_index),
                        start_reg,
                    });
                }
            }

            instruction_facts.use_defs[instr_index] = InstrUseDefs {
                fixed: RegValueMap::from_sparse_entries(fixed_use_entries),
                open: instruction_facts.open_use_defs[instr_index]
                    .iter()
                    .copied()
                    .collect(),
            };

            apply_transfer(
                effect,
                &lookups.fixed[instr_index],
                lookups.open_must[instr_index],
                lookups.open_may[instr_index],
                &mut current_fixed,
                &mut current_open,
            );
        }
    }
}

fn merge_predecessor_state(
    cfg: &Cfg,
    block: BlockRef,
    block_out: &[FixedState],
    open_block_out: &[CompactSet<OpenDefId>],
) -> (FixedState, CompactSet<OpenDefId>) {
    let reg_count = block_out.first().map_or(0, |state| state.regs.len());
    let mut merged_fixed = FixedState::new(reg_count);
    let mut merged_open = CompactSet::Empty;

    for edge_ref in &cfg.preds[block.index()] {
        let pred = cfg.edges[edge_ref.index()].from;
        if !cfg.reachable_blocks.contains(&pred) {
            continue;
        }

        merged_fixed.extend_from(&block_out[pred.index()]);
        merged_open.extend(open_block_out[pred.index()].iter().copied());
    }

    (merged_fixed, merged_open)
}

fn apply_transfer(
    effect: &InstrEffect,
    fixed_def_lookup: &FixedDefLookup,
    open_must_def_lookup: Option<OpenDefId>,
    open_may_def_lookup: Option<OpenDefId>,
    fixed_state: &mut FixedState,
    open_state: &mut CompactSet<OpenDefId>,
) {
    debug_assert_eq!(effect.fixed_must_defs.len(), fixed_def_lookup.must.len());
    debug_assert_eq!(effect.fixed_may_defs.len(), fixed_def_lookup.may.len());

    for &(reg, def) in &fixed_def_lookup.must {
        fixed_state.set_singleton(reg, def);
    }

    for &(reg, def) in &fixed_def_lookup.may {
        fixed_state.insert(reg, def);
    }

    if let Some(open_def) = open_must_def_lookup {
        open_state.clear();
        open_state.insert(open_def);
    }

    if let Some(open_def) = open_may_def_lookup {
        open_state.insert(open_def);
    }
}

fn snapshot_fixed_state(state: &mut FixedState) -> InstrReachingDefs {
    InstrReachingDefs {
        fixed: state.snapshot_map(),
    }
}
