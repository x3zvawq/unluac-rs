use super::*;

pub(super) fn materialize_value_facts(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    instr_effects: &[InstrEffect],
    ctx: ValueMaterializeCtx<'_>,
    reg_count: usize,
    instruction_facts: &mut InstructionFacts,
) {
    let mut block_state = BlockValueState {
        fixed_in: vec![vec![CompactSet::Empty; reg_count]; cfg.blocks.len()],
        fixed_out: vec![vec![CompactSet::Empty; reg_count]; cfg.blocks.len()],
    };

    solve_reaching_values(
        cfg,
        graph_facts,
        instr_effects,
        ctx.lookups,
        ctx.phi_candidates,
        ctx.phi_block_ranges,
        &mut block_state,
    );

    for block in cfg.block_order.iter().copied() {
        let Some(instr_indices) = super::instr_indices(cfg, block) else {
            continue;
        };

        let mut current_fixed = block_state.fixed_in[block.index()].clone();

        for instr_index in instr_indices {
            let effect = &instr_effects[instr_index];
            instruction_facts.reaching_values[instr_index] = snapshot_value_state(&current_fixed);

            let fixed_use_regs = super::resolved_fixed_use_regs(
                effect,
                &instruction_facts.open_reaching_defs[instr_index],
                ctx.open_defs,
            );
            let mut fixed_use_values = RegValueMap::with_reg_count(current_fixed.len());
            for reg in &fixed_use_regs {
                fixed_use_values.insert(
                    *reg,
                    current_fixed.get(reg.index()).cloned().unwrap_or_default(),
                );
            }
            instruction_facts.use_values[instr_index] = InstrUseValues {
                fixed: fixed_use_values,
            };

            apply_value_transfer(effect, &ctx.lookups.fixed[instr_index], &mut current_fixed);
        }
    }
}

fn solve_reaching_values(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    instr_effects: &[InstrEffect],
    lookups: &DefLookupTables,
    phi_candidates: &[PhiCandidate],
    phi_block_ranges: &[std::ops::Range<usize>],
    block_state: &mut BlockValueState,
) {
    let mut changed = true;
    while changed {
        changed = false;

        for block in &graph_facts.rpo {
            let block = *block;
            let mut new_in = merge_predecessor_value_state(cfg, block, &block_state.fixed_out);
            // phi 代表“进入这个 block 之后立刻可见的合流值”，因此它必须覆盖掉
            // predecessor 合并出来的底层 def 集，否则后续 use 仍然会看到多定义。
            apply_block_phi_values(
                &mut new_in,
                &phi_candidates[phi_block_ranges[block.index()].clone()],
            );

            if block_state.fixed_in[block.index()] != new_in {
                block_state.fixed_in[block.index()] = new_in.clone();
                changed = true;
            }

            let mut current_fixed = new_in;
            if let Some(instr_indices) = super::instr_indices(cfg, block) {
                for instr_index in instr_indices {
                    apply_value_transfer(
                        &instr_effects[instr_index],
                        &lookups.fixed[instr_index],
                        &mut current_fixed,
                    );
                }
            }

            if block_state.fixed_out[block.index()] != current_fixed {
                block_state.fixed_out[block.index()] = current_fixed;
                changed = true;
            }
        }
    }
}

fn merge_predecessor_value_state(
    cfg: &Cfg,
    block: BlockRef,
    block_out: &[ValueState],
) -> ValueState {
    let reg_count = block_out.first().map_or(0, Vec::len);
    let mut merged_fixed = vec![CompactSet::Empty; reg_count];

    for edge_ref in &cfg.preds[block.index()] {
        let pred = cfg.edges[edge_ref.index()].from;
        if !cfg.reachable_blocks.contains(&pred) {
            continue;
        }

        for (reg_values, pred_values) in merged_fixed.iter_mut().zip(&block_out[pred.index()]) {
            reg_values.extend(pred_values.iter().copied());
        }
    }

    merged_fixed
}

fn apply_block_phi_values(state: &mut [CompactSet<SsaValue>], phi_candidates: &[PhiCandidate]) {
    for phi in phi_candidates {
        state[phi.reg.index()] = CompactSet::singleton(SsaValue::Phi(phi.id));
    }
}

fn apply_value_transfer(
    effect: &InstrEffect,
    fixed_def_lookup: &BTreeMap<Reg, DefId>,
    fixed_state: &mut [CompactSet<SsaValue>],
) {
    for reg in &effect.fixed_must_defs {
        let def = fixed_def_lookup
            .get(reg)
            .copied()
            .expect("must-def register should already have a concrete DefId");
        fixed_state[reg.index()] = CompactSet::singleton(SsaValue::Def(def));
    }

    for reg in &effect.fixed_may_defs {
        let def = fixed_def_lookup
            .get(reg)
            .copied()
            .expect("may-def register should already have a concrete DefId");
        fixed_state[reg.index()].insert(SsaValue::Def(def));
    }
}

fn snapshot_value_state(state: &[CompactSet<SsaValue>]) -> InstrReachingValues {
    InstrReachingValues {
        fixed: RegValueMap::from_state(state),
    }
}
