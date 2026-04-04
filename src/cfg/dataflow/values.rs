use super::*;

pub(super) struct MaterializedValueFacts {
    pub reaching_values: Vec<InstrReachingValues>,
    pub use_values: Vec<InstrUseValues>,
}

pub(super) fn materialize_value_facts(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    instr_effects: &[InstrEffect],
    ctx: ValueMaterializeCtx<'_>,
    reg_count: usize,
    scratch: &mut MaterializeScratch,
    instruction_facts: &InstructionFacts,
) -> MaterializedValueFacts {
    let mut block_state = BlockValueState {
        fixed_in: vec![TrackedState::new(reg_count); cfg.blocks.len()],
        fixed_out: vec![TrackedState::new(reg_count); cfg.blocks.len()],
    };
    let mut reaching_values =
        vec![InstrReachingValues::default(); instruction_facts.reaching_defs.len()];
    let mut use_values = vec![InstrUseValues::default(); instruction_facts.use_defs.len()];

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
            reaching_values[instr_index] = snapshot_value_state(&mut current_fixed);

            let fixed_use_regs = super::resolved_fixed_use_regs(
                scratch,
                effect,
                &instruction_facts.open_reaching_defs[instr_index],
                ctx.open_defs,
            );
            let mut fixed_use_entries = Vec::with_capacity(fixed_use_regs.len());
            for &reg in fixed_use_regs {
                let values = current_fixed.get(reg).clone();
                if !values.is_empty() {
                    fixed_use_entries.push((reg, values));
                }
            }
            use_values[instr_index] = InstrUseValues {
                fixed: RegValueMap::from_sparse_entries(fixed_use_entries),
            };

            apply_value_transfer(effect, &ctx.lookups.fixed[instr_index], &mut current_fixed);
        }
    }

    MaterializedValueFacts {
        reaching_values,
        use_values,
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
    let reg_count = block_out.first().map_or(0, |state| state.regs.len());
    let mut merged_fixed = ValueState::new(reg_count);

    for edge_ref in &cfg.preds[block.index()] {
        let pred = cfg.edges[edge_ref.index()].from;
        if !cfg.reachable_blocks.contains(&pred) {
            continue;
        }

        merged_fixed.extend_from(&block_out[pred.index()]);
    }

    merged_fixed
}

pub(super) fn apply_block_phi_values(state: &mut ValueState, phi_candidates: &[PhiCandidate]) {
    for phi in phi_candidates {
        state.set_singleton(phi.reg, SsaValue::Phi(phi.id));
    }
}

fn apply_value_transfer(
    effect: &InstrEffect,
    fixed_def_lookup: &FixedDefLookup,
    fixed_state: &mut ValueState,
) {
    debug_assert_eq!(effect.fixed_must_defs.len(), fixed_def_lookup.must.len());
    debug_assert_eq!(effect.fixed_may_defs.len(), fixed_def_lookup.may.len());

    for &(reg, def) in &fixed_def_lookup.must {
        fixed_state.set_singleton(reg, SsaValue::Def(def));
    }

    for &(reg, def) in &fixed_def_lookup.may {
        fixed_state.insert(reg, SsaValue::Def(def));
    }
}

fn snapshot_value_state(state: &mut ValueState) -> InstrReachingValues {
    InstrReachingValues {
        fixed: state.snapshot_map(),
    }
}
