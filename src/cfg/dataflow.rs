//! 这个文件实现基于 low-IR + CFG + GraphFacts 的基础数据流分析。
//!
//! 这里先把后续结构恢复必需的“读写、副作用、def-use、liveness、phi 候选”
//! 一次性统一算出来，避免 StructureFacts 再反向重复扫底层 low-IR。

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::transformer::{
    AccessBase, AccessKey, BranchOperands, CaptureSource, CondOperand, LowInstr, LoweredChunk,
    LoweredProto, Reg, RegRange, ResultPack, ValueOperand, ValuePack,
};

use super::common::{
    BlockRef, Cfg, CfgGraph, DataflowFacts, Def, DefId, EffectTag, GraphFacts, InstrEffect,
    InstrReachingDefs, InstrReachingValues, InstrUseDefs, InstrUseValues, OpenDef, OpenDefId,
    OpenUseSite, PhiCandidate, PhiId, PhiIncoming, SideEffectSummary, SsaValue, UseSite,
};

type FixedState = Vec<BTreeSet<DefId>>;
type ValueState = Vec<BTreeSet<SsaValue>>;

struct DefLookupTables {
    fixed: Vec<BTreeMap<Reg, DefId>>,
    open_must: Vec<Option<OpenDefId>>,
    open_may: Vec<Option<OpenDefId>>,
}

struct BlockReachingState {
    fixed_in: Vec<FixedState>,
    fixed_out: Vec<FixedState>,
    open_in: Vec<BTreeSet<OpenDefId>>,
    open_out: Vec<BTreeSet<OpenDefId>>,
}

struct InstructionFacts {
    reaching_defs: Vec<InstrReachingDefs>,
    reaching_values: Vec<InstrReachingValues>,
    use_defs: Vec<InstrUseDefs>,
    use_values: Vec<InstrUseValues>,
    def_uses: Vec<Vec<UseSite>>,
    open_reaching_defs: Vec<BTreeSet<OpenDefId>>,
    open_use_defs: Vec<BTreeSet<OpenDefId>>,
    open_def_uses: Vec<Vec<OpenUseSite>>,
}

struct BlockValueState {
    fixed_in: Vec<ValueState>,
    fixed_out: Vec<ValueState>,
}

struct ValueMaterializeCtx<'a> {
    lookups: &'a DefLookupTables,
    open_defs: &'a [OpenDef],
}

struct BlockLiveness {
    live_in: Vec<BTreeSet<Reg>>,
    live_out: Vec<BTreeSet<Reg>>,
    open_live_in: Vec<bool>,
    open_live_out: Vec<bool>,
}

/// 对整个 lowered chunk 递归计算数据流事实。
pub fn analyze_dataflow(
    chunk: &LoweredChunk,
    cfg: &CfgGraph,
    graph_facts: &GraphFacts,
) -> DataflowFacts {
    analyze_proto_dataflow(&chunk.main, &cfg.cfg, graph_facts, &cfg.children)
}

fn analyze_proto_dataflow(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    child_cfgs: &[CfgGraph],
) -> DataflowFacts {
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
    let reg_count = compute_reg_count(proto, &instr_effects);

    let mut defs = Vec::new();
    let mut open_defs = Vec::new();
    let mut reg_versions = BTreeMap::<Reg, Vec<DefId>>::new();
    let mut instr_defs = vec![Vec::new(); proto.instrs.len()];
    let mut lookups = DefLookupTables {
        fixed: vec![BTreeMap::<Reg, DefId>::new(); proto.instrs.len()],
        open_must: vec![None; proto.instrs.len()],
        open_may: vec![None; proto.instrs.len()],
    };

    for block in cfg.block_order.iter().copied() {
        let Some(instr_indices) = instr_indices(cfg, block) else {
            continue;
        };

        for instr_index in instr_indices {
            let effect = &instr_effects[instr_index];

            for reg in effect
                .fixed_must_defs
                .iter()
                .chain(effect.fixed_may_defs.iter())
            {
                let id = DefId(defs.len());
                let reg = *reg;
                let def = Def {
                    id,
                    reg,
                    instr: crate::transformer::InstrRef(instr_index),
                    block,
                };
                defs.push(def);
                reg_versions.entry(reg).or_default().push(id);
                instr_defs[instr_index].push(id);
                lookups.fixed[instr_index].insert(reg, id);
            }

            if let Some(start_reg) = effect.open_must_def {
                let id = OpenDefId(open_defs.len());
                open_defs.push(OpenDef {
                    id,
                    start_reg,
                    instr: crate::transformer::InstrRef(instr_index),
                    block,
                });
                lookups.open_must[instr_index] = Some(id);
            }

            if let Some(start_reg) = effect.open_may_def {
                let id = OpenDefId(open_defs.len());
                open_defs.push(OpenDef {
                    id,
                    start_reg,
                    instr: crate::transformer::InstrRef(instr_index),
                    block,
                });
                lookups.open_may[instr_index] = Some(id);
            }
        }
    }

    let mut block_state = BlockReachingState {
        fixed_in: vec![vec![BTreeSet::new(); reg_count]; cfg.blocks.len()],
        fixed_out: vec![vec![BTreeSet::new(); reg_count]; cfg.blocks.len()],
        open_in: vec![BTreeSet::new(); cfg.blocks.len()],
        open_out: vec![BTreeSet::new(); cfg.blocks.len()],
    };

    solve_reaching_defs(cfg, graph_facts, &instr_effects, &lookups, &mut block_state);

    let mut instruction_facts = InstructionFacts {
        reaching_defs: vec![InstrReachingDefs::default(); proto.instrs.len()],
        reaching_values: vec![InstrReachingValues::default(); proto.instrs.len()],
        use_defs: vec![InstrUseDefs::default(); proto.instrs.len()],
        use_values: vec![InstrUseValues::default(); proto.instrs.len()],
        def_uses: vec![Vec::new(); defs.len()],
        open_reaching_defs: vec![BTreeSet::new(); proto.instrs.len()],
        open_use_defs: vec![BTreeSet::new(); proto.instrs.len()],
        open_def_uses: vec![Vec::new(); open_defs.len()],
    };

    materialize_instruction_facts(
        cfg,
        &instr_effects,
        &lookups,
        &open_defs,
        &block_state,
        &mut instruction_facts,
    );

    let liveness = solve_liveness(cfg, graph_facts, &instr_effects, &instruction_facts);

    let phi_candidates = compute_phi_candidates(
        cfg,
        graph_facts,
        &defs,
        &liveness.live_in,
        &block_state.fixed_out,
        &lookups.fixed,
    );

    materialize_value_facts(
        cfg,
        graph_facts,
        &instr_effects,
        ValueMaterializeCtx {
            lookups: &lookups,
            open_defs: &open_defs,
        },
        reg_count,
        &phi_candidates,
        &mut instruction_facts,
    );

    let children = proto
        .children
        .iter()
        .zip(child_cfgs.iter())
        .zip(graph_facts.children.iter())
        .map(|((child_proto, child_cfg), child_graph_facts)| {
            analyze_proto_dataflow(
                child_proto,
                &child_cfg.cfg,
                child_graph_facts,
                &child_cfg.children,
            )
        })
        .collect();

    DataflowFacts {
        instr_effects,
        effect_summaries,
        defs,
        open_defs,
        reg_versions,
        instr_defs,
        reaching_defs: instruction_facts.reaching_defs,
        reaching_values: instruction_facts.reaching_values,
        use_defs: instruction_facts.use_defs,
        use_values: instruction_facts.use_values,
        def_uses: instruction_facts.def_uses,
        open_reaching_defs: instruction_facts.open_reaching_defs,
        open_use_defs: instruction_facts.open_use_defs,
        open_def_uses: instruction_facts.open_def_uses,
        live_in: liveness.live_in,
        live_out: liveness.live_out,
        open_live_in: liveness.open_live_in,
        open_live_out: liveness.open_live_out,
        phi_candidates,
        children,
    }
}

fn solve_reaching_defs(
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

            if let Some(instr_indices) = instr_indices(cfg, block) {
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

fn materialize_instruction_facts(
    cfg: &Cfg,
    instr_effects: &[InstrEffect],
    lookups: &DefLookupTables,
    open_defs: &[OpenDef],
    block_state: &BlockReachingState,
    instruction_facts: &mut InstructionFacts,
) {
    for block in cfg.block_order.iter().copied() {
        let Some(instr_indices) = instr_indices(cfg, block) else {
            continue;
        };

        let mut current_fixed = block_state.fixed_in[block.index()].clone();
        let mut current_open = block_state.open_in[block.index()].clone();

        for instr_index in instr_indices {
            let effect = &instr_effects[instr_index];
            instruction_facts.reaching_defs[instr_index] = snapshot_fixed_state(&current_fixed);
            instruction_facts.open_reaching_defs[instr_index] = current_open.clone();

            let fixed_use_regs = resolved_fixed_use_regs(effect, &current_open, open_defs);
            let mut fixed_use_defs = BTreeMap::new();
            for reg in &fixed_use_regs {
                let defs = current_fixed.get(reg.index()).cloned().unwrap_or_default();
                for def in &defs {
                    instruction_facts.def_uses[def.index()].push(UseSite {
                        instr: crate::transformer::InstrRef(instr_index),
                        reg: *reg,
                    });
                }
                fixed_use_defs.insert(*reg, defs);
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
                fixed: fixed_use_defs,
                open: instruction_facts.open_use_defs[instr_index].clone(),
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

fn solve_liveness(
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
        let Some(instr_indices) = instr_indices(cfg, block) else {
            continue;
        };

        let mut seen_defs = BTreeSet::new();
        let mut seen_open_def = false;

        for instr_index in instr_indices {
            let effect = &instr_effects[instr_index];

            for reg in instruction_facts.use_defs[instr_index].fixed.keys() {
                if !seen_defs.contains(reg) {
                    block_uses[block.index()].insert(*reg);
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

fn compute_phi_candidates(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    defs: &[Def],
    live_in: &[BTreeSet<Reg>],
    block_out: &[Vec<BTreeSet<DefId>>],
    fixed_def_lookup: &[BTreeMap<Reg, DefId>],
) -> Vec<PhiCandidate> {
    let mut def_blocks = BTreeMap::<Reg, BTreeSet<BlockRef>>::new();
    for def in defs {
        if cfg.reachable_blocks.contains(&def.block) {
            def_blocks.entry(def.reg).or_default().insert(def.block);
        }
    }

    let mut phi_candidates = Vec::new();

    for (reg, blocks) in def_blocks {
        let mut placed = BTreeSet::new();
        let mut worklist = blocks.iter().copied().collect::<VecDeque<_>>();

        while let Some(block) = worklist.pop_front() {
            for frontier_block in &graph_facts.dominance_frontier[block.index()] {
                if !live_in[frontier_block.index()].contains(&reg)
                    || !placed.insert(*frontier_block)
                {
                    continue;
                }

                if let Some(candidate) = build_phi_candidate(cfg, *frontier_block, reg, block_out) {
                    phi_candidates.push(candidate);
                }

                if !block_defines_reg(cfg, *frontier_block, reg, fixed_def_lookup) {
                    worklist.push_back(*frontier_block);
                }
            }
        }
    }

    phi_candidates.sort_by_key(|candidate| (candidate.block, candidate.reg));
    for (index, candidate) in phi_candidates.iter_mut().enumerate() {
        candidate.id = PhiId(index);
    }
    phi_candidates
}

fn build_phi_candidate(
    cfg: &Cfg,
    block: BlockRef,
    reg: Reg,
    block_out: &[Vec<BTreeSet<DefId>>],
) -> Option<PhiCandidate> {
    let mut incoming = Vec::new();
    let mut distinct_defs = BTreeSet::new();

    for edge_ref in &cfg.preds[block.index()] {
        let pred = cfg.edges[edge_ref.index()].from;
        if !cfg.reachable_blocks.contains(&pred) {
            continue;
        }

        let defs = block_out
            .get(pred.index())
            .and_then(|defs_by_reg| defs_by_reg.get(reg.index()))?
            .clone();
        if defs.is_empty() {
            return None;
        }

        distinct_defs.extend(defs.iter().copied());
        incoming.push(PhiIncoming { pred, defs });
    }

    if incoming.len() < 2 || distinct_defs.len() < 2 {
        return None;
    }

    incoming.sort_by_key(|incoming| incoming.pred);
    Some(PhiCandidate {
        id: PhiId(0),
        block,
        reg,
        incoming,
    })
}

fn materialize_value_facts(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    instr_effects: &[InstrEffect],
    ctx: ValueMaterializeCtx<'_>,
    reg_count: usize,
    phi_candidates: &[PhiCandidate],
    instruction_facts: &mut InstructionFacts,
) {
    let phi_by_block = index_phi_candidates_by_block(cfg, phi_candidates);
    let mut block_state = BlockValueState {
        fixed_in: vec![vec![BTreeSet::new(); reg_count]; cfg.blocks.len()],
        fixed_out: vec![vec![BTreeSet::new(); reg_count]; cfg.blocks.len()],
    };

    solve_reaching_values(
        cfg,
        graph_facts,
        instr_effects,
        ctx.lookups,
        phi_candidates,
        &phi_by_block,
        &mut block_state,
    );

    for block in cfg.block_order.iter().copied() {
        let Some(instr_indices) = instr_indices(cfg, block) else {
            continue;
        };

        let mut current_fixed = block_state.fixed_in[block.index()].clone();

        for instr_index in instr_indices {
            let effect = &instr_effects[instr_index];
            instruction_facts.reaching_values[instr_index] = snapshot_value_state(&current_fixed);

            let fixed_use_regs = resolved_fixed_use_regs(
                effect,
                &instruction_facts.open_reaching_defs[instr_index],
                ctx.open_defs,
            );
            let mut fixed_use_values = BTreeMap::new();
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

/// `Open(start)` 表示“从 start 到当前 top 的连续值包”，而不是单个开放尾值。
///
/// 因此如果当前 reaching 的 open def 实际从更晚寄存器开始，那么 `start..tail_start-1`
/// 这一段仍然是被这条指令真实读取的固定寄存器前缀，必须进入 use/liveness。
fn resolved_fixed_use_regs(
    effect: &InstrEffect,
    current_open: &BTreeSet<OpenDefId>,
    open_defs: &[OpenDef],
) -> BTreeSet<Reg> {
    let mut regs = effect.fixed_uses.clone();

    let Some(start_reg) = effect.open_use else {
        return regs;
    };

    if current_open.len() != 1 {
        return regs;
    }

    let open_def_id = current_open
        .iter()
        .next()
        .expect("len checked above, exactly one reaching open def exists");
    let Some(open_def) = open_defs.get(open_def_id.index()) else {
        return regs;
    };
    if open_def.start_reg.index() <= start_reg.index() {
        return regs;
    }

    for index in start_reg.index()..open_def.start_reg.index() {
        regs.insert(Reg(index));
    }

    regs
}

fn solve_reaching_values(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    instr_effects: &[InstrEffect],
    lookups: &DefLookupTables,
    phi_candidates: &[PhiCandidate],
    phi_by_block: &[Vec<PhiId>],
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
            apply_block_phi_values(&mut new_in, phi_candidates, &phi_by_block[block.index()]);

            if block_state.fixed_in[block.index()] != new_in {
                block_state.fixed_in[block.index()] = new_in.clone();
                changed = true;
            }

            let mut current_fixed = new_in;
            if let Some(instr_indices) = instr_indices(cfg, block) {
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

fn index_phi_candidates_by_block(cfg: &Cfg, phi_candidates: &[PhiCandidate]) -> Vec<Vec<PhiId>> {
    let mut phi_by_block = vec![Vec::new(); cfg.blocks.len()];
    for phi in phi_candidates {
        phi_by_block[phi.block.index()].push(phi.id);
    }
    phi_by_block
}

fn merge_predecessor_value_state(
    cfg: &Cfg,
    block: BlockRef,
    block_out: &[ValueState],
) -> ValueState {
    let reg_count = block_out.first().map_or(0, Vec::len);
    let mut merged_fixed = vec![BTreeSet::new(); reg_count];

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

fn apply_block_phi_values(
    state: &mut [BTreeSet<SsaValue>],
    phi_candidates: &[PhiCandidate],
    phi_ids: &[PhiId],
) {
    for phi_id in phi_ids {
        let phi = &phi_candidates[phi_id.index()];
        state[phi.reg.index()] = BTreeSet::from([SsaValue::Phi(*phi_id)]);
    }
}

fn apply_value_transfer(
    effect: &InstrEffect,
    fixed_def_lookup: &BTreeMap<Reg, DefId>,
    fixed_state: &mut [BTreeSet<SsaValue>],
) {
    for reg in &effect.fixed_must_defs {
        let def = fixed_def_lookup
            .get(reg)
            .copied()
            .expect("must-def register should already have a concrete DefId");
        fixed_state[reg.index()] = BTreeSet::from([SsaValue::Def(def)]);
    }

    for reg in &effect.fixed_may_defs {
        let def = fixed_def_lookup
            .get(reg)
            .copied()
            .expect("may-def register should already have a concrete DefId");
        fixed_state[reg.index()].insert(SsaValue::Def(def));
    }
}

fn snapshot_value_state(state: &[BTreeSet<SsaValue>]) -> InstrReachingValues {
    let fixed = state
        .iter()
        .enumerate()
        .filter_map(|(index, values)| {
            if values.is_empty() {
                None
            } else {
                Some((Reg(index), values.clone()))
            }
        })
        .collect();

    InstrReachingValues { fixed }
}

fn block_defines_reg(
    cfg: &Cfg,
    block: BlockRef,
    reg: Reg,
    fixed_def_lookup: &[BTreeMap<Reg, DefId>],
) -> bool {
    let Some(mut instr_indices) = instr_indices(cfg, block) else {
        return false;
    };

    instr_indices.any(|instr_index| fixed_def_lookup[instr_index].contains_key(&reg))
}

fn merge_predecessor_state(
    cfg: &Cfg,
    block: BlockRef,
    block_out: &[Vec<BTreeSet<DefId>>],
    open_block_out: &[BTreeSet<OpenDefId>],
) -> (Vec<BTreeSet<DefId>>, BTreeSet<OpenDefId>) {
    let reg_count = block_out.first().map_or(0, Vec::len);
    let mut merged_fixed = vec![BTreeSet::new(); reg_count];
    let mut merged_open = BTreeSet::new();

    for edge_ref in &cfg.preds[block.index()] {
        let pred = cfg.edges[edge_ref.index()].from;
        if !cfg.reachable_blocks.contains(&pred) {
            continue;
        }

        for (reg_defs, pred_defs) in merged_fixed.iter_mut().zip(&block_out[pred.index()]) {
            reg_defs.extend(pred_defs.iter().copied());
        }
        merged_open.extend(open_block_out[pred.index()].iter().copied());
    }

    (merged_fixed, merged_open)
}

fn apply_transfer(
    effect: &InstrEffect,
    fixed_def_lookup: &BTreeMap<Reg, DefId>,
    open_must_def_lookup: Option<OpenDefId>,
    open_may_def_lookup: Option<OpenDefId>,
    fixed_state: &mut [BTreeSet<DefId>],
    open_state: &mut BTreeSet<OpenDefId>,
) {
    for reg in &effect.fixed_must_defs {
        let def = fixed_def_lookup
            .get(reg)
            .copied()
            .expect("must-def register should already have a concrete DefId");
        fixed_state[reg.index()] = BTreeSet::from([def]);
    }

    for reg in &effect.fixed_may_defs {
        let def = fixed_def_lookup
            .get(reg)
            .copied()
            .expect("may-def register should already have a concrete DefId");
        fixed_state[reg.index()].insert(def);
    }

    if let Some(open_def) = open_must_def_lookup {
        open_state.clear();
        open_state.insert(open_def);
    }

    if let Some(open_def) = open_may_def_lookup {
        open_state.insert(open_def);
    }
}

fn snapshot_fixed_state(state: &[BTreeSet<DefId>]) -> InstrReachingDefs {
    let fixed = state
        .iter()
        .enumerate()
        .filter_map(|(index, defs)| {
            if defs.is_empty() {
                None
            } else {
                Some((Reg(index), defs.clone()))
            }
        })
        .collect();

    InstrReachingDefs { fixed }
}

fn compute_reg_count(proto: &LoweredProto, instr_effects: &[InstrEffect]) -> usize {
    let mut max_reg = proto.frame.max_stack_size as usize;

    for effect in instr_effects {
        for reg in effect
            .fixed_uses
            .iter()
            .chain(effect.fixed_must_defs.iter())
            .chain(effect.fixed_may_defs.iter())
        {
            max_reg = max_reg.max(reg.index() + 1);
        }

        if let Some(reg) = effect.open_use {
            max_reg = max_reg.max(reg.index() + 1);
        }
        if let Some(reg) = effect.open_must_def {
            max_reg = max_reg.max(reg.index() + 1);
        }
        if let Some(reg) = effect.open_may_def {
            max_reg = max_reg.max(reg.index() + 1);
        }
    }

    max_reg
}

fn compute_instr_effect(instr: &LowInstr) -> InstrEffect {
    let mut effect = InstrEffect::default();

    match instr {
        LowInstr::Move(instr) => {
            effect.fixed_uses.insert(instr.src);
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::LoadNil(instr) => insert_reg_range_defs(&mut effect.fixed_must_defs, instr.dst),
        LowInstr::LoadBool(instr) => {
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::LoadConst(instr) => {
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::UnaryOp(instr) => {
            effect.fixed_uses.insert(instr.src);
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::BinaryOp(instr) => {
            insert_value_operand_use(&mut effect.fixed_uses, instr.lhs);
            insert_value_operand_use(&mut effect.fixed_uses, instr.rhs);
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::Concat(instr) => {
            insert_reg_range_uses(&mut effect.fixed_uses, instr.src);
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::GetUpvalue(instr) => {
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::SetUpvalue(instr) => {
            effect.fixed_uses.insert(instr.src);
        }
        LowInstr::GetTable(instr) => {
            insert_access_base_use(&mut effect.fixed_uses, instr.base);
            insert_access_key_use(&mut effect.fixed_uses, instr.key);
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::SetTable(instr) => {
            insert_access_base_use(&mut effect.fixed_uses, instr.base);
            insert_access_key_use(&mut effect.fixed_uses, instr.key);
            insert_value_operand_use(&mut effect.fixed_uses, instr.value);
        }
        LowInstr::NewTable(instr) => {
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::SetList(instr) => {
            effect.fixed_uses.insert(instr.base);
            insert_value_pack_use(&mut effect.fixed_uses, &mut effect.open_use, instr.values);
        }
        LowInstr::Call(instr) => {
            effect.fixed_uses.insert(instr.callee);
            insert_value_pack_use(&mut effect.fixed_uses, &mut effect.open_use, instr.args);
            insert_result_pack_def(
                &mut effect.fixed_must_defs,
                &mut effect.open_must_def,
                instr.results,
            );
        }
        LowInstr::TailCall(instr) => {
            effect.fixed_uses.insert(instr.callee);
            insert_value_pack_use(&mut effect.fixed_uses, &mut effect.open_use, instr.args);
        }
        LowInstr::VarArg(instr) => insert_result_pack_def(
            &mut effect.fixed_must_defs,
            &mut effect.open_must_def,
            instr.results,
        ),
        LowInstr::Return(instr) => {
            insert_value_pack_use(&mut effect.fixed_uses, &mut effect.open_use, instr.values);
        }
        LowInstr::Closure(instr) => {
            effect.fixed_must_defs.insert(instr.dst);
            for capture in &instr.captures {
                if let CaptureSource::Reg(reg) = capture.source {
                    effect.fixed_uses.insert(reg);
                }
            }
        }
        LowInstr::Close(_instr) => {}
        LowInstr::NumericForInit(instr) => {
            effect.fixed_uses.insert(instr.index);
            effect.fixed_uses.insert(instr.limit);
            effect.fixed_uses.insert(instr.step);
            effect.fixed_must_defs.insert(instr.index);
        }
        LowInstr::NumericForLoop(instr) => {
            effect.fixed_uses.insert(instr.index);
            effect.fixed_uses.insert(instr.limit);
            effect.fixed_uses.insert(instr.step);
            effect.fixed_must_defs.insert(instr.index);
        }
        LowInstr::GenericForCall(instr) => {
            insert_reg_range_uses(&mut effect.fixed_uses, instr.state);
            insert_result_pack_def(
                &mut effect.fixed_must_defs,
                &mut effect.open_must_def,
                instr.results,
            );
        }
        LowInstr::GenericForLoop(instr) => {
            effect.fixed_uses.insert(instr.control);
            if instr.bindings.len != 0 {
                effect.fixed_uses.insert(instr.bindings.start);
            }
        }
        LowInstr::Jump(_instr) => {}
        LowInstr::Branch(instr) => match instr.cond.operands {
            BranchOperands::Unary(operand) => {
                insert_cond_operand_use(&mut effect.fixed_uses, operand)
            }
            BranchOperands::Binary(lhs, rhs) => {
                insert_cond_operand_use(&mut effect.fixed_uses, lhs);
                insert_cond_operand_use(&mut effect.fixed_uses, rhs);
            }
        },
    }

    effect
}

fn compute_side_effect_summary(instr: &LowInstr) -> SideEffectSummary {
    let mut tags = BTreeSet::new();

    match instr {
        LowInstr::GetUpvalue(_instr) => {
            tags.insert(EffectTag::ReadUpvalue);
        }
        LowInstr::SetUpvalue(_instr) => {
            tags.insert(EffectTag::WriteUpvalue);
        }
        LowInstr::GetTable(instr) => {
            tags.insert(EffectTag::ReadTable);
            if matches!(instr.base, AccessBase::Env) {
                tags.insert(EffectTag::ReadEnv);
            }
        }
        LowInstr::SetTable(instr) => {
            tags.insert(EffectTag::WriteTable);
            if matches!(instr.base, AccessBase::Env) {
                tags.insert(EffectTag::WriteEnv);
            }
        }
        LowInstr::NewTable(_instr) => {
            tags.insert(EffectTag::Alloc);
        }
        LowInstr::Closure(_instr) => {
            tags.insert(EffectTag::Alloc);
        }
        LowInstr::SetList(_instr) => {
            tags.insert(EffectTag::WriteTable);
        }
        LowInstr::Call(_instr) => {
            tags.insert(EffectTag::Call);
        }
        LowInstr::Close(_instr) => {
            tags.insert(EffectTag::Close);
        }
        _ => {}
    }

    SideEffectSummary { tags }
}

fn insert_reg_range_uses(target: &mut BTreeSet<Reg>, range: RegRange) {
    for offset in 0..range.len {
        target.insert(Reg(range.start.index() + offset));
    }
}

fn insert_reg_range_defs(target: &mut BTreeSet<Reg>, range: RegRange) {
    for offset in 0..range.len {
        target.insert(Reg(range.start.index() + offset));
    }
}

fn insert_value_operand_use(target: &mut BTreeSet<Reg>, operand: ValueOperand) {
    if let ValueOperand::Reg(reg) = operand {
        target.insert(reg);
    }
}

fn insert_access_base_use(target: &mut BTreeSet<Reg>, base: AccessBase) {
    if let AccessBase::Reg(reg) = base {
        target.insert(reg);
    }
}

fn insert_access_key_use(target: &mut BTreeSet<Reg>, key: AccessKey) {
    if let AccessKey::Reg(reg) = key {
        target.insert(reg);
    }
}

fn insert_value_pack_use(
    target: &mut BTreeSet<Reg>,
    open_target: &mut Option<Reg>,
    pack: ValuePack,
) {
    match pack {
        ValuePack::Fixed(range) => insert_reg_range_uses(target, range),
        ValuePack::Open(reg) => *open_target = Some(reg),
    }
}

fn insert_result_pack_def(
    target: &mut BTreeSet<Reg>,
    open_target: &mut Option<Reg>,
    pack: ResultPack,
) {
    match pack {
        ResultPack::Fixed(range) => insert_reg_range_defs(target, range),
        ResultPack::Open(reg) => *open_target = Some(reg),
        ResultPack::Ignore => {}
    }
}

fn insert_cond_operand_use(target: &mut BTreeSet<Reg>, operand: CondOperand) {
    if let CondOperand::Reg(reg) = operand {
        target.insert(reg);
    }
}

fn instr_indices(cfg: &Cfg, block: BlockRef) -> Option<impl Iterator<Item = usize>> {
    let range = cfg.blocks.get(block.index())?.instrs;
    if range.is_empty() {
        return None;
    }

    Some(range.start.index()..range.end())
}
