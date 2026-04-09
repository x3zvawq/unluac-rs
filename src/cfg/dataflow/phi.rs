use std::collections::VecDeque;

use super::*;

pub(super) fn compute_phi_candidates(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    defs: &[Def],
    live_in: &[BTreeSet<Reg>],
    block_out: &[FixedState],
    fixed_def_lookup: &[FixedDefLookup],
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
            for frontier_block in graph_facts.dominance_frontier_blocks(block) {
                if !live_in[frontier_block.index()].contains(&reg) || !placed.insert(frontier_block)
                {
                    continue;
                }

                if let Some(candidate) = build_phi_candidate(cfg, frontier_block, reg, block_out) {
                    phi_candidates.push(candidate);
                }

                if !block_defines_reg(cfg, frontier_block, reg, fixed_def_lookup) {
                    worklist.push_back(frontier_block);
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
    block_out: &[FixedState],
) -> Option<PhiCandidate> {
    let mut incoming = Vec::new();
    let mut distinct_defs = BTreeSet::new();
    let mut has_entry_incoming = false;

    for edge_ref in &cfg.preds[block.index()] {
        let pred = cfg.edges[edge_ref.index()].from;
        if !cfg.reachable_blocks.contains(&pred) {
            continue;
        }

        let defs = block_out
            .get(pred.index())
            .map(|defs_by_reg| defs_by_reg.get(reg))?
            .clone();
        if defs.is_empty() {
            has_entry_incoming = true;
        }

        distinct_defs.extend(defs.iter().copied());
        incoming.push(PhiIncoming {
            pred,
            defs: defs.iter().copied().collect(),
        });
    }

    let distinct_sources = distinct_defs.len() + usize::from(has_entry_incoming);
    if incoming.len() < 2 || distinct_sources < 2 {
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

fn block_defines_reg(
    cfg: &Cfg,
    block: BlockRef,
    reg: Reg,
    fixed_def_lookup: &[FixedDefLookup],
) -> bool {
    let Some(mut instr_indices) = super::instr_indices(cfg, block) else {
        return false;
    };

    instr_indices.any(|instr_index| fixed_def_lookup[instr_index].defines(reg))
}
