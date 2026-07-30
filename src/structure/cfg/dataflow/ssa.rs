//! 固定寄存器的 canonical pruned SSA 构建。
//!
//! 本文件消费 CFG、支配/DF 事实、真实 instruction use/must-def 与活跃集合，统一产出
//! `Entry/Def/Phi` 身份、稀疏 block 快照、指令 use 和双向 use graph。它不识别
//! branch/loop/short-circuit，也不决定 HIR lvalue；这些语义归属由 Structure/HIR 消费
//! SSA 事实后完成。
//!
//! 输入形状：两条分支分别写 r2，随后 merge 读取 r2。
//! 输出形状：merge 上一个 pruned phi，读取点直接引用 `SsaValue::Phi`，两条 incoming
//! 分别指向对应 `Def`，不再另跑 reaching-def 与 reaching-value 固定点。

use super::super::common::{InstrUseValues, PhiId, PhiIncoming, SsaRegMap, UseSite};
use super::*;

pub(super) struct SsaAnalysis {
    pub(super) phis: Vec<PhiCandidate>,
    pub(super) phi_block_ranges: Vec<std::ops::Range<usize>>,
    pub(super) block_entry_values: Vec<SsaRegMap>,
    pub(super) block_exit_values: Vec<SsaRegMap>,
    pub(super) use_values: Vec<InstrUseValues>,
    pub(super) def_uses: Vec<Vec<UseSite>>,
    pub(super) def_phi_uses: Vec<Vec<PhiId>>,
    pub(super) phi_uses: Vec<Vec<UseSite>>,
    pub(super) phi_phi_uses: Vec<Vec<PhiId>>,
    pub(super) phi_use_blocks: Vec<Option<BlockRef>>,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn build_ssa(
    cfg: &Cfg,
    graph: &GraphFacts,
    defs: &[Def],
    def_lookup: &[Vec<(Reg, DefId)>],
    fixed_use_regs: &[Vec<Reg>],
    live_in: &[BTreeSet<Reg>],
    live_out: &[BTreeSet<Reg>],
    reg_count: usize,
    instr_count: usize,
    incoming_slots: &[Option<usize>],
) -> Result<SsaAnalysis, StructureError> {
    let mut phis = place_phis(cfg, graph, defs, live_in);
    let phi_block_ranges = super::index_phi_candidate_ranges(cfg, &phis);
    let mut block_entry_values = vec![SsaRegMap::default(); cfg.blocks.len()];
    let mut block_exit_values = vec![SsaRegMap::default(); cfg.blocks.len()];
    let mut use_values = vec![InstrUseValues::default(); instr_count];
    rename(
        cfg,
        graph,
        def_lookup,
        fixed_use_regs,
        live_in,
        live_out,
        reg_count,
        &phi_block_ranges,
        &mut phis,
        &mut block_entry_values,
        &mut block_exit_values,
        &mut use_values,
        incoming_slots,
    )?;

    let replacements = trivial_phi_replacements(&phis)?;
    let (mut phis, remap) = compact_phis(phis, &replacements)?;
    for values in &mut block_entry_values {
        values.try_map_values(|value| remap_value(value, &replacements, &remap))?;
    }
    for values in &mut block_exit_values {
        values.try_map_values(|value| remap_value(value, &replacements, &remap))?;
    }
    for values in &mut use_values {
        values
            .fixed
            .try_map_values(|value| remap_value(value, &replacements, &remap))?;
    }
    for phi in &mut phis {
        for incoming in &mut phi.incoming {
            incoming.value = remap_value(incoming.value, &replacements, &remap)?;
        }
    }
    let phi_block_ranges = super::index_phi_candidate_ranges(cfg, &phis);
    let (def_uses, def_phi_uses, phi_uses, phi_phi_uses, phi_use_blocks) =
        index_uses(cfg, defs.len(), &phis, &use_values)?;

    Ok(SsaAnalysis {
        phis,
        phi_block_ranges,
        block_entry_values,
        block_exit_values,
        use_values,
        def_uses,
        def_phi_uses,
        phi_uses,
        phi_phi_uses,
        phi_use_blocks,
    })
}

fn place_phis(
    cfg: &Cfg,
    graph: &GraphFacts,
    defs: &[Def],
    live_in: &[BTreeSet<Reg>],
) -> Vec<PhiCandidate> {
    let mut def_blocks = std::collections::BTreeMap::<Reg, BTreeSet<BlockRef>>::new();
    for def in defs {
        def_blocks.entry(def.reg).or_default().insert(def.block);
    }
    let mut placements = BTreeSet::new();
    for (reg, blocks) in def_blocks {
        let mut placed = BTreeSet::new();
        let mut pending = blocks.iter().copied().collect::<VecDeque<_>>();
        while let Some(block) = pending.pop_front() {
            for frontier in graph.dominance_frontier_blocks(block) {
                if !live_in[frontier.index()].contains(&reg) || !placed.insert(frontier) {
                    continue;
                }
                placements.insert((frontier, reg));
                if !blocks.contains(&frontier) {
                    pending.push_back(frontier);
                }
            }
        }

        // 入口块同时是 loop header 时，CFG 没有一条显式“函数入口边”，普通
        // dominance frontier 不会替 Entry(reg) 放 phi；把虚拟入口定义纳入后，
        // 回边写入才能与参数/初始栈槽正确合流。
        for natural_loop in &graph.natural_loops {
            if natural_loop.header == cfg.entry_block
                && live_in[cfg.entry_block.index()].contains(&reg)
                && natural_loop
                    .blocks
                    .iter()
                    .any(|block| blocks.contains(block))
            {
                placements.insert((cfg.entry_block, reg));
            }
        }
    }

    placements
        .into_iter()
        .enumerate()
        .map(|(index, (block, reg))| {
            let mut incoming = Vec::new();
            if block == cfg.entry_block {
                incoming.push(PhiIncoming {
                    edge: None,
                    pred: None,
                    value: SsaValue::Entry(reg),
                });
            }
            incoming.extend(
                cfg.preds[block.index()]
                    .iter()
                    .copied()
                    .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
                    .map(|edge| PhiIncoming {
                        edge: Some(edge),
                        pred: Some(cfg.edges[edge.index()].from),
                        value: SsaValue::Entry(reg),
                    }),
            );
            PhiCandidate {
                id: PhiId(index),
                block,
                reg,
                incoming,
            }
        })
        .collect()
}

#[derive(Debug)]
enum RenameEvent {
    Enter(BlockRef),
    Exit(Vec<Reg>),
}

#[allow(clippy::too_many_arguments)]
fn rename(
    cfg: &Cfg,
    graph: &GraphFacts,
    def_lookup: &[Vec<(Reg, DefId)>],
    fixed_use_regs: &[Vec<Reg>],
    live_in: &[BTreeSet<Reg>],
    live_out: &[BTreeSet<Reg>],
    reg_count: usize,
    phi_ranges: &[std::ops::Range<usize>],
    phis: &mut [PhiCandidate],
    block_entry_values: &mut [SsaRegMap],
    block_exit_values: &mut [SsaRegMap],
    use_values: &mut [InstrUseValues],
    incoming_slots: &[Option<usize>],
) -> Result<(), StructureError> {
    let mut stacks = (0..reg_count)
        .map(|index| vec![SsaValue::Entry(Reg(index))])
        .collect::<Vec<_>>();
    let mut events = vec![RenameEvent::Enter(cfg.entry_block)];
    while let Some(event) = events.pop() {
        match event {
            RenameEvent::Exit(regs) => {
                for reg in regs.into_iter().rev() {
                    let Some(stack) = stacks.get_mut(reg.index()) else {
                        return Err(StructureError::invalid(format!(
                            "SSA exit references register r{} outside the stack arena",
                            reg.index()
                        )));
                    };
                    if stack.pop().is_none() {
                        return Err(StructureError::invalid(format!(
                            "SSA stack for register r{} is empty on exit",
                            reg.index()
                        )));
                    }
                }
            }
            RenameEvent::Enter(block) => {
                let mut pushed = Vec::new();
                for phi in &phis[phi_ranges[block.index()].clone()] {
                    let Some(stack) = stacks.get_mut(phi.reg.index()) else {
                        return Err(StructureError::invalid(format!(
                            "{} register r{} exceeds the SSA stack arena",
                            phi.id,
                            phi.reg.index()
                        )));
                    };
                    stack.push(SsaValue::Phi(phi.id));
                    pushed.push(phi.reg);
                }
                block_entry_values[block.index()] = snapshot(&stacks, &live_in[block.index()])?;

                if let Some(indices) = super::instr_indices(cfg, block) {
                    for instr_index in indices {
                        let mut entries = Vec::with_capacity(fixed_use_regs[instr_index].len());
                        for &reg in &fixed_use_regs[instr_index] {
                            entries.push((reg, current(&stacks, reg)?));
                        }
                        use_values[instr_index].fixed = SsaRegMap::from_sorted_entries(entries)?;
                        for &(reg, def) in &def_lookup[instr_index] {
                            let Some(stack) = stacks.get_mut(reg.index()) else {
                                return Err(StructureError::invalid(format!(
                                    "definition {def:?} register r{} exceeds the SSA stack arena",
                                    reg.index()
                                )));
                            };
                            stack.push(SsaValue::Def(def));
                            pushed.push(reg);
                        }
                    }
                }
                block_exit_values[block.index()] = snapshot(&stacks, &live_out[block.index()])?;

                for edge in &cfg.succs[block.index()] {
                    let succ = cfg.edges[edge.index()].to;
                    let range = phi_ranges[succ.index()].clone();
                    if range.is_empty() {
                        continue;
                    }
                    let Some(slot) = incoming_slots.get(edge.index()).copied().flatten() else {
                        return Err(StructureError::invalid(format!(
                            "reachable CFG edge {edge} has no phi incoming slot"
                        )));
                    };
                    for phi in &mut phis[range] {
                        let Some(incoming) = phi.incoming.get_mut(slot) else {
                            return Err(StructureError::invalid(format!(
                                "{} incoming slot #{slot} does not match CFG edge {edge}",
                                phi.id
                            )));
                        };
                        if incoming.edge != Some(*edge) {
                            return Err(StructureError::invalid(format!(
                                "{} incoming slot #{slot} references the wrong CFG edge",
                                phi.id
                            )));
                        }
                        incoming.value = current(&stacks, phi.reg)?;
                    }
                }

                events.push(RenameEvent::Exit(pushed));
                for child in graph.dominator_tree.children[block.index()].iter().rev() {
                    events.push(RenameEvent::Enter(*child));
                }
            }
        }
    }
    Ok(())
}

fn current(stacks: &[Vec<SsaValue>], reg: Reg) -> Result<SsaValue, StructureError> {
    let Some(stack) = stacks.get(reg.index()) else {
        return Err(StructureError::invalid(format!(
            "register r{} exceeds the SSA stack arena",
            reg.index()
        )));
    };
    stack.last().copied().ok_or_else(|| {
        StructureError::invalid(format!("register r{} has an empty SSA stack", reg.index()))
    })
}

fn snapshot(stacks: &[Vec<SsaValue>], live: &BTreeSet<Reg>) -> Result<SsaRegMap, StructureError> {
    let mut entries = Vec::with_capacity(live.len());
    for &reg in live {
        entries.push((reg, current(stacks, reg)?));
    }
    SsaRegMap::from_sorted_entries(entries)
}

fn trivial_phi_replacements(phis: &[PhiCandidate]) -> Result<Vec<SsaValue>, StructureError> {
    let mut replacements = phis
        .iter()
        .map(|phi| SsaValue::Phi(phi.id))
        .collect::<Vec<_>>();
    let mut users = vec![Vec::new(); phis.len()];
    for phi in phis {
        for incoming in &phi.incoming {
            if let SsaValue::Phi(source) = incoming.value
                && source != phi.id
            {
                users[source.index()].push(phi.id);
            }
        }
    }
    let mut pending = phis.iter().map(|phi| phi.id).collect::<VecDeque<_>>();
    let mut queued = vec![true; phis.len()];
    while let Some(phi_id) = pending.pop_front() {
        queued[phi_id.index()] = false;
        let phi = &phis[phi_id.index()];
        let own = SsaValue::Phi(phi_id);
        let mut unique = None;
        let mut conflict = false;
        for incoming in &phi.incoming {
            let value = canonical_value_compress(incoming.value, &mut replacements)?;
            if value == own {
                continue;
            }
            match unique {
                None => unique = Some(value),
                Some(existing) if existing == value => {}
                Some(_) => {
                    conflict = true;
                    break;
                }
            }
        }
        let Some(value) = (!conflict).then_some(unique).flatten() else {
            continue;
        };
        if replacements[phi_id.index()] == value {
            continue;
        }
        replacements[phi_id.index()] = value;
        for user in &users[phi_id.index()] {
            if !queued[user.index()] {
                queued[user.index()] = true;
                pending.push_back(*user);
            }
        }
    }
    for index in 0..replacements.len() {
        replacements[index] =
            canonical_value_compress(SsaValue::Phi(PhiId(index)), &mut replacements)?;
    }
    Ok(replacements)
}

fn canonical_value_compress(
    value: SsaValue,
    replacements: &mut [SsaValue],
) -> Result<SsaValue, StructureError> {
    let mut value = value;
    let mut path = Vec::new();
    while let SsaValue::Phi(phi) = value {
        let Some(next) = replacements.get(phi.index()).copied() else {
            return Err(StructureError::invalid(format!(
                "SSA replacement references missing {phi}"
            )));
        };
        if next == value {
            break;
        }
        path.push(phi);
        value = next;
    }
    for phi in path {
        replacements[phi.index()] = value;
    }
    Ok(value)
}

fn compact_phis(
    phis: Vec<PhiCandidate>,
    replacements: &[SsaValue],
) -> Result<(Vec<PhiCandidate>, Vec<Option<PhiId>>), StructureError> {
    let mut remap = vec![None; phis.len()];
    let mut kept = Vec::new();
    for mut phi in phis {
        if super::canonical_value(SsaValue::Phi(phi.id), replacements)? != SsaValue::Phi(phi.id) {
            continue;
        }
        let id = PhiId(kept.len());
        remap[phi.id.index()] = Some(id);
        phi.id = id;
        kept.push(phi);
    }
    Ok((kept, remap))
}

fn remap_value(
    value: SsaValue,
    replacements: &[SsaValue],
    remap: &[Option<PhiId>],
) -> Result<SsaValue, StructureError> {
    match super::canonical_value(value, replacements)? {
        SsaValue::Phi(old) => {
            let Some(remapped) = remap.get(old.index()).copied().flatten() else {
                return Err(StructureError::invalid(format!(
                    "non-trivial {old} has no compacted identity"
                )));
            };
            Ok(SsaValue::Phi(remapped))
        }
        other => Ok(other),
    }
}

type UseIndex = (
    Vec<Vec<UseSite>>,
    Vec<Vec<PhiId>>,
    Vec<Vec<UseSite>>,
    Vec<Vec<PhiId>>,
    Vec<Option<BlockRef>>,
);

fn index_uses(
    cfg: &Cfg,
    def_count: usize,
    phis: &[PhiCandidate],
    uses: &[InstrUseValues],
) -> Result<UseIndex, StructureError> {
    let mut def_uses = vec![Vec::new(); def_count];
    let mut def_phi_uses = vec![Vec::new(); def_count];
    let mut phi_uses = vec![Vec::new(); phis.len()];
    let mut phi_phi_uses = vec![Vec::new(); phis.len()];
    let mut phi_use_blocks = vec![None; phis.len()];
    for (instr_index, values) in uses.iter().enumerate() {
        let Some(&block) = cfg.instr_to_block.get(instr_index) else {
            return Err(StructureError::invalid(format!(
                "SSA use table contains missing instruction @{instr_index}"
            )));
        };
        for (reg, value) in values.fixed.iter() {
            let site = UseSite {
                instr: InstrRef(instr_index),
                reg,
            };
            match value {
                SsaValue::Entry(_) => {}
                SsaValue::Def(def) => {
                    let Some(sites) = def_uses.get_mut(def.index()) else {
                        return Err(StructureError::invalid(format!(
                            "SSA use references missing definition {def:?}"
                        )));
                    };
                    sites.push(site);
                }
                SsaValue::Phi(phi) => {
                    let Some(sites) = phi_uses.get_mut(phi.index()) else {
                        return Err(StructureError::invalid(format!(
                            "SSA use references missing {phi}"
                        )));
                    };
                    sites.push(site);
                    let is_first_use = sites.len() == 1;
                    let Some(use_block) = phi_use_blocks.get_mut(phi.index()) else {
                        return Err(StructureError::invalid(format!(
                            "SSA use block index references missing {phi}"
                        )));
                    };
                    match *use_block {
                        None if is_first_use => {
                            *use_block = Some(block);
                        }
                        Some(existing) if existing != block => *use_block = None,
                        _ => {}
                    }
                }
            }
        }
    }
    for phi in phis {
        for incoming in &phi.incoming {
            match incoming.value {
                SsaValue::Entry(_) => {}
                SsaValue::Def(def) => {
                    let Some(users) = def_phi_uses.get_mut(def.index()) else {
                        return Err(StructureError::invalid(format!(
                            "{} references missing definition {def:?}",
                            phi.id
                        )));
                    };
                    users.push(phi.id);
                }
                SsaValue::Phi(source) if source != phi.id => {
                    let Some(users) = phi_phi_uses.get_mut(source.index()) else {
                        return Err(StructureError::invalid(format!(
                            "{} references missing source {source}",
                            phi.id
                        )));
                    };
                    users.push(phi.id);
                }
                SsaValue::Phi(_) => {}
            }
        }
    }
    Ok((
        def_uses,
        def_phi_uses,
        phi_uses,
        phi_phi_uses,
        phi_use_blocks,
    ))
}
