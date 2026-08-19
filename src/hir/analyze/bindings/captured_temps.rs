//! 把 fixed/phi temp 投影到捕获槽 local 并生成空声明；依赖捕获槽目标与 binding 表，不负责 debug 命名；例如为先 capture 后赋值的 temp 安排声明。

use super::*;

pub(super) struct CapturedTempFacts {
    pub(super) targets: BTreeMap<TempId, BoundSlotTarget>,
    pub(super) decl_temps: BTreeMap<TempId, LocalId>,
    pub(super) empty_decls: BTreeMap<usize, Vec<LocalId>>,
}

pub(super) struct CapturedTempFactsInput<'a> {
    pub(super) proto: &'a LoweredProto,
    pub(super) cfg: &'a Cfg,
    pub(super) dataflow: &'a DataflowFacts,
    pub(super) plan: &'a StructurePlan,
    pub(super) fixed_temps: &'a [TempId],
    pub(super) phi_temps: &'a [TempId],
    pub(super) captured_slots: &'a CapturedSlotTargets,
    pub(super) epochs: &'a SlotEpochFacts,
    pub(super) numeric_binding_phis: &'a [bool],
}

pub(super) fn collect_captured_temp_facts(input: CapturedTempFactsInput<'_>) -> CapturedTempFacts {
    let CapturedTempFactsInput {
        proto,
        cfg,
        dataflow,
        plan,
        fixed_temps,
        phi_temps,
        captured_slots,
        epochs,
        numeric_binding_phis,
    } = input;
    if captured_slots.slot_targets.is_empty() {
        return CapturedTempFacts {
            targets: BTreeMap::new(),
            decl_temps: BTreeMap::new(),
            empty_decls: BTreeMap::new(),
        };
    }

    let mut targets = BTreeMap::new();
    let mut decl_temps = BTreeMap::new();
    let mut empty_decls = BTreeMap::<usize, Vec<LocalId>>::new();
    let mut declared_locals = captured_slots
        .entry_local_decls
        .iter()
        .chain(captured_slots.region_local_decls.values().flatten())
        .copied()
        .collect::<BTreeSet<_>>();
    let mut defs_by_instr = vec![Vec::<(DefId, Reg)>::new(); proto.instrs.len()];
    for def in &dataflow.defs {
        defs_by_instr[def.instr.index()].push((def.id, def.reg));
    }

    let mut phis_by_instr = vec![Vec::<(crate::structure::PhiId, Reg)>::new(); proto.instrs.len()];
    for phi in plan
        .phis()
        .filter(|phi| phi_participates_in_normal_binding(phi))
    {
        let instrs = cfg.blocks[phi.block.index()].instrs;
        if instrs.is_empty() {
            continue;
        }
        phis_by_instr[instrs.start.index()].push((phi.phi, phi.reg));
    }

    for (instr_index, instr) in proto.instrs.iter().enumerate() {
        if let LowInstr::Closure(closure) = instr {
            for capture in &closure.captures {
                let CaptureSource::ByReference(reg) = capture.source else {
                    continue;
                };
                let Some(BoundSlotTarget::Local(local)) =
                    target_for_slot(reg, instr_index, epochs, captured_slots)
                else {
                    continue;
                };
                if declared_locals.insert(local) {
                    empty_decls.entry(instr_index).or_default().push(local);
                }
            }
        }

        for (phi_id, reg) in phis_by_instr[instr_index].iter().copied() {
            if numeric_binding_phis
                .get(phi_id.index())
                .copied()
                .unwrap_or(false)
            {
                continue;
            }
            if let Some(target) = target_for_slot(reg, instr_index, epochs, captured_slots)
                && let Some(temp) = phi_temps.get(phi_id.index()).copied()
            {
                targets.insert(temp, target);
            }
        }

        for (def_id, reg) in defs_by_instr[instr_index].iter().copied() {
            if let Some(target) = target_for_slot(reg, instr_index, epochs, captured_slots)
                && let Some(temp) = fixed_temps.get(def_id.index()).copied()
            {
                targets.insert(temp, target);
                let BoundSlotTarget::Local(local) = target;
                if declared_locals.insert(local) {
                    decl_temps.insert(temp, local);
                }
            }
        }
    }

    CapturedTempFacts {
        targets,
        decl_temps,
        empty_decls,
    }
}
