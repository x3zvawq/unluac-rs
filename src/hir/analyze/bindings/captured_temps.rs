//! 把 fixed/phi temp 投影到捕获槽绑定并生成 local 空声明；依赖捕获槽目标与 slot epoch，不负责 debug 命名。例如参数先 capture 后赋值仍写回 ParamId，非参数槽使用已分配的 LocalId。

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
    let param_count = usize::from(proto.signature.num_params);
    let has_captured_params =
        (0..param_count).any(|reg| dataflow.reg_is_reference_captured(Reg(reg)));
    if captured_slots.slot_targets.is_empty() && !has_captured_params {
        return CapturedTempFacts {
            targets: BTreeMap::new(),
            decl_temps: BTreeMap::new(),
            empty_decls: BTreeMap::new(),
        };
    }

    let mut targets = BTreeMap::new();
    // 入口参数已拥有词法 cell；引用捕获不能把同一 epoch 的后续写拆成新 local。
    let param_target = |reg: Reg, instr_index: usize| {
        (reg.index() < param_count
            && dataflow.reg_is_reference_captured(reg)
            && epochs.epoch_at(reg, InstrRef(instr_index)) == 0)
            .then_some(BoundSlotTarget::Param(ParamId(reg.index())))
    };
    let mut decl_temps = BTreeMap::new();
    let mut empty_decls = BTreeMap::<usize, Vec<LocalId>>::new();
    let mut declared_locals = captured_slots
        .entry_local_decls
        .iter()
        .chain(captured_slots.region_local_decls.values().flatten())
        .copied()
        .collect::<BTreeSet<_>>();
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
                let Some(local) = target_for_slot(reg, instr_index, epochs, captured_slots) else {
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
            if let Some(target) = param_target(reg, instr_index).or_else(|| {
                target_for_slot(reg, instr_index, epochs, captured_slots)
                    .map(BoundSlotTarget::Local)
            }) && let Some(temp) = phi_temps.get(phi_id.index()).copied()
            {
                targets.insert(temp, target);
            }
        }

        for &def_id in &dataflow.instr_defs[instr_index] {
            let reg = dataflow.def_reg(def_id);
            if let Some(target) = param_target(reg, instr_index).or_else(|| {
                target_for_slot(reg, instr_index, epochs, captured_slots)
                    .map(BoundSlotTarget::Local)
            }) && let Some(temp) = fixed_temps.get(def_id.index()).copied()
            {
                targets.insert(temp, target);
                if let BoundSlotTarget::Local(local) = target
                    && declared_locals.insert(local)
                {
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
