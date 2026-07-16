//! 这个文件专门负责把 Dataflow 的定义身份提升成 HIR 可直接消费的绑定表。
//!
//! 这个 pass 依赖前层已经给好的结构证据和数据流事实，不再回头重扫 CFG/low-IR 去猜
//! loop binding 或 merge 形状；它只负责“分配稳定身份”。
//!
//! 例子：
//! - `for i = 1, n do ... end` 对应的 `NumericForLike + LoopSourceBindings::Numeric(rX)`
//!   会直接产出一个 `LocalId` 绑定到该 loop header
//! - `for k, v in iter() do ... end` 对应的 `LoopSourceBindings::Generic(rA..)` 会直接产出
//!   一组 header locals，而不是再从 `GenericForLoop` terminator 回扫一次

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{LocalId, ParamId, TempId, UpvalueId};
use crate::parser::RawLocalVar;
use crate::structure::{Cfg, DataflowFacts, DefId, SsaValue};
use crate::structure::{LoopSourceBindings, StructureFacts};
use crate::transformer::{CaptureSource, InstrRef, LowInstr, LoweredProto, Reg};

use super::ProtoBindings;
use super::helpers::decode_raw_string;
use super::lower::BoundSlotTarget;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
struct CapturedSlotKey {
    slot: usize,
    epoch: usize,
}

impl CapturedSlotKey {
    fn new(slot: usize, epoch: usize) -> Self {
        Self { slot, epoch }
    }
}

pub(super) fn build_bindings(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    structure: &StructureFacts,
    child_mutable_upvalues: &[Vec<bool>],
) -> ProtoBindings {
    let params = (0..usize::from(proto.signature.num_params))
        .map(ParamId)
        .collect::<Vec<_>>();
    let param_debug_hints = (0..params.len())
        .map(|reg| debug_local_name_for_reg_at_pc(proto, Reg(reg), 0))
        .collect::<Vec<_>>();
    let upvalues = (0..usize::from(proto.upvalues.common.count))
        .map(UpvalueId)
        .collect::<Vec<_>>();
    let upvalue_debug_hints = (0..upvalues.len())
        .map(|index| {
            proto
                .debug_info
                .common
                .upvalue_names
                .get(index)
                .and_then(|name| name.as_ref().map(decode_raw_string))
        })
        .collect::<Vec<_>>();
    let mut locals = Vec::new();
    let mut local_debug_hints = Vec::new();
    let mut entry_local_regs = BTreeMap::new();
    let mut numeric_for_locals = BTreeMap::new();
    let mut generic_for_locals = BTreeMap::new();
    let mut block_local_regs = BTreeMap::new();

    if proto.signature.has_vararg_param_reg {
        let reg = crate::transformer::Reg(usize::from(proto.signature.num_params));
        let local = LocalId(locals.len());
        locals.push(local);
        local_debug_hints.push(debug_local_name_for_reg_at_pc(proto, reg, 0));
        if entry_reg_is_observed(dataflow, reg) {
            entry_local_regs.insert(reg, local);
        }
    }

    let captured_slots = collect_captured_slot_targets(
        proto,
        dataflow,
        &params,
        &mut entry_local_regs,
        &mut locals,
        &mut local_debug_hints,
        child_mutable_upvalues,
    );

    for candidate in &structure.loop_candidates {
        match candidate.source_bindings {
            Some(LoopSourceBindings::Numeric(reg)) => {
                let local = LocalId(locals.len());
                locals.push(local);
                local_debug_hints.push(None);
                numeric_for_locals.insert(candidate.header, local);

                for block in &candidate.body_scope_blocks {
                    block_local_regs
                        .entry(*block)
                        .or_insert_with(BTreeMap::new)
                        .insert(reg, local);
                }
            }
            Some(LoopSourceBindings::Generic(bindings)) => {
                let mut locals_for_loop = Vec::with_capacity(bindings.len);
                for offset in 0..bindings.len {
                    let local = LocalId(locals.len());
                    locals.push(local);
                    local_debug_hints.push(None);
                    let reg = crate::transformer::Reg(bindings.start.index() + offset);
                    locals_for_loop.push(local);

                    for block in &candidate.body_scope_blocks {
                        block_local_regs
                            .entry(*block)
                            .or_insert_with(BTreeMap::new)
                            .insert(reg, local);
                    }
                }
                generic_for_locals.insert(candidate.header, locals_for_loop);
            }
            None => {}
        }
    }

    let fixed_temps = (0..dataflow.defs.len()).map(TempId).collect::<Vec<_>>();
    let mut next_temp_index = fixed_temps.len();

    let mut phi_temps = Vec::with_capacity(dataflow.phi_candidates.len());
    for _phi in &dataflow.phi_candidates {
        phi_temps.push(TempId(next_temp_index));
        next_temp_index += 1;
    }

    let temps = (0..next_temp_index).map(TempId).collect::<Vec<_>>();
    let mut temp_debug_locals = vec![None; next_temp_index];

    for def in &dataflow.defs {
        let temp = fixed_temps[def.id.index()];
        temp_debug_locals[temp.index()] =
            debug_local_name_for_reg_at_instr(proto, def.reg, def.instr);
    }

    for phi in &dataflow.phi_candidates {
        let temp = phi_temps[phi.id.index()];
        temp_debug_locals[temp.index()] =
            debug_local_name_for_reg_at_block_entry(proto, cfg, phi.block, phi.reg);
    }

    let captured_temp_facts = collect_captured_temp_facts(
        proto,
        cfg,
        dataflow,
        &fixed_temps,
        &phi_temps,
        &captured_slots,
    );

    let instr_fixed_defs = dataflow
        .instr_defs
        .iter()
        .map(|defs| {
            defs.iter()
                .map(|def| fixed_temps[def.index()])
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    // 这一层默认只消费 reachable 子图，所以 label/temp 也贴着 shared CFG/Dataflow 的约定。
    let _ = cfg;

    ProtoBindings {
        params,
        param_debug_hints,
        locals,
        local_debug_hints,
        upvalues,
        upvalue_debug_hints,
        temps,
        temp_debug_locals,
        fixed_temps,
        phi_temps,
        instr_fixed_defs,
        captured_temp_targets: captured_temp_facts.targets,
        captured_temp_decl_locals: captured_temp_facts.decl_temps,
        capture_empty_local_decls: captured_temp_facts.empty_decls,
        closure_capture_targets: captured_slots.capture_targets,
        entry_local_regs,
        numeric_for_locals,
        generic_for_locals,
        block_local_regs,
    }
}

fn entry_reg_is_observed(dataflow: &DataflowFacts, reg: Reg) -> bool {
    let entry = SsaValue::Entry(reg);
    let mut pending = dataflow
        .use_values
        .iter()
        .filter_map(|uses| uses.fixed.get(reg))
        .collect::<Vec<_>>();
    let mut seen_phis = BTreeSet::new();

    while let Some(value) = pending.pop() {
        if value == entry {
            return true;
        }
        let SsaValue::Phi(phi_id) = value else {
            continue;
        };
        if seen_phis.insert(phi_id)
            && let Some(phi) = dataflow.phi_candidate(phi_id)
        {
            pending.extend(phi.incoming.iter().map(|incoming| incoming.value));
        }
    }

    false
}

struct CapturedSlotTargets {
    slot_targets: BTreeMap<CapturedSlotKey, CapturedSlotBinding>,
    capture_targets: BTreeMap<(usize, usize), BoundSlotTarget>,
}

#[derive(Debug, Clone, Copy)]
struct CapturedSlotBinding {
    target: BoundSlotTarget,
    start_instr: usize,
}

fn collect_captured_slot_targets(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    params: &[ParamId],
    entry_local_regs: &mut BTreeMap<Reg, LocalId>,
    locals: &mut Vec<LocalId>,
    local_debug_hints: &mut Vec<Option<String>>,
    child_mutable_upvalues: &[Vec<bool>],
) -> CapturedSlotTargets {
    let mut slot_targets = BTreeMap::<CapturedSlotKey, CapturedSlotBinding>::new();
    let mut capture_targets = BTreeMap::new();
    let mut epochs = vec![0usize; usize::from(proto.frame.max_stack_size).saturating_add(1)];
    let lowest_closed_slot = proto
        .instrs
        .iter()
        .filter_map(|instr| {
            let LowInstr::Close(close) = instr else {
                return None;
            };
            Some(close.from.index())
        })
        .min();

    for (instr_index, instr) in proto.instrs.iter().enumerate() {
        if let LowInstr::Closure(closure) = instr {
            for (capture_index, capture) in closure.captures.iter().enumerate() {
                let CaptureSource::Reg(reg) = capture.source else {
                    continue;
                };
                let child_writes = child_mutable_upvalues
                    .get(closure.proto.index())
                    .and_then(|mutable| mutable.get(capture_index))
                    .copied()
                    .unwrap_or(false);
                let entry_local_safe = lowest_closed_slot.is_none_or(|from| reg.index() < from);
                let has_no_reaching_value =
                    capture_has_no_reaching_value(dataflow, InstrRef(instr_index), reg);
                if reg == closure.dst {
                    continue;
                }
                if reg.index() < params.len()
                    || entry_local_regs.contains_key(&reg)
                    || (!child_writes && !has_no_reaching_value)
                {
                    continue;
                }

                ensure_epoch_slot(&mut epochs, reg);
                let key = CapturedSlotKey::new(reg.index(), epochs[reg.index()]);
                let start_instr = captured_slot_start_instr(
                    dataflow,
                    InstrRef(instr_index),
                    reg,
                    has_no_reaching_value,
                );
                let target = if let Some(binding) = slot_targets.get_mut(&key) {
                    binding.start_instr = binding.start_instr.min(start_instr);
                    binding.target
                } else {
                    let local = LocalId(locals.len());
                    locals.push(local);
                    local_debug_hints.push(debug_local_name_for_reg_at_instr(
                        proto,
                        reg,
                        InstrRef(instr_index),
                    ));
                    let target = BoundSlotTarget::Local(local);
                    slot_targets.insert(
                        key,
                        CapturedSlotBinding {
                            target,
                            start_instr,
                        },
                    );
                    target
                };
                capture_targets.insert((instr_index, reg.index()), target);
                // Close 只禁止把同一物理寄存器提升成函数级 entry local；当前 epoch 内，
                // child 可写 capture 仍必须有唯一 local，后续 def 才会写回同一个 upvalue。
                if entry_local_safe && (child_writes || has_no_reaching_value) {
                    let BoundSlotTarget::Local(local) = target;
                    entry_local_regs.entry(reg).or_insert(local);
                }
            }
        }

        if let LowInstr::Close(close) = instr {
            ensure_epoch_slot(&mut epochs, close.from);
            for epoch in epochs.iter_mut().skip(close.from.index()) {
                *epoch += 1;
            }
        }
    }

    CapturedSlotTargets {
        slot_targets,
        capture_targets,
    }
}

fn captured_slot_start_instr(
    dataflow: &DataflowFacts,
    capture_instr: InstrRef,
    reg: Reg,
    has_no_reaching_value: bool,
) -> usize {
    if has_no_reaching_value {
        return capture_instr.index();
    }

    dataflow
        .leaf_defs(dataflow.use_value(capture_instr, reg))
        .into_iter()
        .map(|def| dataflow.def_instr(def).index())
        .min()
        .unwrap_or(capture_instr.index())
}

fn capture_has_no_reaching_value(dataflow: &DataflowFacts, instr_ref: InstrRef, reg: Reg) -> bool {
    dataflow
        .use_values_at(instr_ref)
        .get(reg)
        .is_none_or(|value| matches!(value, crate::structure::SsaValue::Entry(_)))
}

struct CapturedTempFacts {
    targets: BTreeMap<TempId, BoundSlotTarget>,
    decl_temps: BTreeMap<TempId, LocalId>,
    empty_decls: BTreeMap<usize, Vec<LocalId>>,
}

fn collect_captured_temp_facts(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
    captured_slots: &CapturedSlotTargets,
) -> CapturedTempFacts {
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
    let mut declared_locals = BTreeSet::new();
    let mut defs_by_instr = vec![Vec::<(DefId, Reg)>::new(); proto.instrs.len()];
    for def in &dataflow.defs {
        defs_by_instr[def.instr.index()].push((def.id, def.reg));
    }

    let mut phis_by_instr = vec![Vec::<(crate::structure::PhiId, Reg)>::new(); proto.instrs.len()];
    for phi in &dataflow.phi_candidates {
        let instrs = cfg.blocks[phi.block.index()].instrs;
        if instrs.is_empty() {
            continue;
        }
        phis_by_instr[instrs.start.index()].push((phi.id, phi.reg));
    }

    let mut epochs = vec![0usize; usize::from(proto.frame.max_stack_size).saturating_add(1)];
    for (instr_index, instr) in proto.instrs.iter().enumerate() {
        if let LowInstr::Closure(closure) = instr {
            for capture in &closure.captures {
                let CaptureSource::Reg(reg) = capture.source else {
                    continue;
                };
                let Some(BoundSlotTarget::Local(local)) =
                    target_for_slot(reg, instr_index, &mut epochs, captured_slots)
                else {
                    continue;
                };
                if declared_locals.insert(local) {
                    empty_decls.entry(instr_index).or_default().push(local);
                }
            }
        }

        for (phi_id, reg) in phis_by_instr[instr_index].iter().copied() {
            if let Some(target) = target_for_slot(reg, instr_index, &mut epochs, captured_slots)
                && let Some(temp) = phi_temps.get(phi_id.index()).copied()
            {
                targets.insert(temp, target);
            }
        }

        for (def_id, reg) in defs_by_instr[instr_index].iter().copied() {
            if let Some(target) = target_for_slot(reg, instr_index, &mut epochs, captured_slots)
                && let Some(temp) = fixed_temps.get(def_id.index()).copied()
            {
                targets.insert(temp, target);
                let BoundSlotTarget::Local(local) = target;
                if declared_locals.insert(local) {
                    decl_temps.insert(temp, local);
                }
            }
        }

        if let LowInstr::Close(close) = instr {
            ensure_epoch_slot(&mut epochs, close.from);
            for epoch in epochs.iter_mut().skip(close.from.index()) {
                *epoch += 1;
            }
        }
    }

    CapturedTempFacts {
        targets,
        decl_temps,
        empty_decls,
    }
}

fn target_for_slot(
    reg: Reg,
    instr_index: usize,
    epochs: &mut Vec<usize>,
    captured_slots: &CapturedSlotTargets,
) -> Option<BoundSlotTarget> {
    ensure_epoch_slot(epochs, reg);
    captured_slots
        .slot_targets
        .get(&CapturedSlotKey::new(reg.index(), epochs[reg.index()]))
        .filter(|binding| instr_index >= binding.start_instr)
        .map(|binding| binding.target)
}

fn ensure_epoch_slot(epochs: &mut Vec<usize>, reg: Reg) {
    if reg.index() >= epochs.len() {
        epochs.resize(reg.index() + 1, 0);
    }
}

fn debug_local_name_for_reg_at_instr(
    proto: &LoweredProto,
    reg: Reg,
    instr: InstrRef,
) -> Option<String> {
    let pc = proto
        .lowering_map
        .pc_map
        .get(instr.index())?
        .first()
        .copied()?;
    debug_local_name_for_reg_at_pc(proto, reg, pc)
}

fn debug_local_name_for_reg_at_block_entry(
    proto: &LoweredProto,
    cfg: &Cfg,
    block: crate::structure::BlockRef,
    reg: Reg,
) -> Option<String> {
    let instrs = cfg.blocks[block.index()].instrs;
    if instrs.is_empty() {
        return None;
    }
    let instr = instrs.start;
    debug_local_name_for_reg_at_instr(proto, reg, instr)
}

fn debug_local_name_for_reg_at_pc(proto: &LoweredProto, reg: Reg, pc: u32) -> Option<String> {
    if let Some(extra) = proto.debug_info.extra.luau()
        && !extra.local_regs.is_empty()
    {
        return proto
            .debug_info
            .common
            .local_vars
            .iter()
            .zip(extra.local_regs.iter().copied())
            .find_map(|(local, local_reg)| {
                (debug_local_is_active_at_pc(local, pc) && usize::from(local_reg) == reg.index())
                    .then(|| decode_raw_string(&local.name))
            });
    }

    proto
        .debug_info
        .common
        .local_vars
        .iter()
        .filter(|local| debug_local_is_active_at_pc(local, pc))
        .nth(reg.index())
        .map(|local| decode_raw_string(&local.name))
}

fn debug_local_is_active_at_pc(local: &RawLocalVar, pc: u32) -> bool {
    local.start_pc <= pc && pc < local.end_pc
}
