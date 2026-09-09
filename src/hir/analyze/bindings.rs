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
//! - 同一 `(slot, close epoch)` 的引用捕获会共用一次反向写后分析，不会按
//!   `closure 数 × def 数` 重复扫描；这里只决定绑定身份，不改写 closure 语义
//! - loop local 与 captured-slot owner 判定直接借用 Structure 的 region 块切片；
//!   例如嵌套循环的 body 覆盖由已校验的 containment 给出，不再展开 region tree。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{LocalId, ParamId, TempId, UpvalueId};
use crate::structure::{
    BlockRef, BlockTerminatorKind, BranchArm, Cfg, DataflowFacts, DefId, EdgeRef, EdgeTransfer,
    GraphFacts, PhiId, PhiIncomingDisposition, PhiIncomingPlan, PhiPlan, SsaValue,
};
use crate::structure::{
    CleanupDisposition, LoopPlanId, LoopSourceBindings, LoopVmProtocol, ReadyStructureFacts,
    RegionId, RegionPlan, StructurePlan,
};
use crate::transformer::{
    AccessBase, CaptureSource, GetTableKind, InstrRef, LowInstr, LoweredProto, Reg,
};

use super::helpers::decode_raw_string;
use super::lower::{BoundSlotTarget, ProtoBindings};
use crate::hir::promotion::{HomeSlotKey, SlotEpochFacts};

mod captured_slots;
mod captured_temps;
mod debug_entries;
mod debug_names;
mod lexical_windows;
mod loop_bindings;

use captured_slots::*;
use captured_temps::*;
use debug_entries::*;
use debug_names::*;
use loop_bindings::*;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
struct CapturedSlotKey {
    slot: usize,
    epoch: usize,
}

#[derive(Debug, Clone, Copy)]
struct DebugBindingHint<'a> {
    scope: usize,
    name: &'a crate::parser::RawString,
}

impl CapturedSlotKey {
    fn new(slot: usize, epoch: usize) -> Self {
        Self { slot, epoch }
    }
}

pub(super) fn build_bindings(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph: &GraphFacts,
    dataflow: &DataflowFacts,
    structure: &ReadyStructureFacts,
    captured_slot_epochs: &SlotEpochFacts,
    child_mutable_upvalues: &[&[bool]],
) -> ProtoBindings {
    let params = (0..usize::from(proto.signature.num_params))
        .map(ParamId)
        .collect::<Vec<_>>();
    let param_debug_hints = (0..params.len())
        .map(|reg| {
            debug_local_hint_for_ssa(proto, structure, SsaValue::Entry(Reg(reg)))
                .map(|hint| decode_raw_string(hint.name))
                .or_else(|| debug_local_name_for_reg_at_pc(proto, Reg(reg), 0))
        })
        .collect::<Vec<_>>();
    let upvalues = (0..usize::from(proto.upvalue_count))
        .map(UpvalueId)
        .collect::<Vec<_>>();
    let upvalue_debug_hints = (0..upvalues.len())
        .map(|index| {
            proto
                .upvalue_debug_names
                .get(index)
                .and_then(|name| name.as_ref().map(decode_raw_string))
        })
        .collect::<Vec<_>>();
    let mut local_count = 0;
    let mut local_debug_hints = Vec::new();
    let mut entry_local_regs = BTreeMap::new();
    let mut numeric_for_locals = BTreeMap::new();
    let mut generic_for_locals = BTreeMap::new();
    let mut block_local_regs = BTreeMap::new();
    let numeric_binding_phis = numeric_for_binding_phis(structure.plan());
    let phi_debug_hints = structure
        .plan()
        .phis()
        .map(|phi| {
            if !phi_participates_in_normal_binding(phi) {
                return None;
            }
            debug_local_hint_for_ssa(proto, structure, SsaValue::Phi(phi.phi))
                .or_else(|| debug_local_hint_for_reg_at_block_entry(proto, cfg, phi.block, phi.reg))
        })
        .collect::<Vec<_>>();

    let vararg_param_local = if proto.signature.has_vararg_param_reg {
        let reg = crate::transformer::Reg(usize::from(proto.signature.num_params));
        let local = LocalId(local_count);
        local_count += 1;
        local_debug_hints.push(debug_local_name_for_reg_at_pc(proto, reg, 0));
        if entry_reg_is_observed(dataflow, structure.plan(), reg) {
            entry_local_regs.insert(reg, local);
        }
        Some(local)
    } else {
        None
    };

    let (debug_entry_local_decls, debug_scope_targets) = allocate_debug_entry_bindings(
        proto,
        structure,
        &mut entry_local_regs,
        &mut local_count,
        &mut local_debug_hints,
    );

    let captured_slots = collect_captured_slot_targets(
        CapturedSlotInputs {
            proto,
            cfg,
            graph,
            dataflow,
            structure,
            epochs: captured_slot_epochs,
            child_mutable_upvalues,
            numeric_binding_phis: &numeric_binding_phis.bindings,
        },
        &mut entry_local_regs,
        &mut local_count,
        &mut local_debug_hints,
    );

    for (loop_id, loop_plan) in structure.plan().loops() {
        let Some(body_blocks) = loop_body_region(structure.plan(), loop_id)
            .map(|body| structure.plan().region_blocks(body))
        else {
            continue;
        };
        match loop_plan.source_bindings {
            Some(LoopSourceBindings::Numeric(reg)) => {
                let local = LocalId(local_count);
                local_count += 1;
                local_debug_hints.push(
                    debug_local_name_for_reg_in_blocks(proto, cfg, body_blocks, reg).or_else(
                        || {
                            debug_local_name_for_reg_at_block_entry(
                                proto,
                                cfg,
                                loop_plan.header,
                                reg,
                            )
                        },
                    ),
                );
                numeric_for_locals.insert(loop_plan.header, local);

                for &block in body_blocks {
                    block_local_regs
                        .entry(block)
                        .or_insert_with(BTreeMap::new)
                        .insert(reg, local);
                }
            }
            Some(LoopSourceBindings::Generic(bindings)) => {
                let mut locals_for_loop = Vec::with_capacity(bindings.len);
                for offset in 0..bindings.len {
                    let local = LocalId(local_count);
                    local_count += 1;
                    let reg = crate::transformer::Reg(bindings.start.index() + offset);
                    local_debug_hints.push(
                        debug_local_name_for_reg_in_blocks(proto, cfg, body_blocks, reg).or_else(
                            || {
                                debug_local_name_for_reg_at_block_entry(
                                    proto,
                                    cfg,
                                    loop_plan.header,
                                    reg,
                                )
                            },
                        ),
                    );
                    locals_for_loop.push(local);

                    for &block in body_blocks {
                        block_local_regs
                            .entry(block)
                            .or_insert_with(BTreeMap::new)
                            .insert(reg, local);
                    }
                }
                generic_for_locals.insert(loop_plan.header, locals_for_loop);
            }
            None => {}
        }
    }
    let numeric_binding_phi_locals = numeric_binding_phis
        .source_direct
        .iter()
        .enumerate()
        .map(|(index, is_binding)| {
            if !is_binding {
                return None;
            }
            let header = structure.plan().phi_plan(PhiId(index))?.block;
            numeric_for_locals.get(&header).copied()
        })
        .collect::<Vec<_>>();

    let mut fixed_temps = (0..dataflow.defs.len()).map(TempId).collect::<Vec<_>>();
    let mut next_temp_index = fixed_temps.len();

    let mut phi_temps = Vec::with_capacity(structure.plan().phis().len());
    for _phi in structure.plan().phis() {
        phi_temps.push(TempId(next_temp_index));
        next_temp_index += 1;
    }
    let nested_carried_parents =
        coalesce_nested_loop_carried_temps(structure.plan(), dataflow, &mut phi_temps);
    let nested_carried_child_owners = nested_carried_parents
        .iter()
        .enumerate()
        .filter_map(|(child, parent)| {
            Some((
                (*parent)?,
                loop_carried_binding(structure.plan(), structure.plan().phi_plan(PhiId(child))?)?
                    .owner,
            ))
        })
        .collect::<BTreeSet<_>>();
    coalesce_loop_state_temps(
        cfg,
        dataflow,
        structure.plan(),
        &nested_carried_parents,
        (&numeric_binding_phis.bindings, &phi_debug_hints),
        (&mut phi_temps, &mut fixed_temps),
    );
    preserve_loop_state_overwrites(
        proto,
        cfg,
        dataflow,
        structure.plan(),
        captured_slot_epochs,
        (&numeric_binding_phis.bindings, &phi_debug_hints),
        (&phi_temps, &mut fixed_temps),
    );
    // 只有下面实际分配 HIR staging 身份的 owner 才登记；复用 carried temp 的
    // repeat stage 保留其 canonical physical provenance。
    let mut home_free_temps = BTreeSet::new();
    let loop_guard_temps = structure
        .plan()
        .loops()
        .map(|(_, loop_plan)| {
            loop_plan.normal_tail.as_ref().map(|_| {
                let temp = TempId(next_temp_index);
                next_temp_index += 1;
                home_free_temps.insert(temp);
                temp
            })
        })
        .collect::<Vec<_>>();
    let repeat_staged_temps = structure
        .plan()
        .loops()
        .map(|(loop_id, loop_plan)| {
            let len = loop_plan
                .protocol
                .as_ref()
                .and_then(|protocol| match protocol {
                    LoopVmProtocol::Repeat(repeat) => Some(repeat.value_plan.staged_results.len()),
                    _ => None,
                })
                .unwrap_or(0);
            let mut temps = Vec::with_capacity(len);
            for result in loop_plan
                .protocol
                .as_ref()
                .and_then(|protocol| match protocol {
                    LoopVmProtocol::Repeat(repeat) => {
                        Some(repeat.value_plan.staged_results.as_slice())
                    }
                    _ => None,
                })
                .unwrap_or_default()
            {
                if let Some(temp) = repeat_stage_carried_temp(
                    structure.plan(),
                    loop_id,
                    result.target,
                    dataflow,
                    &nested_carried_child_owners,
                    &phi_temps,
                ) {
                    temps.push(temp);
                } else {
                    let temp = TempId(next_temp_index);
                    next_temp_index += 1;
                    home_free_temps.insert(temp);
                    temps.push(temp);
                }
            }
            temps
        })
        .collect::<Vec<_>>();

    let mut temp_debug_locals = vec![None; next_temp_index];
    let mut temp_debug_scopes = vec![None; next_temp_index];

    for def in &dataflow.defs {
        let temp = fixed_temps[def.id.index()];
        let instr = proto.instrs.get(def.instr.index());
        let hint = match instr {
            Some(LowInstr::GetTable(get_table)) if get_table.kind == GetTableKind::Method => None,
            Some(LowInstr::Move(receiver))
                if matches!(
                    proto.instrs.get(def.instr.index() + 1),
                    Some(LowInstr::GetTable(method))
                        if method.kind == GetTableKind::Method
                            && method.base == AccessBase::Reg(receiver.dst)
                ) =>
            {
                None
            }
            _ => debug_local_hint_for_ssa(proto, structure, SsaValue::Def(def.id))
                .or_else(|| debug_local_hint_for_reg_at_instr(proto, def.reg, def.instr)),
        };
        temp_debug_locals[temp.index()] = hint
            .as_ref()
            .map(|hint| decode_raw_string(hint.name))
            .or_else(|| closure_debug_name(proto, instr));
        temp_debug_scopes[temp.index()] = hint.map(|hint| hint.scope);
    }

    for phi in structure.plan().phis() {
        let Some(temp) = phi_temps.get(phi.phi.index()).copied() else {
            continue;
        };
        if phi_participates_in_normal_binding(phi) {
            let hint = phi_debug_hints[phi.phi.index()];
            temp_debug_locals[temp.index()] =
                hint.as_ref().map(|hint| decode_raw_string(hint.name));
            temp_debug_scopes[temp.index()] = hint.map(|hint| hint.scope);
        }
    }

    let debug_temp_targets = temp_debug_scopes
        .iter()
        .enumerate()
        .filter_map(|(index, scope)| {
            let scope = (*scope)?;
            let target = debug_scope_targets.get(&scope).copied()?;
            Some((TempId(index), target))
        })
        .collect::<BTreeMap<_, _>>();
    let mut local_debug_scopes = vec![None; local_count];
    for (&scope, &target) in &debug_scope_targets {
        if let BoundSlotTarget::Local(local) = target {
            local_debug_scopes[local.index()] = Some(scope);
        }
    }
    let mut conflicted_local_debug_scopes = BTreeSet::new();
    for (&temp, &target) in &debug_temp_targets {
        let BoundSlotTarget::Local(local) = target else {
            continue;
        };
        let Some(scope) = temp_debug_scopes[temp.index()] else {
            continue;
        };
        if conflicted_local_debug_scopes.contains(&local) {
            continue;
        }
        let local_scope = &mut local_debug_scopes[local.index()];
        if local_scope.is_none() || *local_scope == Some(scope) {
            *local_scope = Some(scope);
        } else {
            *local_scope = None;
            conflicted_local_debug_scopes.insert(local);
        }
    }

    let captured_temp_facts = collect_captured_temp_facts(CapturedTempFactsInput {
        proto,
        cfg,
        dataflow,
        plan: structure.plan(),
        fixed_temps: &fixed_temps,
        phi_temps: &phi_temps,
        captured_slots: &captured_slots,
        epochs: captured_slot_epochs,
        numeric_binding_phis: &numeric_binding_phis.bindings,
    });

    // CapturedSlotKey 与 HomeSlotKey 使用同一 `(reg, close epoch)` 坐标；保留全部 pair，
    // 若未来一个 local 吸收多个 key，promotion facts 会把它合流成 Conflict。
    let captured_local_home_slots = captured_slots
        .slot_targets
        .iter()
        .map(|(key, binding)| (binding.target, HomeSlotKey::new(key.slot, key.epoch)))
        .collect();

    // 这一层默认只消费 reachable 子图，所以 label/temp 也贴着 shared CFG/Dataflow 的约定。
    let _ = cfg;

    ProtoBindings {
        params,
        param_debug_hints,
        local_count,
        vararg_param_local,
        local_debug_hints,
        local_debug_scopes,
        upvalues,
        upvalue_debug_hints,
        temp_count: next_temp_index,
        temp_debug_locals,
        temp_debug_scopes,
        fixed_temps,
        phi_temps,
        home_free_temps,
        loop_guard_temps,
        repeat_staged_temps,
        debug_temp_targets,
        captured_temp_targets: captured_temp_facts.targets,
        captured_temp_decl_locals: captured_temp_facts.decl_temps,
        captured_local_home_slots,
        capture_empty_local_decls: captured_temp_facts.empty_decls,
        capture_entry_local_decls: captured_slots.entry_local_decls,
        debug_entry_local_decls,
        capture_region_local_decls: captured_slots.region_local_decls,
        closure_capture_targets: captured_slots.capture_targets,
        lexical_scopes: lexical_windows::collect_lexical_scopes(
            proto,
            cfg,
            dataflow,
            structure,
            captured_slots.lexical_scopes,
        ),
        entry_local_regs,
        numeric_for_locals,
        numeric_binding_phi_locals,
        generic_for_locals,
        block_local_regs,
    }
}
