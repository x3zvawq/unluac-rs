//! 将 Dataflow 定义与 Structure 证据映射为 HIR 稳定绑定。
//!
//! 消费前层发布的 loop binding、debug scope、capture 与词法槽事实，分配 LocalId
//! 或复用参数身份；不回扫 CFG/low-IR 猜循环形状。
//! 例如 NumericForLike + LoopSourceBindings::Numeric(rX) 直接为用户循环变量
//! 建立 local，hidden control 不成为可写源码变量。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{LocalId, ParamId, TempId, UpvalueId};
use crate::hir::emission::HirEmissionFacts;
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

pub(super) fn bind_parameter_slots(
    bindings: &mut ProtoBindings,
    facts: &crate::hir::promotion::ProtoPromotionFacts,
    dataflow: &DataflowFacts,
    emission: &HirEmissionFacts<'_>,
) {
    let mut hoisted_temps = BTreeSet::new();
    for def in &dataflow.defs {
        if emission.prefix_is_hoisted(def.block) {
            hoisted_temps.insert(bindings.fixed_temps[def.id.index()]);
        }
    }
    for index in 0..bindings.temp_count {
        let temp = TempId(index);
        let Some(home) = facts.trusted_temp_home_slot(temp) else {
            continue;
        };
        let Some(&param) = bindings.params.get(home.slot()) else {
            continue;
        };
        if facts.trusted_param_home_slot(param) != Some(home)
            || bindings.home_free_temps.contains(&temp)
            || bindings.temp_debug_scopes[index].is_some()
            || bindings.captured_temp_targets.contains_key(&temp)
            || hoisted_temps.contains(&temp)
        {
            continue;
        }
        // 完整合流的 home 必须仍为入口参数槽；跨槽、CLOSE 后的新 epoch 与
        // 合成 staging 不具备此身份。旧值 COPY 仍保留它自己的目标槽和 SSA 定义。
        bindings
            .bound_temp_targets
            .entry(temp)
            .or_insert(BoundSlotTarget::Param(param));
    }
}

mod call_results;
mod captured_slots;
mod captured_temps;
mod closed_outputs;
mod copy_roots;
mod debug_entries;
mod debug_names;
mod lexical_windows;
mod loop_bindings;
mod reused_frames;

pub(super) use call_results::bind_discarded_call_results;
use captured_slots::*;
use captured_temps::*;
pub(super) use copy_roots::{
    bind_allocation_copy_scopes, bind_copy_root_holders, bind_copy_root_initializers,
    bind_copy_root_scopes,
};
use debug_entries::*;
use debug_names::*;
use loop_bindings::*;
pub(super) use reused_frames::bind_reused_frames;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
struct CapturedSlotKey {
    slot: usize,
    epoch: usize,
    /// 原 CLOSE 窗口的独立 cell 激活；物理 close epoch 不区分互斥分支的声明。
    activation: Option<usize>,
}

#[derive(Debug, Clone, Copy)]
struct DebugBindingHint<'a> {
    scope: usize,
    name: &'a crate::parser::RawString,
}

impl CapturedSlotKey {
    fn new(slot: usize, epoch: usize) -> Self {
        Self {
            slot,
            epoch,
            activation: None,
        }
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "绑定分配显式借用各层事实及共享发射投影"
)]
pub(super) fn build_bindings(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph: &GraphFacts,
    dataflow: &DataflowFacts,
    structure: &ReadyStructureFacts,
    emission: &HirEmissionFacts<'_>,
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
    let mut numeric_binding_copies = BTreeSet::new();
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

    let (mut entry_nil_local_decls, mut debug_scope_targets) = allocate_debug_entry_bindings(
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
            Some(LoopSourceBindings::Numeric(control)) => {
                let reg = match structure.plan().loop_protocol(loop_id) {
                    Some(LoopVmProtocol::NumericFor(protocol)) => {
                        protocol.writable_binding.map_or(control, |(copy, reg)| {
                            numeric_binding_copies.insert(copy);
                            reg
                        })
                    }
                    _ => control,
                };
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
                if let Some(LoopVmProtocol::NumericFor(protocol)) =
                    structure.plan().loop_protocol(loop_id)
                    && let Some((copy, _)) = protocol.writable_binding
                {
                    // 单块 numeric body 的普通指令可归在 control region 的前缀，未必
                    // 出现在语法 body 的 region_blocks。原 COPY 的已验执行块才是用户
                    // 槽每轮读写的 owner；否则跳过入口 COPY 后仍会读取未初始化 temp。
                    block_local_regs
                        .entry(cfg.instr_to_block[copy.index()])
                        .or_insert_with(BTreeMap::new)
                        .insert(reg, local);
                }

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
                    if let Some(LoopVmProtocol::GenericFor(protocol)) =
                        structure.plan().loop_protocol(loop_id)
                        && let Some(def) = dataflow.instr_def_for_reg(protocol.call_instr, reg)
                        && let Some(hint) =
                            debug_local_hint_for_ssa(proto, structure, SsaValue::Def(def))
                    {
                        // 循环语法已经声明了这个 source scope。内层循环的 phi 和入口
                        // 复制也须复用它，不能因保留 debug 信息再提升一套同名 carried local。
                        debug_scope_targets.insert(hint.scope, BoundSlotTarget::Local(local));
                    }
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
                structure
                    .plan()
                    .phi_plan(PhiId(child))?
                    .loop_carried()?
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
        captured_slot_epochs,
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
            loop_plan
                .normal_tail
                .as_ref()
                .filter(|tail| !tail.in_exit_arm)
                .map(|_| {
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

    // 显式 nil 声明已经有原位置与 source scope。后续内层写和外层读共用该身份，
    // 不能等 block-local promotion 把它们分开后，再由 AST 给跨块 temp 补另一份声明。
    // 捕获槽仍由原 cell owner 分配；这里不接管其快照或 CLOSE 协议。
    let mut debug_nil_decls = BTreeMap::new();
    let mut declared_local_home_slots = Vec::new();
    for fact in structure.debug_bindings().accepted() {
        let SsaValue::Def(def) = fact.value else {
            continue;
        };
        let instr = dataflow.def_instr(def);
        let temp = fixed_temps[def.index()];
        let home = HomeSlotKey::new(
            fact.reg.index(),
            captured_slot_epochs.epoch_at(fact.reg, instr),
        );
        if !matches!(proto.instrs[instr.index()], LowInstr::LoadNil(_))
            || temp != TempId(def.index())
            || !captured_slots.debug_nil_binding_is_uncaptured(home, fact.scope)
            || debug_scope_targets.contains_key(&fact.scope)
        {
            continue;
        }
        let local = LocalId(local_count);
        local_count += 1;
        local_debug_hints.push(Some(decode_raw_string(
            &proto.debug_locals[fact.scope].name,
        )));
        debug_scope_targets.insert(fact.scope, BoundSlotTarget::Local(local));
        debug_nil_decls.insert(temp, local);
        declared_local_home_slots.push((local, home));
    }
    let mut bound_temp_targets = temp_debug_scopes
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
    for (&temp, &target) in &bound_temp_targets {
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

    let mut captured_temp_facts = collect_captured_temp_facts(CapturedTempFactsInput {
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
    captured_temp_facts.decl_temps.extend(debug_nil_decls);

    let lexical_scopes = lexical_windows::collect_lexical_scopes(
        proto,
        cfg,
        dataflow,
        graph,
        structure,
        emission,
        captured_slots.lexical_scopes.clone(),
    );
    let captured_entry_locals = captured_slots
        .entry_local_decls
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let occupied_entry_slots = entry_local_regs
        .keys()
        .map(|reg| reg.index())
        .chain(
            captured_slots
                .slot_targets
                .iter()
                .filter_map(|(home, binding)| {
                    captured_entry_locals
                        .contains(&binding.target)
                        .then_some(home.slot)
                }),
        )
        .collect::<BTreeSet<_>>();
    let captured_entry_first_slot = captured_slots
        .slot_targets
        .iter()
        .filter_map(|(home, binding)| {
            captured_entry_locals
                .contains(&binding.target)
                .then_some(home.slot)
        })
        .min();
    let original_entry_nil_locals = entry_nil_local_decls
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let original_entry_nil_last_slot = entry_local_regs
        .iter()
        .filter_map(|(reg, local)| {
            original_entry_nil_locals
                .contains(local)
                .then_some(reg.index())
        })
        .max();
    let mut new_entry_nil_locals = BTreeMap::new();
    for output in closed_outputs::collect(
        proto,
        cfg,
        graph,
        dataflow,
        structure,
        emission,
        captured_slot_epochs,
        &captured_slots,
        &lexical_scopes,
        &fixed_temps,
    ) {
        let temps = output.initial.into_iter().chain([output.output]);
        if (output.initial.is_none()
            && (occupied_entry_slots.contains(&output.home.slot())
                || original_entry_nil_last_slot.is_some_and(|last| output.home.slot() <= last)
                // 入口 nil 组在 capture entry 声明之前发射；不能交换已有 cell 的槽位置。
                || captured_entry_first_slot.is_some_and(|first| output.home.slot() >= first)))
            || temps.clone().any(|temp| {
                bound_temp_targets.contains_key(&temp)
                    || captured_temp_facts.targets.contains_key(&temp)
                    || captured_temp_facts.decl_temps.contains_key(&temp)
                    || temp_debug_scopes[temp.index()].is_some()
                    || temp_debug_locals[temp.index()].is_some()
            })
        {
            continue;
        }
        let local = LocalId(local_count);
        local_count += 1;
        local_debug_hints.push(None);
        local_debug_scopes.push(None);
        for temp in temps {
            bound_temp_targets.insert(temp, BoundSlotTarget::Local(local));
        }
        if let Some(initial) = output.initial {
            captured_temp_facts.decl_temps.insert(initial, local);
        } else {
            // 不改 entry_local_regs：旧 Entry SSA 读取仍是 nil，只有原输出 Def 写入 holder。
            new_entry_nil_locals.insert(output.home.slot(), local);
        }
        declared_local_home_slots.push((local, output.home));
    }
    entry_nil_local_decls.extend(new_entry_nil_locals.into_values());

    // 独立词法 cell 可以复用同一物理 `(reg, close epoch)`；activation 只区分绑定，
    // 不伪造新 home。一个 local 若吸收多个物理 key，promotion 仍合流成 Conflict。
    declared_local_home_slots.extend(
        captured_slots
            .slot_targets
            .iter()
            .map(|(key, binding)| (binding.target, HomeSlotKey::new(key.slot, key.epoch))),
    );

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
        bound_temp_targets,
        captured_temp_targets: captured_temp_facts.targets,
        temp_decl_locals: captured_temp_facts.decl_temps,
        declared_local_home_slots,
        capture_empty_local_decls: captured_temp_facts.empty_decls,
        capture_entry_local_decls: captured_slots.entry_local_decls,
        entry_nil_local_decls,
        capture_region_local_decls: captured_slots.region_local_decls,
        closure_capture_targets: captured_slots.capture_targets,
        lexical_scopes,
        entry_local_regs,
        numeric_for_locals,
        numeric_binding_copies,
        numeric_binding_phi_locals,
        generic_for_locals,
        block_local_regs,
    }
}
