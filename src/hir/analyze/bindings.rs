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
use super::lower::{BoundSlotTarget, LexicalScope, ProtoBindings};
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
mod scalar_slots;

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
pub(super) use scalar_slots::bind_scalar_slots;

/// 无读取的比较结果没有 SSA phi，但互斥的 Boolean 初始化仍属于同一物理结果。
/// 在分配 debug/capture 身份前接回该绑定，让现有 branch-values 保留比较并恢复初始化。
fn coalesce_unused_comparison_initializers(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    structure: &ReadyStructureFacts,
    epochs: &SlotEpochFacts,
    fixed_temps: &mut [TempId],
) {
    let plan = structure.plan();
    for (owner, _) in plan.regions() {
        let Some(initializer) = plan.unused_comparison_initializer(owner, proto, cfg, dataflow)
        else {
            continue;
        };
        let [then_def, else_def] = initializer.defs;
        let independent = initializer.defs.iter().all(|&def| {
            fixed_temps[def.index()] == TempId(def.index())
                && debug_local_hint_for_ssa(proto, structure, SsaValue::Def(def)).is_none()
                && debug_local_hint_for_reg_at_instr(
                    proto,
                    initializer.reg,
                    dataflow.def_instr(def),
                )
                .is_none()
        });
        if independent
            && epochs.epoch_at(initializer.reg, dataflow.def_instr(then_def))
                == epochs.epoch_at(initializer.reg, dataflow.def_instr(else_def))
        {
            // SemanticBarrier:Binding：原有独立绑定和不同 CLOSE epoch 不能合并。
            // 同一源码 scope 在分支汇合后生效，由 debug binding fact 连接共同结果。
            fixed_temps[else_def.index()] = fixed_temps[then_def.index()];
        }
    }
}

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
            emission,
            epochs: captured_slot_epochs,
            child_mutable_upvalues,
            numeric_binding_phis: &numeric_binding_phis.bindings,
        },
        &mut entry_local_regs,
        &mut local_count,
        &mut local_debug_hints,
    );
    let closed_entry_locals = captured_slots
        .closed_entry_local_decls
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    // debug 入口声明也属于同一 cell；已确认 CLOSE 窗口后由窗口内部发射一次。
    entry_nil_local_decls.retain(|local| !closed_entry_locals.contains(local));

    for (loop_id, loop_plan) in structure.plan().loops() {
        let Some(binding_blocks) = loop_binding_blocks(structure.plan(), loop_id) else {
            continue;
        };
        let binding_blocks = binding_blocks.copied().collect::<Vec<_>>();
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
                    debug_local_name_for_reg_in_blocks(proto, cfg, &binding_blocks, reg).or_else(
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
                let binding_debug =
                    debug_local_hint_for_reg_at_block_entry(proto, cfg, loop_plan.header, reg)
                        .or_else(|| {
                            let LoopVmProtocol::NumericFor(protocol) =
                                structure.plan().loop_protocol(loop_id)?
                            else {
                                return None;
                            };
                            let instr = protocol
                                .writable_binding
                                .map_or(protocol.init_instr, |(copy, _)| copy);
                            let def = dataflow.instr_def_for_reg(instr, reg)?;
                            debug_local_hint_for_ssa(proto, structure, SsaValue::Def(def))
                        });
                if let Some(hint) = binding_debug {
                    // 循环语法已经声明这个 scope；分支出口的同一 debug phi
                    // 必须认回它，不能再次物化为另一个同名 local。
                    debug_scope_targets.insert(hint.scope, BoundSlotTarget::Local(local));
                    local_debug_hints[local.index()] = Some(decode_raw_string(hint.name));
                }
                for &block in &binding_blocks {
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
                    let mut binding_debug = None;
                    if let Some(LoopVmProtocol::GenericFor(protocol)) =
                        structure.plan().loop_protocol(loop_id)
                        && let Some(def) = dataflow.instr_def_for_reg(protocol.call_instr, reg)
                        && let Some(hint) =
                            debug_local_hint_for_ssa(proto, structure, SsaValue::Def(def))
                    {
                        // 循环语法已经声明了这个 source scope。内层循环的 phi 和入口
                        // 复制也须复用它，不能因保留 debug 信息再提升一套同名 carried local。
                        debug_scope_targets.insert(hint.scope, BoundSlotTarget::Local(local));
                        binding_debug = Some(decode_raw_string(hint.name));
                    }
                    local_debug_hints.push(
                        binding_debug
                            .or_else(|| {
                                debug_local_name_for_reg_in_blocks(proto, cfg, &binding_blocks, reg)
                            })
                            .or_else(|| {
                                debug_local_name_for_reg_at_block_entry(
                                    proto,
                                    cfg,
                                    loop_plan.header,
                                    reg,
                                )
                            }),
                    );
                    locals_for_loop.push(local);

                    for &block in &binding_blocks {
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
    let mut for_binding_phi_locals = numeric_binding_phis
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
    bind_generic_for_phis(
        cfg,
        dataflow,
        structure.plan(),
        &generic_for_locals,
        &block_local_regs,
        &mut for_binding_phi_locals,
    );

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
        (
            &numeric_binding_phis.bindings,
            &phi_debug_hints,
            &captured_slots,
        ),
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
    coalesce_unused_comparison_initializers(
        proto,
        cfg,
        dataflow,
        structure,
        captured_slot_epochs,
        &mut fixed_temps,
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
        // Luau 的子函数 debug_name 也会来自字段名，它不证明创建点存在源码 local。
        // 只有变量表的 binding hint 能建立声明身份，否则匿名字段闭包会被强制拆出。
        temp_debug_locals[temp.index()] = hint.as_ref().map(|hint| decode_raw_string(hint.name));
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

    for fact in structure.debug_bindings().accepted() {
        let crate::structure::DebugBindingValue::BranchInitializer(owner) = fact.value else {
            continue;
        };
        let Some(initializer) = structure
            .plan()
            .unused_comparison_initializer(owner, proto, cfg, dataflow)
        else {
            continue;
        };
        let [then_def, else_def] = initializer.defs;
        let temp = fixed_temps[then_def.index()];
        if temp == fixed_temps[else_def.index()] {
            temp_debug_locals[temp.index()] =
                Some(decode_raw_string(&proto.debug_locals[fact.scope].name));
            temp_debug_scopes[temp.index()] = Some(fact.scope);
        }
    }

    let lexical_scopes = lexical_windows::collect_lexical_scopes(
        proto,
        cfg,
        dataflow,
        graph,
        structure,
        emission,
        &captured_slots,
    );
    let mut scope_starts = lexical_scopes.iter().peekable();
    let mut scope_ends = Vec::new();
    let lexical_end_at = (0..proto.instrs.len())
        .map(|index| {
            while scope_ends.last().is_some_and(|&end| end <= index) {
                scope_ends.pop();
            }
            while scope_starts
                .peek()
                .is_some_and(|scope| scope.start == index)
            {
                scope_ends.push(scope_starts.next().expect("queried scope exists").end);
            }
            scope_ends.last().copied()
        })
        .collect::<Vec<_>>();

    // 显式 nil、根作用域字面量或 MOVE 声明已有原位置与 source scope。后续内层写和外层读共用该身份，
    // 不能等 block-local promotion 把它们分开后，再由 AST 给跨块 temp 补另一份声明。
    // 捕获槽仍由原 cell owner 分配；这里不接管其快照或 CLOSE 协议。
    let mut debug_initializer_decls = BTreeMap::new();
    let mut debug_preheader_targets = BTreeMap::new();
    let mut declared_local_home_slots = Vec::new();
    let mut debug_scope_values = vec![0usize; proto.debug_locals.len()];
    for &scope in temp_debug_scopes.iter().flatten() {
        debug_scope_values[scope] += 1;
    }
    let function_exit_start = proto
        .instrs
        .last()
        .filter(|instr| matches!(instr, LowInstr::Return(_)))
        .map(|_| {
            let return_index = proto.instrs.len() - 1;
            return_index
                - proto.instrs[..return_index]
                    .iter()
                    .rev()
                    .take_while(|instr| matches!(instr, LowInstr::Close(_)))
                    .count()
        });
    for fact in structure.debug_bindings().accepted() {
        let def = match fact.value.ssa() {
            Some(SsaValue::Def(def)) => def,
            Some(SsaValue::Phi(phi)) => {
                let Some(SsaValue::Def(def)) = structure
                    .plan()
                    .phi_plan(phi)
                    .and_then(|phi| phi.loop_carried())
                    .map(|binding| binding.input)
                else {
                    continue;
                };
                // 声明紧接循环入口时，debug 入口看到的是回边 phi。唯一 preheader
                // 输入才是本次初始化；循环内其它值版本仍属于同一个源码 scope。
                def
            }
            Some(SsaValue::Entry(_)) | None => continue,
        };
        let instr = dataflow.def_instr(def);
        let temp = fixed_temps[def.index()];
        let home = HomeSlotKey::new(
            fact.reg.index(),
            captured_slot_epochs.epoch_at(fact.reg, instr),
        );
        if !matches!(
            proto.instrs[instr.index()],
            LowInstr::LoadNil(_)
                | LowInstr::LoadBool(_)
                | LowInstr::LoadConst(_)
                | LowInstr::LoadInteger(_)
                | LowInstr::LoadNumber(_)
                | LowInstr::Move(_)
        ) || temp != TempId(def.index())
            || dataflow.def_reg(def) != fact.reg
            || !captured_slots.debug_binding_is_uncaptured(home, fact.scope)
            || debug_scope_targets.contains_key(&fact.scope)
        {
            continue;
        }
        if matches!(proto.instrs[instr.index()], LowInstr::Move(_))
            && fact
                .end_instr
                .is_some_and(|end| function_exit_start.is_none_or(|exit| end.index() < exit))
        {
            // 候选拒绝[ProofIncomplete]：这里只持有函数根作用域 owner，不能接管中途
            // 结束的对象快照 scope；否则 numeric-for 重用旧槽时会延长其 GC root。
            continue;
        }
        let block = cfg.instr_to_block[instr.index()];
        // goto 区域的共同入口也可位于前置循环之后。所有外部边都经过其首块，且
        // 内部没有回边再进初始化时，原前缀声明先于整个区域，仍由根词法 owner 持有。
        if !matches!(proto.instrs[instr.index()], LowInstr::LoadNil(_))
            && (emission.scope_owner(block) != Some(structure.plan().root())
                || (block != cfg.entry_block
                    && !emission.ordinary_block(block)
                    && !(emission.island_entry_prefix(block) && !graph.block_is_cyclic(block)))
                || emission.prefix_is_hoisted(block)
                || !emission
                    .regular_prefix(block)
                    .is_some_and(|range| range.contains(&instr.index()))
                || debug_scope_values[fact.scope] < 2
                || lexical_end_at[instr.index()].is_some_and(|window_end| {
                    fact.end_instr.is_none_or(|end| end.index() > window_end)
                }))
        {
            // 候选拒绝[ProofIncomplete]：这里只统一函数根作用域声明的多次写；前置分支或
            // 循环不改变后继声明的 owner，不能用 CFG 入口块替代词法可见性。内层声明的
            // 词法提升、单写声明帧的槽复用仍由原 owner 决定。CLOSE 窗口早于 debug
            // scope 结束时，也不能把本应跨窗口的身份声明固定在窗口内部。
            continue;
        }
        let local = LocalId(local_count);
        local_count += 1;
        local_debug_hints.push(Some(decode_raw_string(
            &proto.debug_locals[fact.scope].name,
        )));
        debug_scope_targets.insert(fact.scope, BoundSlotTarget::Local(local));
        debug_initializer_decls.insert(temp, local);
        if matches!(fact.value.ssa(), Some(SsaValue::Phi(_))) {
            debug_preheader_targets.insert(temp, BoundSlotTarget::Local(local));
        }
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
    // phi 入口的 preheader Def 早于 debug start，未必带名称 hint；原初始化发射为
    // local 后，其出边读取也必须指向该身份，不能留下未定义的旧 temp。
    bound_temp_targets.extend(debug_preheader_targets);
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
    captured_temp_facts
        .decl_temps
        .extend(debug_initializer_decls);

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
        closed_capture_temps: captured_slots
            .closed_capture_defs
            .iter()
            .filter_map(|def| {
                (fixed_temps[def.index()] == TempId(def.index()))
                    .then_some(fixed_temps[def.index()])
            })
            .collect(),
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
        for_binding_phi_locals,
        generic_for_locals,
        block_local_regs,
    }
}
