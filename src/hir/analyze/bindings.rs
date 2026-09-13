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
//! - 可写 numeric-for 用户槽只消费 protocol 的原入口 COPY 和目标寄存器；body 的读写
//!   都绑定到同一语法 local，不把 hidden control 当作可写变量，也不在这里猜 MOVE 形状。
//! - 同一 `(slot, close epoch)` 的引用捕获会共用一次反向写后分析，不会按
//!   `closure 数 × def 数` 重复扫描；这里只决定绑定身份，不改写 closure 语义
//! - loop local 与 captured-slot owner 判定直接借用 Structure 的 region 块切片；
//!   例如嵌套循环的 body 覆盖由已校验的 containment 给出，不再展开 region tree。
//! - 原显式 nil 声明的未捕获 debug scope 在原指令位置绑定，内层写和外层读共用身份；
//!   例如 `local result; do result = closure end; return result` 不交给 AST 另造前向声明。

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

mod captured_slots;
mod captured_temps;
mod copy_roots;
mod debug_entries;
mod debug_names;
mod lexical_windows;
mod loop_bindings;

use captured_slots::*;
use captured_temps::*;
pub(super) use copy_roots::{bind_copy_root_holders, bind_copy_root_scopes};
use debug_entries::*;
use debug_names::*;
use loop_bindings::*;

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

    let (debug_entry_local_decls, mut debug_scope_targets) = allocate_debug_entry_bindings(
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
        if !matches!(proto.instrs[instr.index()], LowInstr::LoadNil(_))
            || temp != TempId(def.index())
            || dataflow.reg_is_captured(fact.reg)
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
        declared_local_home_slots.push((
            local,
            HomeSlotKey::new(
                fact.reg.index(),
                captured_slot_epochs.epoch_at(fact.reg, instr),
            ),
        ));
    }
    let bound_temp_targets = temp_debug_scopes
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
        debug_entry_local_decls,
        capture_region_local_decls: captured_slots.region_local_decls,
        closure_capture_targets: captured_slots.capture_targets,
        lexical_scopes: lexical_windows::collect_lexical_scopes(
            proto,
            cfg,
            dataflow,
            graph,
            structure,
            emission,
            captured_slots.lexical_scopes,
        ),
        entry_local_regs,
        numeric_for_locals,
        numeric_binding_copies,
        numeric_binding_phi_locals,
        generic_for_locals,
        block_local_regs,
    }
}
