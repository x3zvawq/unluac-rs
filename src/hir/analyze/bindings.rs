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

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::hir::common::{LocalId, ParamId, TempId, UpvalueId};
use crate::structure::{
    BlockRef, Cfg, DataflowFacts, DefId, GraphFacts, PhiId, PhiIncomingDisposition, PhiPlan,
    SsaValue,
};
use crate::structure::{
    LoopPlanId, LoopSourceBindings, LoopVmProtocol, RegionId, RegionPlan, StructureFacts,
    StructurePlan, UnstructuredLayoutItem,
};
use crate::transformer::{
    AccessBase, CaptureSource, GetTableKind, InstrRef, LowInstr, LoweredProto, Reg,
};

use super::helpers::decode_raw_string;
use super::lower::{BoundSlotTarget, ProtoBindings};
use crate::hir::promotion::SlotEpochFacts;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
struct CapturedSlotKey {
    slot: usize,
    epoch: usize,
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct DebugBindingHint {
    scope: usize,
    name: String,
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
    structure: &StructureFacts,
    captured_slot_epochs: &SlotEpochFacts,
    child_mutable_upvalues: &[Vec<bool>],
) -> ProtoBindings {
    let debug_names_by_ssa = debug_names_by_ssa(proto, structure);
    let params = (0..usize::from(proto.signature.num_params))
        .map(ParamId)
        .collect::<Vec<_>>();
    let param_debug_hints = (0..params.len())
        .map(|reg| {
            debug_names_by_ssa
                .get(&SsaValue::Entry(Reg(reg)))
                .map(|hint| hint.name.clone())
                .or_else(|| debug_local_name_for_reg_at_pc(proto, Reg(reg), 0))
        })
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
    let reference_captured_regs = (0..usize::from(proto.frame.max_stack_size))
        .map(Reg)
        .map(|reg| captured_slot_epochs.tracks_reference_capture(reg))
        .collect::<Vec<_>>();
    let mut locals = Vec::new();
    let mut local_debug_hints = Vec::new();
    let mut entry_local_regs = BTreeMap::new();
    let mut numeric_for_locals = BTreeMap::new();
    let mut generic_for_locals = BTreeMap::new();
    let mut block_local_regs = BTreeMap::new();
    let numeric_binding_phis = numeric_for_binding_phis(structure.plan());

    if proto.signature.has_vararg_param_reg {
        let reg = crate::transformer::Reg(usize::from(proto.signature.num_params));
        let local = LocalId(locals.len());
        locals.push(local);
        local_debug_hints.push(debug_local_name_for_reg_at_pc(proto, reg, 0));
        if entry_reg_is_observed(dataflow, structure.plan(), reg) {
            entry_local_regs.insert(reg, local);
        }
    }

    let (debug_entry_local_decls, debug_scope_locals) = allocate_debug_entry_locals(
        proto,
        structure,
        &mut entry_local_regs,
        &mut locals,
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
        &mut locals,
        &mut local_debug_hints,
    );

    for (loop_id, loop_plan) in structure.plan().loops() {
        let Some(body) = loop_body_region(structure.plan(), loop_id) else {
            continue;
        };
        let body_blocks = region_blocks(structure.plan(), body);
        match loop_plan.source_bindings {
            Some(LoopSourceBindings::Numeric(reg)) => {
                let local = LocalId(locals.len());
                locals.push(local);
                local_debug_hints.push(
                    debug_local_name_for_reg_in_blocks(proto, cfg, &body_blocks, reg).or_else(
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

                for block in &body_blocks {
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
                    let reg = crate::transformer::Reg(bindings.start.index() + offset);
                    local_debug_hints.push(
                        debug_local_name_for_reg_in_blocks(proto, cfg, &body_blocks, reg).or_else(
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

                    for block in &body_blocks {
                        block_local_regs
                            .entry(*block)
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
    let captured_regs = captured_regs(proto);
    let nested_carried_parents =
        coalesce_nested_loop_carried_temps(structure.plan(), &captured_regs, &mut phi_temps);
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
        dataflow,
        structure.plan(),
        &captured_regs,
        &nested_carried_parents,
        &numeric_binding_phis.bindings,
        &mut phi_temps,
        &mut fixed_temps,
    );
    let loop_guard_temps = structure
        .plan()
        .loops()
        .map(|(_, loop_plan)| {
            loop_plan.normal_tail.as_ref().map(|_| {
                let temp = TempId(next_temp_index);
                next_temp_index += 1;
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
                    &captured_regs,
                    &nested_carried_child_owners,
                    &phi_temps,
                ) {
                    temps.push(temp);
                } else {
                    temps.push(TempId(next_temp_index));
                    next_temp_index += 1;
                }
            }
            temps
        })
        .collect::<Vec<_>>();

    let temps = (0..next_temp_index).map(TempId).collect::<Vec<_>>();
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
            _ => debug_names_by_ssa
                .get(&SsaValue::Def(def.id))
                .cloned()
                .or_else(|| debug_local_hint_for_reg_at_instr(proto, def.reg, def.instr)),
        };
        temp_debug_locals[temp.index()] = hint
            .as_ref()
            .map(|hint| hint.name.clone())
            .or_else(|| closure_debug_name(proto, instr));
        temp_debug_scopes[temp.index()] = hint.map(|hint| hint.scope);
    }

    for phi in structure.plan().phis() {
        let Some(temp) = phi_temps.get(phi.phi.index()).copied() else {
            continue;
        };
        if phi_participates_in_normal_binding(phi) {
            let hint = debug_names_by_ssa
                .get(&SsaValue::Phi(phi.phi))
                .cloned()
                .or_else(|| {
                    debug_local_hint_for_reg_at_block_entry(proto, cfg, phi.block, phi.reg)
                });
            temp_debug_locals[temp.index()] = hint.as_ref().map(|hint| hint.name.clone());
            temp_debug_scopes[temp.index()] = hint.map(|hint| hint.scope);
        }
    }

    let debug_temp_targets = temp_debug_scopes
        .iter()
        .enumerate()
        .filter_map(|(index, scope)| {
            let scope = (*scope)?;
            let local = debug_scope_locals.get(&scope).copied()?;
            Some((TempId(index), BoundSlotTarget::Local(local)))
        })
        .collect::<BTreeMap<_, _>>();

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
        temp_debug_scopes,
        fixed_temps,
        phi_temps,
        loop_guard_temps,
        repeat_staged_temps,
        instr_fixed_defs,
        debug_temp_targets,
        captured_temp_targets: captured_temp_facts.targets,
        captured_temp_decl_locals: captured_temp_facts.decl_temps,
        capture_empty_local_decls: captured_temp_facts.empty_decls,
        capture_entry_local_decls: captured_slots.entry_local_decls,
        debug_entry_local_decls,
        capture_region_local_decls: captured_slots.region_local_decls,
        closure_capture_targets: captured_slots.capture_targets,
        reference_captured_regs,
        entry_local_regs,
        numeric_for_locals,
        numeric_binding_phi_locals,
        generic_for_locals,
        block_local_regs,
    }
}

/// 函数入口已经活跃、且没有显式 producer 的源码 local 由 VM 的 nil 初值承载。
///
/// 若继续把 `Entry(reg)` 只当作一个普通 nil 值，loop-carried phi 会在循环前才被
/// `locals` 提升，进而把源码声明错误地移动到前置调用之后。这里直接建立 scope 对应的
/// `LocalId`，后续同 scope 的 def/phi temp 都写回这个绑定。
fn allocate_debug_entry_locals(
    proto: &LoweredProto,
    structure: &StructureFacts,
    entry_local_regs: &mut BTreeMap<Reg, LocalId>,
    locals: &mut Vec<LocalId>,
    local_debug_hints: &mut Vec<Option<String>>,
) -> (Vec<LocalId>, BTreeMap<usize, LocalId>) {
    let param_count = usize::from(proto.signature.num_params);
    let vararg_reg = proto
        .signature
        .has_vararg_param_reg
        .then_some(Reg(param_count));
    let mut declarations = Vec::new();
    let mut scope_locals = BTreeMap::new();

    for fact in &structure.debug_bindings().accepted {
        let SsaValue::Entry(reg) = fact.value else {
            continue;
        };
        if fact.start_pc != 0 || reg.index() < param_count || Some(reg) == vararg_reg {
            continue;
        }
        let Some(debug_local) = proto.debug_locals.get(fact.scope) else {
            continue;
        };
        let local = if let Some(local) = entry_local_regs.get(&reg).copied() {
            local
        } else {
            let local = LocalId(locals.len());
            locals.push(local);
            local_debug_hints.push(Some(decode_raw_string(&debug_local.name)));
            entry_local_regs.insert(reg, local);
            declarations.push(local);
            local
        };
        scope_locals.insert(fact.scope, local);
    }

    (declarations, scope_locals)
}

fn closure_debug_name(proto: &LoweredProto, instr: Option<&LowInstr>) -> Option<String> {
    let LowInstr::Closure(closure) = instr? else {
        return None;
    };
    proto
        .children
        .get(closure.proto.index())?
        .debug_name
        .as_ref()
        .map(decode_raw_string)
}

#[derive(Clone, Copy)]
struct LoopCarriedBinding {
    owner: RegionId,
    input: SsaValue,
}

/// 嵌套 loop 只在最终 value plan 明确证明“沿用祖先 carried 槽位”时复用 HIR temp。
///
/// phi arena identity 与 incoming owner 保持不变；这里只收敛 lowering binding，避免
/// 每层 loop 为同一源码状态制造一组机械 handoff local。capture 或混合 owner 会让
/// 提前写回变得可观察，因此保守保留独立 temp。
fn coalesce_nested_loop_carried_temps(
    plan: &StructurePlan,
    captured_regs: &[bool],
    phi_temps: &mut [TempId],
) -> Vec<Option<PhiId>> {
    let carried = plan
        .phis()
        .map(|phi| loop_carried_binding(plan, phi))
        .collect::<Vec<_>>();
    let mut parents = vec![None; carried.len()];

    for phi in plan.phis() {
        if reg_is_captured(captured_regs, phi.reg) {
            continue;
        }
        let Some(binding) = carried.get(phi.phi.index()).copied().flatten() else {
            continue;
        };
        let SsaValue::Phi(source) = binding.input else {
            continue;
        };
        let Some(source_plan) = plan.phi_plan(source) else {
            continue;
        };
        let Some(source_binding) = carried.get(source.index()).copied().flatten() else {
            continue;
        };
        if source_plan.reg == phi.reg
            && source_binding.owner != binding.owner
            && plan.region_contains(source_binding.owner, binding.owner)
        {
            parents[phi.phi.index()] = Some(source);
        }
    }

    let mut roots = vec![None; parents.len()];
    let mut seen_at = vec![usize::MAX; parents.len()];
    for start in 0..parents.len() {
        if roots[start].is_some() {
            continue;
        }
        let mut path = Vec::new();
        let mut current = start;
        while roots[current].is_none() && seen_at[current] != start {
            seen_at[current] = start;
            path.push(current);
            let Some(parent) = parents[current] else {
                break;
            };
            current = parent.index();
        }
        let root = if seen_at[current] == start && parents[current].is_some() {
            None
        } else {
            Some(roots[current].unwrap_or(PhiId(current)))
        };
        for phi in path {
            roots[phi] = root.or(Some(PhiId(phi)));
        }
    }

    for (phi, root) in roots.iter().copied().enumerate() {
        let Some(root_temp) = root.and_then(|root| phi_temps.get(root.index()).copied()) else {
            continue;
        };
        phi_temps[phi] = root_temp;
    }
    parents
}

fn captured_regs(proto: &LoweredProto) -> Vec<bool> {
    let mut captured = vec![false; usize::from(proto.frame.max_stack_size)];
    for reg in proto
        .instrs
        .iter()
        .filter_map(|instr| match instr {
            LowInstr::Closure(closure) => Some(&closure.captures),
            _ => None,
        })
        .flatten()
        .filter_map(|capture| match capture.source {
            CaptureSource::ByValue(reg) | CaptureSource::ByReference(reg) => Some(reg),
            CaptureSource::Upvalue(_) => None,
        })
    {
        if reg.index() >= captured.len() {
            captured.resize(reg.index() + 1, false);
        }
        captured[reg.index()] = true;
    }
    captured
}

fn reg_is_captured(captured: &[bool], reg: Reg) -> bool {
    captured.get(reg.index()).copied().unwrap_or(false)
}

#[derive(Clone, Copy)]
struct BindingCandidate<T> {
    target: Option<T>,
    conflict: bool,
}

impl<T> Default for BindingCandidate<T> {
    fn default() -> Self {
        Self {
            target: None,
            conflict: false,
        }
    }
}

impl<T: Copy + Eq> BindingCandidate<T> {
    fn add(&mut self, target: T) {
        if self.target.is_some_and(|current| current != target) {
            self.conflict = true;
        } else {
            self.target = Some(target);
        }
    }

    fn resolved(self) -> Option<T> {
        (!self.conflict).then_some(self.target).flatten()
    }
}

/// 同一未捕获 VM 槽的 loop state 在原定义点直接写回 carried temp；这里只合并 identity，
/// 不移动表达式。候选从 carried target 出发一次构建，避免 result × owner 的重复扫描。
fn coalesce_loop_state_temps(
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    captured_regs: &[bool],
    nested_carried_parents: &[Option<PhiId>],
    numeric_binding_phis: &[bool],
    phi_temps: &mut [TempId],
    fixed_temps: &mut [TempId],
) {
    let pure_result_owners = plan
        .phis()
        .map(|phi| {
            let mut owner = None;
            let compatible = phi
                .incomings
                .iter()
                .all(|incoming| match incoming.disposition {
                    PhiIncomingDisposition::RegionResult(region) => {
                        owner.replace(region).is_none_or(|owner| owner == region)
                    }
                    PhiIncomingDisposition::Dead => true,
                    _ => false,
                });
            owner.filter(|_| compatible)
        })
        .collect::<Vec<_>>();
    let mut def_candidates = vec![BindingCandidate::default(); fixed_temps.len()];
    let mut result_candidates = vec![BindingCandidate::default(); phi_temps.len()];

    for phi in plan.phis() {
        if reg_is_captured(captured_regs, phi.reg) || numeric_binding_phis[phi.phi.index()] {
            continue;
        }
        let Some(carried) = loop_carried_binding(plan, phi) else {
            continue;
        };
        let Some(RegionPlan::Loop {
            body: loop_body, ..
        }) = plan.region(carried.owner)
        else {
            continue;
        };
        let target = phi_temps[phi.phi.index()];
        let has_nested_parent = nested_carried_parents[phi.phi.index()].is_some();
        let direct_region = if has_nested_parent {
            carried.owner
        } else {
            *loop_body
        };
        let mut result_source = None;
        let mut direct_compatible = true;
        let mut result_compatible = true;
        for incoming in &phi.incomings {
            if incoming.disposition != PhiIncomingDisposition::LoopCarried(carried.owner) {
                continue;
            }
            match incoming.value {
                SsaValue::Def(def)
                    if def_is_same_reg_in_region(dataflow, plan, def, phi.reg, direct_region) =>
                {
                    result_compatible = false;
                }
                SsaValue::Phi(source) => {
                    direct_compatible = false;
                    let result_region = pure_result_owners
                        .get(source.index())
                        .copied()
                        .flatten()
                        .and_then(|owner| {
                            if source == phi.phi
                                || plan
                                    .phi_plan(source)
                                    .is_none_or(|source| source.reg != phi.reg)
                            {
                                None
                            } else if plan.region_contains(*loop_body, owner) {
                                Some(owner)
                            } else if has_nested_parent && owner == carried.owner {
                                Some(carried.owner)
                            } else {
                                None
                            }
                        });
                    let Some(result_region) = result_region else {
                        result_compatible = false;
                        continue;
                    };
                    if result_source
                        .replace((source, result_region))
                        .is_some_and(|current| current != (source, result_region))
                    {
                        result_compatible = false;
                    }
                }
                _ => {
                    direct_compatible = false;
                    result_compatible = false;
                }
            }
        }
        if direct_compatible {
            for incoming in &phi.incomings {
                if incoming.disposition != PhiIncomingDisposition::LoopCarried(carried.owner) {
                    continue;
                }
                let SsaValue::Def(def) = incoming.value else {
                    continue;
                };
                def_candidates[def.index()].add(target);
            }
        } else if result_compatible && let Some((source, result_region)) = result_source {
            result_candidates[source.index()].add((target, result_region));
        }
    }

    let result_targets = result_candidates
        .into_iter()
        .map(BindingCandidate::resolved)
        .collect::<Vec<_>>();
    for (temp, target) in phi_temps.iter_mut().zip(&result_targets) {
        if let Some((target, _)) = target {
            *temp = *target;
        }
    }

    for phi in plan.phis() {
        let Some((target, result_region)) = result_targets[phi.phi.index()] else {
            continue;
        };
        for incoming in &phi.incomings {
            let SsaValue::Def(def) = incoming.value else {
                continue;
            };
            if !matches!(
                incoming.disposition,
                PhiIncomingDisposition::RegionResult(_)
            ) || !def_is_same_reg_in_region(dataflow, plan, def, phi.reg, result_region)
            {
                continue;
            }
            def_candidates[def.index()].add(target);
        }
    }

    for (temp, candidate) in fixed_temps.iter_mut().zip(def_candidates) {
        if let Some(target) = candidate.resolved() {
            *temp = target;
        }
    }
}

fn def_is_same_reg_in_region(
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    def: DefId,
    reg: Reg,
    region: RegionId,
) -> bool {
    dataflow.defs.get(def.index()).is_some_and(|definition| {
        definition.reg == reg
            && plan
                .region_for_block(definition.block)
                .is_some_and(|owner| plan.region_contains(region, owner))
    })
}

fn repeat_stage_carried_temp(
    plan: &StructurePlan,
    loop_id: LoopPlanId,
    target: PhiId,
    captured_regs: &[bool],
    nested_carried_child_owners: &BTreeSet<(PhiId, RegionId)>,
    phi_temps: &[TempId],
) -> Option<TempId> {
    let owner = plan.loop_region(loop_id)?;
    let result = plan.phi_plan(target)?;
    if reg_is_captured(captured_regs, result.reg) {
        return None;
    }
    let carried = loop_carried_binding(plan, result)?;
    if carried.owner == owner
        || !plan.region_contains(carried.owner, owner)
        || !nested_carried_child_owners.contains(&(target, owner))
    {
        return None;
    }
    phi_temps.get(target.index()).copied()
}

fn loop_carried_binding(plan: &StructurePlan, phi: &PhiPlan) -> Option<LoopCarriedBinding> {
    let mut owner = None;
    let mut input = None;
    let mut has_carried = false;
    for incoming in &phi.incomings {
        let region = match incoming.disposition {
            PhiIncomingDisposition::RegionInput(region) => {
                if input.replace(incoming.value).is_some() {
                    return None;
                }
                region
            }
            PhiIncomingDisposition::LoopCarried(region) => {
                has_carried = true;
                region
            }
            PhiIncomingDisposition::Dead => continue,
            PhiIncomingDisposition::RegionResult(_)
            | PhiIncomingDisposition::EdgeCopy
            | PhiIncomingDisposition::DiagnosticUnresolved => return None,
        };
        if owner.replace(region).is_some_and(|owner| owner != region) {
            return None;
        }
    }
    let owner = owner?;
    (has_carried && matches!(plan.region(owner), Some(RegionPlan::Loop { .. }))).then_some(
        LoopCarriedBinding {
            owner,
            input: input?,
        },
    )
}

fn loop_body_region(plan: &StructurePlan, loop_id: LoopPlanId) -> Option<RegionId> {
    let region = plan.loop_region(loop_id)?;
    match plan.region(region)? {
        RegionPlan::Loop { body, .. } => Some(*body),
        _ => None,
    }
}

struct NumericBindingPhiFacts {
    bindings: Vec<bool>,
    source_direct: Vec<bool>,
}

/// capture 所有权需要识别全部 exact header phi；只有 Structure 已冻结为 elided target 的
/// phi 才能把读取直接绑定到循环语法 local。寄存器相同不足以建立任一别名。
fn numeric_for_binding_phis(plan: &StructurePlan) -> NumericBindingPhiFacts {
    let mut phi_by_block_reg = BTreeMap::<(BlockRef, Reg), Option<PhiId>>::new();
    for phi in plan.phis() {
        phi_by_block_reg
            .entry((phi.block, phi.reg))
            .and_modify(|candidate| *candidate = None)
            .or_insert(Some(phi.phi));
    }

    let mut bindings = vec![false; plan.phis().len()];
    let mut source_direct = vec![false; plan.phis().len()];
    for (phi, direct) in plan.loops().filter_map(|(_, loop_plan)| {
        let LoopSourceBindings::Numeric(binding) = loop_plan.source_bindings? else {
            return None;
        };
        let phi = phi_by_block_reg
            .get(&(loop_plan.header, binding))
            .copied()
            .flatten()?;
        let direct = loop_plan
            .value_actions
            .as_ref()
            .is_some_and(|actions| actions.elided.iter().any(|origin| origin.target == phi));
        Some((phi, direct))
    }) {
        bindings[phi.index()] = true;
        source_direct[phi.index()] |= direct;
    }
    NumericBindingPhiFacts {
        bindings,
        source_direct,
    }
}

fn region_blocks(plan: &StructurePlan, region: RegionId) -> BTreeSet<BlockRef> {
    fn collect(plan: &StructurePlan, region: RegionId, blocks: &mut BTreeSet<BlockRef>) {
        let Some(node) = plan.region(region) else {
            return;
        };
        match node {
            RegionPlan::Block { block, .. } => {
                blocks.insert(*block);
            }
            RegionPlan::Sequence { children, .. } => {
                for child in children {
                    collect(plan, *child, blocks);
                }
            }
            RegionPlan::Branch {
                condition,
                then_arm,
                else_arm,
                ..
            } => {
                collect(plan, *condition, blocks);
                collect(plan, *then_arm, blocks);
                if let Some(else_arm) = else_arm {
                    collect(plan, *else_arm, blocks);
                }
            }
            RegionPlan::ValueDecision { plan: decision, .. } => {
                if let Some(decision) = plan.value_decision(*decision) {
                    blocks.extend(decision.blocks());
                }
            }
            RegionPlan::Loop {
                preheader,
                control,
                body,
                normal_tail,
                ..
            } => {
                if let Some(preheader) = preheader {
                    collect(plan, *preheader, blocks);
                }
                collect(plan, *control, blocks);
                collect(plan, *body, blocks);
                if let Some(normal_tail) = normal_tail {
                    collect(plan, *normal_tail, blocks);
                }
            }
            RegionPlan::Unstructured { layout, .. } => {
                for item in layout {
                    match item {
                        UnstructuredLayoutItem::Block(block) => {
                            blocks.insert(*block);
                        }
                        UnstructuredLayoutItem::Region(child) => collect(plan, *child, blocks),
                    }
                }
            }
        }
    }

    let mut blocks = BTreeSet::new();
    collect(plan, region, &mut blocks);
    blocks
}

fn phi_incoming_is_normal(disposition: PhiIncomingDisposition) -> bool {
    matches!(
        disposition,
        PhiIncomingDisposition::RegionInput(_)
            | PhiIncomingDisposition::RegionResult(_)
            | PhiIncomingDisposition::LoopCarried(_)
            | PhiIncomingDisposition::EdgeCopy
    )
}

fn phi_participates_in_normal_binding(phi: &PhiPlan) -> bool {
    !phi.has_unresolved()
        && phi
            .incomings
            .iter()
            .any(|incoming| phi_incoming_is_normal(incoming.disposition))
}

fn entry_reg_is_observed(dataflow: &DataflowFacts, plan: &StructurePlan, reg: Reg) -> bool {
    let entry = SsaValue::Entry(reg);
    let mut pending = dataflow
        .use_values
        .iter()
        .filter_map(|uses| uses.fixed.get(reg))
        .collect::<Vec<_>>();
    let mut seen_phis = vec![false; plan.phis().len()];

    while let Some(value) = pending.pop() {
        if value == entry {
            return true;
        }
        let SsaValue::Phi(phi_id) = value else {
            continue;
        };
        let Some(seen) = seen_phis.get_mut(phi_id.index()) else {
            continue;
        };
        if *seen {
            continue;
        }
        *seen = true;
        if let Some(phi) = plan.phi_plan(phi_id) {
            pending.extend(
                phi.incomings
                    .iter()
                    .filter(|incoming| phi_incoming_is_normal(incoming.disposition))
                    .map(|incoming| incoming.value),
            );
        }
    }

    false
}

struct CapturedSlotTargets {
    slot_targets: BTreeMap<CapturedSlotKey, CapturedSlotBinding>,
    capture_targets: BTreeMap<(usize, usize), BoundSlotTarget>,
    entry_local_decls: Vec<LocalId>,
    region_local_decls: BTreeMap<RegionId, Vec<LocalId>>,
}

#[derive(Debug, Clone, Copy)]
struct CapturedSlotBinding {
    target: BoundSlotTarget,
    start_instr: usize,
}

struct CapturedSlotUse {
    instr_index: usize,
    reg: Reg,
    key: CapturedSlotKey,
    start_instr: usize,
    requires_local: bool,
    entry_local_safe: bool,
}

#[derive(Default)]
struct CapturedSlotWriteQueries {
    uses: Vec<usize>,
    defs: Vec<(usize, BlockRef)>,
}

struct CapturedSlotWriteWorkspace {
    epoch: usize,
    def_epoch: Vec<usize>,
    last_def_instr: Vec<usize>,
    def_blocks: Vec<BlockRef>,
    reach_epoch: Vec<usize>,
    pending: VecDeque<BlockRef>,
}

impl CapturedSlotWriteWorkspace {
    fn new(block_count: usize) -> Self {
        Self {
            epoch: 0,
            def_epoch: vec![0; block_count],
            last_def_instr: vec![0; block_count],
            def_blocks: Vec::new(),
            reach_epoch: vec![0; block_count],
            pending: VecDeque::new(),
        }
    }

    fn analyze(&mut self, cfg: &Cfg, defs: &[(usize, BlockRef)]) {
        self.begin();
        for &(instr_index, block) in defs {
            if !cfg.reachable_blocks.contains(&block) {
                continue;
            }
            if self.def_epoch[block.index()] != self.epoch {
                self.def_epoch[block.index()] = self.epoch;
                self.last_def_instr[block.index()] = instr_index;
                self.def_blocks.push(block);
            } else {
                self.last_def_instr[block.index()] =
                    self.last_def_instr[block.index()].max(instr_index);
            }
        }

        // Def block 本身不是 seed：从 predecessor 开始才表示“至少经过一条边”。
        // 这使同块且位于 capture 之前的 def 只有在真实回路中才会命中。
        for index in 0..self.def_blocks.len() {
            let def_block = self.def_blocks[index];
            for edge_ref in &cfg.preds[def_block.index()] {
                self.enqueue(cfg, cfg.edges[edge_ref.index()].from);
            }
        }
        while let Some(block) = self.pending.pop_front() {
            for edge_ref in &cfg.preds[block.index()] {
                self.enqueue(cfg, cfg.edges[edge_ref.index()].from);
            }
        }
    }

    fn has_write_after(&self, cfg: &Cfg, capture_instr: usize) -> bool {
        let block = cfg.instr_to_block[capture_instr];
        // Closure 只定义 dst，且收集阶段已排除 dst 自捕获，所以不存在同指令
        // 定义 capture reg 的 equality 形状；若 Closure effect 改为多定义，必须重审此谓词。
        cfg.reachable_blocks.contains(&block)
            && ((self.def_epoch[block.index()] == self.epoch
                && self.last_def_instr[block.index()] > capture_instr)
                || self.reach_epoch[block.index()] == self.epoch)
    }

    fn begin(&mut self) {
        if self.epoch == usize::MAX {
            self.def_epoch.fill(0);
            self.reach_epoch.fill(0);
            self.epoch = 1;
        } else {
            self.epoch += 1;
        }
        self.def_blocks.clear();
        self.pending.clear();
    }

    fn enqueue(&mut self, cfg: &Cfg, block: BlockRef) {
        if cfg.reachable_blocks.contains(&block) && self.reach_epoch[block.index()] != self.epoch {
            self.reach_epoch[block.index()] = self.epoch;
            self.pending.push_back(block);
        }
    }
}

struct CapturedSlotStartWorkspace {
    epoch: usize,
    seen_phi_epoch: Vec<usize>,
    pending: Vec<SsaValue>,
}

impl CapturedSlotStartWorkspace {
    fn new(phi_count: usize) -> Self {
        Self {
            epoch: 0,
            seen_phi_epoch: vec![0; phi_count],
            pending: Vec::new(),
        }
    }

    fn begin(&mut self, root: SsaValue) {
        if self.epoch == usize::MAX {
            self.seen_phi_epoch.fill(0);
            self.epoch = 1;
        } else {
            self.epoch += 1;
        }
        self.pending.clear();
        self.pending.push(root);
    }

    fn visit(&mut self, phi: PhiId) -> bool {
        let Some(seen_epoch) = self.seen_phi_epoch.get_mut(phi.index()) else {
            return false;
        };
        if *seen_epoch == self.epoch {
            return false;
        }
        *seen_epoch = self.epoch;
        true
    }
}

struct CapturedSlotInputs<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    graph: &'a GraphFacts,
    dataflow: &'a DataflowFacts,
    structure: &'a StructureFacts,
    epochs: &'a SlotEpochFacts,
    child_mutable_upvalues: &'a [Vec<bool>],
    numeric_binding_phis: &'a [bool],
}

fn collect_captured_slot_targets(
    inputs: CapturedSlotInputs<'_>,
    entry_local_regs: &mut BTreeMap<Reg, LocalId>,
    locals: &mut Vec<LocalId>,
    local_debug_hints: &mut Vec<Option<String>>,
) -> CapturedSlotTargets {
    let CapturedSlotInputs {
        proto,
        cfg,
        graph,
        dataflow,
        structure,
        epochs,
        child_mutable_upvalues,
        numeric_binding_phis,
    } = inputs;
    let mut slot_targets = BTreeMap::<CapturedSlotKey, CapturedSlotBinding>::new();
    let mut capture_targets = BTreeMap::new();
    let mut captured_uses = Vec::new();
    let mut loop_owned_slots = BTreeSet::new();
    for (loop_id, loop_plan) in structure.plan().loops() {
        let Some(body) = loop_body_region(structure.plan(), loop_id) else {
            continue;
        };
        for block in region_blocks(structure.plan(), body) {
            match loop_plan.source_bindings {
                Some(LoopSourceBindings::Numeric(_)) => {}
                Some(LoopSourceBindings::Generic(bindings)) => {
                    for offset in 0..bindings.len {
                        loop_owned_slots.insert((block, Reg(bindings.start.index() + offset)));
                    }
                }
                None => {}
            }
            for value in &loop_plan.header_values {
                if matches!(
                    loop_plan.source_bindings,
                    Some(LoopSourceBindings::Numeric(binding)) if value.reg == binding
                ) {
                    continue;
                }
                loop_owned_slots.insert((block, value.reg));
            }
        }
    }
    let mut write_queries = BTreeMap::<CapturedSlotKey, CapturedSlotWriteQueries>::new();
    let mut start_workspace = CapturedSlotStartWorkspace::new(structure.plan().phis().len());
    let mut entry_decl_keys = BTreeSet::new();
    let mut region_decl_keys = BTreeMap::new();
    let mut conflicting_region_decl_keys = BTreeSet::new();
    let mut entry_safe_by_key = BTreeMap::new();

    for (instr_index, instr) in proto.instrs.iter().enumerate() {
        let LowInstr::Closure(closure) = instr else {
            continue;
        };
        for (capture_index, capture) in closure.captures.iter().enumerate() {
            let CaptureSource::ByReference(reg) = capture.source else {
                continue;
            };
            if reg == closure.dst
                || reg.index() < usize::from(proto.signature.num_params)
                || entry_local_regs.contains_key(&reg)
                || matches!(
                    dataflow.use_value(InstrRef(instr_index), reg),
                    SsaValue::Phi(phi)
                        if numeric_binding_phis.get(phi.index()).copied().unwrap_or(false)
                )
                || loop_owned_slots.contains(&(cfg.instr_to_block[instr_index], reg))
            {
                continue;
            }
            let has_no_reaching_value =
                capture_has_no_reaching_value(dataflow, InstrRef(instr_index), reg);
            let start_instr = captured_slot_start_instr(
                dataflow,
                structure.plan(),
                InstrRef(instr_index),
                reg,
                has_no_reaching_value,
                &mut start_workspace,
            );
            let entry_local_safe = epochs.spans_entry(reg);
            let key =
                CapturedSlotKey::new(reg.index(), epochs.epoch_at(reg, InstrRef(start_instr)));
            let child_writes = child_mutable_upvalues
                .get(closure.proto.index())
                .and_then(|mutable| mutable.get(capture_index))
                .copied()
                .unwrap_or(false);
            let requires_local = child_writes || has_no_reaching_value;
            let use_index = captured_uses.len();
            captured_uses.push(CapturedSlotUse {
                instr_index,
                reg,
                key,
                start_instr,
                requires_local,
                entry_local_safe,
            });
            if !requires_local {
                write_queries.entry(key).or_default().uses.push(use_index);
            }
        }
    }

    resolve_parent_writes_after_capture(
        cfg,
        dataflow,
        epochs,
        &mut write_queries,
        &mut captured_uses,
    );
    for captured in &captured_uses {
        entry_safe_by_key
            .entry(captured.key)
            .and_modify(|safe| *safe &= captured.entry_local_safe)
            .or_insert(captured.entry_local_safe);
        if captured.requires_local
            && captured.entry_local_safe
            && graph.block_is_cyclic(cfg.instr_to_block[captured.instr_index])
        {
            entry_decl_keys.insert(captured.key);
        }
        if captured.requires_local
            && let Some(region) = captured_slot_declaration_region(
                dataflow,
                structure.plan(),
                InstrRef(captured.instr_index),
                captured.reg,
            )
            && !conflicting_region_decl_keys.contains(&captured.key)
        {
            match region_decl_keys.get(&captured.key).copied() {
                None => {
                    region_decl_keys.insert(captured.key, region);
                }
                Some(existing) if existing == region => {}
                Some(_) => {
                    region_decl_keys.remove(&captured.key);
                    conflicting_region_decl_keys.insert(captured.key);
                }
            }
        }
    }

    for captured in captured_uses
        .iter()
        .filter(|captured| captured.requires_local)
    {
        let target = if let Some(binding) = slot_targets.get_mut(&captured.key) {
            binding.start_instr = binding.start_instr.min(captured.start_instr);
            binding.target
        } else {
            let local = LocalId(locals.len());
            locals.push(local);
            local_debug_hints.push(debug_local_name_for_reg_at_instr(
                proto,
                captured.reg,
                InstrRef(captured.instr_index),
            ));
            let target = BoundSlotTarget::Local(local);
            slot_targets.insert(
                captured.key,
                CapturedSlotBinding {
                    target,
                    start_instr: captured.start_instr,
                },
            );
            target
        };
        if captured.entry_local_safe {
            let BoundSlotTarget::Local(local) = target;
            entry_local_regs.entry(captured.reg).or_insert(local);
        }
    }

    for captured in captured_uses {
        if let Some(binding) = slot_targets.get_mut(&captured.key) {
            binding.start_instr = binding.start_instr.min(captured.start_instr);
            capture_targets.insert((captured.instr_index, captured.reg.index()), binding.target);
        }
    }

    entry_decl_keys.extend(
        conflicting_region_decl_keys
            .into_iter()
            .filter(|key| entry_safe_by_key.get(key).copied().unwrap_or(false)),
    );
    for key in &entry_decl_keys {
        region_decl_keys.remove(key);
    }
    let entry_local_decls = entry_decl_keys
        .iter()
        .filter_map(|key| slot_targets.get(key))
        .map(|binding| {
            let BoundSlotTarget::Local(local) = binding.target;
            local
        })
        .collect();
    let mut region_local_decls = BTreeMap::<RegionId, Vec<LocalId>>::new();
    for (key, region) in region_decl_keys {
        let Some(binding) = slot_targets.get(&key) else {
            continue;
        };
        let BoundSlotTarget::Local(local) = binding.target;
        region_local_decls.entry(region).or_default().push(local);
    }
    CapturedSlotTargets {
        slot_targets,
        capture_targets,
        entry_local_decls,
        region_local_decls,
    }
}

fn captured_slot_declaration_region(
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    capture_instr: InstrRef,
    reg: Reg,
) -> Option<RegionId> {
    let SsaValue::Phi(phi_id) = dataflow.use_value(capture_instr, reg) else {
        return None;
    };
    let phi = plan.phi_plan(phi_id)?;
    let mut owner = None;
    for incoming in phi
        .incomings
        .iter()
        .filter(|incoming| phi_incoming_is_normal(incoming.disposition))
    {
        let region = match incoming.disposition {
            // RegionInput copy 在进入 region 的 edge 上执行；声明若放在 target region
            // prefix，会排在首次写入之后并把刚写入的 capture slot 重置为 nil。
            PhiIncomingDisposition::RegionInput(region) => {
                plan.region(region)?.parent().unwrap_or(plan.root())
            }
            PhiIncomingDisposition::RegionResult(region)
            | PhiIncomingDisposition::LoopCarried(region) => region,
            PhiIncomingDisposition::EdgeCopy => {
                let relation = plan.edge_region_relation(incoming.edge?)?;
                relation
                    .lca
                    .or(relation.source_owner)
                    .or(relation.target_owner)?
            }
            PhiIncomingDisposition::Dead | PhiIncomingDisposition::DiagnosticUnresolved => {
                continue;
            }
        };
        owner = Some(owner.map_or(region, |owner| {
            captured_slot_common_owner(plan, owner, region).unwrap_or(plan.root())
        }));
    }
    captured_slot_lexical_owner(plan, owner?)
}

fn captured_slot_common_owner(
    plan: &StructurePlan,
    mut left: RegionId,
    right: RegionId,
) -> Option<RegionId> {
    loop {
        if plan.region_contains(left, right) {
            return Some(left);
        }
        left = plan.region(left)?.parent()?;
    }
}

fn captured_slot_lexical_owner(plan: &StructurePlan, owner: RegionId) -> Option<RegionId> {
    let mut declaration = owner;
    let mut cursor = Some(owner);
    while let Some(region) = cursor {
        let parent = plan.region(region)?.parent();
        if plan.single_pass_for_region(region).is_some() {
            declaration = parent?;
        }
        cursor = parent;
    }
    Some(declaration)
}

fn resolve_parent_writes_after_capture(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    queries_by_key: &mut BTreeMap<CapturedSlotKey, CapturedSlotWriteQueries>,
    captured_uses: &mut [CapturedSlotUse],
) {
    for def in &dataflow.defs {
        let key = CapturedSlotKey::new(def.reg.index(), epochs.epoch_at(def.reg, def.instr));
        let Some(queries) = queries_by_key.get_mut(&key) else {
            continue;
        };
        let instr_index = def.instr.index();
        queries
            .defs
            .push((instr_index, cfg.instr_to_block[instr_index]));
    }

    let mut workspace = CapturedSlotWriteWorkspace::new(cfg.blocks.len());
    for queries in queries_by_key.values() {
        workspace.analyze(cfg, &queries.defs);
        for &use_index in &queries.uses {
            let captured = &mut captured_uses[use_index];
            captured.requires_local = workspace.has_write_after(cfg, captured.instr_index);
        }
    }
}

fn captured_slot_start_instr(
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    capture_instr: InstrRef,
    reg: Reg,
    has_no_reaching_value: bool,
    workspace: &mut CapturedSlotStartWorkspace,
) -> usize {
    if has_no_reaching_value {
        return capture_instr.index();
    }

    let mut earliest = None;
    workspace.begin(dataflow.use_value(capture_instr, reg));
    while let Some(value) = workspace.pending.pop() {
        match value {
            SsaValue::Entry(_) => {}
            SsaValue::Def(def) => {
                let instr = dataflow.def_instr(def).index();
                earliest = Some(earliest.map_or(instr, |current: usize| current.min(instr)));
            }
            SsaValue::Phi(phi_id) => {
                if !workspace.visit(phi_id) {
                    continue;
                }
                if let Some(phi) = plan.phi_plan(phi_id) {
                    workspace.pending.extend(
                        phi.incomings
                            .iter()
                            .filter(|incoming| phi_incoming_is_normal(incoming.disposition))
                            .map(|incoming| incoming.value),
                    );
                }
            }
        }
    }
    earliest.unwrap_or(capture_instr.index())
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

struct CapturedTempFactsInput<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    dataflow: &'a DataflowFacts,
    plan: &'a StructurePlan,
    fixed_temps: &'a [TempId],
    phi_temps: &'a [TempId],
    captured_slots: &'a CapturedSlotTargets,
    epochs: &'a SlotEpochFacts,
    numeric_binding_phis: &'a [bool],
}

fn collect_captured_temp_facts(input: CapturedTempFactsInput<'_>) -> CapturedTempFacts {
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

fn target_for_slot(
    reg: Reg,
    instr_index: usize,
    epochs: &SlotEpochFacts,
    captured_slots: &CapturedSlotTargets,
) -> Option<BoundSlotTarget> {
    captured_slots
        .slot_targets
        .get(&CapturedSlotKey::new(
            reg.index(),
            epochs.epoch_at(reg, InstrRef(instr_index)),
        ))
        .filter(|binding| instr_index >= binding.start_instr)
        .map(|binding| binding.target)
}

fn debug_local_name_for_reg_at_instr(
    proto: &LoweredProto,
    reg: Reg,
    instr: InstrRef,
) -> Option<String> {
    debug_local_hint_for_reg_at_instr(proto, reg, instr).map(|hint| hint.name)
}

fn debug_local_hint_for_reg_at_instr(
    proto: &LoweredProto,
    reg: Reg,
    instr: InstrRef,
) -> Option<DebugBindingHint> {
    let pc = proto
        .lowering_map
        .pc_map
        .get(instr.index())?
        .first()
        .copied()?;
    debug_local_hint_for_reg_at_pc(proto, reg, pc)
}

fn debug_local_name_for_reg_at_block_entry(
    proto: &LoweredProto,
    cfg: &Cfg,
    block: crate::structure::BlockRef,
    reg: Reg,
) -> Option<String> {
    debug_local_hint_for_reg_at_block_entry(proto, cfg, block, reg).map(|hint| hint.name)
}

fn debug_local_hint_for_reg_at_block_entry(
    proto: &LoweredProto,
    cfg: &Cfg,
    block: crate::structure::BlockRef,
    reg: Reg,
) -> Option<DebugBindingHint> {
    let instrs = cfg.blocks[block.index()].instrs;
    if instrs.is_empty() {
        return None;
    }
    let instr = instrs.start;
    debug_local_hint_for_reg_at_instr(proto, reg, instr)
}

fn debug_local_name_for_reg_in_blocks(
    proto: &LoweredProto,
    cfg: &Cfg,
    blocks: &BTreeSet<BlockRef>,
    reg: Reg,
) -> Option<String> {
    blocks
        .iter()
        .filter_map(|block| {
            let instr = cfg.blocks[block.index()].instrs.start;
            let pc = proto
                .lowering_map
                .pc_map
                .get(instr.index())?
                .first()
                .copied()?;
            Some((pc, *block))
        })
        .min_by_key(|(pc, block)| (*pc, *block))
        .and_then(|(_, block)| debug_local_name_for_reg_at_block_entry(proto, cfg, block, reg))
}

fn debug_local_name_for_reg_at_pc(proto: &LoweredProto, reg: Reg, pc: u32) -> Option<String> {
    debug_local_hint_for_reg_at_pc(proto, reg, pc).map(|hint| hint.name)
}

fn debug_local_hint_for_reg_at_pc(
    proto: &LoweredProto,
    reg: Reg,
    pc: u32,
) -> Option<DebugBindingHint> {
    proto
        .debug_locals
        .iter()
        .enumerate()
        .find(|(_, local)| local.is_source() && local.reg == reg && local.is_active_at(pc))
        .map(|(scope, local)| DebugBindingHint {
            scope,
            name: decode_raw_string(&local.name),
        })
}

fn debug_names_by_ssa(
    proto: &LoweredProto,
    structure: &StructureFacts,
) -> BTreeMap<SsaValue, DebugBindingHint> {
    structure
        .debug_bindings()
        .accepted
        .iter()
        .filter_map(|fact| {
            let local = proto.debug_locals.get(fact.scope)?;
            local.is_source().then_some((
                fact.value,
                DebugBindingHint {
                    scope: fact.scope,
                    name: decode_raw_string(&local.name),
                },
            ))
        })
        .collect()
}
