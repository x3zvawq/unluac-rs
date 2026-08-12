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
use crate::structure::{
    BlockRef, Cfg, DataflowFacts, DefId, PhiId, PhiIncomingDisposition, PhiPlan, SsaValue,
};
use crate::structure::{
    LoopPlanId, LoopSourceBindings, RegionId, RegionPlan, StructureFacts, StructurePlan,
    UnstructuredLayoutItem,
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
    captured_slot_epochs: &SlotEpochFacts,
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

    if proto.signature.has_vararg_param_reg {
        let reg = crate::transformer::Reg(usize::from(proto.signature.num_params));
        let local = LocalId(locals.len());
        locals.push(local);
        local_debug_hints.push(debug_local_name_for_reg_at_pc(proto, reg, 0));
        if entry_reg_is_observed(dataflow, structure.plan(), reg) {
            entry_local_regs.insert(reg, local);
        }
    }

    let captured_slots = collect_captured_slot_targets(
        CapturedSlotInputs {
            proto,
            cfg,
            dataflow,
            structure,
            epochs: captured_slot_epochs,
            child_mutable_upvalues,
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
                local_debug_hints.push(None);
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
                    local_debug_hints.push(None);
                    let reg = crate::transformer::Reg(bindings.start.index() + offset);
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
    let nested_results = coalesce_nested_loop_result_temps(
        structure.plan(),
        &captured_regs,
        &nested_carried_parents,
        &mut phi_temps,
    );
    coalesce_nested_loop_state_defs(
        dataflow,
        structure.plan(),
        &captured_regs,
        &nested_carried_parents,
        &nested_results,
        &phi_temps,
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
                    crate::structure::LoopVmProtocol::Repeat(repeat) => {
                        Some(repeat.value_plan.staged_results.len())
                    }
                    _ => None,
                })
                .unwrap_or(0);
            let mut temps = Vec::with_capacity(len);
            for result in loop_plan
                .protocol
                .as_ref()
                .and_then(|protocol| match protocol {
                    crate::structure::LoopVmProtocol::Repeat(repeat) => {
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

    for def in &dataflow.defs {
        let temp = fixed_temps[def.id.index()];
        temp_debug_locals[temp.index()] = match proto.instrs.get(def.instr.index()) {
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
            _ => debug_local_name_for_reg_at_instr(proto, def.reg, def.instr),
        };
    }

    for phi in structure.plan().phis() {
        let Some(temp) = phi_temps.get(phi.phi.index()).copied() else {
            continue;
        };
        if phi_participates_in_normal_binding(phi) {
            temp_debug_locals[temp.index()] =
                debug_local_name_for_reg_at_block_entry(proto, cfg, phi.block, phi.reg);
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
        fixed_temps,
        phi_temps,
        loop_guard_temps,
        repeat_staged_temps,
        instr_fixed_defs,
        captured_temp_targets: captured_temp_facts.targets,
        captured_temp_decl_locals: captured_temp_facts.decl_temps,
        capture_empty_local_decls: captured_temp_facts.empty_decls,
        capture_entry_local_decls: captured_slots.entry_local_decls,
        capture_region_local_decls: captured_slots.region_local_decls,
        closure_capture_targets: captured_slots.capture_targets,
        reference_captured_regs,
        entry_local_regs,
        numeric_for_locals,
        generic_for_locals,
        block_local_regs,
    }
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
    captured_regs: &BTreeSet<Reg>,
    phi_temps: &mut [TempId],
) -> Vec<Option<PhiId>> {
    let carried = plan
        .phis()
        .map(|phi| loop_carried_binding(plan, phi))
        .collect::<Vec<_>>();
    let mut parents = vec![None; carried.len()];

    for phi in plan.phis() {
        if captured_regs.contains(&phi.reg) {
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

fn captured_regs(proto: &LoweredProto) -> BTreeSet<Reg> {
    proto
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
        .collect()
}

fn coalesce_nested_loop_result_temps(
    plan: &StructurePlan,
    captured_regs: &BTreeSet<Reg>,
    nested_carried_parents: &[Option<PhiId>],
    phi_temps: &mut [TempId],
) -> Vec<bool> {
    let mut coalesced = vec![false; phi_temps.len()];
    for result in plan.phis() {
        if captured_regs.contains(&result.reg) {
            continue;
        }
        let mut owner = None;
        let mut has_result = false;
        let compatible = result
            .incomings
            .iter()
            .all(|incoming| match incoming.disposition {
                PhiIncomingDisposition::RegionResult(region) => {
                    has_result = true;
                    owner.replace(region).is_none_or(|owner| owner == region)
                }
                PhiIncomingDisposition::Dead => true,
                _ => false,
            });
        let Some(owner) = owner.filter(|_| compatible && has_result) else {
            continue;
        };

        let mut candidates = plan
            .phis_for_region(owner)
            .iter()
            .filter_map(|phi| plan.phi_plan(*phi))
            .filter(|phi| phi.reg == result.reg)
            .filter(|phi| {
                loop_carried_binding(plan, phi).is_some_and(|binding| binding.owner == owner)
                    && nested_carried_parents
                        .get(phi.phi.index())
                        .copied()
                        .flatten()
                        .is_some()
                    && phi.incomings.iter().any(|incoming| {
                        incoming.disposition == PhiIncomingDisposition::LoopCarried(owner)
                    })
                    && phi.incomings.iter().all(|incoming| {
                        incoming.disposition != PhiIncomingDisposition::LoopCarried(owner)
                            || incoming.value == SsaValue::Phi(result.phi)
                    })
            });
        let Some(carried) = candidates.next() else {
            continue;
        };
        if candidates.next().is_some() {
            continue;
        }
        let Some(carried_temp) = phi_temps.get(carried.phi.index()).copied() else {
            continue;
        };
        if let Some(result_temp) = phi_temps.get_mut(result.phi.index()) {
            *result_temp = carried_temp;
            coalesced[result.phi.index()] = true;
        }
    }
    coalesced
}

#[derive(Clone, Copy, Default)]
struct DefBindingCandidate {
    target: Option<TempId>,
    conflict: bool,
}

fn coalesce_nested_loop_state_defs(
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    captured_regs: &BTreeSet<Reg>,
    nested_carried_parents: &[Option<PhiId>],
    nested_results: &[bool],
    phi_temps: &[TempId],
    fixed_temps: &mut [TempId],
) {
    let mut candidates = vec![DefBindingCandidate::default(); fixed_temps.len()];
    for phi in plan.phis() {
        if captured_regs.contains(&phi.reg) {
            continue;
        }
        let carried_owner = loop_carried_binding(plan, phi)
            .filter(|_| {
                nested_carried_parents
                    .get(phi.phi.index())
                    .copied()
                    .flatten()
                    .is_some()
            })
            .map(|binding| binding.owner);
        let result_is_coalesced = nested_results
            .get(phi.phi.index())
            .copied()
            .unwrap_or(false);
        let Some(target) = phi_temps.get(phi.phi.index()).copied() else {
            continue;
        };
        for incoming in &phi.incomings {
            let owns_def = carried_owner.is_some_and(|owner| {
                incoming.disposition == PhiIncomingDisposition::LoopCarried(owner)
            }) || (result_is_coalesced
                && matches!(
                    incoming.disposition,
                    PhiIncomingDisposition::RegionResult(_)
                ));
            let SsaValue::Def(def) = incoming.value else {
                continue;
            };
            if !owns_def
                || dataflow
                    .defs
                    .get(def.index())
                    .is_none_or(|definition| definition.reg != phi.reg)
            {
                continue;
            }
            let Some(candidate) = candidates.get_mut(def.index()) else {
                continue;
            };
            if candidate.target.is_some_and(|current| current != target) {
                candidate.conflict = true;
            } else {
                candidate.target = Some(target);
            }
        }
    }
    for (temp, candidate) in fixed_temps.iter_mut().zip(candidates) {
        if !candidate.conflict
            && let Some(target) = candidate.target
        {
            *temp = target;
        }
    }
}

fn repeat_stage_carried_temp(
    plan: &StructurePlan,
    loop_id: LoopPlanId,
    target: PhiId,
    captured_regs: &BTreeSet<Reg>,
    nested_carried_child_owners: &BTreeSet<(PhiId, RegionId)>,
    phi_temps: &[TempId],
) -> Option<TempId> {
    let owner = plan.loop_region(loop_id)?;
    let result = plan.phi_plan(target)?;
    if captured_regs.contains(&result.reg) {
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

struct CapturedSlotInputs<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    dataflow: &'a DataflowFacts,
    structure: &'a StructureFacts,
    epochs: &'a SlotEpochFacts,
    child_mutable_upvalues: &'a [Vec<bool>],
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
        dataflow,
        structure,
        epochs,
        child_mutable_upvalues,
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
                Some(LoopSourceBindings::Numeric(reg)) => {
                    loop_owned_slots.insert((block, reg));
                }
                Some(LoopSourceBindings::Generic(bindings)) => {
                    for offset in 0..bindings.len {
                        loop_owned_slots.insert((block, Reg(bindings.start.index() + offset)));
                    }
                }
                None => {}
            }
            for value in &loop_plan.header_values {
                loop_owned_slots.insert((block, value.reg));
            }
        }
    }
    let mut defs_by_slot = BTreeMap::<CapturedSlotKey, Vec<(usize, BlockRef)>>::new();
    for def in &dataflow.defs {
        let instr_index = def.instr.index();
        defs_by_slot
            .entry(CapturedSlotKey::new(
                def.reg.index(),
                epochs.epoch_at(def.reg, def.instr),
            ))
            .or_default()
            .push((instr_index, cfg.instr_to_block[instr_index]));
    }
    let mut reachability = BTreeMap::new();
    let mut cyclic_blocks = BTreeMap::new();
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
            );
            let entry_local_safe = epochs.spans_entry(reg);
            let key =
                CapturedSlotKey::new(reg.index(), epochs.epoch_at(reg, InstrRef(start_instr)));
            let child_writes = child_mutable_upvalues
                .get(closure.proto.index())
                .and_then(|mutable| mutable.get(capture_index))
                .copied()
                .unwrap_or(false);
            let parent_writes_after_capture = parent_writes_after_capture_same_epoch(
                cfg,
                instr_index,
                key,
                &defs_by_slot,
                &mut reachability,
                &mut cyclic_blocks,
            );
            let requires_local =
                child_writes || has_no_reaching_value || parent_writes_after_capture;
            entry_safe_by_key
                .entry(key)
                .and_modify(|safe| *safe &= entry_local_safe)
                .or_insert(entry_local_safe);
            if requires_local
                && entry_local_safe
                && block_has_real_cycle(
                    cfg,
                    cfg.instr_to_block[instr_index],
                    &mut reachability,
                    &mut cyclic_blocks,
                )
            {
                entry_decl_keys.insert(key);
            }
            if requires_local
                && let Some(region) = captured_slot_declaration_region(
                    dataflow,
                    structure.plan(),
                    InstrRef(instr_index),
                    reg,
                )
                && !conflicting_region_decl_keys.contains(&key)
            {
                match region_decl_keys.get(&key).copied() {
                    None => {
                        region_decl_keys.insert(key, region);
                    }
                    Some(existing) if existing == region => {}
                    Some(_) => {
                        region_decl_keys.remove(&key);
                        conflicting_region_decl_keys.insert(key);
                    }
                }
            }
            captured_uses.push(CapturedSlotUse {
                instr_index,
                reg,
                key,
                start_instr,
                requires_local,
                entry_local_safe,
            });
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

fn parent_writes_after_capture_same_epoch(
    cfg: &Cfg,
    capture_instr: usize,
    key: CapturedSlotKey,
    defs_by_slot: &BTreeMap<CapturedSlotKey, Vec<(usize, BlockRef)>>,
    reachability: &mut BTreeMap<(BlockRef, BlockRef), bool>,
    cyclic_blocks: &mut BTreeMap<BlockRef, bool>,
) -> bool {
    let capture_block = cfg.instr_to_block[capture_instr];
    if !cfg.reachable_blocks.contains(&capture_block) {
        return false;
    }

    defs_by_slot.get(&key).is_some_and(|defs| {
        defs.iter().any(|&(def_instr, def_block)| {
            if !cfg.reachable_blocks.contains(&def_block) {
                return false;
            }
            if def_block != capture_block {
                return cached_can_reach(cfg, capture_block, def_block, reachability);
            }
            def_instr > capture_instr
                || (def_instr < capture_instr
                    && block_has_real_cycle(cfg, capture_block, reachability, cyclic_blocks))
        })
    })
}

fn block_has_real_cycle(
    cfg: &Cfg,
    block: BlockRef,
    reachability: &mut BTreeMap<(BlockRef, BlockRef), bool>,
    cyclic_blocks: &mut BTreeMap<BlockRef, bool>,
) -> bool {
    if let Some(cyclic) = cyclic_blocks.get(&block) {
        return *cyclic;
    }
    let cyclic = cfg.succs[block.index()].iter().any(|edge_ref| {
        let succ = cfg.edges[edge_ref.index()].to;
        succ == block || cached_can_reach(cfg, succ, block, reachability)
    });
    cyclic_blocks.insert(block, cyclic);
    cyclic
}

fn cached_can_reach(
    cfg: &Cfg,
    from: BlockRef,
    to: BlockRef,
    reachability: &mut BTreeMap<(BlockRef, BlockRef), bool>,
) -> bool {
    *reachability
        .entry((from, to))
        .or_insert_with(|| cfg.can_reach(from, to))
}

fn captured_slot_start_instr(
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    capture_instr: InstrRef,
    reg: Reg,
    has_no_reaching_value: bool,
) -> usize {
    if has_no_reaching_value {
        return capture_instr.index();
    }

    let mut earliest = None;
    let mut pending = vec![dataflow.use_value(capture_instr, reg)];
    let mut seen_phis = vec![false; plan.phis().len()];
    while let Some(value) = pending.pop() {
        match value {
            SsaValue::Entry(_) => {}
            SsaValue::Def(def) => {
                let instr = dataflow.def_instr(def).index();
                earliest = Some(earliest.map_or(instr, |current: usize| current.min(instr)));
            }
            SsaValue::Phi(phi_id) => {
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
