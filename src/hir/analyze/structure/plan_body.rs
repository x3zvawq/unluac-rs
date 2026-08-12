//! 这个文件直接消费 Structure 最终 region/edge plan。
//!
//! 这里不按 header 搜候选、不做试降回滚，也不把 emitted 集合作为结构决策依据。
//! region、edge 与 value identity 已在 Structure 冻结；本模块只执行计划并校验引用一致性。

use std::collections::BTreeMap;

use crate::hir::HirLowerError;
use crate::hir::common::{
    HirBlock, HirExpr, HirGenericFor, HirLValue, HirLabel, HirLabelId, HirNumericFor, HirProtoRef,
    HirRepeat, HirStmt, HirWhile, TempId,
};
use crate::hir::decision::{finalize_condition_decision_expr, finalize_value_decision_expr};
use crate::structure::{
    BlockEmissionPlan, BlockRef, BlockTerminatorKind, BlockTerminatorPlan, CleanupDisposition,
    EdgeKind, EdgePlan, EdgeRef, EdgeTransfer, LabelPlacement, LoopConditionProtocol,
    LoopIterationDisposition, LoopRepeatForm, LoopRepeatProtocol, LoopValuePhase, LoopValueSource,
    LoopVmProtocol, PhiId, PhiIncomingDisposition, PlanRequirement, RegionId, RegionPlan, SsaValue,
    UnstructuredLayoutItem,
};
use crate::transformer::{InstrRef, LowInstr, Reg};

use super::super::exprs::{expr_for_reg_use, lower_branch_cond};
use super::super::helpers::{assign_stmt, branch_stmt, goto_block};
use super::super::instrs::{local_decl_stmts, lower_regular_instr, lower_terminal_instr};
use super::super::lower::ProtoLowering;
use super::super::short_circuit::{build_condition_decision_expr, build_value_decision_expr};
use super::generic_for::lower_generic_for_iterator;

/// 从最终 region arena 构造 HIR body。
pub(super) fn build_planned_body(
    proto: HirProtoRef,
    lowering: &ProtoLowering<'_>,
) -> Result<HirBlock, HirLowerError> {
    let mut lowerer = PlanBodyLowerer::new(proto, lowering)?;
    let body = lowerer.lower_plan_node(lowering.structure.plan().root())?;
    #[cfg(debug_assertions)]
    if lowerer.emitted_label_count != lowering.structure.plan().labels().len() {
        return Err(HirLowerError::InvalidPlanRegion {
            proto: proto.index(),
            region: lowering.structure.plan().root().index(),
            detail: "final plan contains a label outside the emitted region tree",
        });
    }
    Ok(body)
}

struct PlanBodyLowerer<'a, 'b> {
    proto: HirProtoRef,
    lowering: &'b ProtoLowering<'a>,
    index: PlanLoweringIndex,
    #[cfg(debug_assertions)]
    emitted_labels: Vec<bool>,
    #[cfg(debug_assertions)]
    emitted_label_count: usize,
    #[cfg(debug_assertions)]
    emitted_blocks: Vec<bool>,
    #[cfg(debug_assertions)]
    emitted_synthetic_inputs: Vec<bool>,
    condition_block_seen_at: Vec<usize>,
    condition_epoch: usize,
}

struct PlanLoweringIndex {
    plain_block_count: Vec<Option<usize>>,
    single_plain_block: Vec<Option<BlockRef>>,
    region_inputs: Vec<Vec<(PhiId, SsaValue)>>,
    unresolved_requirement: Vec<Option<(BlockRef, Reg)>>,
    normal_tail_guard_by_edge: Vec<Option<(RegionId, TempId)>>,
    consumed_loop_copy_targets: Vec<Vec<PhiId>>,
    repeat_staged_result_by_phi: Vec<Option<(RegionId, TempId)>>,
    canonical_move_source: Vec<Option<SsaValue>>,
    absorbed_region_result_moves: Vec<bool>,
}

struct PlannedLoopCondition {
    prefix: Vec<HirStmt>,
    cond: HirExpr,
}

#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
enum CopyBinding {
    Temp(TempId),
    Local(crate::hir::common::LocalId),
}

fn copy_target_binding(target: &HirLValue) -> Option<CopyBinding> {
    match target {
        HirLValue::Temp(temp) => Some(CopyBinding::Temp(*temp)),
        HirLValue::Local(local) => Some(CopyBinding::Local(*local)),
        _ => None,
    }
}

fn copy_value_binding(value: &HirExpr) -> Option<CopyBinding> {
    match value {
        HirExpr::TempRef(temp) => Some(CopyBinding::Temp(*temp)),
        HirExpr::LocalRef(local) => Some(CopyBinding::Local(*local)),
        _ => None,
    }
}

fn copy_assignment_stmt(targets: Vec<HirLValue>, values: Vec<HirExpr>) -> Option<HirStmt> {
    if targets.len() != values.len() {
        return Some(assign_stmt(targets, values));
    }
    let mut target_counts = BTreeMap::<CopyBinding, usize>::new();
    for binding in targets.iter().filter_map(copy_target_binding) {
        *target_counts.entry(binding).or_default() += 1;
    }
    let mut retained_targets = Vec::with_capacity(targets.len());
    let mut retained_values = Vec::with_capacity(values.len());
    for (target, value) in targets.into_iter().zip(values) {
        let binding = copy_target_binding(&target);
        let is_unique_self_copy = binding == copy_value_binding(&value)
            && binding.is_some_and(|binding| target_counts.get(&binding) == Some(&1));
        if !is_unique_self_copy {
            retained_targets.push(target);
            retained_values.push(value);
        }
    }
    (!retained_targets.is_empty()).then(|| assign_stmt(retained_targets, retained_values))
}

struct PlannedForRegions {
    preheader: Option<RegionId>,
    control: RegionId,
    normal_tail: Option<(HirBlock, TempId)>,
}

struct PlannedLoopParts {
    preheader: Option<RegionId>,
    control: RegionId,
    body: HirBlock,
    normal_tail_region: Option<RegionId>,
    normal_tail_body: Option<HirBlock>,
}

#[derive(Clone, Copy)]
struct PlannedLoopIdentity {
    header: BlockRef,
    source_bindings: Option<crate::structure::LoopSourceBindings>,
    preheader_body: Option<EdgeRef>,
    preheader_exit: Option<EdgeRef>,
    has_normal_tail: bool,
}

enum LowerTask {
    Region(RegionId),
    Block {
        owner: RegionId,
        block: BlockRef,
    },
    FinishSequence {
        region: RegionId,
        outer_prefix: Vec<HirStmt>,
        prefix: Vec<HirStmt>,
        result_start: usize,
        child_count: usize,
        single_pass: bool,
    },
    FinishBranch {
        region: RegionId,
        prefix: Vec<HirStmt>,
        plan: crate::structure::BranchPlanId,
        condition: RegionId,
        has_else: bool,
        result_start: usize,
    },
    FinishLoop {
        region: RegionId,
        prefix: Vec<HirStmt>,
        plan: crate::structure::LoopPlanId,
        preheader: Option<RegionId>,
        control: RegionId,
        normal_tail: Option<RegionId>,
        result_start: usize,
    },
    FinishUnstructured {
        region: RegionId,
        outer_prefix: Vec<HirStmt>,
        prefix: Vec<HirStmt>,
        result_start: usize,
        item_count: usize,
        single_pass: bool,
    },
}

impl PlanLoweringIndex {
    fn build(proto: HirProtoRef, lowering: &ProtoLowering<'_>) -> Result<Self, HirLowerError> {
        let plan = lowering.structure.plan();
        let root = plan.root();
        let region_count = plan.regions().len();
        let invalid = |region: RegionId, detail: &'static str| HirLowerError::InvalidPlanRegion {
            proto: proto.index(),
            region: region.index(),
            detail,
        };
        if root.index() >= region_count {
            return Err(HirLowerError::MissingPlanRegion {
                proto: proto.index(),
                region: root.index(),
            });
        }

        let mut plain_block_count = vec![None; region_count];
        let mut single_plain_block = vec![None; region_count];
        for region in plan.region_postorder().iter().copied() {
            let node = plan
                .region(region)
                .ok_or(HirLowerError::MissingPlanRegion {
                    proto: proto.index(),
                    region: region.index(),
                })?;
            match node {
                RegionPlan::Block { block, .. } => {
                    plain_block_count[region.index()] = Some(1);
                    single_plain_block[region.index()] = Some(*block);
                }
                RegionPlan::Sequence {
                    children: sequence, ..
                } => {
                    let mut total = Some(0_usize);
                    for child in sequence {
                        total = match (
                            total,
                            plain_block_count.get(child.index()).copied().flatten(),
                        ) {
                            (Some(total), Some(child_count)) => total.checked_add(child_count),
                            _ => None,
                        };
                    }
                    plain_block_count[region.index()] = total;
                    if let [child] = sequence.as_slice() {
                        single_plain_block[region.index()] =
                            single_plain_block.get(child.index()).copied().flatten();
                    }
                }
                RegionPlan::Branch { .. }
                | RegionPlan::ValueDecision { .. }
                | RegionPlan::Loop { .. }
                | RegionPlan::Unstructured { .. } => {}
            }
        }

        let phi_count = plan.phis().len();
        if lowering.bindings.fixed_temps.len() < lowering.dataflow.defs.len()
            || lowering.bindings.phi_temps.len() < phi_count
        {
            return Err(invalid(
                root,
                "HIR temp bindings do not cover the final SSA arenas",
            ));
        }
        for uses in &lowering.dataflow.use_values {
            for value in uses.fixed.values() {
                let bound = match value {
                    SsaValue::Entry(_) => true,
                    SsaValue::Def(def) => def.index() < lowering.bindings.fixed_temps.len(),
                    SsaValue::Phi(phi) => phi.index() < lowering.bindings.phi_temps.len(),
                };
                if !bound {
                    return Err(invalid(
                        root,
                        "instruction use references an unbound SSA value",
                    ));
                }
            }
        }
        let mut repeat_staged_result_by_phi = vec![None; phi_count];
        for (loop_id, payload) in plan.loops() {
            let Some(LoopVmProtocol::Repeat(protocol)) = payload.protocol.as_ref() else {
                continue;
            };
            let region = plan
                .loop_region(loop_id)
                .ok_or_else(|| invalid(root, "repeat staged result has no loop region"))?;
            let temps = lowering
                .bindings
                .repeat_staged_temps
                .get(loop_id.index())
                .ok_or_else(|| invalid(region, "repeat staged-result bindings are missing"))?;
            if temps.len() != protocol.value_plan.staged_results.len() {
                return Err(invalid(
                    region,
                    "repeat staged-result bindings contradict the protocol",
                ));
            }
            for (result, temp) in protocol.value_plan.staged_results.iter().zip(temps) {
                let slot = repeat_staged_result_by_phi
                    .get_mut(result.target.index())
                    .ok_or_else(|| invalid(region, "repeat staged result targets a missing phi"))?;
                if slot.replace((region, *temp)).is_some() {
                    return Err(invalid(
                        region,
                        "one final phi is staged by multiple repeat loops",
                    ));
                }
            }
        }
        let mut region_inputs = vec![Vec::new(); region_count];
        let mut input_seen_at = vec![usize::MAX; region_count];
        for phi_plan in plan.phis() {
            if phi_plan.phi.index() >= phi_count {
                return Err(invalid(root, "final phi arena is not densely indexed"));
            }
            for incoming in &phi_plan.incomings {
                let PhiIncomingDisposition::RegionInput(region) = incoming.disposition else {
                    continue;
                };
                if incoming.edge.is_some() {
                    continue;
                }
                let Some(seen_at) = input_seen_at.get_mut(region.index()) else {
                    return Err(invalid(
                        region,
                        "region input owner is outside the dense arena",
                    ));
                };
                if *seen_at == phi_plan.phi.index() {
                    return Err(invalid(
                        region,
                        "region input has multiple synthetic values",
                    ));
                }
                *seen_at = phi_plan.phi.index();
                region_inputs[region.index()].push((phi_plan.phi, incoming.value));
            }
        }

        let mut unresolved_requirement = vec![None; phi_count];
        for (_, requirement) in plan.requirements().iter() {
            let PlanRequirement::UnresolvedValue { phi_id, block, reg } = requirement else {
                continue;
            };
            let Some(slot) = unresolved_requirement.get_mut(phi_id.index()) else {
                return Err(invalid(
                    root,
                    "unresolved requirement references a missing phi",
                ));
            };
            let identity = (*block, *reg);
            if slot.is_some_and(|current| current != identity) {
                return Err(invalid(
                    root,
                    "one phi has conflicting unresolved requirements",
                ));
            }
            *slot = Some(identity);
        }

        let mut normal_tail_guard_by_edge = vec![None; lowering.cfg.edges.len()];
        for (loop_id, payload) in plan.loops() {
            let Some(tail) = &payload.normal_tail else {
                continue;
            };
            let region = plan
                .loop_region(loop_id)
                .ok_or(HirLowerError::MissingPlanPayload {
                    proto: proto.index(),
                    kind: "loop-region",
                    id: loop_id.index(),
                })?;
            let guard = lowering
                .bindings
                .loop_guard_temps
                .get(loop_id.index())
                .copied()
                .flatten()
                .ok_or(HirLowerError::InvalidPlanRegion {
                    proto: proto.index(),
                    region: region.index(),
                    detail: "normal-tail loop has no guard binding",
                })?;
            for edge in &tail.early_exits {
                let Some(slot) = normal_tail_guard_by_edge.get_mut(edge.index()) else {
                    return Err(invalid(
                        region,
                        "normal-tail exit is outside the edge arena",
                    ));
                };
                let identity = (region, guard);
                if slot.is_some_and(|current| current != identity) {
                    return Err(invalid(
                        region,
                        "normal-tail exit has conflicting loop owners",
                    ));
                }
                *slot = Some(identity);
            }
        }
        let mut consumed_loop_copy_targets = vec![Vec::new(); lowering.cfg.edges.len()];
        for (loop_id, _) in plan.loops() {
            let region = plan
                .loop_region(loop_id)
                .ok_or_else(|| invalid(root, "loop value actions have no owning region"))?;
            let actions = plan
                .loop_value_actions(loop_id)
                .ok_or_else(|| invalid(region, "loop value actions are missing"))?;
            let completion_exits = plan
                .loop_(loop_id)
                .and_then(|payload| payload.normal_tail.as_ref())
                .map(|tail| tail.completion_exits.as_slice())
                .unwrap_or_default();
            let completion_origins = actions
                .batches
                .iter()
                .flat_map(|batch| &batch.writes)
                .flat_map(|write| &write.origins)
                .filter(|origin| completion_exits.binary_search(&origin.edge).is_ok());
            for origin in completion_origins.chain(&actions.elided) {
                let Some(targets) = consumed_loop_copy_targets.get_mut(origin.edge.index()) else {
                    return Err(invalid(
                        region,
                        "consumed loop copy is outside the edge arena",
                    ));
                };
                targets.push(origin.target);
            }
        }
        for targets in &mut consumed_loop_copy_targets {
            targets.sort_unstable();
            if targets.windows(2).any(|pair| pair[0] == pair[1]) {
                return Err(invalid(
                    root,
                    "one edge copy is consumed by multiple loop actions",
                ));
            }
        }
        let mut canonical_move_source = vec![None; lowering.dataflow.defs.len()];
        let mut edge_action_use_count = vec![0_usize; lowering.dataflow.defs.len()];
        let mut canonical_moves =
            crate::structure::CanonicalMoveIndex::new(lowering.proto, lowering.dataflow);
        for edge_index in 0..lowering.cfg.edges.len() {
            let edge = plan
                .edge_plan(EdgeRef(edge_index))
                .ok_or_else(|| invalid(root, "final plan has no action entry for one CFG edge"))?;
            for copy in &edge.phi_copies {
                cache_canonical_move_source(
                    &mut canonical_moves,
                    &mut canonical_move_source,
                    &mut edge_action_use_count,
                    copy.value,
                    root,
                    invalid,
                )?;
            }
            for disposition in &edge.iteration {
                cache_canonical_move_source(
                    &mut canonical_moves,
                    &mut canonical_move_source,
                    &mut edge_action_use_count,
                    disposition.incoming,
                    root,
                    invalid,
                )?;
                if let LoopValueSource::Ssa(value) = disposition.source {
                    cache_canonical_move_source(
                        &mut canonical_moves,
                        &mut canonical_move_source,
                        &mut edge_action_use_count,
                        value,
                        root,
                        invalid,
                    )?;
                }
            }
        }
        let absorbed_region_result_moves = build_absorbed_region_result_moves(
            proto,
            lowering,
            &canonical_move_source,
            &edge_action_use_count,
        )?;

        Ok(Self {
            plain_block_count,
            single_plain_block,
            region_inputs,
            unresolved_requirement,
            normal_tail_guard_by_edge,
            consumed_loop_copy_targets,
            repeat_staged_result_by_phi,
            canonical_move_source,
            absorbed_region_result_moves,
        })
    }
}

fn cache_canonical_move_source(
    canonical_moves: &mut crate::structure::CanonicalMoveIndex<'_>,
    cache: &mut [Option<SsaValue>],
    action_use_count: &mut [usize],
    value: SsaValue,
    owner: RegionId,
    invalid: impl Fn(RegionId, &'static str) -> HirLowerError,
) -> Result<(), HirLowerError> {
    let SsaValue::Def(def) = value else {
        return Ok(());
    };
    let slot = cache
        .get_mut(def.index())
        .ok_or_else(|| invalid(owner, "edge action references a missing SSA def"))?;
    let uses = action_use_count
        .get_mut(def.index())
        .ok_or_else(|| invalid(owner, "edge action use index misses one SSA def"))?;
    *uses = uses
        .checked_add(1)
        .ok_or_else(|| invalid(owner, "edge action use count overflowed"))?;
    let canonical = canonical_moves
        .resolve(value)
        .map_err(|_| invalid(owner, "edge action Move chain has no canonical SSA source"))?;
    *slot = Some(canonical);
    Ok(())
}

fn build_absorbed_region_result_moves(
    proto: HirProtoRef,
    lowering: &ProtoLowering<'_>,
    canonical_move_source: &[Option<SsaValue>],
    edge_action_use_count: &[usize],
) -> Result<Vec<bool>, HirLowerError> {
    // 只有 final plan 已把末尾 Move 的唯一结果写入冻结为同边 copy 时，物理 temp 才是
    // 纯机械中转；任何普通 use、第二 owner 或词法 binding 都必须保留原指令。
    let plan = lowering.structure.plan();
    let root = plan.root();
    let invalid = |region: RegionId, detail: &'static str| HirLowerError::InvalidPlanRegion {
        proto: proto.index(),
        region: region.index(),
        detail,
    };
    let mut absorbed = vec![false; lowering.proto.instrs.len()];

    for (def_index, definition) in lowering.dataflow.defs.iter().enumerate() {
        if definition.id.index() != def_index {
            return Err(invalid(root, "SSA definition arena is not densely indexed"));
        }
        let Some(LowInstr::Move(move_)) = lowering.proto.instrs.get(definition.instr.index())
        else {
            continue;
        };
        if move_.dst != definition.reg {
            return Err(invalid(
                root,
                "Move definition register contradicts its SSA metadata",
            ));
        }
        let instr_defs = lowering
            .dataflow
            .instr_defs
            .get(definition.instr.index())
            .ok_or_else(|| invalid(root, "Move has no SSA instruction definition entry"))?;
        if instr_defs.as_slice() != [definition.id] {
            return Err(invalid(
                root,
                "Move does not have one canonical SSA definition",
            ));
        }
        if lowering
            .cfg
            .instr_to_block
            .get(definition.instr.index())
            .copied()
            != Some(definition.block)
        {
            return Err(invalid(root, "Move definition block contradicts the CFG"));
        }

        let Some(canonical) = canonical_move_source.get(def_index).copied().flatten() else {
            continue;
        };
        if canonical == SsaValue::Def(definition.id) {
            continue;
        }
        let immediate_source = lowering
            .dataflow
            .use_values
            .get(definition.instr.index())
            .and_then(|uses| uses.fixed.get(move_.src))
            .ok_or_else(|| invalid(root, "Move has no immediate SSA source"))?;
        if canonical != immediate_source {
            // 多跳链的 immediate source 可能是为并行赋值保存的旧值；把 edge read
            // 穿透到 mutable canonical home 会越过中间覆写。单跳才可无条件延后读取。
            continue;
        }
        let action_uses = edge_action_use_count
            .get(def_index)
            .copied()
            .ok_or_else(|| invalid(root, "edge action use index misses one Move definition"))?;
        if action_uses != 1 {
            continue;
        }
        let ordinary_uses = lowering
            .dataflow
            .def_uses
            .get(def_index)
            .ok_or_else(|| invalid(root, "Move definition has no ordinary-use index"))?;
        if !ordinary_uses.is_empty() {
            continue;
        }
        let phi_uses = lowering
            .dataflow
            .def_phi_uses
            .get(def_index)
            .ok_or_else(|| invalid(root, "Move definition has no phi-use index"))?;
        let [phi_id] = phi_uses.as_slice() else {
            continue;
        };
        let phi_id = *phi_id;
        let phi = plan
            .phi_plan(phi_id)
            .filter(|phi| phi.phi == phi_id)
            .ok_or_else(|| invalid(root, "Move phi consumer has no dense final plan"))?;
        let mut matching_incomings = phi
            .incomings
            .iter()
            .filter(|incoming| incoming.value == SsaValue::Def(definition.id));
        let incoming = matching_incomings
            .next()
            .ok_or_else(|| invalid(root, "Move phi-use index contradicts the final phi plan"))?;
        if matching_incomings.next().is_some() {
            return Err(invalid(
                root,
                "Move phi consumer has multiple matching final incomings",
            ));
        }
        let PhiIncomingDisposition::RegionResult(owner) = incoming.disposition else {
            continue;
        };
        let Some(RegionPlan::Branch {
            plan: branch_id, ..
        }) = plan.region(owner)
        else {
            continue;
        };
        let branch = plan.branch(*branch_id).ok_or_else(|| {
            invalid(
                owner,
                "RegionResult Move owner references a missing branch plan",
            )
        })?;
        let Some(value_plan) = branch.value_plan.as_ref() else {
            continue;
        };
        let mut matching_values = value_plan
            .values
            .iter()
            .filter(|value| value.phi_id == phi_id);
        if matching_values.next().is_none() {
            continue;
        }
        if matching_values.next().is_some() {
            return Err(invalid(
                owner,
                "branch value plan contains one result phi more than once",
            ));
        }

        let Some(edge) = incoming.edge else {
            continue;
        };
        let edge_plan = plan
            .edge_plan(edge)
            .filter(|edge_plan| edge_plan.edge == edge)
            .ok_or_else(|| invalid(owner, "RegionResult Move references a missing edge plan"))?;
        if edge_plan.forward_route.is_some()
            || plan.edge_action_is_forwarded_only(edge)
            || edge_plan.actions_before_trailing_cleanup().is_some()
        {
            continue;
        }
        let cfg_edge = lowering
            .cfg
            .edges
            .get(edge.index())
            .ok_or_else(|| invalid(owner, "RegionResult Move references a missing CFG edge"))?;
        if cfg_edge.from != definition.block {
            continue;
        }
        let matching_copy_count = edge_plan
            .phi_copies
            .iter()
            .filter(|copy| copy.phi_id == phi_id && copy.value == SsaValue::Def(definition.id))
            .count();
        if matching_copy_count != 1 {
            continue;
        }
        let terminator = plan
            .block_terminator(definition.block)
            .filter(|terminator| terminator.block == definition.block)
            .ok_or_else(|| invalid(owner, "RegionResult Move block has no terminator plan"))?;
        let terminal_move = match terminator.kind {
            BlockTerminatorKind::Jump {
                instr: jump,
                edge: jump_edge,
            } => {
                jump_edge == edge
                    && terminator.instrs.last() == Some(jump)
                    && definition
                        .instr
                        .index()
                        .checked_add(1)
                        .is_some_and(|next| next == jump.index())
            }
            BlockTerminatorKind::Linear {
                edge: Some(linear_edge),
            } => linear_edge == edge && terminator.instrs.last() == Some(definition.instr),
            _ => false,
        };
        if !terminal_move {
            continue;
        }

        let fixed_temp = lowering
            .bindings
            .fixed_temps
            .get(def_index)
            .copied()
            .ok_or_else(|| invalid(owner, "RegionResult Move has no fixed-temp binding"))?;
        let instr_temps = lowering
            .bindings
            .instr_fixed_defs
            .get(definition.instr.index())
            .ok_or_else(|| invalid(owner, "RegionResult Move has no instruction-temp binding"))?;
        if instr_temps.as_slice() != [fixed_temp] {
            return Err(invalid(
                owner,
                "RegionResult Move instruction binding contradicts its fixed temp",
            ));
        }
        let debug_owner = lowering
            .bindings
            .temp_debug_locals
            .get(fixed_temp.index())
            .ok_or_else(|| invalid(owner, "RegionResult Move temp is outside the debug arena"))?;
        if debug_owner.is_some()
            || lowering
                .bindings
                .captured_temp_targets
                .contains_key(&fixed_temp)
            || lowering
                .bindings
                .captured_temp_decl_locals
                .contains_key(&fixed_temp)
            || lowering.bindings.reg_is_reference_captured(move_.dst)
            || lowering.bindings.reg_is_reference_captured(move_.src)
            || lowering
                .bindings
                .local_for_reg_in_block(definition.block, move_.dst)
                .is_some()
        {
            continue;
        }

        let slot = absorbed
            .get_mut(definition.instr.index())
            .ok_or_else(|| invalid(owner, "RegionResult Move is outside the instruction arena"))?;
        if std::mem::replace(slot, true) {
            return Err(invalid(
                owner,
                "one instruction owns multiple absorbed RegionResult Moves",
            ));
        }
    }

    Ok(absorbed)
}

impl<'a, 'b> PlanBodyLowerer<'a, 'b> {
    fn new(proto: HirProtoRef, lowering: &'b ProtoLowering<'a>) -> Result<Self, HirLowerError> {
        let index = PlanLoweringIndex::build(proto, lowering)?;
        Ok(Self {
            proto,
            lowering,
            index,
            #[cfg(debug_assertions)]
            emitted_labels: vec![false; lowering.structure.plan().labels().len()],
            #[cfg(debug_assertions)]
            emitted_label_count: 0,
            #[cfg(debug_assertions)]
            emitted_blocks: vec![false; lowering.cfg.blocks.len()],
            #[cfg(debug_assertions)]
            emitted_synthetic_inputs: vec![false; lowering.structure.plan().phis().len()],
            condition_block_seen_at: vec![0; lowering.cfg.blocks.len()],
            condition_epoch: 0,
        })
    }

    fn lower_plan_node(&mut self, id: RegionId) -> Result<HirBlock, HirLowerError> {
        let mut tasks = vec![LowerTask::Region(id)];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                LowerTask::Region(region) => {
                    let node = self
                        .lowering
                        .structure
                        .plan()
                        .region(region)
                        .cloned()
                        .ok_or(HirLowerError::MissingPlanRegion {
                            proto: self.proto.index(),
                            region: region.index(),
                        })?;
                    let mut prefix = Vec::new();
                    self.emit_region_label(region, &mut prefix)?;
                    let mut region_local_decls = local_decl_stmts(
                        self.lowering
                            .bindings
                            .capture_region_local_decls
                            .get(&region)
                            .cloned()
                            .unwrap_or_default(),
                    );
                    let single_pass = self
                        .lowering
                        .structure
                        .plan()
                        .single_pass_for_region(region)
                        .is_some();
                    let outer_prefix = if single_pass {
                        std::mem::take(&mut region_local_decls)
                    } else {
                        Vec::new()
                    };
                    prefix.append(&mut region_local_decls);
                    prefix.extend(self.lower_region_inputs(region)?);
                    match node {
                        RegionPlan::Block { block, .. } => {
                            prefix.extend(self.lower_block(region, block)?.stmts);
                            results.push(HirBlock { stmts: prefix });
                        }
                        RegionPlan::Sequence { children, .. } => {
                            let result_start = results.len();
                            tasks.push(LowerTask::FinishSequence {
                                region,
                                outer_prefix,
                                prefix,
                                result_start,
                                child_count: children.len(),
                                single_pass,
                            });
                            tasks.extend(children.into_iter().rev().map(LowerTask::Region));
                        }
                        RegionPlan::Branch {
                            plan,
                            condition,
                            then_arm,
                            else_arm,
                            ..
                        } => {
                            let result_start = results.len();
                            tasks.push(LowerTask::FinishBranch {
                                region,
                                prefix,
                                plan,
                                condition,
                                has_else: else_arm.is_some(),
                                result_start,
                            });
                            if let Some(else_arm) = else_arm {
                                tasks.push(LowerTask::Region(else_arm));
                            }
                            tasks.push(LowerTask::Region(then_arm));
                        }
                        RegionPlan::ValueDecision { plan, .. } => {
                            prefix.extend(self.lower_value_decision(region, plan)?.stmts);
                            results.push(HirBlock { stmts: prefix });
                        }
                        RegionPlan::Loop {
                            plan,
                            preheader,
                            control,
                            body,
                            normal_tail,
                            ..
                        } => {
                            let result_start = results.len();
                            tasks.push(LowerTask::FinishLoop {
                                region,
                                prefix,
                                plan,
                                preheader,
                                control,
                                normal_tail,
                                result_start,
                            });
                            if let Some(normal_tail) = normal_tail {
                                tasks.push(LowerTask::Region(normal_tail));
                            }
                            tasks.push(LowerTask::Region(body));
                        }
                        RegionPlan::Unstructured { layout, .. } => {
                            let result_start = results.len();
                            tasks.push(LowerTask::FinishUnstructured {
                                region,
                                outer_prefix,
                                prefix,
                                result_start,
                                item_count: layout.len(),
                                single_pass: false,
                            });
                            tasks.extend(layout.into_iter().rev().map(|item| match item {
                                UnstructuredLayoutItem::Block(block) => LowerTask::Block {
                                    owner: region,
                                    block,
                                },
                                UnstructuredLayoutItem::Region(child) => LowerTask::Region(child),
                            }));
                        }
                    }
                }
                LowerTask::Block { owner, block } => {
                    results.push(self.lower_block(owner, block)?);
                }
                LowerTask::FinishSequence {
                    region,
                    mut outer_prefix,
                    mut prefix,
                    result_start,
                    child_count,
                    single_pass,
                }
                | LowerTask::FinishUnstructured {
                    region,
                    mut outer_prefix,
                    mut prefix,
                    result_start,
                    item_count: child_count,
                    single_pass,
                } => {
                    for child in
                        self.take_lowered_children(region, &mut results, result_start, child_count)?
                    {
                        prefix.extend(child.stmts);
                    }
                    if single_pass {
                        let Some((_, fence)) = self
                            .lowering
                            .structure
                            .plan()
                            .single_pass_for_region(region)
                        else {
                            return self.invalid_region(
                                region,
                                "single-pass sequence has no frozen fence payload",
                            );
                        };
                        if fence.region != region {
                            return self.invalid_region(
                                region,
                                "single-pass payload is bound to another region",
                            );
                        }
                        let mut outer = Vec::new();
                        self.emit_label(
                            fence.entry,
                            LabelPlacement::BeforeRegion(region),
                            &mut outer,
                        )?;
                        outer.append(&mut outer_prefix);
                        outer.push(HirStmt::Repeat(Box::new(HirRepeat {
                            body: HirBlock { stmts: prefix },
                            cond: HirExpr::Boolean(true),
                        })));
                        prefix = outer;
                    } else {
                        outer_prefix.append(&mut prefix);
                        prefix = outer_prefix;
                    }
                    results.push(HirBlock { stmts: prefix });
                }
                LowerTask::FinishBranch {
                    region,
                    mut prefix,
                    plan,
                    condition,
                    has_else,
                    result_start,
                } => {
                    let mut children = self.take_lowered_children(
                        region,
                        &mut results,
                        result_start,
                        usize::from(has_else) + 1,
                    )?;
                    let then_arm = children.remove(0);
                    let else_arm = has_else.then(|| children.remove(0));
                    prefix.extend(
                        self.lower_branch(region, plan, condition, then_arm, else_arm)?
                            .stmts,
                    );
                    results.push(HirBlock { stmts: prefix });
                }
                LowerTask::FinishLoop {
                    region,
                    mut prefix,
                    plan,
                    preheader,
                    control,
                    normal_tail,
                    result_start,
                } => {
                    let mut children = self.take_lowered_children(
                        region,
                        &mut results,
                        result_start,
                        usize::from(normal_tail.is_some()) + 1,
                    )?;
                    let body = children.remove(0);
                    let tail = normal_tail.map(|_| children.remove(0));
                    prefix.extend(
                        self.lower_loop(
                            region,
                            plan,
                            PlannedLoopParts {
                                preheader,
                                control,
                                body,
                                normal_tail_region: normal_tail,
                                normal_tail_body: tail,
                            },
                        )?
                        .stmts,
                    );
                    results.push(HirBlock { stmts: prefix });
                }
            }
        }
        if results.len() != 1 {
            return self.invalid_region(id, "iterative region lowering left orphaned results");
        }
        results.pop().ok_or(HirLowerError::MissingPlanRegion {
            proto: self.proto.index(),
            region: id.index(),
        })
    }

    fn take_lowered_children(
        &self,
        region: RegionId,
        results: &mut Vec<HirBlock>,
        start: usize,
        expected: usize,
    ) -> Result<Vec<HirBlock>, HirLowerError> {
        if results.len() != start.saturating_add(expected) {
            return self.invalid_region(region, "region child results contradict containment");
        }
        Ok(results.split_off(start))
    }

    fn lower_region_inputs(&mut self, region: RegionId) -> Result<Vec<HirStmt>, HirLowerError> {
        let inputs = self.index.region_inputs.get(region.index()).ok_or(
            HirLowerError::MissingPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
            },
        )?;
        let mut assignments = Vec::new();
        for &(phi_id, value) in inputs {
            #[cfg(debug_assertions)]
            if self
                .emitted_synthetic_inputs
                .get_mut(phi_id.index())
                .is_none_or(|emitted| std::mem::replace(emitted, true))
            {
                return self.invalid_region(region, "synthetic region input is emitted twice");
            }
            assignments.push((phi_id, self.ssa_expr(region, value)?));
        }
        self.copy_assignments(region, assignments)
    }

    fn lower_branch(
        &mut self,
        region: RegionId,
        plan: crate::structure::BranchPlanId,
        condition: RegionId,
        mut then_arm: HirBlock,
        else_arm: Option<HirBlock>,
    ) -> Result<HirBlock, HirLowerError> {
        let payload = self.lowering.structure.plan().branch(plan).cloned().ok_or(
            HirLowerError::MissingPlanPayload {
                proto: self.proto.index(),
                kind: "branch",
                id: plan.index(),
            },
        )?;
        let (mut stmts, mut cond) =
            self.lower_short_circuit_condition(region, condition, payload.condition)?;
        if payload.condition_inverted {
            cond = cond.negate();
        }

        let mut then_block = self.lower_edge(region, payload.then_edge)?;
        then_block.stmts.append(&mut then_arm.stmts);
        let mut else_block = self.lower_edge(region, payload.else_edge)?;
        if let Some(mut arm) = else_arm {
            else_block.stmts.append(&mut arm.stmts);
        }
        let else_block = (!else_block.stmts.is_empty()).then_some(else_block);
        stmts.push(branch_stmt(cond, then_block, else_block));
        Ok(HirBlock { stmts })
    }

    fn lower_short_circuit_condition(
        &mut self,
        owner: RegionId,
        condition_region: RegionId,
        condition_plan: crate::structure::ConditionPlanId,
    ) -> Result<(Vec<HirStmt>, HirExpr), HirLowerError> {
        let selected = self
            .lowering
            .structure
            .plan()
            .condition(condition_plan)
            .cloned()
            .ok_or(HirLowerError::MissingPlanPayload {
                proto: self.proto.index(),
                kind: "condition",
                id: condition_plan.index(),
            })?;
        self.verify_condition_plan(owner, &selected)?;
        let decision = build_condition_decision_expr(self.lowering, &selected).ok_or(
            HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "frozen short-circuit condition cannot be materialized",
            },
        )?;
        self.verify_condition_region(owner, condition_region, &selected.blocks)?;
        let header = selected.header().ok_or(HirLowerError::InvalidPlanRegion {
            proto: self.proto.index(),
            region: owner.index(),
            detail: "frozen condition has no entry node",
        })?;
        let stmts = self.lower_condition_prefix(owner, header)?;
        #[cfg(debug_assertions)]
        for block in selected.blocks {
            if block != header {
                self.mark_block_emitted(
                    owner,
                    block,
                    "plan emits one condition block more than once",
                )?;
            }
        }
        Ok((stmts, finalize_condition_decision_expr(decision)))
    }

    fn lower_value_decision(
        &mut self,
        region: RegionId,
        plan: crate::structure::ValueDecisionPlanId,
    ) -> Result<HirBlock, HirLowerError> {
        let selected = self
            .lowering
            .structure
            .plan()
            .value_decision(plan)
            .cloned()
            .ok_or(HirLowerError::MissingPlanPayload {
                proto: self.proto.index(),
                kind: "value-decision",
                id: plan.index(),
            })?;
        self.verify_value_decision_plan(region, &selected)?;
        if self.lowering.structure.plan().value_decision_region(plan) != Some(region) {
            return self
                .invalid_region(region, "value decision payload is bound to another region");
        }
        let header = selected.header().ok_or(HirLowerError::InvalidPlanRegion {
            proto: self.proto.index(),
            region: region.index(),
            detail: "value decision has no entry node",
        })?;
        let decision = build_value_decision_expr(self.lowering, &selected).ok_or(
            HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "frozen value decision cannot be materialized",
            },
        )?;
        let mut stmts = self.lower_condition_prefix(region, header)?;
        let target = self
            .lowering
            .bindings
            .phi_temps
            .get(selected.result_phi.index())
            .copied()
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "value decision result phi has no HIR binding",
            })?;
        stmts.push(assign_stmt(
            vec![self.lowering.bindings.lvalue_for_temp(target)],
            vec![finalize_value_decision_expr(decision)],
        ));
        stmts.extend(self.lower_edge_effects(region, selected.shared_exit_action)?);
        #[cfg(debug_assertions)]
        for block in selected.blocks().filter(|block| *block != header) {
            self.mark_block_emitted(region, block, "plan emits one value block more than once")?;
        }
        Ok(HirBlock { stmts })
    }

    fn verify_condition_region(
        &mut self,
        owner: RegionId,
        region: RegionId,
        blocks: &[BlockRef],
    ) -> Result<(), HirLowerError> {
        let Some(expected_count) = self
            .index
            .plain_block_count
            .get(region.index())
            .copied()
            .flatten()
        else {
            return self.invalid_region(
                region,
                "condition region contains a non-condition control region",
            );
        };
        if blocks.len() != expected_count {
            return self.invalid_region(
                owner,
                "condition materialization did not consume the exact planned region",
            );
        }

        self.condition_epoch = self.condition_epoch.wrapping_add(1);
        if self.condition_epoch == 0 {
            self.condition_block_seen_at.fill(0);
            self.condition_epoch = 1;
        }
        for block in blocks {
            let Some(seen_at) = self.condition_block_seen_at.get_mut(block.index()) else {
                return self.invalid_region(owner, "condition block is outside the CFG arena");
            };
            if std::mem::replace(seen_at, self.condition_epoch) == self.condition_epoch {
                return self.invalid_region(owner, "condition plan contains one block twice");
            }
            let Some(block_region) = self.lowering.structure.plan().region_for_block(*block) else {
                return self.invalid_region(owner, "condition block has no containment owner");
            };
            if !self
                .lowering
                .structure
                .plan()
                .region_contains(region, block_region)
            {
                return self.invalid_region(
                    owner,
                    "condition materialization did not consume the exact planned region",
                );
            }
        }
        Ok(())
    }

    fn lower_loop(
        &mut self,
        region: RegionId,
        plan: crate::structure::LoopPlanId,
        parts: PlannedLoopParts,
    ) -> Result<HirBlock, HirLowerError> {
        let PlannedLoopParts {
            preheader,
            control,
            body,
            normal_tail_region,
            normal_tail_body,
        } = parts;
        let payload = self.lowering.structure.plan().loop_(plan).ok_or(
            HirLowerError::MissingPlanPayload {
                proto: self.proto.index(),
                kind: "loop",
                id: plan.index(),
            },
        )?;
        let identity = PlannedLoopIdentity {
            header: payload.header,
            source_bindings: payload.source_bindings,
            preheader_body: payload.control_edges.preheader_body,
            preheader_exit: payload.control_edges.preheader_exit,
            has_normal_tail: payload.normal_tail.is_some(),
        };
        let propagated_break = payload.propagated_break;
        if self.lowering.structure.plan().loop_region(plan) != Some(region) {
            return self.invalid_region(region, "loop payload is bound to another region");
        }
        let normal_tail = match (
            identity.has_normal_tail,
            normal_tail_region,
            normal_tail_body,
        ) {
            (false, None, None) => None,
            (true, Some(_), Some(tail)) if tail.stmts.is_empty() => None,
            (true, Some(_), Some(tail)) => Some((
                tail,
                self.lowering
                    .bindings
                    .loop_guard_temps
                    .get(plan.index())
                    .copied()
                    .flatten()
                    .ok_or(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: region.index(),
                        detail: "normal-tail loop has no guard binding",
                    })?,
            )),
            _ => {
                return self.invalid_region(region, "normal-tail payload and region slot disagree");
            }
        };
        let protocol = self
            .lowering
            .structure
            .plan()
            .loop_protocol(plan)
            .cloned()
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "loop payload has no finalized VM protocol",
            })?;
        let mut lowered = match protocol {
            LoopVmProtocol::While(protocol) => self.lower_while_loop(
                region,
                control,
                body,
                normal_tail,
                propagated_break,
                protocol,
            ),
            LoopVmProtocol::Repeat(protocol) if normal_tail.is_none() => {
                self.lower_repeat_loop(region, plan, control, body, protocol)
            }
            LoopVmProtocol::NumericFor(protocol) => self.lower_numeric_for(
                region,
                identity,
                PlannedForRegions {
                    preheader,
                    control,
                    normal_tail,
                },
                body,
                protocol,
            ),
            LoopVmProtocol::GenericFor(protocol) => self.lower_generic_for(
                region,
                identity,
                PlannedForRegions {
                    preheader,
                    control,
                    normal_tail,
                },
                body,
                protocol,
            ),
            LoopVmProtocol::WhileTrue if normal_tail.is_none() => {
                if preheader.is_some() {
                    return self.invalid_region(region, "plain loop unexpectedly owns a preheader");
                }
                self.lower_while_true_loop(region, control, body)
            }
            _ => self.invalid_region(region, "loop protocol contradicts region slots"),
        }?;
        if let Some(target) = propagated_break {
            if target == region || !self.loop_contains_region(target, region) {
                return self
                    .invalid_region(region, "propagated break does not target a containing loop");
            }
            lowered.stmts.push(HirStmt::Break);
        }
        Ok(lowered)
    }

    fn lower_while_loop(
        &mut self,
        region: RegionId,
        control: RegionId,
        mut body: HirBlock,
        normal_tail: Option<(HirBlock, TempId)>,
        propagated_break: Option<RegionId>,
        protocol: LoopConditionProtocol,
    ) -> Result<HirBlock, HirLowerError> {
        let condition = self.lower_loop_condition(region, control, Some(protocol.condition))?;
        let body_edge = protocol.body_edge;
        let exit_edge = protocol.exit_edge;
        let cond = if protocol.body_on_truthy {
            condition.cond.clone()
        } else {
            condition.cond.clone().negate()
        };
        let exit_transfer = self.planned_edge(region, exit_edge)?.transfer;
        let cross_loop_transfer = match exit_transfer {
            EdgeTransfer::LoopBack(target) | EdgeTransfer::Continue(target) if target != region => {
                Some(target)
            }
            EdgeTransfer::Break(target) if target != region && propagated_break != Some(target) => {
                Some(target)
            }
            _ => None,
        };

        let mut stmts = Vec::new();
        if let Some((_, guard)) = &normal_tail {
            stmts.push(assign_stmt(
                vec![HirLValue::Temp(*guard)],
                vec![HirExpr::Boolean(false)],
            ));
        }
        let mut loop_body = condition.prefix;
        let exit = match exit_transfer {
            EdgeTransfer::BranchArm(crate::structure::BranchArm::LoopExit) => {
                let mut exit = self.lower_edge(region, exit_edge)?;
                exit.stmts.push(HirStmt::Break);
                exit
            }
            EdgeTransfer::LoopBack(target) | EdgeTransfer::Continue(target) if target != region => {
                HirBlock {
                    stmts: vec![HirStmt::Break],
                }
            }
            EdgeTransfer::Break(target) if target != region && propagated_break == Some(target) => {
                self.lower_edge(region, exit_edge)?
            }
            EdgeTransfer::Break(target) if target != region => HirBlock {
                stmts: vec![HirStmt::Break],
            },
            EdgeTransfer::Break(target) if target == region => {
                self.lower_edge(region, exit_edge)?
            }
            EdgeTransfer::Goto(..) => self.lower_edge(region, exit_edge)?,
            _ => {
                return self.invalid_region(
                    region,
                    "while condition exit contradicts its final transfer",
                );
            }
        };
        if normal_tail.is_none()
            && loop_body.is_empty()
            && cross_loop_transfer.is_none()
            && matches!(exit.stmts.as_slice(), [HirStmt::Break])
        {
            loop_body.extend(self.lower_edge(region, body_edge)?.stmts);
            loop_body.append(&mut body.stmts);
            stmts.push(HirStmt::While(Box::new(HirWhile {
                cond,
                body: HirBlock { stmts: loop_body },
            })));
            return Ok(HirBlock { stmts });
        }
        loop_body.push(branch_stmt(cond.negate(), exit, None));
        loop_body.extend(self.lower_edge(region, body_edge)?.stmts);
        loop_body.append(&mut body.stmts);
        if normal_tail.is_some()
            && exit_transfer == EdgeTransfer::BranchArm(crate::structure::BranchArm::LoopExit)
        {
            // generalized while 的 normal-tail guard 已把“正常退出”和提前 break
            // 分开；自然 LoopExit 证明这份独占 tail 是 post-tested 词法形状。
            stmts.push(HirStmt::Repeat(Box::new(HirRepeat {
                body: HirBlock { stmts: loop_body },
                cond: HirExpr::Boolean(false),
            })));
        } else {
            stmts.push(HirStmt::While(Box::new(HirWhile {
                cond: HirExpr::Boolean(true),
                body: HirBlock { stmts: loop_body },
            })));
        }
        if let Some(target) = cross_loop_transfer {
            if !self.loop_contains_region(target, region) {
                return self.invalid_region(
                    region,
                    "loop condition exit breaks a non-containing outer loop",
                );
            }
            // control_edges.exit 冻结内层语法退出，edge transfer 冻结退出后继续
            // break 外层；phi actions 只在内层 loop 完成后消费一次。
            stmts.extend(self.lower_edge(region, exit_edge)?.stmts);
        }
        if let Some((tail, guard)) = normal_tail {
            stmts.push(branch_stmt(HirExpr::TempRef(guard).negate(), tail, None));
        }
        Ok(HirBlock { stmts })
    }

    fn lower_repeat_loop(
        &mut self,
        region: RegionId,
        plan: crate::structure::LoopPlanId,
        control: RegionId,
        mut body: HirBlock,
        protocol: LoopRepeatProtocol,
    ) -> Result<HirBlock, HirLowerError> {
        let condition =
            self.lower_loop_condition(region, control, Some(protocol.condition.condition))?;
        let backedge = protocol.condition.body_edge;
        let exit = protocol.condition.exit_edge;
        let exit_cond = if protocol.condition.body_on_truthy {
            condition.cond.clone().negate()
        } else {
            condition.cond.clone()
        };
        let exit_plan = self
            .lowering
            .structure
            .plan()
            .edge_plan(exit)
            .cloned()
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "repeat exit has no final edge plan",
            })?;
        let staged_temps = self
            .lowering
            .bindings
            .repeat_staged_temps
            .get(plan.index())
            .cloned()
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "repeat staged-result bindings are missing",
            })?;
        if staged_temps.len() != protocol.value_plan.staged_results.len() {
            return self.invalid_region(
                region,
                "repeat staged-result bindings contradict the protocol",
            );
        }
        let normal_stage = protocol
            .value_plan
            .staged_results
            .iter()
            .zip(&staged_temps)
            .filter(|(result, temp)| !self.repeat_stage_is_direct(result.target, **temp))
            .map(|(result, temp)| Ok((*temp, self.ssa_expr(region, result.normal_value)?)))
            .collect::<Result<Vec<_>, HirLowerError>>()?;
        let final_stage = protocol
            .value_plan
            .staged_results
            .iter()
            .zip(&staged_temps)
            .filter(|(result, temp)| !self.repeat_stage_is_direct(result.target, **temp))
            .map(|(result, temp)| {
                let target = self
                    .lowering
                    .bindings
                    .phi_temps
                    .get(result.target.index())
                    .copied()
                    .ok_or(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: region.index(),
                        detail: "repeat staged result has no final phi binding",
                    })?;
                Ok((
                    self.lowering.bindings.lvalue_for_temp(target),
                    HirExpr::TempRef(*temp),
                ))
            })
            .collect::<Result<Vec<_>, HirLowerError>>()?;

        let mut body_stmts = Vec::new();
        if protocol.prefix_placement == crate::structure::LoopConditionPrefixPlacement::BeforeBody {
            body_stmts.extend(condition.prefix.clone());
        }
        body_stmts.append(&mut body.stmts);
        if protocol.prefix_placement == crate::structure::LoopConditionPrefixPlacement::AfterBody {
            body_stmts.extend(condition.prefix);
        }
        if !normal_stage.is_empty() {
            body_stmts.push(assign_stmt(
                normal_stage
                    .iter()
                    .map(|(temp, _)| HirLValue::Temp(*temp))
                    .collect::<Vec<_>>(),
                normal_stage
                    .iter()
                    .map(|(_, value)| value.clone())
                    .collect::<Vec<_>>(),
            ));
        }
        let backedge_stmts = if protocol.value_plan.backedge_copies.is_empty() {
            self.lower_edge(region, backedge)?.stmts
        } else {
            let transfer = self.planned_edge(region, backedge)?.transfer;
            if !matches!(transfer, EdgeTransfer::LoopBack(target) if target == region) {
                return self.invalid_region(
                    region,
                    "repeat native-latch copies contradict the backedge transfer",
                );
            }
            self.lower_edge_copy_set(
                region,
                backedge,
                &protocol.value_plan.backedge_copies,
                &[],
                transfer,
            )?
        };
        if matches!(protocol.form, LoopRepeatForm::Native) {
            let exit_transfer_matches = if protocol.exit_after_loop {
                !matches!(exit_plan.transfer, EdgeTransfer::Break(target) if target == region)
            } else {
                matches!(exit_plan.transfer, EdgeTransfer::Break(target) if target == region)
                    || exit_plan.transfer
                        == EdgeTransfer::BranchArm(crate::structure::BranchArm::LoopExit)
            };
            if !exit_transfer_matches {
                return self.invalid_region(
                    region,
                    "repeat native exit contradicts its staged-result protocol",
                );
            }
            body_stmts.extend(backedge_stmts);
            let mut stmts = vec![HirStmt::Repeat(Box::new(HirRepeat {
                body: HirBlock { stmts: body_stmts },
                cond: exit_cond,
            }))];
            if !final_stage.is_empty() {
                stmts.push(assign_stmt(
                    final_stage
                        .iter()
                        .map(|(target, _)| target.clone())
                        .collect::<Vec<_>>(),
                    final_stage
                        .iter()
                        .map(|(_, value)| value.clone())
                        .collect::<Vec<_>>(),
                ));
            }
            if protocol.exit_after_loop {
                stmts.extend(self.lower_edge(region, exit)?.stmts);
            }
            return Ok(HirBlock { stmts });
        }
        if !protocol.value_plan.staged_results.is_empty() || protocol.exit_after_loop {
            return self.invalid_region(region, "non-native repeat retains native exit actions");
        }
        let exit_stmts = self.lower_edge(region, exit)?.stmts;
        body_stmts.push(branch_stmt(
            exit_cond,
            HirBlock { stmts: exit_stmts },
            Some(HirBlock {
                stmts: backedge_stmts,
            }),
        ));
        // terminal edge 带值动作时仍可保留 repeat 作用域：尾分支只求值一次条件，
        // 两个 arm 分别执行 final plan 冻结的 exit/backedge actions。显式 continue
        // 会直接跳到 repeat 条件，因而不能在这里把真实条件替换成 false。
        if matches!(protocol.form, LoopRepeatForm::TailBranchRepeat) {
            return Ok(HirBlock {
                stmts: vec![HirStmt::Repeat(Box::new(HirRepeat {
                    body: HirBlock { stmts: body_stmts },
                    cond: HirExpr::Boolean(false),
                }))],
            });
        }
        self.invalid_region(region, "repeat protocol has an unknown lowering form")
    }

    fn lower_while_true_loop(
        &mut self,
        region: RegionId,
        control: RegionId,
        mut body: HirBlock,
    ) -> Result<HirBlock, HirLowerError> {
        let mut stmts = self.lower_syntax_region_prefix(region, control, None)?;
        stmts.append(&mut body.stmts);
        Ok(HirBlock {
            stmts: vec![HirStmt::While(Box::new(HirWhile {
                cond: HirExpr::Boolean(true),
                body: HirBlock { stmts },
            }))],
        })
    }

    fn lower_numeric_for(
        &mut self,
        region: RegionId,
        loop_: PlannedLoopIdentity,
        regions: PlannedForRegions,
        mut body: HirBlock,
        protocol: crate::structure::NumericForProtocol,
    ) -> Result<HirBlock, HirLowerError> {
        let PlannedForRegions {
            preheader,
            control,
            normal_tail,
        } = regions;
        let preheader_region = preheader.ok_or(HirLowerError::InvalidPlanRegion {
            proto: self.proto.index(),
            region: region.index(),
            detail: "numeric for has no planned preheader region",
        })?;
        let preheader = self.single_block_region(preheader_region)?;
        let Some(LowInstr::NumericForInit(init)) =
            self.lowering.proto.instrs.get(protocol.init_instr.index())
        else {
            return self.invalid_region(region, "numeric for plan references a non-init opcode");
        };
        if loop_.preheader_body != Some(protocol.body_edge)
            || loop_.preheader_exit != Some(protocol.exit_edge)
            || init.index != protocol.index
            || init.limit != protocol.limit
            || init.step != protocol.step
            || init.binding != protocol.binding
        {
            return self.invalid_region(region, "numeric for payload contradicts VM control");
        }
        let binding = self
            .lowering
            .bindings
            .numeric_for_locals
            .get(&loop_.header)
            .copied()
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "numeric for has no selected source binding",
            })?;
        let mut stmts = self.lower_syntax_region_prefix(region, preheader_region, None)?;
        stmts.extend(self.lower_loop_value_phase(region, LoopValuePhase::BeforeLoop)?);
        if let Some((_, guard)) = &normal_tail {
            stmts.push(assign_stmt(
                vec![HirLValue::Temp(*guard)],
                vec![HirExpr::Boolean(false)],
            ));
        }

        let start = expr_for_reg_use(
            self.lowering,
            preheader,
            protocol.init_instr,
            protocol.index,
        );
        let limit = expr_for_reg_use(
            self.lowering,
            preheader,
            protocol.init_instr,
            protocol.limit,
        );
        let step = expr_for_reg_use(self.lowering, preheader, protocol.init_instr, protocol.step);
        let mut loop_stmts = self.lower_loop_value_phase(region, LoopValuePhase::BodyPrologue)?;
        loop_stmts.append(&mut body.stmts);
        if protocol.body_completes_normally {
            loop_stmts.extend(self.lower_syntax_region_prefix(region, control, None)?);
            loop_stmts
                .extend(self.lower_loop_value_phase(region, LoopValuePhase::IterationEpilogue)?);
            loop_stmts.extend(self.lower_loop_value_phase(region, LoopValuePhase::LatchEpilogue)?);
        } else {
            self.consume_syntax_region(region, control)?;
        }
        stmts.push(HirStmt::NumericFor(Box::new(HirNumericFor {
            binding,
            start,
            limit,
            step,
            body: HirBlock { stmts: loop_stmts },
        })));
        stmts.extend(self.lower_loop_value_phase(region, LoopValuePhase::AfterLoop)?);
        if let Some((tail, guard)) = normal_tail {
            stmts.push(branch_stmt(HirExpr::TempRef(guard).negate(), tail, None));
        }
        let exit_plan = self.planned_edge(region, protocol.exit_edge)?;
        stmts.extend(self.lower_edge_after_effects(region, protocol.exit_edge, exit_plan)?);
        Ok(HirBlock { stmts })
    }

    fn lower_generic_for(
        &mut self,
        region: RegionId,
        loop_: PlannedLoopIdentity,
        regions: PlannedForRegions,
        mut body: HirBlock,
        protocol: crate::structure::GenericForProtocol,
    ) -> Result<HirBlock, HirLowerError> {
        let PlannedForRegions {
            preheader,
            control,
            normal_tail,
        } = regions;
        let preheader_region = preheader.ok_or(HirLowerError::InvalidPlanRegion {
            proto: self.proto.index(),
            region: region.index(),
            detail: "generic for has no planned preheader region",
        })?;
        let preheader = self.single_block_region(preheader_region)?;
        let header = loop_.header;
        let Some(LowInstr::GenericForLoop(_loop_instr)) =
            self.lowering.proto.instrs.get(protocol.loop_instr.index())
        else {
            return self
                .invalid_region(region, "generic for protocol references a non-loop opcode");
        };
        if !matches!(
            loop_.source_bindings,
            Some(crate::structure::LoopSourceBindings::Generic(bindings))
                if bindings == protocol.bindings
        ) {
            return self.invalid_region(region, "generic for payload contradicts VM bindings");
        }
        let bindings = self
            .lowering
            .bindings
            .generic_for_locals
            .get(&header)
            .cloned()
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "generic for has no selected source bindings",
            })?;
        if bindings.len() != protocol.bindings.len {
            return self.invalid_region(region, "generic for binding arity changed after planning");
        }
        let mut stmts =
            self.lower_syntax_region_prefix(region, preheader_region, protocol.prep_instr)?;
        stmts.extend(self.lower_loop_value_phase(region, LoopValuePhase::BeforeLoop)?);
        if let Some((_, guard)) = &normal_tail {
            stmts.push(assign_stmt(
                vec![HirLValue::Temp(*guard)],
                vec![HirExpr::Boolean(false)],
            ));
        }
        let mut loop_stmts = self.lower_loop_value_phase(region, LoopValuePhase::BodyPrologue)?;
        loop_stmts.append(&mut body.stmts);
        self.consume_syntax_region(region, control)?;
        if protocol.body_completes_normally {
            loop_stmts
                .extend(self.lower_loop_value_phase(region, LoopValuePhase::IterationEpilogue)?);
            if protocol.immediate_break {
                loop_stmts.push(HirStmt::Break);
            } else {
                loop_stmts
                    .extend(self.lower_loop_value_phase(region, LoopValuePhase::LatchEpilogue)?);
            }
        }
        stmts.push(HirStmt::GenericFor(Box::new(HirGenericFor {
            bindings,
            iterator: lower_generic_for_iterator(self.lowering, preheader, protocol).into(),
            body: HirBlock { stmts: loop_stmts },
        })));
        stmts.extend(self.lower_loop_value_phase(region, LoopValuePhase::AfterLoop)?);
        if let Some((tail, guard)) = normal_tail {
            stmts.push(branch_stmt(HirExpr::TempRef(guard).negate(), tail, None));
        }
        let exit_plan = self.planned_edge(region, protocol.exit_edge)?;
        stmts.extend(self.lower_edge_after_effects(region, protocol.exit_edge, exit_plan)?);
        Ok(HirBlock { stmts })
    }

    fn lower_loop_condition(
        &mut self,
        owner: RegionId,
        control: RegionId,
        selected: Option<crate::structure::ConditionPlanId>,
    ) -> Result<PlannedLoopCondition, HirLowerError> {
        let Some(selected) = selected else {
            return self.invalid_region(owner, "loop payload is missing its frozen condition plan");
        };

        let condition = self
            .lowering
            .structure
            .plan()
            .condition(selected)
            .cloned()
            .ok_or(HirLowerError::MissingPlanPayload {
                proto: self.proto.index(),
                kind: "condition",
                id: selected.index(),
            })?;
        self.verify_condition_plan(owner, &condition)?;
        let decision = build_condition_decision_expr(self.lowering, &condition).ok_or(
            HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "frozen loop condition cannot be materialized",
            },
        )?;
        self.verify_condition_region(owner, control, &condition.blocks)?;
        let header = condition.header().ok_or(HirLowerError::InvalidPlanRegion {
            proto: self.proto.index(),
            region: owner.index(),
            detail: "frozen loop condition has no entry node",
        })?;
        for block in condition
            .blocks
            .iter()
            .copied()
            .filter(|block| *block != header)
        {
            self.consume_syntax_block(owner, block, None)?;
        }
        Ok(PlannedLoopCondition {
            prefix: self.lower_condition_prefix(owner, header)?,
            cond: finalize_condition_decision_expr(decision),
        })
    }

    fn loop_contains_region(&self, loop_region: RegionId, region: RegionId) -> bool {
        matches!(
            self.lowering.structure.plan().region(loop_region),
            Some(RegionPlan::Loop { .. })
        ) && self
            .lowering
            .structure
            .plan()
            .region_contains(loop_region, region)
    }

    fn lower_syntax_region_prefix(
        &mut self,
        owner: RegionId,
        region: RegionId,
        skipped: Option<InstrRef>,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let mut stmts = Vec::new();
        let mut pending = vec![region];
        while let Some(region) = pending.pop() {
            match self.lowering.structure.plan().region(region) {
                Some(RegionPlan::Block { block, .. }) => {
                    stmts.extend(self.lower_syntax_block_prefix(owner, *block, skipped)?);
                }
                Some(RegionPlan::Sequence { children, .. }) => {
                    pending.extend(children.iter().rev().copied());
                }
                Some(
                    RegionPlan::Branch { .. }
                    | RegionPlan::ValueDecision { .. }
                    | RegionPlan::Loop { .. }
                    | RegionPlan::Unstructured { .. },
                ) => {
                    return self
                        .invalid_region(owner, "loop syntax partition is not a plain sequence");
                }
                None => {
                    return Err(HirLowerError::MissingPlanRegion {
                        proto: self.proto.index(),
                        region: region.index(),
                    });
                }
            }
        }
        Ok(stmts)
    }

    fn consume_syntax_region(
        &mut self,
        owner: RegionId,
        region: RegionId,
    ) -> Result<(), HirLowerError> {
        let mut pending = vec![region];
        while let Some(region) = pending.pop() {
            match self.lowering.structure.plan().region(region) {
                Some(RegionPlan::Block { block, .. }) => {
                    self.consume_syntax_block(owner, *block, None)?;
                }
                Some(RegionPlan::Sequence { children, .. }) => {
                    pending.extend(children.iter().rev().copied());
                }
                Some(
                    RegionPlan::Branch { .. }
                    | RegionPlan::ValueDecision { .. }
                    | RegionPlan::Loop { .. }
                    | RegionPlan::Unstructured { .. },
                ) => {
                    return self
                        .invalid_region(owner, "loop syntax partition is not a plain sequence");
                }
                None => {
                    return Err(HirLowerError::MissingPlanRegion {
                        proto: self.proto.index(),
                        region: region.index(),
                    });
                }
            }
        }
        Ok(())
    }

    fn consume_syntax_block(
        &mut self,
        owner: RegionId,
        block: BlockRef,
        _skipped: Option<InstrRef>,
    ) -> Result<(), HirLowerError> {
        if self
            .lowering
            .structure
            .plan()
            .label_for_block(block)
            .is_some()
        {
            return self.invalid_region(owner, "loop syntax block owns a planned label");
        }
        if self
            .lowering
            .structure
            .plan()
            .phis_in_block(block)
            .iter()
            .any(|phi| {
                self.lowering
                    .structure
                    .plan()
                    .phi_plan(*phi)
                    .is_some_and(|phi| phi.has_unresolved())
            })
        {
            return self.invalid_region(owner, "loop syntax block owns unresolved values");
        }
        #[cfg(debug_assertions)]
        self.mark_block_emitted(
            owner,
            block,
            "plan consumes one loop syntax block more than once",
        )?;
        Ok(())
    }

    fn lower_syntax_block_prefix(
        &mut self,
        owner: RegionId,
        block: BlockRef,
        skipped: Option<InstrRef>,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        #[cfg(debug_assertions)]
        self.mark_block_emitted(
            owner,
            block,
            "plan emits one loop syntax block more than once",
        )?;
        let mut stmts = Vec::new();
        self.emit_label(block, LabelPlacement::BeforeBlock, &mut stmts)?;
        stmts.extend(self.lower_unresolved_phis(owner, block)?);
        let terminator = self.block_terminator(owner, block)?.clone();
        let end = terminator
            .kind
            .instr()
            .map_or(terminator.instrs.end(), InstrRef::index);
        for index in terminator.instrs.start.index()..end {
            let instr_ref = InstrRef(index);
            if skipped == Some(instr_ref) {
                continue;
            }
            stmts.extend(self.lower_planned_regular(owner, block, instr_ref)?);
        }
        Ok(stmts)
    }

    fn lower_loop_value_phase(
        &self,
        owner: RegionId,
        phase: LoopValuePhase,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let mut stmts = Vec::new();
        let plan_id = match self.lowering.structure.plan().region(owner) {
            Some(RegionPlan::Loop { plan, .. }) => *plan,
            _ => return self.invalid_region(owner, "loop value action owner is not a loop"),
        };
        let actions = self
            .lowering
            .structure
            .plan()
            .loop_value_actions(plan_id)
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "loop payload has no finalized value actions",
            })?;
        for batch in actions.batches.iter().filter(|batch| batch.phase == phase) {
            stmts.extend(self.lower_loop_value_batch(owner, batch)?);
        }
        Ok(stmts)
    }

    fn lower_loop_value_batch(
        &self,
        owner: RegionId,
        batch: &crate::structure::LoopValueActionBatch,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let assignments = batch
            .writes
            .iter()
            .map(|write| {
                Ok((
                    write.target,
                    self.lower_loop_value_source(owner, write.source)?,
                ))
            })
            .collect::<Result<Vec<_>, HirLowerError>>()?;
        self.copy_assignments(owner, assignments)
    }

    fn lower_loop_value_source(
        &self,
        owner: RegionId,
        source: LoopValueSource,
    ) -> Result<HirExpr, HirLowerError> {
        Ok(match source {
            LoopValueSource::Ssa(value) => self.ssa_expr(owner, value)?,
            LoopValueSource::Binding(reg) => self
                .binding_local_for_reg(owner, reg)
                .map(HirExpr::LocalRef)
                .ok_or(HirLowerError::InvalidPlanRegion {
                    proto: self.proto.index(),
                    region: owner.index(),
                    detail: "loop action binding lost its selected local",
                })?,
            LoopValueSource::Carried(phi) => {
                HirExpr::TempRef(*self.lowering.bindings.phi_temps.get(phi.index()).ok_or(
                    HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "loop action carried source has no temp binding",
                    },
                )?)
            }
        })
    }

    fn copy_assignments(
        &self,
        owner: RegionId,
        copies: Vec<(PhiId, HirExpr)>,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        if copies.is_empty() {
            return Ok(Vec::new());
        }
        let mut targets = Vec::with_capacity(copies.len());
        let mut values = Vec::with_capacity(copies.len());
        for (phi, value) in copies {
            let target = self
                .lowering
                .bindings
                .phi_temps
                .get(phi.index())
                .copied()
                .ok_or(HirLowerError::InvalidPlanRegion {
                    proto: self.proto.index(),
                    region: owner.index(),
                    detail: "phi copy target has no HIR temp binding",
                })?;
            targets.push(self.lowering.bindings.lvalue_for_temp(target));
            values.push(value);
        }
        Ok(copy_assignment_stmt(targets, values).into_iter().collect())
    }

    fn verify_condition_plan(
        &self,
        owner: RegionId,
        condition: &crate::structure::ConditionPlan,
    ) -> Result<(), HirLowerError> {
        if condition.entry.index() >= condition.nodes.len() {
            return self.invalid_region(owner, "condition entry is outside its node arena");
        }
        for (index, node) in condition.nodes.iter().enumerate() {
            if node.id.index() != index
                || !matches!(
                    self.lowering.proto.instrs.get(node.predicate.index()),
                    Some(LowInstr::Branch(_))
                )
            {
                return self
                    .invalid_region(owner, "condition node identity or predicate is invalid");
            }
            for arc in &node.arcs {
                if arc.source != node.id
                    || matches!(
                        arc.target,
                        crate::structure::ConditionTarget::Node(target)
                            if target.index() >= condition.nodes.len()
                    )
                {
                    return self.invalid_region(owner, "condition arc is outside its node arena");
                }
            }
            if let Some(value) = node.materialized_value
                && (value.consumer.index() >= condition.nodes.len()
                    || value.phi.index() >= self.lowering.bindings.phi_temps.len()
                    || value
                        .forwarded_callee
                        .is_some_and(|def| def.index() >= self.lowering.bindings.fixed_temps.len()))
            {
                return self.invalid_region(
                    owner,
                    "condition materialized value references an unbound identity",
                );
            }
        }
        Ok(())
    }

    fn verify_value_decision_plan(
        &self,
        owner: RegionId,
        decision: &crate::structure::ValueDecisionPlan,
    ) -> Result<(), HirLowerError> {
        if decision.entry.index() >= decision.nodes.len()
            || decision.result_phi.index() >= self.lowering.bindings.phi_temps.len()
        {
            return self.invalid_region(owner, "value decision root identity is unbound");
        }
        for (index, node) in decision.nodes.iter().enumerate() {
            if node.id.index() != index
                || !matches!(
                    self.lowering.proto.instrs.get(node.predicate.index()),
                    Some(LowInstr::Branch(_))
                )
            {
                return self.invalid_region(
                    owner,
                    "value decision node identity or predicate is invalid",
                );
            }
            for target in [node.truthy.target, node.falsy.target] {
                let valid = match target {
                    crate::structure::ValueDecisionTarget::Node(target) => {
                        target.index() < decision.nodes.len()
                    }
                    crate::structure::ValueDecisionTarget::Leaf(target)
                    | crate::structure::ValueDecisionTarget::CurrentValue(target) => {
                        target.index() < decision.leaves.len()
                    }
                };
                if !valid {
                    return self
                        .invalid_region(owner, "value decision target is outside its arena");
                }
            }
        }
        for (index, leaf) in decision.leaves.iter().enumerate() {
            if leaf.id.index() != index
                || leaf.latest_local_def.is_some_and(|def| {
                    def.index() >= self.lowering.dataflow.defs.len()
                        || def.index() >= self.lowering.bindings.fixed_temps.len()
                })
            {
                return self.invalid_region(owner, "value decision leaf identity is invalid");
            }
            self.ensure_ssa_binding(owner, leaf.value)?;
        }
        Ok(())
    }

    fn binding_local_for_reg(
        &self,
        owner: RegionId,
        reg: crate::transformer::Reg,
    ) -> Option<crate::hir::common::LocalId> {
        let loop_id = match self.lowering.structure.plan().region(owner)? {
            RegionPlan::Loop { plan, .. } => *plan,
            _ => return None,
        };
        let payload = self.lowering.structure.plan().loop_(loop_id)?;
        match payload.source_bindings? {
            crate::structure::LoopSourceBindings::Numeric(binding) if reg == binding => self
                .lowering
                .bindings
                .numeric_for_locals
                .get(&payload.header)
                .copied(),
            crate::structure::LoopSourceBindings::Generic(bindings)
                if reg.index() >= bindings.start.index()
                    && reg.index() < bindings.start.index() + bindings.len =>
            {
                self.lowering
                    .bindings
                    .generic_for_locals
                    .get(&payload.header)
                    .and_then(|locals| locals.get(reg.index() - bindings.start.index()))
                    .copied()
            }
            _ => None,
        }
    }

    fn ssa_expr(
        &self,
        owner: RegionId,
        value: crate::structure::SsaValue,
    ) -> Result<HirExpr, HirLowerError> {
        self.ensure_ssa_binding(owner, value)?;
        let target = match value {
            SsaValue::Entry(_) => None,
            SsaValue::Def(def) => self.lowering.bindings.fixed_temps.get(def.index()).copied(),
            SsaValue::Phi(phi) => self.lowering.bindings.phi_temps.get(phi.index()).copied(),
        };
        Ok(target.map_or_else(
            || super::super::exprs::expr_for_ssa_value(self.lowering, value),
            |temp| self.lowering.bindings.expr_for_temp(temp),
        ))
    }

    fn ensure_ssa_binding(&self, owner: RegionId, value: SsaValue) -> Result<(), HirLowerError> {
        let bound = match value {
            SsaValue::Entry(_) => true,
            SsaValue::Def(def) => def.index() < self.lowering.bindings.fixed_temps.len(),
            SsaValue::Phi(phi) => phi.index() < self.lowering.bindings.phi_temps.len(),
        };
        if bound {
            Ok(())
        } else {
            self.invalid_region(owner, "SSA value has no HIR temp binding")
        }
    }

    /// 条件 region 会吸收内部纯 `Move`，通常必须沿 SSA 恒等链读取真实来源。若 bindings
    /// 已让一个未吸收 def 在原指令处直接写入 copy target，则必须读取该 target；再次穿透
    /// Move 会复制赋值并让后续 local 提升拆散 loop-carried identity。
    fn edge_copy_expr(
        &self,
        owner: RegionId,
        source_block: BlockRef,
        target: TempId,
        value: SsaValue,
    ) -> Result<HirExpr, HirLowerError> {
        let value = match value {
            SsaValue::Def(def) => {
                let fixed = self
                    .lowering
                    .bindings
                    .fixed_temps
                    .get(def.index())
                    .copied()
                    .ok_or(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "edge copy source has no fixed-temp binding",
                    })?;
                let definition = self.lowering.dataflow.defs.get(def.index()).ok_or(
                    HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "edge copy source references a missing SSA def",
                    },
                )?;
                let absorbed = self
                    .index
                    .absorbed_region_result_moves
                    .get(definition.instr.index())
                    .copied()
                    .ok_or(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "edge copy source has no absorption disposition",
                    })?;
                let writes_fixed_temp = self
                    .lowering
                    .bindings
                    .local_for_reg_in_block(definition.block, definition.reg)
                    .is_none();
                if fixed == target && !absorbed && writes_fixed_temp {
                    value
                } else {
                    self.index
                        .canonical_move_source
                        .get(def.index())
                        .copied()
                        .flatten()
                        .unwrap_or(value)
                }
            }
            _ => value,
        };
        let reg = self.ssa_reg(owner, value)?;
        if let Some(local) = self
            .lowering
            .bindings
            .local_for_reg_in_block(source_block, reg)
        {
            return Ok(HirExpr::LocalRef(local));
        }
        self.ssa_expr(owner, value)
    }

    fn ssa_reg(&self, owner: RegionId, value: SsaValue) -> Result<Reg, HirLowerError> {
        match value {
            SsaValue::Entry(reg) => Ok(reg),
            SsaValue::Def(def) => self
                .lowering
                .dataflow
                .defs
                .get(def.index())
                .map(|def| def.reg)
                .ok_or(HirLowerError::InvalidPlanRegion {
                    proto: self.proto.index(),
                    region: owner.index(),
                    detail: "SSA value references a missing def",
                }),
            SsaValue::Phi(phi) => self
                .lowering
                .structure
                .plan()
                .phi_plan(phi)
                .map(|phi| phi.reg)
                .ok_or(HirLowerError::InvalidPlanRegion {
                    proto: self.proto.index(),
                    region: owner.index(),
                    detail: "SSA value references a missing final phi plan",
                }),
        }
    }

    fn lower_block(&mut self, owner: RegionId, block: BlockRef) -> Result<HirBlock, HirLowerError> {
        #[cfg(debug_assertions)]
        self.mark_block_emitted(owner, block, "plan emits one basic block more than once")?;

        match self.lowering.structure.plan().block_emission(block) {
            Some(BlockEmissionPlan::Emit) => {}
            Some(BlockEmissionPlan::ForwardedControl { .. }) => {
                return Ok(HirBlock { stmts: Vec::new() });
            }
            None => return self.invalid_region(owner, "block has no dense emission plan"),
        }

        let mut stmts = Vec::new();
        let terminator = self.block_terminator(owner, block)?.clone();
        let range = terminator.instrs;
        let prefix_start = match self
            .lowering
            .structure
            .plan()
            .loop_exit_tail_for_block(block)
        {
            Some((_, tail))
                if tail.block == block
                    && tail.continuation == block
                    && tail.range.start == range.start
                    && tail.range.end() <= range.end() =>
            {
                tail.range.end()
            }
            Some(_) => {
                return self.invalid_region(owner, "loop exit tail block range is stale");
            }
            None => range.start.index(),
        };
        let prefix_end = terminator.kind.instr().map_or(range.end(), InstrRef::index);
        let jump_edge = match terminator.kind {
            BlockTerminatorKind::Jump { edge, .. } => Some(edge),
            _ => None,
        };
        let trailing_cleanup = jump_edge.and_then(|edge| {
            self.lowering
                .structure
                .plan()
                .edge_plan(edge)
                .and_then(EdgePlan::actions_before_trailing_cleanup)
        });
        let regular_end = if let Some(cleanup) = trailing_cleanup {
            if cleanup.is_empty()
                || cleanup.start.index() < prefix_start
                || cleanup.end() != prefix_end
            {
                return self.invalid_region(owner, "edge trailing-cleanup range is stale");
            }
            cleanup.start.index()
        } else {
            prefix_end
        };
        let placement = self
            .lowering
            .structure
            .plan()
            .label_for_block(block)
            .map(|label| {
                self.lowering
                    .structure
                    .plan()
                    .label(label)
                    .map(|label| label.placement)
                    .ok_or(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "block label has no frozen payload",
                    })
            })
            .transpose()?;
        let regular_start = match placement {
            Some(LabelPlacement::AfterCleanup(last)) => {
                if last.index() < prefix_start || last.index() >= regular_end {
                    return self.invalid_region(
                        owner,
                        "label cleanup placement is outside the regular block prefix",
                    );
                }
                for instr_index in prefix_start..=last.index() {
                    stmts.extend(self.lower_planned_regular(
                        owner,
                        block,
                        InstrRef(instr_index),
                    )?);
                }
                self.emit_label(block, LabelPlacement::AfterCleanup(last), &mut stmts)?;
                stmts.extend(self.lower_unresolved_phis(owner, block)?);
                last.index() + 1
            }
            Some(LabelPlacement::BeforeRegion(_)) => {
                stmts.extend(self.lower_unresolved_phis(owner, block)?);
                prefix_start
            }
            Some(LabelPlacement::BeforeBlock) | None => {
                self.emit_label(block, LabelPlacement::BeforeBlock, &mut stmts)?;
                stmts.extend(self.lower_unresolved_phis(owner, block)?);
                prefix_start
            }
        };
        for instr_index in regular_start..regular_end {
            let instr_ref = InstrRef(instr_index);
            stmts.extend(self.lower_planned_regular(owner, block, instr_ref)?);
        }

        if let Some(cleanup) = trailing_cleanup {
            let Some(edge) = jump_edge else {
                return self.invalid_region(owner, "cleanup placement has no source jump");
            };
            let edge_plan = self.planned_edge(owner, edge)?;
            stmts.extend(self.lower_edge_effects(owner, edge)?);
            for instr_index in cleanup.start.index()..cleanup.end() {
                stmts.extend(self.lower_planned_regular(owner, block, InstrRef(instr_index))?);
            }
            stmts.extend(self.lower_edge_after_effects(owner, edge, edge_plan)?);
            return Ok(HirBlock { stmts });
        }

        match terminator.kind {
            BlockTerminatorKind::Linear { edge } => {
                if let Some(edge) = edge {
                    stmts.extend(self.lower_edge(owner, edge)?.stmts);
                }
            }
            BlockTerminatorKind::Jump { edge, .. } => {
                stmts.extend(self.lower_edge(owner, edge)?.stmts);
            }
            BlockTerminatorKind::Branch {
                instr,
                truthy,
                falsy,
            } => {
                let Some(LowInstr::Branch(branch)) = self.lowering.proto.instrs.get(instr.index())
                else {
                    return self.invalid_region(
                        owner,
                        "branch terminator plan references a non-branch opcode",
                    );
                };
                stmts.push(branch_stmt(
                    lower_branch_cond(self.lowering, block, instr, branch.cond),
                    self.lower_edge(owner, truthy)?,
                    Some(self.lower_edge(owner, falsy)?),
                ));
            }
            BlockTerminatorKind::Return { instr, .. }
            | BlockTerminatorKind::TailCall { instr, .. } => {
                let Some(low) = self.lowering.proto.instrs.get(instr.index()) else {
                    return self.invalid_region(
                        owner,
                        "terminal plan references an instruction outside the proto",
                    );
                };
                let Some(terminal) = lower_terminal_instr(self.lowering, block, instr, low) else {
                    return self.invalid_region(owner, "planned terminal lowering rejected opcode");
                };
                stmts.extend(terminal);
            }
            BlockTerminatorKind::NumericForInit { .. }
            | BlockTerminatorKind::NumericForLoop { .. }
            | BlockTerminatorKind::GenericForLoop { .. } => {
                return self
                    .invalid_region(owner, "for control block is not owned by a loop region");
            }
            BlockTerminatorKind::SyntheticExit => {
                return self.invalid_region(owner, "synthetic exit is owned by an emitted region");
            }
        }
        Ok(HirBlock { stmts })
    }

    fn single_block_region(&self, region: RegionId) -> Result<BlockRef, HirLowerError> {
        self.index
            .single_plain_block
            .get(region.index())
            .copied()
            .flatten()
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "region does not contain exactly one plain block",
            })
    }

    fn lower_condition_prefix(
        &mut self,
        owner: RegionId,
        block: BlockRef,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        #[cfg(debug_assertions)]
        self.mark_block_emitted(
            owner,
            block,
            "plan emits one condition block more than once",
        )?;
        let terminator = self.block_terminator(owner, block)?.clone();
        let BlockTerminatorKind::Branch { instr, .. } = terminator.kind else {
            return self.invalid_region(owner, "condition block has no frozen branch terminator");
        };
        let mut stmts = Vec::new();
        self.emit_label(block, LabelPlacement::BeforeBlock, &mut stmts)?;
        stmts.extend(self.lower_unresolved_phis(owner, block)?);
        for instr_index in terminator.instrs.start.index()..instr.index() {
            let instr_ref = InstrRef(instr_index);
            stmts.extend(self.lower_planned_regular(owner, block, instr_ref)?);
        }
        Ok(stmts)
    }

    fn lower_planned_regular(
        &self,
        owner: RegionId,
        block: BlockRef,
        instr_ref: InstrRef,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let Some(instr) = self.lowering.proto.instrs.get(instr_ref.index()) else {
            return self
                .invalid_region(owner, "regular instruction reference is outside the proto");
        };
        let absorbed_region_result_move = self
            .index
            .absorbed_region_result_moves
            .get(instr_ref.index())
            .copied()
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "RegionResult Move index does not cover one regular instruction",
            })?;
        if absorbed_region_result_move {
            if !matches!(instr, LowInstr::Move(_)) {
                return self.invalid_region(
                    owner,
                    "RegionResult Move index marks a non-Move instruction",
                );
            }
            return Ok(Vec::new());
        }
        if matches!(instr, LowInstr::GenericForPrep(_)) {
            return self.invalid_region(owner, "generic-for prep escaped its selected loop");
        }
        if let Some((_, tail)) = self
            .lowering
            .structure
            .plan()
            .loop_exit_tail_for_cleanup_instr(instr_ref)
        {
            if tail.cleanup_block != block {
                return self.invalid_region(owner, "loop exit tail cleanup index is stale");
            }
            return Ok(Vec::new());
        }
        if matches!(instr, LowInstr::Close(_) | LowInstr::Tbc(_)) {
            let disposition = self
                .lowering
                .structure
                .plan()
                .cleanup_disposition(instr_ref)
                .ok_or(HirLowerError::InvalidPlanRegion {
                    proto: self.proto.index(),
                    region: owner.index(),
                    detail: "cleanup instruction has no final disposition",
                })?;
            match disposition {
                CleanupDisposition::Unreachable | CleanupDisposition::LexicalScope(_) => {
                    return Ok(Vec::new());
                }
                // 退出块可以同时承载 loop 词法 cleanup 和循环后的用户指令，因此它
                // 不一定还是 loop region 的 child。最终 disposition 已在 Structure
                // 校验过 owner 与边界位置；HIR 只消费该结论，不能再按 lowering 栈重判。
                CleanupDisposition::LoopTbcBoundary(_) => return Ok(Vec::new()),
                CleanupDisposition::ExplicitTbcExit(_) => return Ok(Vec::new()),
                CleanupDisposition::ExplicitTbc | CleanupDisposition::ExplicitTbcBoundary(_) => {}
            }
        }
        lower_regular_instr(self.lowering, block, instr_ref, instr).ok_or(
            HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "regular block contains an unplanned control instruction",
            },
        )
    }

    fn lower_unresolved_phis(
        &self,
        owner: RegionId,
        block: BlockRef,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let plan = self.lowering.structure.plan();
        let stmts = plan
            .phis_in_block(block)
            .iter()
            .map(|phi_id| {
                let phi = plan
                    .phi_plan(*phi_id)
                    .ok_or(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "block references a missing phi plan",
                    })?;
                if !phi.has_unresolved() {
                    return Ok(None);
                }
                if self
                    .index
                    .unresolved_requirement
                    .get(phi.phi.index())
                    .copied()
                    .flatten()
                    != Some((phi.block, phi.reg))
                {
                    return Err(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "unresolved phi has no matching plan requirement",
                    });
                }
                let target = self
                    .lowering
                    .bindings
                    .phi_temps
                    .get(phi.phi.index())
                    .copied()
                    .ok_or(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "unresolved phi has no HIR temp target",
                    })?;
                let incoming = phi
                    .incomings
                    .iter()
                    .map(|incoming| {
                        let edge = incoming
                            .edge
                            .map_or_else(|| "entry".to_owned(), |edge| edge.to_string());
                        format!("{edge}:{}", incoming.value)
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                Ok(Some(assign_stmt(
                    vec![self.lowering.bindings.lvalue_for_temp(target)],
                    vec![super::super::helpers::unresolved_expr(format!(
                        "unresolved {} for {} at block {}; incoming [{}]",
                        phi.phi, phi.reg, phi.block, incoming
                    ))],
                )))
            })
            .collect::<Result<Vec<_>, HirLowerError>>()?;
        Ok(stmts.into_iter().flatten().collect())
    }

    fn lower_edge(&self, owner: RegionId, edge: EdgeRef) -> Result<HirBlock, HirLowerError> {
        let plan = self.planned_edge(owner, edge)?;
        if plan.actions_before_trailing_cleanup().is_some() {
            return self.invalid_region(
                owner,
                "trailing-cleanup edge actions escaped their source jump",
            );
        }
        let mut stmts = self.lower_edge_effects(owner, edge)?;
        stmts.extend(self.lower_edge_after_effects(owner, edge, plan)?);
        Ok(HirBlock { stmts })
    }

    fn planned_edge(&self, owner: RegionId, edge: EdgeRef) -> Result<&EdgePlan, HirLowerError> {
        let plan = self.lowering.structure.plan().edge_plan(edge).ok_or(
            HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "CFG edge has no final edge plan",
            },
        )?;
        if !self.edge_requirement_matches(edge, plan.transfer) {
            return self.invalid_region(owner, "edge transfer contradicts plan requirements");
        }
        Ok(plan)
    }

    fn lower_edge_after_effects(
        &self,
        owner: RegionId,
        edge: EdgeRef,
        plan: &EdgePlan,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let mut stmts = Vec::new();
        if let Some((loop_id, tail)) = self.lowering.structure.plan().loop_exit_tail_for_edge(edge)
        {
            let loop_region = self.lowering.structure.plan().loop_region(loop_id).ok_or(
                HirLowerError::InvalidPlanRegion {
                    proto: self.proto.index(),
                    region: owner.index(),
                    detail: "loop exit tail has no owning loop region",
                },
            )?;
            if !self.loop_contains_region(loop_region, owner)
                || tail.normal_exit != edge
                || plan.transfer != EdgeTransfer::Break(loop_region)
            {
                return self.invalid_region(owner, "loop exit tail edge ownership is stale");
            }
            stmts.extend(self.lower_loop_exit_tail(loop_region, tail.block, tail.range)?);
        }
        match plan.transfer {
            EdgeTransfer::Unreachable => {
                return self.invalid_region(owner, "reachable region uses unreachable edge plan");
            }
            EdgeTransfer::Fallthrough | EdgeTransfer::BranchArm(_) | EdgeTransfer::LoopBack(_) => {}
            EdgeTransfer::Return | EdgeTransfer::TailCall => {
                let cfg_edge = self.lowering.cfg.edges.get(edge.index()).ok_or(
                    HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "terminal transfer references a missing CFG edge",
                    },
                )?;
                if !matches!(cfg_edge.kind, EdgeKind::Return | EdgeKind::TailCall) {
                    let terminator = self.block_terminator(owner, cfg_edge.to)?;
                    let (instr, matches_transfer) = match terminator.kind {
                        BlockTerminatorKind::Return { instr, .. } => {
                            (instr, plan.transfer == EdgeTransfer::Return)
                        }
                        BlockTerminatorKind::TailCall { instr, .. } => {
                            (instr, plan.transfer == EdgeTransfer::TailCall)
                        }
                        _ => {
                            return self.invalid_region(
                                owner,
                                "forwarded terminal target is not terminal",
                            );
                        }
                    };
                    if !matches_transfer || terminator.instrs.start != instr {
                        return self.invalid_region(
                            owner,
                            "forwarded terminal target has a non-empty prefix",
                        );
                    }
                    let Some(low) = self.lowering.proto.instrs.get(instr.index()) else {
                        return self.invalid_region(
                            owner,
                            "forwarded terminal instruction is outside the proto",
                        );
                    };
                    let Some(terminal) =
                        lower_terminal_instr(self.lowering, cfg_edge.to, instr, low)
                    else {
                        return self
                            .invalid_region(owner, "forwarded terminal lowering rejected opcode");
                    };
                    stmts.extend(terminal);
                }
            }
            EdgeTransfer::Break(loop_region) => {
                if !self.break_target_contains_region(loop_region, owner) {
                    return self
                        .invalid_region(owner, "break targets a non-containing lexical region");
                }
                if let Some(guard) = self.normal_tail_guard_for_break(loop_region, edge)? {
                    stmts.push(assign_stmt(
                        vec![HirLValue::Temp(guard)],
                        vec![HirExpr::Boolean(true)],
                    ));
                }
                stmts.push(HirStmt::Break);
            }
            EdgeTransfer::Continue(loop_region) => {
                if !self.loop_contains_region(loop_region, owner) {
                    return self
                        .invalid_region(owner, "continue targets a non-containing loop region");
                }
                stmts.extend(
                    self.lower_loop_value_phase(loop_region, LoopValuePhase::LatchEpilogue)?,
                );
                stmts.extend(self.lower_repeat_normal_stage(loop_region)?);
                stmts.push(HirStmt::Continue);
            }
            EdgeTransfer::Goto(label, _) => {
                let Some(target) = self.lowering.structure.plan().label(label) else {
                    return self.invalid_region(owner, "goto target has no planned label");
                };
                let Some(cfg_edge) = self.lowering.cfg.edges.get(edge.index()) else {
                    return self.invalid_region(owner, "goto transfer references a missing edge");
                };
                if cfg_edge.to != target.block {
                    return self.invalid_region(owner, "goto edge disagrees with planned label");
                }
                stmts.extend(goto_block(HirLabelId(label.index())).stmts);
            }
        }
        Ok(stmts)
    }

    fn lower_repeat_normal_stage(
        &self,
        loop_region: RegionId,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let loop_id = match self.lowering.structure.plan().region(loop_region) {
            Some(RegionPlan::Loop { plan, .. }) => *plan,
            _ => return self.invalid_region(loop_region, "continue target is not a loop region"),
        };
        let Some(LoopVmProtocol::Repeat(protocol)) =
            self.lowering.structure.plan().loop_protocol(loop_id)
        else {
            return Ok(Vec::new());
        };
        let temps = self
            .lowering
            .bindings
            .repeat_staged_temps
            .get(loop_id.index())
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: loop_region.index(),
                detail: "repeat staged-result bindings are missing",
            })?;
        if temps.len() != protocol.value_plan.staged_results.len() {
            return self.invalid_region(
                loop_region,
                "repeat staged-result bindings contradict the protocol",
            );
        }
        if temps.is_empty() {
            return Ok(Vec::new());
        }
        let values = protocol
            .value_plan
            .staged_results
            .iter()
            .zip(temps)
            .filter(|(result, temp)| !self.repeat_stage_is_direct(result.target, **temp))
            .map(|(result, _)| self.ssa_expr(loop_region, result.normal_value))
            .collect::<Result<Vec<_>, _>>()?;
        let targets = protocol
            .value_plan
            .staged_results
            .iter()
            .zip(temps)
            .filter(|(result, temp)| !self.repeat_stage_is_direct(result.target, **temp))
            .map(|(_, temp)| HirLValue::Temp(*temp))
            .collect::<Vec<_>>();
        if targets.is_empty() {
            return Ok(Vec::new());
        }
        Ok(vec![assign_stmt(targets, values)])
    }

    fn repeat_stage_is_direct(&self, target: PhiId, stage: TempId) -> bool {
        self.lowering.bindings.phi_temps.get(target.index()) == Some(&stage)
    }

    fn lower_loop_exit_tail(
        &self,
        owner: RegionId,
        block: BlockRef,
        range: crate::structure::InstrRange,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let block_range = self.block_terminator(owner, block)?.instrs;
        if range.start != block_range.start || range.is_empty() || range.end() >= block_range.end()
        {
            return self.invalid_region(owner, "loop exit tail instruction range is stale");
        }
        let mut stmts = Vec::new();
        for index in range.start.index()..range.end() {
            stmts.extend(self.lower_planned_regular(owner, block, InstrRef(index))?);
        }
        Ok(stmts)
    }

    fn normal_tail_guard_for_break(
        &self,
        loop_region: RegionId,
        edge: EdgeRef,
    ) -> Result<Option<TempId>, HirLowerError> {
        if self
            .lowering
            .structure
            .plan()
            .single_pass_for_region(loop_region)
            .is_some()
        {
            return Ok(None);
        }
        if !matches!(
            self.lowering.structure.plan().region(loop_region),
            Some(RegionPlan::Loop { .. })
        ) {
            return self.invalid_region(loop_region, "break target is not a loop region");
        }
        match self
            .index
            .normal_tail_guard_by_edge
            .get(edge.index())
            .copied()
            .flatten()
        {
            None => Ok(None),
            Some((owner, guard)) if owner == loop_region => Ok(Some(guard)),
            Some(_) => self.invalid_region(
                loop_region,
                "normal-tail break has a conflicting loop owner",
            ),
        }
    }

    fn break_target_contains_region(&self, target: RegionId, region: RegionId) -> bool {
        let plan = self.lowering.structure.plan();
        (matches!(plan.region(target), Some(RegionPlan::Loop { .. }))
            || plan.single_pass_for_region(target).is_some())
            && plan.region_contains(target, region)
    }

    fn lower_edge_effects(
        &self,
        owner: RegionId,
        edge: EdgeRef,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let edge_plan = self.lowering.structure.plan().edge_plan(edge).ok_or(
            HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "CFG edge has no final edge plan",
            },
        )?;
        let direct_copies = if self
            .lowering
            .structure
            .plan()
            .edge_action_is_forwarded_only(edge)
        {
            &[][..]
        } else {
            edge_plan.phi_copies.as_slice()
        };
        let mut stmts = self.lower_edge_copy_set(
            owner,
            edge,
            direct_copies,
            &edge_plan.iteration,
            edge_plan.transfer,
        )?;
        if let Some(route) = edge_plan.forward_route {
            for action_edge in self
                .lowering
                .structure
                .plan()
                .forward_route_action_edges(route)
            {
                let action_plan = self
                    .lowering
                    .structure
                    .plan()
                    .edge_plan(action_edge)
                    .ok_or(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "forwarded action references a missing edge plan",
                    })?;
                stmts.extend(self.lower_edge_copy_set(
                    owner,
                    action_edge,
                    &action_plan.phi_copies,
                    &[],
                    edge_plan.transfer,
                )?);
            }
        }
        Ok(stmts)
    }

    fn lower_edge_copy_set(
        &self,
        owner: RegionId,
        edge: EdgeRef,
        copies: &[crate::structure::PhiEdgeCopy],
        iteration: &[LoopIterationDisposition],
        effective_transfer: EdgeTransfer,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        self.planned_edge(owner, edge)?;
        let source_block = self
            .lowering
            .cfg
            .edges
            .get(edge.index())
            .map(|edge| edge.from)
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "final edge plan references a missing CFG edge",
            })?;
        let mut targets = Vec::new();
        let mut values = Vec::new();
        let elided = self
            .index
            .consumed_loop_copy_targets
            .get(edge.index())
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "edge copy elision index misses a final edge",
            })?;
        for copy in copies {
            if copy.value == crate::structure::SsaValue::Phi(copy.phi_id)
                || elided.binary_search(&copy.phi_id).is_ok()
            {
                continue;
            }
            let phi_target = self
                .lowering
                .bindings
                .phi_temps
                .get(copy.phi_id.index())
                .copied()
                .ok_or(HirLowerError::InvalidPlanRegion {
                    proto: self.proto.index(),
                    region: owner.index(),
                    detail: "edge phi copy target has no HIR temp binding",
                })?;
            let source_reg = self.ssa_reg(owner, copy.value)?;
            let value = if let Some(local) = self
                .lowering
                .bindings
                .local_for_reg_in_block(source_block, source_reg)
            {
                HirExpr::LocalRef(local)
            } else {
                self.edge_copy_expr(owner, source_block, phi_target, copy.value)?
            };
            let staged_target = match effective_transfer {
                EdgeTransfer::Break(loop_region) => self
                    .index
                    .repeat_staged_result_by_phi
                    .get(copy.phi_id.index())
                    .copied()
                    .flatten()
                    .filter(|(owner, _)| *owner == loop_region)
                    .map(|(_, temp)| temp),
                _ => None,
            };
            let target = if let Some(stage) = staged_target {
                HirLValue::Temp(stage)
            } else {
                self.lowering.bindings.lvalue_for_temp(phi_target)
            };
            targets.push(target);
            values.push(value);
        }
        for disposition in iteration {
            let LoopIterationDisposition {
                loop_region,
                target,
                incoming,
                source,
            } = *disposition;
            if !self.loop_contains_region(loop_region, owner) {
                return self
                    .invalid_region(owner, "iteration edge action targets a non-containing loop");
            }
            match self.lowering.structure.plan().region(loop_region) {
                Some(RegionPlan::Loop { .. }) => {}
                _ => {
                    return self
                        .invalid_region(owner, "iteration edge action owner is not a loop region");
                }
            }
            let target = self
                .lowering
                .bindings
                .phi_temps
                .get(target.index())
                .copied()
                .ok_or(HirLowerError::InvalidPlanRegion {
                    proto: self.proto.index(),
                    region: owner.index(),
                    detail: "iteration edge target has no HIR temp binding",
                })?;
            let value = match source {
                LoopValueSource::Ssa(value) if value == incoming => {
                    self.edge_copy_expr(owner, source_block, target, value)?
                }
                LoopValueSource::Ssa(_) => {
                    return self.invalid_region(
                        owner,
                        "iteration edge source changed its canonical SSA identity",
                    );
                }
                source => self.lower_loop_value_source(loop_region, source)?,
            };
            targets.push(self.lowering.bindings.lvalue_for_temp(target));
            values.push(value);
        }
        Ok(copy_assignment_stmt(targets, values).into_iter().collect())
    }

    fn edge_requirement_matches(&self, edge: EdgeRef, transfer: EdgeTransfer) -> bool {
        let requirements = self.lowering.structure.plan().requirements();
        let planned = || {
            requirements
                .for_edge(edge)
                .iter()
                .filter_map(|id| requirements.get(*id))
        };
        match transfer {
            EdgeTransfer::Goto(label, reason) => planned().any(|requirement| {
                matches!(
                    requirement,
                    PlanRequirement::Goto {
                        label: planned_label,
                        reason: planned_reason,
                        ..
                    } if *planned_label == label && *planned_reason == reason
                )
            }),
            EdgeTransfer::Continue(loop_region) => planned().any(|requirement| {
                matches!(
                    requirement,
                    PlanRequirement::Continue {
                        loop_region: planned_loop,
                        ..
                    } if *planned_loop == loop_region
                )
            }),
            _ => !planned().any(|requirement| {
                matches!(
                    requirement,
                    PlanRequirement::Goto { .. } | PlanRequirement::Continue { .. }
                )
            }),
        }
    }

    fn emit_label(
        &mut self,
        block: BlockRef,
        expected_placement: LabelPlacement,
        stmts: &mut Vec<HirStmt>,
    ) -> Result<(), HirLowerError> {
        let Some(label) = self.lowering.structure.plan().label_for_block(block) else {
            return Ok(());
        };
        let Some(payload) = self.lowering.structure.plan().label(label) else {
            return self.invalid_region(
                self.lowering
                    .structure
                    .plan()
                    .region_for_block(block)
                    .unwrap_or(self.lowering.structure.plan().root()),
                "block label has no frozen payload",
            );
        };
        if matches!(payload.placement, LabelPlacement::BeforeRegion(_))
            && payload.placement != expected_placement
        {
            return Ok(());
        }
        if payload.placement != expected_placement {
            return self.invalid_region(
                self.lowering
                    .structure
                    .plan()
                    .region_for_block(block)
                    .unwrap_or(self.lowering.structure.plan().root()),
                "block label was emitted at the wrong cleanup boundary",
            );
        }
        #[cfg(debug_assertions)]
        {
            let duplicate = self
                .emitted_labels
                .get_mut(label.index())
                .is_none_or(|emitted| std::mem::replace(emitted, true));
            if duplicate {
                return self.invalid_region(
                    self.lowering
                        .structure
                        .plan()
                        .region_for_block(block)
                        .unwrap_or(self.lowering.structure.plan().root()),
                    "plan emits one label more than once",
                );
            }
            self.emitted_label_count += 1;
        }
        stmts.push(HirStmt::Label(Box::new(HirLabel {
            id: HirLabelId(label.index()),
            tbc_barriers: payload.tbc_barriers.clone(),
        })));
        Ok(())
    }

    fn emit_region_label(
        &mut self,
        region: RegionId,
        stmts: &mut Vec<HirStmt>,
    ) -> Result<(), HirLowerError> {
        let entry = match self.lowering.structure.plan().region(region) {
            Some(
                RegionPlan::Branch { entry, .. }
                | RegionPlan::ValueDecision { entry, .. }
                | RegionPlan::Loop { entry, .. }
                | RegionPlan::Unstructured { entry, .. },
            ) => *entry,
            Some(RegionPlan::Block { .. } | RegionPlan::Sequence { .. }) => return Ok(()),
            None => {
                return Err(HirLowerError::MissingPlanRegion {
                    proto: self.proto.index(),
                    region: region.index(),
                });
            }
        };
        let Some(label) = self.lowering.structure.plan().label_for_block(entry) else {
            return Ok(());
        };
        if self
            .lowering
            .structure
            .plan()
            .label(label)
            .is_some_and(|label| label.placement == LabelPlacement::BeforeRegion(region))
        {
            self.emit_label(entry, LabelPlacement::BeforeRegion(region), stmts)?;
        }
        Ok(())
    }

    #[cfg(debug_assertions)]
    fn mark_block_emitted(
        &mut self,
        owner: RegionId,
        block: BlockRef,
        detail: &'static str,
    ) -> Result<(), HirLowerError> {
        if self
            .emitted_blocks
            .get_mut(block.index())
            .is_none_or(|emitted| std::mem::replace(emitted, true))
        {
            return self.invalid_region(owner, detail);
        }
        Ok(())
    }

    fn block_terminator(
        &self,
        owner: RegionId,
        block: BlockRef,
    ) -> Result<&BlockTerminatorPlan, HirLowerError> {
        self.lowering
            .structure
            .plan()
            .block_terminator(block)
            .filter(|terminator| terminator.block == block)
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "block has no dense terminator plan",
            })
    }

    fn invalid_region<T>(
        &self,
        region: RegionId,
        detail: &'static str,
    ) -> Result<T, HirLowerError> {
        Err(HirLowerError::InvalidPlanRegion {
            proto: self.proto.index(),
            region: region.index(),
            detail,
        })
    }
}
