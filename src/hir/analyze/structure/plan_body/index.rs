//! 构建计划 lowering 的稠密反向索引与吸收动作缓存；依赖最终 StructurePlan/SSA，不负责发射 HIR；例如预计算 region 输入和 canonical Move 来源。

use super::*;

impl PlanLoweringIndex {
    pub(super) fn build(
        proto: HirProtoRef,
        lowering: &ProtoLowering<'_>,
    ) -> Result<Self, HirLowerError> {
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
        let mut seen_ssa_temps = vec![false; lowering.bindings.temps.len()];
        let mut shared_ssa_temps = vec![false; lowering.bindings.temps.len()];
        for temp in lowering
            .bindings
            .fixed_temps
            .iter()
            .chain(&lowering.bindings.phi_temps)
        {
            let Some(seen) = seen_ssa_temps.get_mut(temp.index()) else {
                return Err(invalid(root, "SSA binding is outside the HIR temp arena"));
            };
            if std::mem::replace(seen, true) {
                shared_ssa_temps[temp.index()] = true;
            }
        }

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
            shared_ssa_temps,
        })
    }
}

pub(super) fn cache_canonical_move_source(
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

pub(super) fn build_absorbed_region_result_moves(
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
