//! 分类并冻结循环前后、body 与 latch 的值复制动作；依赖 canonical phi copy，不负责 repeat 专属 staging；例如把 VM 控制值与用户可见 carried 值分开。

use super::*;

pub(super) fn freeze_value_actions(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    analysis: &LoopValueAnalysis,
    owner: RegionId,
    payload: &LoopPlanData,
) -> Result<LoopValueActions, StructureError> {
    if !matches!(
        payload.kind,
        LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
    ) {
        return Ok(LoopValueActions::default());
    }
    let control = loop_control_region(plan, owner)?;
    let context = LoopValueContext {
        proto,
        cfg,
        dataflow,
        plan,
        analysis,
        owner,
        control,
        payload,
    };
    let mut actions = LoopValueActions::default();
    if let Some(edge) = payload.control_edges.preheader_body {
        let copies = edge_copies(plan, owner, edge)?;
        let (before, body, elided) = classify_edge_copies(&context, copies)?;
        push_batch(&mut actions.batches, LoopValuePhase::BeforeLoop, before);
        push_batch(&mut actions.batches, LoopValuePhase::BodyPrologue, body);
        actions.elided.extend(elided);
    }

    let mut latch_edges = payload.control_edges.body.clone();
    latch_edges.extend(
        payload
            .control_edges
            .backedges
            .iter()
            .copied()
            .filter(|edge| {
                cfg.edges
                    .get(edge.index())
                    .is_some_and(|cfg_edge| block_is_in_region(plan, control, cfg_edge.from))
            }),
    );
    latch_edges.sort_by_key(|edge| edge.index());
    latch_edges.dedup();
    let latch_copies = uniform_edge_copies(plan, owner, &latch_edges)?;
    let (iteration, elided) = classify_latch_copies(&context, latch_copies)?;
    actions.elided.extend(elided);
    push_batch(
        &mut actions.batches,
        if payload.kind == LoopKindHint::GenericForLike {
            LoopValuePhase::BodyPrologue
        } else {
            LoopValuePhase::LatchEpilogue
        },
        iteration,
    );

    // 普通 body 回边仍由自己的 region 执行真实 carried copy；但 VM-for 的隐藏
    // control copy 已被循环语法消费，不能因此物化一个源码 local。
    for edge in payload.control_edges.backedges.iter().copied() {
        if latch_edges.binary_search(&edge).is_ok() {
            continue;
        }
        if analysis
            .absorbed_owner_by_edge
            .get(edge.index())
            .copied()
            .flatten()
            .and_then(|loop_id| plan.loop_region(loop_id))
            .is_some_and(|absorbed_owner| absorbed_owner != owner)
        {
            continue;
        }
        let edge_plan = plan
            .edge_plan(edge)
            .ok_or_else(|| StructureError::invalid("loop backedge has no final edge plan"))?;
        for copy in &edge_plan.phi_copies {
            let origin = EdgeCopyOrigin {
                edge,
                target: copy.phi_id,
            };
            if classify_copy_source(&context, copy.value, copy.phi_id, &[origin])?.is_none() {
                actions.elided.push(origin);
            }
        }
    }

    let exit = freeze_exit_actions(&context)?;
    push_batch(
        &mut actions.batches,
        LoopValuePhase::BeforeLoop,
        exit.before_loop,
    );
    push_batch(
        &mut actions.batches,
        LoopValuePhase::IterationEpilogue,
        exit.iteration_epilogue,
    );
    push_batch(
        &mut actions.batches,
        LoopValuePhase::AfterLoop,
        exit.after_loop,
    );
    actions.elided.extend(exit.elided);
    actions.elided.sort();
    actions.elided.dedup();
    Ok(actions)
}

pub(super) fn freeze_exit_actions(
    context: &LoopValueContext<'_>,
) -> Result<FrozenExitActions, StructureError> {
    let LoopValueContext {
        plan,
        analysis,
        owner,
        payload,
        ..
    } = *context;
    let preheader = payload
        .control_edges
        .preheader_exit
        .map(|edge| edge_copies(plan, owner, edge))
        .transpose()?
        .unwrap_or_default();
    let mut normal = uniform_edge_copies(plan, owner, &payload.control_edges.exit)?;
    let completion_is_absorbed = payload.normal_tail.as_ref().is_some_and(|tail| {
        tail.completion_exits.iter().all(|edge| {
            analysis
                .absorbed_owner_by_edge
                .get(edge.index())
                .copied()
                .flatten()
                .and_then(|loop_id| plan.loop_region(loop_id))
                == Some(owner)
        })
    });
    if completion_is_absorbed
        && let Some(completion) = normal_tail_completion_copies(plan, owner, payload)?
    {
        normal.extend(completion);
    }
    freeze_exit_copy_actions(context, preheader, normal)
}

/// 只有 normal-tail 的每条完成边都由当前 loop 直接拥有、以 fallthrough 完成，且
/// canonical copy 完全一致时，才允许把它们提升为统一的 loop exit action。其它形状
/// 继续由 tail region 原位执行，保留 guard 语义。
pub(super) fn normal_tail_completion_copies(
    plan: &StructurePlan,
    owner: RegionId,
    payload: &LoopPlanData,
) -> Result<Option<UniformEdgeCopies>, StructureError> {
    let Some(tail) = &payload.normal_tail else {
        return Ok(None);
    };
    let mut expected = None;
    for edge in &tail.completion_exits {
        let edge_plan = plan.edge_plan(*edge).ok_or_else(|| {
            StructureError::invalid("normal-tail completion has no final edge plan")
        })?;
        if edge_plan.owner != owner || edge_plan.transfer != EdgeTransfer::Fallthrough {
            return Ok(None);
        }
        if let Some(expected) = expected
            && expected != edge_plan.phi_copies.as_slice()
        {
            return Ok(None);
        }
        expected = Some(edge_plan.phi_copies.as_slice());
    }
    let Some(expected) = expected.filter(|copies| !copies.is_empty()) else {
        return Ok(None);
    };

    let mut syntax_targets = BTreeSet::new();
    for edge in payload
        .control_edges
        .preheader_exit
        .into_iter()
        .chain(payload.control_edges.exit.iter().copied())
    {
        let edge_plan = plan
            .edge_plan(edge)
            .ok_or_else(|| StructureError::invalid("loop syntax exit has no final edge plan"))?;
        if edge_plan.owner == owner {
            syntax_targets.extend(edge_plan.phi_copies.iter().map(|copy| copy.phi_id));
        }
    }
    if expected
        .iter()
        .any(|copy| syntax_targets.contains(&copy.phi_id))
    {
        return Ok(None);
    }
    uniform_edge_copies(plan, owner, &tail.completion_exits).map(Some)
}

pub(super) fn freeze_exit_copy_actions(
    context: &LoopValueContext<'_>,
    preheader: Vec<(EdgeRef, crate::structure::PhiEdgeCopy)>,
    normal: UniformEdgeCopies,
) -> Result<FrozenExitActions, StructureError> {
    let LoopValueContext {
        dataflow,
        plan,
        payload,
        ..
    } = *context;
    if preheader.is_empty() && normal.is_empty() {
        return Ok(FrozenExitActions::default());
    }

    let mut by_target = BTreeMap::<
        PhiId,
        (
            Option<(SsaValue, Vec<EdgeCopyOrigin>)>,
            Option<(SsaValue, Vec<EdgeCopyOrigin>)>,
        ),
    >::new();
    for (edge, copy) in preheader {
        by_target.entry(copy.phi_id).or_default().0 = Some((
            copy.value,
            vec![EdgeCopyOrigin {
                edge,
                target: copy.phi_id,
            }],
        ));
    }
    for (copy, origins) in normal {
        let entry = by_target.entry(copy.phi_id).or_default();
        match &mut entry.1 {
            Some((value, existing_origins)) if *value == copy.value => {
                existing_origins.extend(origins);
            }
            Some(_) => {
                return Err(StructureError::invalid(
                    "loop exit syntax edges disagree on their frozen copies",
                ));
            }
            slot @ None => {
                *slot = Some((copy.value, origins));
            }
        }
    }

    let break_targets = payload
        .break_edges
        .iter()
        .copied()
        .filter(|edge| {
            !payload.control_edges.exit.contains(edge)
                && payload.control_edges.preheader_exit != Some(*edge)
        })
        .flat_map(|edge| {
            plan.edge_plan(edge)
                .into_iter()
                .flat_map(|plan| plan.phi_copies.iter().map(|copy| copy.phi_id))
        })
        .collect::<BTreeSet<_>>();

    let mut actions = FrozenExitActions::default();
    for (target, (zero_value, normal_value)) in by_target {
        if break_targets.contains(&target) {
            let (value, origins) = common_exit_value(
                target,
                zero_value,
                normal_value,
                "for early-break state has no common normal default",
            )?;
            match classify_copy_source(context, value, target, &origins)? {
                Some(source) => actions.before_loop.push(LoopValueWrite {
                    target,
                    source,
                    origins,
                }),
                None => actions.elided.extend(origins),
            }
            continue;
        }

        let reg = dataflow
            .phi_candidate(target)
            .ok_or_else(|| StructureError::invalid("for exit action targets a missing phi"))?
            .reg;
        if let Some(header) = payload.header_values.iter().find(|value| value.reg == reg) {
            let zero_matches = zero_value.as_ref().is_none_or(|(value, _)| {
                header
                    .outside_arm
                    .values()
                    .any(|incoming| incoming == *value)
            });
            let normal_matches = normal_value.as_ref().is_none_or(|(value, _)| {
                *value == SsaValue::Phi(header.phi_id)
                    || header
                        .inside_arm
                        .values()
                        .any(|incoming| incoming == *value)
            });
            if !zero_matches || !normal_matches {
                return Err(StructureError::invalid(
                    "for exit actions contradict the selected loop state",
                ));
            }
            let mut origins = Vec::new();
            if let Some((_, source)) = zero_value {
                origins.extend(source);
            }
            if let Some((_, source)) = normal_value {
                origins.extend(source);
            }
            origins.sort();
            origins.dedup();
            actions.after_loop.push(LoopValueWrite {
                target,
                source: LoopValueSource::Carried(header.phi_id),
                origins,
            });
            continue;
        }

        if let (Some((zero, zero_origins)), Some((normal, normal_origins))) =
            (zero_value.as_ref(), normal_value.as_ref())
            && zero != normal
        {
            if let Some(source) = classify_copy_source(context, *zero, target, zero_origins)? {
                actions.before_loop.push(LoopValueWrite {
                    target,
                    source,
                    origins: zero_origins.clone(),
                });
            } else {
                actions.elided.extend(zero_origins.iter().copied());
            }
            if let Some(source) = classify_copy_source(context, *normal, target, normal_origins)? {
                actions.iteration_epilogue.push(LoopValueWrite {
                    target,
                    source,
                    origins: normal_origins.clone(),
                });
            } else {
                actions.elided.extend(normal_origins.iter().copied());
            }
            continue;
        }

        let (value, origins) = common_exit_value(
            target,
            zero_value,
            normal_value,
            "for exit actions have no common state identity",
        )?;
        match classify_copy_source(context, value, target, &origins)? {
            Some(source) => actions.after_loop.push(LoopValueWrite {
                target,
                source,
                origins,
            }),
            None => actions.elided.extend(origins),
        }
    }
    Ok(actions)
}

pub(super) fn common_exit_value(
    target: PhiId,
    zero_value: Option<(SsaValue, Vec<EdgeCopyOrigin>)>,
    normal_value: Option<(SsaValue, Vec<EdgeCopyOrigin>)>,
    error: &str,
) -> Result<(SsaValue, Vec<EdgeCopyOrigin>), StructureError> {
    match (zero_value, normal_value) {
        (Some((zero, mut zero_origins)), Some((normal, normal_origins))) if zero == normal => {
            zero_origins.extend(normal_origins);
            zero_origins.sort();
            zero_origins.dedup();
            Ok((zero, zero_origins))
        }
        (Some((value, origins)), None) | (None, Some((value, origins))) => Ok((value, origins)),
        (zero, normal) => Err(StructureError::invalid(format!(
            "{error}: {target} zero={zero:?} normal={normal:?}"
        ))),
    }
}

type ClassifiedEdgeCopies = (
    Vec<LoopValueWrite>,
    Vec<LoopValueWrite>,
    Vec<EdgeCopyOrigin>,
);

pub(super) fn classify_edge_copies(
    context: &LoopValueContext<'_>,
    copies: Vec<(EdgeRef, crate::structure::PhiEdgeCopy)>,
) -> Result<ClassifiedEdgeCopies, StructureError> {
    let mut before = Vec::new();
    let mut body = Vec::new();
    let mut elided = Vec::new();
    for (edge, copy) in copies {
        let mut origins = vec![EdgeCopyOrigin {
            edge,
            target: copy.phi_id,
        }];
        origins.sort();
        let Some(source) = classify_copy_source(context, copy.value, copy.phi_id, &origins)? else {
            elided.extend(origins);
            continue;
        };
        let write = LoopValueWrite {
            target: copy.phi_id,
            source,
            origins,
        };
        if matches!(write.source, LoopValueSource::Binding(_)) {
            body.push(write);
        } else {
            before.push(write);
        }
    }
    Ok((before, body, elided))
}

pub(super) fn classify_latch_copies(
    context: &LoopValueContext<'_>,
    copies: UniformEdgeCopies,
) -> Result<(Vec<LoopValueWrite>, Vec<EdgeCopyOrigin>), StructureError> {
    let mut writes = Vec::new();
    let mut elided = Vec::new();
    for (copy, mut origins) in copies {
        origins.sort();
        let Some(source) = classify_latch_copy_source(context, copy.value, copy.phi_id, &origins)?
        else {
            elided.extend(origins);
            continue;
        };
        writes.push(LoopValueWrite {
            target: copy.phi_id,
            source,
            origins,
        });
    }
    Ok((writes, elided))
}

pub(super) fn classify_latch_copy_source(
    context: &LoopValueContext<'_>,
    value: SsaValue,
    target: PhiId,
    origins: &[EdgeCopyOrigin],
) -> Result<Option<LoopValueSource>, StructureError> {
    if context.payload.kind == LoopKindHint::NumericForLike
        && target_is_vm_for_control(
            context.proto,
            context.dataflow,
            context.plan,
            context.payload,
            target,
        )
        && context
            .analysis
            .value_is_vm_for_control(context.proto, context.dataflow, value)
    {
        // 下一轮 body 会先由 BodyPrologue 重新绑定；normal latch 的同值写回不可观察。
        // 仍调用通用分类以保留 escape 校验，不能把同一规则扩大到 preheader。
        return classify_value_source(context, value, target).map(|_| None);
    }
    classify_copy_source(context, value, target, origins)
}

pub(super) fn classify_copy_source(
    context: &LoopValueContext<'_>,
    value: SsaValue,
    target: PhiId,
    origins: &[EdgeCopyOrigin],
) -> Result<Option<LoopValueSource>, StructureError> {
    if !origins.is_empty()
        && origins.iter().all(|origin| {
            edge_copy_is_ancestor_vm_control(
                context.proto,
                context.dataflow,
                context.plan,
                context.analysis,
                context.owner,
                origin.edge,
                crate::structure::PhiEdgeCopy {
                    phi_id: target,
                    value,
                },
            )
        })
    {
        return Ok(None);
    }
    classify_value_source(context, value, target)
}

pub(super) fn classify_value_source(
    context: &LoopValueContext<'_>,
    value: SsaValue,
    target: PhiId,
) -> Result<Option<LoopValueSource>, StructureError> {
    if target_is_vm_for_control(
        context.proto,
        context.dataflow,
        context.plan,
        context.payload,
        target,
    ) {
        let numeric_binding = context.payload.kind == LoopKindHint::NumericForLike;
        let syntax_region = if numeric_binding {
            context.owner
        } else {
            context.control
        };
        if context
            .analysis
            .phi_observed_outside(context.plan, syntax_region, target)
        {
            return Err(StructureError::invalid(format!(
                "VM for-control value {value:?} for {target} escapes loop header {} syntax region #{}",
                context.payload.header,
                syntax_region.index(),
            )));
        }
        if !numeric_binding
            || numeric_binding_is_protocol_only(context.proto, context.dataflow, target)
        {
            return Ok(None);
        }
    }
    if let Some(binding) = binding_source(context.dataflow, context.payload, value) {
        return Ok(Some(LoopValueSource::Binding(binding)));
    }
    if context
        .analysis
        .value_is_vm_for_control(context.proto, context.dataflow, value)
    {
        if context
            .analysis
            .phi_observed_outside(context.plan, context.control, target)
        {
            return Err(StructureError::invalid(format!(
                "VM for-control value {value:?} for {target} escapes loop header {} control region #{}",
                context.payload.header,
                context.control.index(),
            )));
        }
        return Ok(None);
    }
    Ok(Some(LoopValueSource::Ssa(value)))
}

pub(super) fn numeric_binding_is_protocol_only(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    target: PhiId,
) -> bool {
    dataflow
        .phi_phi_uses
        .get(target.index())
        .is_some_and(Vec::is_empty)
        && dataflow.phi_uses.get(target.index()).is_some_and(|uses| {
            uses.iter().all(|site| {
                matches!(
                    proto.instrs.get(site.instr.index()),
                    Some(LowInstr::NumericForLoop(loop_))
                        if loop_.index == loop_.binding && site.reg == loop_.binding
                )
            })
        })
}

pub(super) fn target_is_vm_for_control(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    payload: &LoopPlanData,
    target: PhiId,
) -> bool {
    let Some(candidate) = dataflow.phi_candidate(target) else {
        return false;
    };
    match payload.source_bindings {
        Some(LoopSourceBindings::Numeric(binding)) => {
            payload.kind == LoopKindHint::NumericForLike
                && candidate.block == payload.header
                && candidate.reg == binding
        }
        Some(LoopSourceBindings::Generic(_)) if payload.kind == LoopKindHint::GenericForLike => {
            let Some(terminator) = plan.block_terminator(payload.header) else {
                return false;
            };
            let Some((_, call, loop_)) = generic_for_header_instrs(proto, terminator) else {
                return false;
            };
            candidate.block == payload.header
                && candidate.reg == call.control
                && candidate.reg == loop_.control_target
        }
        _ => false,
    }
}

pub(super) fn binding_source(
    dataflow: &DataflowFacts,
    payload: &LoopPlanData,
    value: SsaValue,
) -> Option<Reg> {
    let reg = match value {
        SsaValue::Def(def) => dataflow.def_reg(def),
        SsaValue::Phi(phi) => dataflow.phi_candidate(phi)?.reg,
        SsaValue::Entry(reg) => reg,
    };
    match payload.source_bindings? {
        LoopSourceBindings::Numeric(binding) if reg == binding => Some(reg),
        LoopSourceBindings::Generic(bindings)
            if reg.index() >= bindings.start.index()
                && reg.index() < bindings.start.index() + bindings.len =>
        {
            Some(reg)
        }
        _ => None,
    }
}

pub(super) fn edge_copies(
    plan: &StructurePlan,
    owner: RegionId,
    edge: EdgeRef,
) -> Result<Vec<(EdgeRef, crate::structure::PhiEdgeCopy)>, StructureError> {
    let plan = plan
        .edge_plan(edge)
        .ok_or_else(|| StructureError::invalid("loop syntax edge has no final edge plan"))?;
    Ok(if plan.owner == owner {
        plan.phi_copies
            .iter()
            .copied()
            .map(|copy| (edge, copy))
            .collect()
    } else {
        Vec::new()
    })
}

pub(super) fn uniform_edge_copies(
    plan: &StructurePlan,
    owner: RegionId,
    edges: &[EdgeRef],
) -> Result<UniformEdgeCopies, StructureError> {
    let Some(first) = edges.first().copied() else {
        return Ok(Vec::new());
    };
    let first_copies = edge_copies(plan, owner, first)?;
    let mut uniform = first_copies
        .iter()
        .map(|(_, copy)| {
            (
                *copy,
                vec![EdgeCopyOrigin {
                    edge: first,
                    target: copy.phi_id,
                }],
            )
        })
        .collect::<Vec<_>>();
    for edge in &edges[1..] {
        let copies = edge_copies(plan, owner, *edge)?;
        if copies.len() != uniform.len()
            || copies
                .iter()
                .map(|(_, copy)| *copy)
                .zip(uniform.iter().map(|(copy, _)| *copy))
                .any(|(left, right)| left != right)
        {
            return Err(StructureError::invalid(
                "alternative for syntax edges require different value actions",
            ));
        }
        for ((_, copy), (_, origins)) in copies.into_iter().zip(uniform.iter_mut()) {
            origins.push(EdgeCopyOrigin {
                edge: *edge,
                target: copy.phi_id,
            });
        }
    }
    Ok(uniform)
}

pub(super) fn push_batch(
    batches: &mut Vec<LoopValueActionBatch>,
    phase: LoopValuePhase,
    writes: Vec<LoopValueWrite>,
) {
    if writes.is_empty() {
        return;
    }
    batches.push(LoopValueActionBatch { phase, writes });
}

pub(super) fn edge_is_loop_body(payload: &LoopPlanData, edge: EdgeRef) -> bool {
    payload.control_edges.preheader_body == Some(edge) || payload.control_edges.body.contains(&edge)
}

pub(super) fn edge_is_loop_exit(payload: &LoopPlanData, edge: EdgeRef) -> bool {
    payload.control_edges.preheader_exit == Some(edge) || payload.control_edges.exit.contains(&edge)
}

pub(super) fn edge_emits_no_stmt(plan: &StructurePlan, edge: EdgeRef) -> bool {
    plan.edge_plan(edge).is_some_and(|edge_plan| {
        edge_plan.phi_copies.is_empty()
            && edge_plan.actions_before_trailing_cleanup().is_none()
            && !matches!(
                edge_plan.transfer,
                EdgeTransfer::Break(_) | EdgeTransfer::Continue(_) | EdgeTransfer::Goto(..)
            )
            && plan.loop_exit_tail_for_edge(edge).is_none()
    })
}
