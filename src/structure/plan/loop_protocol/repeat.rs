//! 冻结 repeat 的 staged result 与 native/break 退出合同；依赖终端边动作和外层 loop 所有权，不负责其他 loop kind；例如决定尾分支是否可直接保留 repeat。

use super::*;

pub(super) fn freeze_repeat_value_plan(
    context: &LoopValueContext<'_>,
    backedge: EdgeRef,
    exit: EdgeRef,
) -> Result<LoopRepeatValuePlan, StructureError> {
    let LoopValueContext {
        proto,
        cfg,
        dataflow,
        plan,
        analysis,
        owner,
        payload,
        ..
    } = *context;
    let Some(edge_plan) = plan.edge_plan(exit) else {
        return Err(StructureError::invalid(
            "repeat exit has no final edge plan",
        ));
    };
    let early_breaks = payload
        .break_edges
        .iter()
        .copied()
        .filter(|edge| *edge != exit)
        .collect::<Vec<_>>();
    let early_break_copies = early_breaks
        .iter()
        .map(|edge| crate::structure::phi_facts::effective_edge_copies(cfg, dataflow, plan, *edge))
        .collect::<Result<Vec<_>, _>>()?;
    let mut value_plan = LoopRepeatValuePlan::default();
    let backedge_plan = plan
        .edge_plan(backedge)
        .ok_or_else(|| StructureError::invalid("repeat backedge has no final edge plan"))?;
    if matches!(backedge_plan.transfer, EdgeTransfer::LoopBack(target) if target == owner)
        && backedge_plan.actions_before_trailing_cleanup().is_none()
        && backedge_plan.forward_route.is_none()
        && plan.loop_exit_tail_for_edge(backedge).is_none()
    {
        value_plan
            .backedge_copies
            .extend(crate::structure::phi_facts::effective_edge_copies(
                cfg, dataflow, plan, backedge,
            )?);
    }
    value_plan
        .exit_copies
        .extend(crate::structure::phi_facts::effective_edge_copies(
            cfg, dataflow, plan, exit,
        )?);
    for copy in value_plan.exit_copies.iter().copied() {
        if edge_copy_is_ancestor_vm_control(proto, dataflow, plan, analysis, owner, exit, copy) {
            value_plan.outer_loop_owned_exit_copies.push(copy);
        }
    }
    if !matches!(edge_plan.transfer, EdgeTransfer::Break(target) if target == owner)
        || edge_plan.actions_before_trailing_cleanup().is_some()
        || edge_plan.forward_route.is_some()
        || plan.loop_exit_tail_for_edge(exit).is_some()
    {
        return Ok(value_plan);
    }
    let Some(condition_header) = payload
        .condition
        .and_then(|condition| plan.condition(condition))
        .and_then(|condition| condition.header())
    else {
        return Ok(value_plan);
    };
    let local_exit_copies = locally_owned_repeat_exit_copies(&value_plan).collect::<Vec<_>>();
    let mut early_break_coverage = vec![0usize; dataflow.phi_candidates.len()];
    let mut duplicate_early_break_copy = vec![false; dataflow.phi_candidates.len()];
    let mut seen_at_break = vec![usize::MAX; dataflow.phi_candidates.len()];
    let mut early_break_transfers_valid = true;
    for (break_index, (edge, copies)) in early_breaks.iter().zip(&early_break_copies).enumerate() {
        early_break_transfers_valid &= plan
            .edge_plan(*edge)
            .is_some_and(|edge_plan| {
                matches!(edge_plan.transfer, EdgeTransfer::Break(target) if target == owner)
            });
        for early in copies {
            let Some(seen) = seen_at_break.get_mut(early.phi_id.index()) else {
                continue;
            };
            if *seen == break_index {
                duplicate_early_break_copy[early.phi_id.index()] = true;
            } else {
                *seen = break_index;
                early_break_coverage[early.phi_id.index()] += 1;
            }
        }
    }
    for copy in &local_exit_copies {
        let early_breaks_cover_target = early_break_transfers_valid
            && (early_breaks.is_empty()
                || early_break_coverage.get(copy.phi_id.index()).copied()
                    == Some(early_breaks.len())
                    && !duplicate_early_break_copy
                        .get(copy.phi_id.index())
                        .copied()
                        .unwrap_or(true));
        if copy.value == SsaValue::Phi(copy.phi_id)
            || !repeat_normal_value_is_stable(
                plan,
                dataflow,
                payload.header,
                condition_header,
                copy.value,
            )
            || !early_breaks_cover_target
        {
            value_plan.staged_results.clear();
            return Ok(value_plan);
        }
        value_plan.staged_results.push(LoopRepeatStagedResult {
            target: copy.phi_id,
            normal_value: copy.value,
        });
    }
    Ok(value_plan)
}

pub(super) fn edge_copy_is_ancestor_vm_control(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    analysis: &LoopValueAnalysis,
    owner: RegionId,
    exit: EdgeRef,
    copy: crate::structure::PhiEdgeCopy,
) -> bool {
    let Some(phi) = plan.phi_plan(copy.phi_id) else {
        return false;
    };
    let mut incomings = phi
        .incomings
        .iter()
        .filter(|incoming| incoming.edge == Some(exit));
    let Some(incoming) = incomings.next() else {
        return false;
    };
    let super::super::PhiIncomingDisposition::LoopCarried(region) = incoming.disposition else {
        return false;
    };
    if incomings.next().is_some()
        || incoming.value != copy.value
        || region == owner
        || !plan.region_contains(region, owner)
    {
        return false;
    }
    let Some(RegionPlan::Loop {
        plan: loop_id,
        control,
        ..
    }) = plan.region(region)
    else {
        return false;
    };
    let Some(payload) = plan.loop_(*loop_id) else {
        return false;
    };
    matches!(
        payload.kind,
        LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
    ) && analysis.value_is_vm_for_control(proto, dataflow, copy.value)
        && !analysis.phi_observed_outside(plan, *control, copy.phi_id)
}

pub(super) fn validate_repeat_outer_loop_owned_exit_copies(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    analysis: &LoopValueAnalysis,
    owner: RegionId,
    repeat: &LoopRepeatProtocol,
) -> Result<(), StructureError> {
    let exit = repeat.condition.exit_edge;
    if repeat.value_plan.exit_copies
        != crate::structure::phi_facts::effective_edge_copies(cfg, dataflow, plan, exit)?
    {
        return Err(StructureError::invalid(
            "repeat exit value plan does not match its canonical edge copies",
        ));
    }

    let mut exit_values = vec![None; dataflow.phi_candidates.len()];
    for copy in &repeat.value_plan.exit_copies {
        let slot = exit_values
            .get_mut(copy.phi_id.index())
            .ok_or_else(|| StructureError::invalid("repeat exit copy targets a missing phi"))?;
        if slot.replace(copy.value).is_some() {
            return Err(StructureError::invalid(
                "repeat exit contains duplicate canonical phi copies",
            ));
        }
    }
    let mut marked = vec![false; dataflow.phi_candidates.len()];
    for copy in &repeat.value_plan.outer_loop_owned_exit_copies {
        let slot = marked.get_mut(copy.phi_id.index()).ok_or_else(|| {
            StructureError::invalid("repeat outer-loop-owned copy targets a missing phi")
        })?;
        if std::mem::replace(slot, true)
            || exit_values.get(copy.phi_id.index()).copied().flatten() != Some(copy.value)
        {
            return Err(StructureError::invalid(
                "repeat exit has duplicate or non-canonical outer-loop-owned copies",
            ));
        }

        let phi = plan.phi_plan(copy.phi_id).ok_or_else(|| {
            StructureError::invalid("repeat outer-loop-owned copy targets a missing phi")
        })?;
        let mut incomings = phi
            .incomings
            .iter()
            .filter(|incoming| incoming.edge == Some(exit));
        let incoming = incomings.next().ok_or_else(|| {
            StructureError::invalid("repeat outer-loop-owned copy has no exact phi incoming")
        })?;
        let super::super::PhiIncomingDisposition::LoopCarried(outer) = incoming.disposition else {
            return Err(StructureError::invalid(
                "repeat outer-loop-owned copy is not owned by LoopCarried",
            ));
        };
        if incomings.next().is_some()
            || incoming.value != copy.value
            || outer == owner
            || !plan.region_contains(outer, owner)
        {
            return Err(StructureError::invalid(
                "repeat outer-loop-owned copy has an ambiguous or non-ancestor owner",
            ));
        }
        let Some(RegionPlan::Loop {
            plan: outer_loop,
            control,
            ..
        }) = plan.region(outer)
        else {
            return Err(StructureError::invalid(
                "repeat outer-loop-owned copy owner is not a loop region",
            ));
        };
        let outer_payload = plan.loop_(*outer_loop).ok_or_else(|| {
            StructureError::invalid("repeat outer-loop-owned copy owner has no loop payload")
        })?;
        if !matches!(
            outer_payload.kind,
            LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
        ) || !analysis.value_is_vm_for_control(proto, dataflow, copy.value)
            || analysis.phi_observed_outside(plan, *control, copy.phi_id)
        {
            return Err(StructureError::invalid(
                "repeat outer-loop-owned copy is not an unobservable ancestor VM-for control value",
            ));
        }
    }

    for copy in &repeat.value_plan.exit_copies {
        let proven =
            edge_copy_is_ancestor_vm_control(proto, dataflow, plan, analysis, owner, exit, *copy);
        if proven != marked.get(copy.phi_id.index()).copied().unwrap_or(false) {
            return Err(StructureError::invalid(
                "repeat exit copy partition disagrees with its outer loop-carried owner proof",
            ));
        }
    }
    Ok(())
}

pub(super) fn repeat_normal_value_is_stable(
    plan: &StructurePlan,
    dataflow: &DataflowFacts,
    loop_header: BlockRef,
    condition_header: BlockRef,
    value: SsaValue,
) -> bool {
    match value {
        SsaValue::Entry(_) => true,
        SsaValue::Phi(phi) => plan
            .phi_plan(phi)
            .is_some_and(|phi| phi.block == condition_header),
        SsaValue::Def(def) => dataflow.defs.get(def.index()).is_some_and(|definition| {
            definition.block == condition_header
                || dataflow.block_entry_value(loop_header, definition.reg) == value
        }),
    }
}

pub(super) fn locally_owned_repeat_exit_copies(
    value_plan: &LoopRepeatValuePlan,
) -> impl Iterator<Item = crate::structure::PhiEdgeCopy> + '_ {
    let mut outer = value_plan
        .outer_loop_owned_exit_copies
        .iter()
        .copied()
        .peekable();
    value_plan.exit_copies.iter().copied().filter(move |copy| {
        if outer.peek() == Some(copy) {
            outer.next();
            false
        } else {
            true
        }
    })
}

pub(super) fn repeat_backedge_copies_are_movable(
    plan: &StructurePlan,
    owner: RegionId,
    backedge: EdgeRef,
    value_plan: &LoopRepeatValuePlan,
) -> Result<bool, StructureError> {
    let edge_plan = plan
        .edge_plan(backedge)
        .ok_or_else(|| StructureError::invalid("repeat backedge has no final edge plan"))?;
    Ok(!value_plan.backedge_copies.is_empty()
        && matches!(edge_plan.transfer, EdgeTransfer::LoopBack(target) if target == owner)
        && edge_plan.phi_copies == value_plan.backedge_copies
        && edge_plan.actions_before_trailing_cleanup().is_none()
        && edge_plan.forward_route.is_none()
        && plan.loop_exit_tail_for_edge(backedge).is_none())
}

pub(super) fn repeat_exit_is_plain_break(
    plan: &StructurePlan,
    owner: RegionId,
    exit: EdgeRef,
    value_plan: &LoopRepeatValuePlan,
) -> Result<bool, StructureError> {
    let Some(edge_plan) = plan.edge_plan(exit) else {
        return Err(StructureError::invalid(
            "repeat exit has no final edge plan",
        ));
    };
    Ok(
        (matches!(edge_plan.transfer, EdgeTransfer::Break(target) if target == owner)
            || edge_plan.transfer == EdgeTransfer::BranchArm(super::super::BranchArm::LoopExit))
            && plan.loop_exit_tail_for_edge(exit).is_none()
            && locally_owned_repeat_exit_copies(value_plan)
                .next()
                .is_none(),
    )
}

pub(super) fn repeat_exit_is_staged_break(
    plan: &StructurePlan,
    owner: RegionId,
    exit: EdgeRef,
    value_plan: &LoopRepeatValuePlan,
) -> Result<bool, StructureError> {
    let edge_plan = plan
        .edge_plan(exit)
        .ok_or_else(|| StructureError::invalid("repeat exit has no final edge plan"))?;
    let staged_targets = value_plan
        .staged_results
        .iter()
        .map(|result| result.target)
        .collect::<BTreeSet<_>>();
    let exit_targets = locally_owned_repeat_exit_copies(value_plan)
        .filter(|copy| copy.value != SsaValue::Phi(copy.phi_id))
        .map(|copy| copy.phi_id)
        .collect::<BTreeSet<_>>();
    Ok(!exit_targets.is_empty()
        && staged_targets == exit_targets
        && matches!(edge_plan.transfer, EdgeTransfer::Break(target) if target == owner)
        && edge_plan.actions_before_trailing_cleanup().is_none()
        && edge_plan.forward_route.is_none()
        && plan.loop_exit_tail_for_edge(exit).is_none())
}

pub(super) fn repeat_exit_can_follow_native(
    plan: &StructurePlan,
    owner: RegionId,
    payload: &LoopPlanData,
    exit: EdgeRef,
) -> Result<bool, StructureError> {
    let edge_plan = plan
        .edge_plan(exit)
        .ok_or_else(|| StructureError::invalid("repeat exit has no final edge plan"))?;
    let has_early_break = payload.break_edges.iter().copied().any(|edge| {
        edge != exit
            && plan.edge_plan(edge).is_some_and(
                |edge| matches!(edge.transfer, EdgeTransfer::Break(target) if target == owner),
            )
    });
    if has_early_break
        || edge_plan.actions_before_trailing_cleanup().is_some()
        || plan.loop_exit_tail_for_edge(exit).is_some()
    {
        return Ok(false);
    }
    Ok(match edge_plan.transfer {
        EdgeTransfer::Fallthrough | EdgeTransfer::BranchArm(_) | EdgeTransfer::Goto(..) => true,
        EdgeTransfer::LoopBack(target)
        | EdgeTransfer::Break(target)
        | EdgeTransfer::Continue(target) => target != owner,
        EdgeTransfer::Unreachable | EdgeTransfer::Return | EdgeTransfer::TailCall => false,
    })
}
