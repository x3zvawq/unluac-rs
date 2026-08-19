//! 按 loop kind 冻结 while/repeat/numeric-for/generic-for VM 协议；依赖块终结器和区域完成端口，不负责 phi 值动作；例如核对 for header/preheader 指令身份。

use super::*;

#[derive(Clone, Copy)]
pub(super) struct LoopProtocolContext<'a> {
    pub(super) proto: &'a LoweredProto,
    pub(super) cfg: &'a Cfg,
    pub(super) dataflow: &'a DataflowFacts,
    pub(super) plan: &'a StructurePlan,
    pub(super) analysis: &'a LoopValueAnalysis,
    pub(super) region: RegionId,
    pub(super) payload: &'a LoopPlanData,
    pub(super) body_completes_normally: bool,
}

pub(super) fn freeze_protocol(
    context: &LoopProtocolContext<'_>,
) -> Result<LoopVmProtocol, StructureError> {
    let LoopProtocolContext {
        proto,
        cfg,
        dataflow,
        plan,
        analysis,
        region,
        payload,
        body_completes_normally,
    } = *context;
    Ok(match payload.kind {
        LoopKindHint::WhileLike => LoopVmProtocol::While(freeze_condition_protocol(plan, payload)?),
        LoopKindHint::RepeatLike => {
            let condition = freeze_condition_protocol(plan, payload)?;
            let prefix_placement = payload.condition_prefix_placement.ok_or_else(|| {
                StructureError::invalid("repeat loop is missing its condition prefix placement")
            })?;
            let context = LoopValueContext {
                proto,
                cfg,
                dataflow,
                plan,
                analysis,
                owner: region,
                control: loop_control_region(plan, region)?,
                payload,
            };
            let value_plan =
                freeze_repeat_value_plan(&context, condition.body_edge, condition.exit_edge)?;
            let plain_backedge = edge_emits_no_stmt(plan, condition.body_edge)
                || repeat_backedge_copies_are_movable(
                    plan,
                    region,
                    condition.body_edge,
                    &value_plan,
                )?;
            let plain_break =
                repeat_exit_is_plain_break(plan, region, condition.exit_edge, &value_plan)?;
            let staged_break =
                repeat_exit_is_staged_break(plan, region, condition.exit_edge, &value_plan)?;
            let exit_after_loop =
                repeat_exit_can_follow_native(plan, region, payload, condition.exit_edge)?;
            let has_direct_continue = payload.control_edges.continues.iter().copied().any(|edge| {
                plan.edge_plan(edge).is_some_and(|edge| {
                    matches!(
                        edge.transfer,
                        EdgeTransfer::Continue(_) | EdgeTransfer::Goto(..)
                    )
                })
            });
            let form = if plain_backedge && (plain_break || staged_break || exit_after_loop) {
                LoopRepeatForm::Native
            } else {
                LoopRepeatForm::TailBranchRepeat
            };
            if (has_direct_continue || exit_after_loop) && form != LoopRepeatForm::Native {
                return Err(StructureError::invalid(format!(
                    "repeat requiring native exit has no complete protocol: backedge={} plain={}, exit={} plain={} staged={} post={}, backedge-plan={:?}, exit-plan={:?}, values={:?}",
                    condition.body_edge,
                    plain_backedge,
                    condition.exit_edge,
                    plain_break,
                    staged_break,
                    exit_after_loop,
                    plan.edge_plan(condition.body_edge),
                    plan.edge_plan(condition.exit_edge),
                    value_plan,
                )));
            }
            LoopVmProtocol::Repeat(LoopRepeatProtocol {
                condition,
                prefix_placement,
                form,
                exit_after_loop,
                value_plan,
            })
        }
        LoopKindHint::NumericForLike => LoopVmProtocol::NumericFor(freeze_numeric_for_protocol(
            proto,
            plan,
            region,
            payload,
            body_completes_normally,
        )?),
        LoopKindHint::GenericForLike => LoopVmProtocol::GenericFor(freeze_generic_for_protocol(
            proto,
            cfg,
            plan,
            region,
            payload,
            body_completes_normally,
        )?),
        LoopKindHint::WhileTrueLike => LoopVmProtocol::WhileTrue,
        LoopKindHint::Unknown => {
            if payload.condition.is_some()
                && (!payload.control_edges.body.is_empty()
                    || !payload.control_edges.exit.is_empty())
            {
                LoopVmProtocol::While(freeze_condition_protocol(plan, payload)?)
            } else {
                LoopVmProtocol::WhileTrue
            }
        }
    })
}

pub(super) fn freeze_condition_protocol(
    plan: &StructurePlan,
    payload: &LoopPlanData,
) -> Result<LoopConditionProtocol, StructureError> {
    let condition_id = payload
        .condition
        .ok_or_else(|| StructureError::invalid("loop is missing its frozen condition plan"))?;
    let condition = plan
        .condition(condition_id)
        .ok_or_else(|| StructureError::invalid("loop condition references a missing payload"))?;
    let truthy_body = edge_is_loop_body(payload, condition.truthy);
    let falsy_body = edge_is_loop_body(payload, condition.falsy);
    let truthy_exit = edge_is_loop_exit(payload, condition.truthy);
    let falsy_exit = edge_is_loop_exit(payload, condition.falsy);
    if truthy_body == falsy_body || truthy_exit == falsy_exit || !(truthy_exit || falsy_exit) {
        return Err(StructureError::invalid(format!(
            "loop condition terminals contradict frozen syntax roles: truthy={} body={} exit={}, falsy={} body={} exit={}, control={:?}",
            condition.truthy,
            truthy_body,
            truthy_exit,
            condition.falsy,
            falsy_body,
            falsy_exit,
            payload.control_edges,
        )));
    }
    let body_on_truthy = truthy_body;
    Ok(LoopConditionProtocol {
        condition: condition_id,
        body_edge: if body_on_truthy {
            condition.truthy
        } else {
            condition.falsy
        },
        exit_edge: if body_on_truthy {
            condition.falsy
        } else {
            condition.truthy
        },
        body_on_truthy,
    })
}

pub(super) fn freeze_numeric_for_protocol(
    proto: &LoweredProto,
    plan: &StructurePlan,
    region: RegionId,
    payload: &LoopPlanData,
    body_completes_normally: bool,
) -> Result<NumericForProtocol, StructureError> {
    let preheader = payload
        .preheader_block
        .ok_or_else(|| StructureError::invalid("numeric-for loop has no frozen preheader block"))?;
    let terminator = plan
        .block_terminator(preheader)
        .ok_or_else(|| StructureError::invalid("numeric-for preheader has no terminator plan"))?;
    let BlockTerminatorKind::NumericForInit { instr, body, exit } = terminator.kind else {
        return Err(StructureError::invalid(
            "numeric-for preheader does not end with NumericForInit",
        ));
    };
    let Some(LowInstr::NumericForInit(init)) = proto.instrs.get(instr.index()) else {
        return Err(StructureError::invalid(
            "numeric-for protocol references a non-init opcode",
        ));
    };
    if payload.control_edges.preheader_body != Some(body)
        || payload.control_edges.preheader_exit != Some(exit)
        || !matches!(payload.source_bindings, Some(LoopSourceBindings::Numeric(reg)) if reg == init.binding)
    {
        return Err(StructureError::invalid(format!(
            "numeric-for loop #{} contradicts its VM preheader contract",
            region.index()
        )));
    }
    Ok(NumericForProtocol {
        init_instr: instr,
        body_edge: body,
        exit_edge: exit,
        body_completes_normally,
        index: init.index,
        limit: init.limit,
        step: init.step,
        binding: init.binding,
    })
}

pub(super) fn freeze_generic_for_protocol(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &StructurePlan,
    region: RegionId,
    payload: &LoopPlanData,
    body_completes_normally: bool,
) -> Result<GenericForProtocol, StructureError> {
    let header_terminator = plan
        .block_terminator(payload.header)
        .ok_or_else(|| StructureError::invalid("generic-for header has no terminator plan"))?;
    let BlockTerminatorKind::GenericForLoop {
        instr: loop_instr_ref,
        body,
        exit,
    } = header_terminator.kind
    else {
        return Err(StructureError::invalid(
            "generic-for header does not end with GenericForLoop",
        ));
    };
    let Some((call_instr_ref, call, loop_instr)) =
        generic_for_header_instrs(proto, header_terminator)
    else {
        return Err(StructureError::invalid(
            "generic-for header has no stable call/loop pair",
        ));
    };
    let preheader = payload
        .preheader_block
        .ok_or_else(|| StructureError::invalid("generic-for loop has no frozen preheader block"))?;
    let preheader_terminator = plan
        .block_terminator(preheader)
        .ok_or_else(|| StructureError::invalid("generic-for preheader has no terminator plan"))?;
    let (prep_instr, iterator) = generic_for_source(proto, preheader, preheader_terminator, call)?;
    if !payload.control_edges.body.contains(&body) || !payload.control_edges.exit.contains(&exit) {
        return Err(StructureError::invalid(format!(
            "generic-for loop #{} contradicts its syntax edges: body={body} in {:?}, exit={exit} in {:?}",
            region.index(),
            payload.control_edges.body,
            payload.control_edges.exit,
        )));
    }
    if !matches!(
        payload.source_bindings,
        Some(LoopSourceBindings::Generic(bindings)) if bindings == loop_instr.bindings
    ) {
        return Err(StructureError::invalid(format!(
            "generic-for loop #{} contradicts its selected bindings",
            region.index()
        )));
    }
    Ok(GenericForProtocol {
        prep_instr,
        call_instr: call_instr_ref,
        loop_instr: loop_instr_ref,
        body_edge: body,
        exit_edge: exit,
        body_completes_normally,
        iterator,
        bindings: loop_instr.bindings,
        immediate_break: super::super::super::loops::generic_for_immediate_break(
            proto,
            cfg,
            &loop_instr,
        ),
    })
}

/// 一次 edge sweep 冻结 VM-for body 是否存在普通完成路径。
///
/// HIR 形状会受表达式内联和可读性规范化影响，不能再检查 lowering 后最后一条语句。
/// region relation 已把跨 `body -> control` 的物理边投影到 loop 的直接 child，因此一条
/// edge 最多证明一个 loop，不会按 loop 重扫整个 CFG。显式 continue/goto 是终止当前
/// HIR body 的语句；自然边、普通条件 arm、本 loop 回边，以及最后一个 structured
/// child 被自身语法吸收的 exit，都会让外围 body 在 child 之后继续。
pub(super) fn freeze_vm_for_body_completion(
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<Vec<bool>, StructureError> {
    let mut completion = vec![false; plan.loops.len()];
    let mut body_tail = vec![None; plan.loops.len()];
    for (index, payload) in plan.loops.iter().enumerate() {
        if !matches!(
            payload.kind,
            LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
        ) {
            continue;
        }
        let region = plan
            .loop_region_by_plan
            .get(index)
            .copied()
            .ok_or_else(|| StructureError::invalid("loop region reverse index is stale"))?;
        let body = match plan.region(region) {
            Some(RegionPlan::Loop { body, .. }) => *body,
            _ => {
                return Err(StructureError::invalid(
                    "VM-for protocol owner is not a loop region",
                ));
            }
        };
        let Some(RegionPlan::Sequence { children, .. }) = plan.region(body) else {
            return Err(StructureError::invalid(
                "VM-for body partition is not a sequence region",
            ));
        };
        completion[index] = children.is_empty();
        body_tail[index] = children.last().copied();
    }

    for edge in &plan.edge_plans {
        let cfg_edge = cfg.edges.get(edge.edge.index()).ok_or_else(|| {
            StructureError::invalid("planned VM-for completion edge is outside the CFG arena")
        })?;
        let relation = plan
            .edge_region_relation(edge.edge)
            .ok_or_else(|| StructureError::invalid("planned edge has no region relation"))?;
        let Some(loop_region) = relation.lca else {
            continue;
        };
        let Some(RegionPlan::Loop {
            plan: loop_id,
            body,
            control,
            ..
        }) = plan.region(loop_region)
        else {
            continue;
        };
        let Some(payload) = plan.loops.get(loop_id.index()) else {
            return Err(StructureError::invalid(
                "loop region references a missing payload",
            ));
        };
        if !matches!(
            payload.kind,
            LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
        ) || relation.source_child != Some(*body)
            || relation.target_child != Some(*control)
        {
            continue;
        }
        let Some(tail) = body_tail[loop_id.index()] else {
            continue;
        };
        let Some(source_owner) = relation.source_owner else {
            continue;
        };
        if !region_completion_port_accepts(plan, tail, source_owner, cfg_edge.from) {
            continue;
        }
        let nested_structured_exit = plan.region_contains(tail, edge.owner)
            && matches!(
                edge.transfer,
                EdgeTransfer::Break(_) | EdgeTransfer::BranchArm(super::super::BranchArm::LoopExit)
            );
        let completes = matches!(
            edge.transfer,
            EdgeTransfer::Fallthrough
                | EdgeTransfer::BranchArm(
                    super::super::BranchArm::Truthy | super::super::BranchArm::Falsy
                )
        ) || matches!(edge.transfer, EdgeTransfer::LoopBack(owner) if owner == loop_region)
            || nested_structured_exit;
        if completes {
            completion[loop_id.index()] = true;
        }
    }
    Ok(completion)
}

pub(super) fn region_completion_port_accepts(
    plan: &StructurePlan,
    tail: RegionId,
    source_owner: RegionId,
    source_block: BlockRef,
) -> bool {
    if !plan
        .navigation
        .region_can_complete_from(tail, source_owner, source_block)
    {
        return false;
    }

    let mut current = Some(source_owner);
    while let Some(region) = current {
        if matches!(plan.region(region), Some(RegionPlan::Unstructured { .. }))
            && !plan
                .navigation
                .region_can_complete_from(region, source_owner, source_block)
        {
            return false;
        }
        if region == tail {
            return true;
        }
        current = plan
            .navigation
            .parent
            .get(region.index())
            .copied()
            .flatten();
    }
    false
}
