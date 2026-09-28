//! 按 loop kind 冻结 while/repeat/numeric-for/generic-for VM 协议；依赖块终结器和区域完成端口，不负责 phi 值动作。

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
            cfg,
            dataflow,
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
    cfg: &Cfg,
    dataflow: &DataflowFacts,
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
    let mut controls = plan
        .region_blocks(loop_control_region(plan, region)?)
        .iter()
        .filter_map(|&block| match plan.block_terminator(block)?.kind {
            BlockTerminatorKind::NumericForLoop { instr, .. } => Some(instr),
            _ => None,
        });
    let loop_instr = controls.next();
    if loop_instr.is_none() && body_completes_normally {
        return Err(StructureError::invalid(
            "completing numeric-for body has no frozen loop instruction",
        ));
    }
    if controls.next().is_some() {
        return Err(StructureError::invalid(
            "numeric-for control owns multiple loop instructions",
        ));
    }
    validate_normalized_numeric_controls(dataflow, instr, init, loop_instr)?;
    Ok(NumericForProtocol {
        init_instr: instr,
        loop_instr,
        body_edge: body,
        exit_edge: exit,
        body_completes_normally,
        index: init.index,
        limit: init.limit,
        step: init.step,
        binding: init.binding,
        writable_binding: numeric_writable_binding(
            proto, cfg, dataflow, preheader, init, loop_instr,
        ),
    })
}

/// FORPREP 的原位转换由源码 for 隐式执行，不存在可供普通语句读取的转换结果 Temp。
/// 例如字符串 step 在准备后成为数字，只能继续交给同一 latch；把新的 SSA Def 映射回
/// header 输入会恢复成字符串。Phi 的通用 control 分类只证明使用区域，不能证明它仍是
/// 同一转换值，因此没有独立值归属的合流必须在协议发布处拒绝，而不是留给 HIR 猜测。
fn validate_normalized_numeric_controls(
    dataflow: &DataflowFacts,
    init_instr: InstrRef,
    init: &crate::transformer::NumericForInitInstr,
    loop_instr: Option<InstrRef>,
) -> Result<(), StructureError> {
    if !init.normalizes_controls {
        return Ok(());
    }
    for reg in [init.limit, init.step] {
        let def = dataflow.instr_def_for_reg(init_instr, reg).ok_or_else(|| {
            StructureError::invalid(format!(
                "numeric-for normalization at {init_instr} has no definition for {reg}",
            ))
        })?;
        if let Some(site) = dataflow.def_uses[def.index()]
            .iter()
            .find(|site| Some(site.instr) != loop_instr || site.reg != reg)
        {
            return Err(StructureError::invalid(format!(
                "normalized numeric-for control {reg} at {init_instr} has an unowned value read at {}",
                site.instr,
            )));
        }
        if dataflow.def_phi_uses[def.index()]
            .iter()
            .any(|&phi| !dataflow.phi_is_truly_dead(phi))
        {
            return Err(StructureError::invalid(format!(
                "normalized numeric-for control {reg} at {init_instr} enters an SSA merge without a source value owner",
            )));
        }
    }
    Ok(())
}

/// 独立控制 index 后的可写用户槽是原 VM-for 协议的一部分，不是任意 body COPY。
/// 单入口 body 的首条复制每次必达，控制值除此以外不作普通读取，用户槽确有
/// 后续写且不捕获。`for i=1,n do local old=i; i=i+1 end` 因而保持控制槽和 old 快照，
/// 不会在重编译时把可写 i 变成一个不可写的循环变量并触发新的展开。
fn numeric_writable_binding(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    preheader: BlockRef,
    init: &crate::transformer::NumericForInitInstr,
    loop_instr: Option<InstrRef>,
) -> Option<(InstrRef, Reg)> {
    let latch = loop_instr?;
    let body = *cfg.instr_to_block.get(init.body_target.index())?;
    let latch_block = *cfg.instr_to_block.get(latch.index())?;
    let block = cfg.blocks.get(body.index())?;
    if init.index != init.binding
        || init.index.index() != init.limit.index().checked_add(2)?
        || init.step.index() != init.limit.index().checked_add(1)?
        || block.instrs.start != init.body_target
        || body.index() > latch_block.index()
        || cfg.preds[body.index()].iter().any(|edge| {
            let source = cfg.edges[edge.index()].from;
            source != preheader && source != latch_block
        })
    {
        return None;
    }
    let LowInstr::NumericForLoop(loop_) = proto.instrs.get(latch.index())? else {
        return None;
    };
    let LowInstr::Move(copy) = proto.instrs.get(init.body_target.index())? else {
        return None;
    };
    if loop_.index != init.index
        || loop_.binding != init.binding
        || loop_.limit != init.limit
        || loop_.step != init.step
        || loop_.body_target != init.body_target
        || loop_.exit_target != init.exit_target
        || copy.src != init.index
        || copy.dst.index() != init.index.index().checked_add(1)?
        || dataflow.reg_is_captured(copy.dst)
        || dataflow.reg_is_captured(init.index)
    {
        return None;
    }
    let mut written = false;
    let mut debug_scope = None;
    for index in init.body_target.index()..latch.index() {
        // 候选拒绝[ProofIncomplete]：嵌套 numeric-for 需共享区间摘要；当前扫描
        // 不越过其入口，避免每层外循环重复遍历同一内层协议而形成平方复杂度。
        if matches!(proto.instrs[index], LowInstr::NumericForInit(_)) {
            return None;
        }
        let effects = &dataflow.instr_effects[index];
        if [init.limit, init.step, init.index].into_iter().any(|reg| {
            effects.fixed_must_defs().contains(&reg)
                || effects.uses_fixed(reg)
                    && !(index == init.body_target.index() && reg == init.index)
        }) {
            return None;
        }
        // OPEN 后缀不能借固定寄存器集合证明未触及控制/用户槽。
        if effects.open_use.is_some() || effects.open_must_def.is_some() {
            return None;
        }
        if index != init.body_target.index() && effects.fixed_must_defs().contains(&copy.dst) {
            written = true;
        }
        for &pc in &proto.lowering_map.pc_map()[index] {
            // 有源码控制 binding 时，首 COPY 是另一个显式 local，不能吞掉两个 debug 身份。
            if proto.debug_locals.source_at(init.index, pc).is_some() {
                return None;
            }
            if let Some((scope, _)) = proto.debug_locals.source_at(copy.dst, pc) {
                if debug_scope.is_some_and(|previous| previous != scope) {
                    return None;
                }
                debug_scope = Some(scope);
            }
        }
    }
    // 分支可以把本轮 body 切成多个块，但不可从外部绕过入口 COPY。
    // 按原连续指令区间一次检查 incoming edges；不为每个 use 重建支配关系。
    for block_index in body.index() + 1..=latch_block.index() {
        if cfg.preds[block_index].iter().any(|edge| {
            let source = cfg.edges[edge.index()].from.index();
            source < body.index() || source > latch_block.index()
        }) {
            return None;
        }
    }
    written.then_some((init.body_target, copy.dst))
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
