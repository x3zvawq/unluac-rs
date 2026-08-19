//! 合并嵌套 loop-carried temp 并分配 for/phi 状态绑定；依赖最终 loop value plan，不负责捕获槽位；例如复用祖先 carried 槽而保留可观察 capture。

use super::*;

#[derive(Clone, Copy)]
pub(super) struct LoopCarriedBinding {
    pub(super) owner: RegionId,
    pub(super) input: SsaValue,
}

/// 嵌套 loop 只在最终 value plan 明确证明“沿用祖先 carried 槽位”时复用 HIR temp。
///
/// phi arena identity 与 incoming owner 保持不变；这里只收敛 lowering binding，避免
/// 每层 loop 为同一源码状态制造一组机械 handoff local。capture 或混合 owner 会让
/// 提前写回变得可观察，因此保守保留独立 temp。
pub(super) fn coalesce_nested_loop_carried_temps(
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

pub(super) fn captured_regs(proto: &LoweredProto) -> Vec<bool> {
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

pub(super) fn reg_is_captured(captured: &[bool], reg: Reg) -> bool {
    captured.get(reg.index()).copied().unwrap_or(false)
}

#[derive(Clone, Copy)]
pub(super) struct BindingCandidate<T> {
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
    pub(super) fn add(&mut self, target: T) {
        if self.target.is_some_and(|current| current != target) {
            self.conflict = true;
        } else {
            self.target = Some(target);
        }
    }

    pub(super) fn resolved(self) -> Option<T> {
        (!self.conflict).then_some(self.target).flatten()
    }
}

/// 同一未捕获 VM 槽的 loop state 在原定义点直接写回 carried temp；这里只合并 identity，
/// 不移动表达式。无真实读取的同 loop phi stage 也只有在全部消费者仍属于该 carried/result
/// 协议时才共址；nested carried target 仅额外接纳直接正常出口上唯一的独立 snapshot，
/// 避免其它 edge copy 延后读取已被覆盖的状态。候选从 carried target 出发一次构建，
/// 避免 result × owner 的重复扫描。
pub(super) fn coalesce_loop_state_temps(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    captured_regs: &[bool],
    nested_carried_parents: &[Option<PhiId>],
    binding_barriers: (&[bool], &[Option<DebugBindingHint>]),
    binding_temps: (&mut [TempId], &mut [TempId]),
) {
    let (numeric_binding_phis, phi_debug_hints) = binding_barriers;
    let (phi_temps, fixed_temps) = binding_temps;
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
    let stage_source_eligible = plan
        .phis()
        .map(|phi| {
            pure_result_owners[phi.phi.index()].is_none()
                && nested_carried_parents[phi.phi.index()].is_none()
                && !numeric_binding_phis[phi.phi.index()]
                && phi_debug_hints[phi.phi.index()].is_none()
                && dataflow.phi_use_count(phi.phi) == 0
                && phi_participates_in_normal_binding(phi)
                // Numeric-for 的独立 exit identity 让后续 pass 能把 VM control pack 收回循环头；
                // 提前并入外围 carried temp 反而会把 state seed 固化成 preheader local。
                && !phi.incomings.iter().any(|incoming| {
                    let PhiIncomingDisposition::RegionResult(owner) = incoming.disposition else {
                        return false;
                    };
                    matches!(
                        plan.region(owner),
                        Some(RegionPlan::Loop { plan: loop_id, .. })
                            if matches!(
                                plan.loop_protocol(*loop_id),
                                Some(LoopVmProtocol::NumericFor(_))
                            )
                    )
                })
        })
        .collect::<Vec<_>>();
    let mut direct_exit_stages = vec![BindingCandidate::default(); phi_temps.len()];
    for consumer in plan.phis() {
        for incoming in &consumer.incomings {
            let Some((source, owner, edge)) =
                direct_loop_exit_stage_snapshot(cfg, plan, consumer.phi, incoming)
            else {
                continue;
            };
            direct_exit_stages[source.index()].add((owner, edge));
        }
    }
    let mut nested_stage_barrier_temps = vec![false; fixed_temps.len() + phi_temps.len()];
    for ((temp, is_numeric), debug_hint) in phi_temps
        .iter()
        .zip(numeric_binding_phis)
        .zip(phi_debug_hints)
    {
        if *is_numeric || debug_hint.is_some() {
            nested_stage_barrier_temps[temp.index()] = true;
        }
    }
    let mut def_candidates = vec![BindingCandidate::default(); fixed_temps.len()];
    let mut phi_candidates = vec![BindingCandidate::default(); phi_temps.len()];

    for phi in plan.phis() {
        if reg_is_captured(captured_regs, phi.reg) || numeric_binding_phis[phi.phi.index()] {
            continue;
        }
        let Some(carried) = loop_carried_binding(plan, phi) else {
            continue;
        };
        let Some(RegionPlan::Loop {
            plan: loop_id,
            control: loop_control,
            body: loop_body,
            ..
        }) = plan.region(carried.owner)
        else {
            continue;
        };
        let target = phi_temps[phi.phi.index()];
        let has_nested_parent = nested_carried_parents[phi.phi.index()].is_some();
        let repeat_control = (!has_nested_parent
            && matches!(
                plan.loop_(*loop_id)
                    .and_then(|loop_| loop_.protocol.as_ref()),
                Some(LoopVmProtocol::Repeat(_))
            ))
        .then_some(*loop_control);
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
                    if def_is_same_reg_in_region(dataflow, plan, def, phi.reg, direct_region)
                        || repeat_control.is_some_and(|control| {
                            def_is_same_reg_in_region(dataflow, plan, def, phi.reg, control)
                        }) =>
                {
                    result_compatible = false;
                }
                SsaValue::Phi(source) => {
                    direct_compatible = false;
                    let source_plan = plan.phi_plan(source);
                    let loop_stage = source != phi.phi
                        && (!has_nested_parent
                            || (!nested_stage_barrier_temps[target.index()]
                                && direct_exit_stages[source.index()]
                                    .resolved()
                                    .is_some_and(|(owner, _)| owner == carried.owner)))
                        && phi_debug_hints[phi.phi.index()].is_none()
                        && stage_source_eligible[source.index()]
                        && source_plan.is_some_and(|source| {
                            source.reg == phi.reg
                                && plan.region_for_block(source.block).is_some_and(|owner| {
                                    plan.region_contains(*loop_body, owner)
                                        || plan.region_contains(*loop_control, owner)
                                })
                        });
                    if loop_stage {
                        phi_candidates[source.index()].add((target, carried.owner, Some(phi.phi)));
                        result_compatible = false;
                        continue;
                    }
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
            phi_candidates[source.index()].add((target, result_region, None));
        }
    }

    let mut phi_targets = phi_candidates
        .into_iter()
        .map(BindingCandidate::resolved)
        .collect::<Vec<_>>();
    for consumer in plan.phis() {
        for incoming in &consumer.incomings {
            let SsaValue::Phi(source) = incoming.value else {
                continue;
            };
            let Some((target_temp, owner, Some(target))) = phi_targets[source.index()] else {
                continue;
            };
            let nested_target = nested_carried_parents[target.index()].is_some();
            let compatible = match incoming.disposition {
                PhiIncomingDisposition::LoopCarried(region) => {
                    consumer.phi == target && region == owner
                }
                PhiIncomingDisposition::RegionResult(region) => !nested_target && region == owner,
                PhiIncomingDisposition::EdgeCopy => {
                    nested_target
                        && incoming.edge.is_some_and(|edge| {
                            direct_exit_stages[source.index()].resolved() == Some((owner, edge))
                        })
                        && phi_temps[consumer.phi.index()] != target_temp
                }
                PhiIncomingDisposition::Dead => true,
                _ => false,
            };
            if !compatible {
                phi_targets[source.index()] = None;
            }
        }
    }
    for (temp, target) in phi_temps.iter_mut().zip(&phi_targets) {
        if let Some((target, _, _)) = target {
            *temp = *target;
        }
    }

    for phi in plan.phis() {
        let Some((target, result_region, None)) = phi_targets[phi.phi.index()] else {
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

/// 普通 loop control prefix 可能在 exit 前观察 binding，因此这里只接受无普通前缀的
/// numeric-for control；forwarded action、cleanup、iteration 或并行 batch 也保留独立 snapshot。
pub(super) fn direct_loop_exit_stage_snapshot(
    cfg: &Cfg,
    plan: &StructurePlan,
    consumer: PhiId,
    incoming: &PhiIncomingPlan,
) -> Option<(PhiId, RegionId, EdgeRef)> {
    if incoming.disposition != PhiIncomingDisposition::EdgeCopy {
        return None;
    }
    let SsaValue::Phi(source) = incoming.value else {
        return None;
    };
    let edge = incoming.edge?;
    let edge_plan = plan.edge_plan(edge)?;
    let cfg_edge = cfg.edges.get(edge.index())?;
    let source_block = plan.phi_plan(source)?.block;
    let source_region = plan.region_for_block(source_block)?;
    let Some(RegionPlan::Loop { control, .. }) = plan.region(edge_plan.owner) else {
        return None;
    };
    let terminator = plan.block_terminator(source_block)?;
    let BlockTerminatorKind::NumericForLoop { instr, exit, .. } = terminator.kind else {
        return None;
    };
    let [copy] = edge_plan.phi_copies.as_slice() else {
        return None;
    };
    if edge_plan.forward_route.is_some()
        || plan.edge_action_is_forwarded_only(edge)
        || edge_plan.actions_before_trailing_cleanup().is_some()
        || !edge_plan.iteration.is_empty()
        || !plan.region_contains(*control, source_region)
        || !matches!(
            edge_plan.transfer,
            EdgeTransfer::BranchArm(BranchArm::LoopExit)
        )
        || cfg_edge.from != source_block
        || exit != edge
        || terminator.instrs.start != instr
        || copy.phi_id != consumer
        || copy.value != incoming.value
    {
        return None;
    }
    Some((source, edge_plan.owner, edge))
}

pub(super) fn def_is_same_reg_in_region(
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

pub(super) fn repeat_stage_carried_temp(
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

pub(super) fn loop_carried_binding(
    plan: &StructurePlan,
    phi: &PhiPlan,
) -> Option<LoopCarriedBinding> {
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

pub(super) fn loop_body_region(plan: &StructurePlan, loop_id: LoopPlanId) -> Option<RegionId> {
    let region = plan.loop_region(loop_id)?;
    match plan.region(region)? {
        RegionPlan::Loop { body, .. } => Some(*body),
        _ => None,
    }
}

pub(super) struct NumericBindingPhiFacts {
    pub(super) bindings: Vec<bool>,
    pub(super) source_direct: Vec<bool>,
}

/// capture 所有权需要识别全部 exact header phi；只有 Structure 已冻结为 elided target 的
/// phi 才能把读取直接绑定到循环语法 local。寄存器相同不足以建立任一别名。
pub(super) fn numeric_for_binding_phis(plan: &StructurePlan) -> NumericBindingPhiFacts {
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

pub(super) fn region_blocks(plan: &StructurePlan, region: RegionId) -> BTreeSet<BlockRef> {
    pub(super) fn collect(plan: &StructurePlan, region: RegionId, blocks: &mut BTreeSet<BlockRef>) {
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

pub(super) fn phi_incoming_is_normal(disposition: PhiIncomingDisposition) -> bool {
    matches!(
        disposition,
        PhiIncomingDisposition::RegionInput(_)
            | PhiIncomingDisposition::RegionResult(_)
            | PhiIncomingDisposition::LoopCarried(_)
            | PhiIncomingDisposition::EdgeCopy
    )
}

pub(super) fn phi_participates_in_normal_binding(phi: &PhiPlan) -> bool {
    !phi.has_unresolved()
        && phi
            .incomings
            .iter()
            .any(|incoming| phi_incoming_is_normal(incoming.disposition))
}

pub(super) fn entry_reg_is_observed(
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    reg: Reg,
) -> bool {
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
