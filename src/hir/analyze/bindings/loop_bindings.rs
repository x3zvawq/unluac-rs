//! 分配 for/phi 状态绑定并保留其物理覆盖终点；依赖最终 loop value plan 与 Dataflow
//! 覆盖关系，不负责捕获槽位。例如循环后的 `state = nil` 仍写回 carried 身份，
//! 不会成为独立死 temp 而丢失原 VM 清根行为。
//! 循环 owner 与唯一入口值直接消费 PhiPlan 的已证明输入，不在 binding 分配中重建处置。

use super::*;

/// scalar 写入仍可能结束循环状态的强根。只接回已证明的 carried 身份，
/// 不按槽号合并不同 value epoch，也不把新分配对象的根延长到旧 local 的作用域末尾。
pub(super) fn preserve_loop_state_overwrites(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    epochs: &SlotEpochFacts,
    barriers: (&[bool], &[Option<DebugBindingHint<'_>>]),
    temps: (&[TempId], &mut [TempId]),
) {
    let (numeric_phis, debug_hints) = barriers;
    let (phi_temps, fixed_temps) = temps;
    let mut carried_temps = BTreeMap::<TempId, Option<RegionId>>::new();
    let mut blocked_temps = BTreeSet::new();
    // 已合并的 loop/result Phi 共享最终 temp；按最外层循环 owner 判断退出，
    // 不能要求覆盖关系指向的中间 result Phi 自身也是 loop-carried。
    for phi in plan.phis() {
        let temp = phi_temps[phi.phi.index()];
        if numeric_phis[phi.phi.index()] || debug_hints[phi.phi.index()].is_some() {
            blocked_temps.insert(temp);
        } else if let Some(carried) = phi.loop_carried() {
            carried_temps
                .entry(temp)
                .and_modify(|owner| {
                    *owner = match *owner {
                        Some(current) if plan.region_contains(current, carried.owner) => {
                            Some(current)
                        }
                        Some(current) if plan.region_contains(carried.owner, current) => {
                            Some(carried.owner)
                        }
                        _ => None,
                    };
                })
                .or_insert(Some(carried.owner));
        }
    }
    for def in &dataflow.defs {
        if fixed_temps[def.id.index()] != TempId(def.id.index())
            || dataflow.reg_is_captured(def.reg)
            || !dataflow.def_phi_uses[def.id.index()].is_empty()
            || debug_local_hint_for_reg_at_instr(proto, def.reg, def.instr).is_some()
        {
            continue;
        }
        let Some(SsaValue::Def(value)) = dataflow.canonical_move_value(SsaValue::Def(def.id))
        else {
            continue;
        };
        if crate::hir::promotion::direct_scalar_overwrite_value(
            &proto.instrs[dataflow.def_instr(value).index()],
            dataflow.def_reg(value),
        )
        .is_none()
        {
            continue;
        }
        let Some(SsaValue::Phi(source)) = dataflow.def_overwritten_value(def.id) else {
            continue;
        };
        let Some(phi) = plan.phi_plan(source) else {
            continue;
        };
        let target = phi_temps[source.index()];
        if !dataflow.def_uses[def.id.index()].is_empty()
            && carried_temps
                .get(&target)
                .copied()
                .flatten()
                .is_none_or(|carried| {
                    plan.region_for_block(def.block)
                        .is_none_or(|owner| plan.region_contains(carried, owner))
                })
        {
            // 候选拒绝[ProofIncomplete]：循环内仍有读取的版本属于循环值/帧协议，
            // 需由 coalesce_loop_state_temps 连同回边证明；这里只补齐循环外的退休端点。
            continue;
        }
        if phi.reg == def.reg
            && carried_temps.contains_key(&target)
            && !blocked_temps.contains(&target)
            && epochs.epoch_at(def.reg, def.instr)
                == epochs.epoch_at(phi.reg, cfg.blocks[phi.block.index()].instrs.start)
        {
            // 后续直接读取只观察这次原位写入的值，不会取消它对旧根的覆盖。
            // Phi 消费者的独立快照仍在上方拒绝，不能据同槽关系合并其它合流身份。
            fixed_temps[def.id.index()] = target;
        }
    }
}

/// 嵌套 loop 只在最终 value plan 明确证明“沿用祖先 carried 槽位”时复用 HIR temp。
///
/// phi arena identity 与 incoming owner 保持不变；这里只收敛 lowering binding，避免
/// 每层 loop 为同一源码状态制造一组机械 handoff local。capture 或混合 owner 会让
/// 提前写回变得可观察，因此保守保留独立 temp。
pub(super) fn coalesce_nested_loop_carried_temps(
    plan: &StructurePlan,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    debug_hints: &[Option<DebugBindingHint<'_>>],
    phi_temps: &mut [TempId],
) -> Vec<Option<PhiId>> {
    let mut parents = vec![None; plan.phis().len()];

    for phi in plan.phis() {
        if dataflow.reg_is_captured(phi.reg) {
            continue;
        }
        let Some(binding) = phi.loop_carried() else {
            continue;
        };
        let source = match binding.input {
            Some(SsaValue::Phi(source)) => source,
            Some(SsaValue::Def(def)) => {
                // 内层入口也可能是祖先状态在原槽中的一次更新。只消费 Dataflow
                // 的直接覆盖事实；COPY 的 canonical 源和跨 epoch/debug 身份不能
                // 据此共址，原更新仍在原定义点求值。
                let definition = &dataflow.defs[def.index()];
                let Some(SsaValue::Phi(source)) = dataflow.def_overwritten_value(def) else {
                    continue;
                };
                let Some(source_plan) = plan.phi_plan(source) else {
                    continue;
                };
                let epoch = epochs.epoch_at(phi.reg, cfg.blocks[phi.block.index()].instrs.start);
                if definition.reg != phi.reg
                    || dataflow.canonical_move_value(SsaValue::Def(def)) != Some(SsaValue::Def(def))
                    || epochs.epoch_at(phi.reg, definition.instr) != epoch
                    || epochs.epoch_at(
                        source_plan.reg,
                        cfg.blocks[source_plan.block.index()].instrs.start,
                    ) != epoch
                    || debug_hints[phi.phi.index()].is_some()
                    || debug_hints[source.index()].is_some()
                {
                    // ProofIncomplete：同槽覆盖尚不能证明跨身份的可观察绑定一致。
                    continue;
                }
                source
            }
            _ => continue,
        };
        let Some(source_plan) = plan.phi_plan(source) else {
            continue;
        };
        let Some(source_binding) = source_plan.loop_carried() else {
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
/// 协议时才共址；nested carried target 的结果消费者必须已证明共址，独立 snapshot
/// 仅接纳直接正常出口的唯一读取，避免其它 edge copy 延后读取已覆盖状态。候选从 carried target 出发一次构建，
/// 避免 result × owner 的重复扫描。
pub(super) fn coalesce_loop_state_temps(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    nested_carried_parents: &[Option<PhiId>],
    binding_barriers: (
        &[bool],
        &[Option<DebugBindingHint<'_>>],
        &CapturedSlotTargets,
    ),
    binding_temps: (&mut [TempId], &mut [TempId]),
    epochs: &SlotEpochFacts,
) {
    let (numeric_binding_phis, phi_debug_hints, captured_slots) = binding_barriers;
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
                        // 内层提前退出可以直接汇入外层 continuation。结果仍属于
                        // 已冻结的外层 region；保留嵌套 owner 链，不要求每条边都
                        // 恰好在同一层产生，也不合并互不包含的 region。
                        match owner {
                            None => owner = Some(region),
                            Some(current) if plan.region_contains(region, current) => {
                                owner = Some(region);
                            }
                            Some(current) if plan.region_contains(current, region) => {}
                            Some(_) => return false,
                        }
                        true
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
    // 同一 stage 可以被多个 carried 候选引用，逐 phi 冻结输入 owner，避免反复扫描输入。
    let carried_stage_owners = plan
        .phis()
        .map(|phi| {
            let PhiIncomingDisposition::LoopCarried(owner) = phi.incomings.first()?.disposition
            else {
                return None;
            };
            phi.incomings
                .iter()
                .all(|incoming| incoming.disposition == PhiIncomingDisposition::LoopCarried(owner))
                .then_some(owner)
        })
        .collect::<Vec<_>>();
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
        if numeric_binding_phis[phi.phi.index()] {
            continue;
        }
        let Some(carried) = phi.loop_carried() else {
            continue;
        };
        if dataflow.reg_is_captured(phi.reg) {
            let epoch = epochs.epoch_at(phi.reg, cfg.blocks[phi.block.index()].instrs.start);
            let home = HomeSlotKey::new(phi.reg.index(), epoch);
            // CLOSE 后的旧 cell 或其它 SSA 版本的 ByValue 快照不观察当前状态。
            // 只接纳同 epoch、未被捕获的直接回边定义，不混合嵌套结果或捕获身份。
            if !captured_slots.version_is_uncaptured(home, SsaValue::Phi(phi.phi))
                || !phi
                    .incomings
                    .iter()
                    .filter(|incoming| {
                        incoming.disposition == PhiIncomingDisposition::LoopCarried(carried.owner)
                    })
                    .all(|incoming| {
                        matches!(incoming.value, SsaValue::Def(def)
                        if dataflow.def_reg(def) == phi.reg
                            && epochs.epoch_at(phi.reg, dataflow.def_instr(def)) == epoch
                            && captured_slots.version_is_uncaptured(home, incoming.value))
                    })
            {
                continue;
            }
        }
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
        let while_control_def = (!has_nested_parent
            && phi_debug_hints[phi.phi.index()].is_none()
            && matches!(plan.loop_protocol(*loop_id), Some(LoopVmProtocol::While(_))))
        .then(|| direct_while_control_write(cfg, dataflow, plan, epochs, phi.phi, *loop_control))
        .flatten();
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
                // 内层重试边可直接保留同一 SSA 状态；它没有交接，也不否定其它回边的写回证明。
                SsaValue::Phi(source) if source == phi.phi => {}
                SsaValue::Def(def)
                    if def_is_same_reg_in_region(dataflow, plan, def, phi.reg, direct_region)
                        || while_control_def == Some(def)
                        || repeat_control.is_some_and(|control| {
                            def_is_same_reg_in_region(dataflow, plan, def, phi.reg, control)
                        }) =>
                {
                    result_compatible = false;
                }
                SsaValue::Phi(source) => {
                    direct_compatible = false;
                    let source_plan = plan.phi_plan(source);
                    let repeat_state_stage = matches!(
                        plan.loop_protocol(*loop_id),
                        Some(LoopVmProtocol::Repeat(_))
                    ) && carried_stage_owners[source.index()]
                        == Some(carried.owner);
                    let loop_stage = source != phi.phi
                        && (!has_nested_parent
                            || (!nested_stage_barrier_temps[target.index()]
                                && (repeat_state_stage
                                    || direct_exit_stages[source.index()]
                                        .resolved()
                                        .is_some_and(|(owner, _)| owner == carried.owner))))
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
                PhiIncomingDisposition::RegionResult(region) => {
                    region == owner
                        && (!nested_target
                            // 结果合流已独立证明写回同一 binding，条件入口的 stage
                            // 无需保存第二份状态；独立出口快照仍不能借此合并。
                            || phi_targets[consumer.phi.index()]
                                .is_some_and(|(temp, _, stage)| {
                                    temp == target_temp && stage.is_none()
                                }))
                }
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

/// while 头的原同槽覆盖在条件前已经发生，不能等回边 phi COPY 才写回。
/// 例如 `<close> guard; state = state + 1; if stop then break end`，提前保留旧 state
/// 会让回边从已关闭的临时声明读取。这里只接同块、同 epoch 的唯一覆盖，且旧 phi
/// 只在原覆盖指令读取；额外 COPY 可能保留旧快照，不能借 raw SSA 读索引将其合并。
fn direct_while_control_write(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    epochs: &SlotEpochFacts,
    phi_id: PhiId,
    control: RegionId,
) -> Option<DefId> {
    let phi = plan.phi_plan(phi_id)?;
    let carried = phi.loop_carried()?;
    let mut output = None;
    for incoming in &phi.incomings {
        if incoming.disposition != PhiIncomingDisposition::LoopCarried(carried.owner) {
            continue;
        }
        let SsaValue::Def(def) = incoming.value else {
            return None;
        };
        if output.replace(def).is_some_and(|previous| previous != def) {
            return None;
        }
    }
    let def = output?;
    let definition = &dataflow.defs[def.index()];
    let header_start = cfg.blocks[phi.block.index()].instrs.start;
    (definition.block == phi.block
        && def_is_same_reg_in_region(dataflow, plan, def, phi.reg, control)
        && dataflow.canonical_move_value(SsaValue::Def(def)) == Some(SsaValue::Def(def))
        && dataflow.def_overwritten_value(def) == Some(SsaValue::Phi(phi_id))
        && epochs.epoch_at(phi.reg, header_start) == epochs.epoch_at(phi.reg, definition.instr)
        && dataflow.phi_uses[phi_id.index()]
            .iter()
            .all(|site| site.instr == definition.instr && site.reg == phi.reg)
        && dataflow.phi_phi_uses[phi_id.index()]
            .iter()
            .all(|&consumer| dataflow.phi_is_truly_dead(consumer))
        && dataflow.def_phi_uses[def.index()]
            .iter()
            .all(|&consumer| consumer == phi_id || dataflow.phi_is_truly_dead(consumer)))
    .then_some(def)
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
    (target, normal_value): (PhiId, SsaValue),
    dataflow: &DataflowFacts,
    nested_carried_child_owners: &BTreeSet<(TempId, RegionId)>,
    carried_temp_owners: &BTreeSet<(TempId, RegionId)>,
    (phi_temps, fixed_temps): (&[TempId], &[TempId]),
) -> Option<TempId> {
    let owner = plan.loop_region(loop_id)?;
    let result = plan.phi_plan(target)?;
    if dataflow.reg_is_captured(result.reg) {
        return None;
    }
    // binding 分配已证明出口合流和正常输入共用 carried 身份时，额外 stage
    // 只会复制该身份。正常输入既可能是条件入口 Phi，也可能是本轮最后的 Def；
    // 读取已分配的 temp 身份，不按寄存器重新猜测两份状态等价。
    let normal_temp = match normal_value {
        SsaValue::Phi(source) if plan.phi_plan(source)?.reg == result.reg => {
            phi_temps.get(source.index())
        }
        SsaValue::Def(source) if dataflow.def_reg(source) == result.reg => {
            fixed_temps.get(source.index())
        }
        _ => None,
    };
    if normal_temp.is_some() && normal_temp == phi_temps.get(target.index()) {
        return normal_temp.copied();
    }
    if matches!(normal_value, SsaValue::Def(_))
        && let Some(&temp) = normal_temp
        && carried_temp_owners.contains(&(temp, owner))
    {
        // 本轮计算已由 carried 绑定在原定义点接管。复用它承接出口暂存，
        // 独立结果 phi 仍按原协议在循环后提交；不省略尚未共址的合流 COPY。
        return Some(temp);
    }
    // 完整条件入口的 phi 已属于本轮 carried 状态时，出口快照仍是同一个 VM 槽。
    // 正常路径不改值，break 按原边写入该槽；独立出口 phi 只在循环后读取最终状态。
    if let SsaValue::Phi(source) = normal_value
        && let Some(source_plan) = plan.phi_plan(source)
        && source_plan.reg == result.reg
        && !source_plan.incomings.is_empty()
        && source_plan
            .incomings
            .iter()
            .all(|incoming| incoming.disposition == PhiIncomingDisposition::LoopCarried(owner))
    {
        return phi_temps.get(source.index()).copied();
    }
    let target = *phi_temps.get(target.index())?;
    // nested-carried 索引已经证明本 loop 沿用祖先 binding；出口 phi 也可能
    // 经结果合流取得该身份，不要求它自己仍是祖先 loop header 的 phi。
    nested_carried_child_owners
        .contains(&(target, owner))
        .then_some(target)
}

/// 绑定分配完成后，repeat 的全部出口输入若已归于同一 Local，直接复用该 owner。
/// 捕获 cell、debug 声明与独立快照沿用 lowering 的统一身份查询，不按寄存器是否捕获猜测。
pub(super) fn reuse_bound_repeat_stages(plan: &StructurePlan, bindings: &mut ProtoBindings) {
    for (loop_id, payload) in plan.loops() {
        let Some(LoopVmProtocol::Repeat(protocol)) = &payload.protocol else {
            continue;
        };
        for (index, result) in protocol.value_plan.staged_results.iter().enumerate() {
            let target_for = |value| {
                let temp = match value {
                    SsaValue::Def(def) => *bindings.fixed_temps.get(def.index())?,
                    SsaValue::Phi(phi) => *bindings.phi_temps.get(phi.index())?,
                    SsaValue::Entry(_) => return None,
                };
                bindings.temp_target(temp)
            };
            let Some(phi) = plan.phi_plan(result.target) else {
                continue;
            };
            let Some(owner @ BoundSlotTarget::Local(_)) = target_for(SsaValue::Phi(result.target))
            else {
                continue;
            };
            if target_for(result.normal_value) != Some(owner)
                || !phi.incomings.iter().all(|incoming| {
                    incoming.disposition == PhiIncomingDisposition::Dead
                        || target_for(incoming.value) == Some(owner)
                })
            {
                continue;
            }
            // 原写入和各出口都已属于同一词法身份，stage 只重复合流；捕获 cell 的
            // 更新仍由该 Local 承接。独立快照没有这个投影，不能凭相同槽位合并。
            bindings.repeat_staged_temps[loop_id.index()][index] =
                bindings.phi_temps[result.target.index()];
        }
    }
}

/// NumericFor 的 control 前缀在本轮 body 尾部发射，仍处于同一 binding 作用域。
/// GenericFor 的 control 包含下一次 iterator 调用，不能同样归入当前 yield 的绑定。
pub(super) fn loop_binding_blocks(
    plan: &StructurePlan,
    loop_id: LoopPlanId,
) -> Option<impl Iterator<Item = &BlockRef>> {
    let region = plan.loop_region(loop_id)?;
    let RegionPlan::Loop { body, control, .. } = plan.region(region)? else {
        return None;
    };
    let tail = matches!(plan.loop_protocol(loop_id),
        Some(LoopVmProtocol::NumericFor(protocol)) if protocol.body_completes_normally)
    .then_some(*control);
    Some(
        plan.region_blocks(*body)
            .iter()
            .chain(tail.into_iter().flat_map(|tail| plan.region_blocks(tail))),
    )
}

pub(super) struct NumericBindingPhiFacts {
    pub(super) bindings: Vec<bool>,
    pub(super) source_direct: Vec<bool>,
}

/// generic-for 的语法变量已承接 body 中的真实写入；其内部合流不再分配第二套状态。
pub(super) fn bind_generic_for_phis(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    generic_locals: &BTreeMap<BlockRef, Vec<LocalId>>,
    block_locals: &BTreeMap<BlockRef, BTreeMap<Reg, LocalId>>,
    phi_locals: &mut [Option<LocalId>],
) {
    let mut dispatch_results = BTreeMap::new();
    let mut locals = BTreeSet::new();
    for (loop_id, payload) in plan.loops() {
        let Some(bindings) = generic_locals.get(&payload.header) else {
            continue;
        };
        let Some(LoopVmProtocol::GenericFor(protocol)) = plan.loop_protocol(loop_id) else {
            continue;
        };
        let Some(LoopSourceBindings::Generic(regs)) = payload.source_bindings else {
            continue;
        };
        for (offset, &local) in bindings.iter().enumerate() {
            locals.insert(local);
            if let Some(def) =
                dataflow.instr_def_for_reg(protocol.call_instr, Reg(regs.start.index() + offset))
            {
                dispatch_results.insert(def, local);
            }
        }
    }
    for phi in plan.phis() {
        let Some(&local) = block_locals
            .get(&phi.block)
            .and_then(|bindings| bindings.get(&phi.reg))
        else {
            continue;
        };
        if !locals.contains(&local) || phi.has_unresolved() {
            continue;
        }
        // 每条输入必须是该边末端的当前寄存器值，且由同一语法变量或原 dispatch
        // 建立。旧 Def 快照、循环外状态与不同绑定不能借相同槽号取得这个身份。
        if phi.incomings.iter().all(|incoming| {
            if incoming.disposition == PhiIncomingDisposition::Dead { return true; }
            let Some(edge) = incoming.edge else { return false };
            let source = cfg.edges[edge.index()].from;
            dataflow.block_exit_value(source, phi.reg) == incoming.value
                && (block_locals.get(&source).and_then(|bindings| bindings.get(&phi.reg)) == Some(&local)
                    || matches!(incoming.value, SsaValue::Def(def) if dispatch_results.get(&def) == Some(&local)))
        }) {
            phi_locals[phi.phi.index()] = Some(local);
        }
    }
}

/// capture 所有权需要识别全部 exact header phi；只有 Structure 已冻结为 elided target 的
/// phi 才能把读取直接绑定到循环语法 local。寄存器相同不足以建立任一别名。
pub(super) fn numeric_for_binding_phis(plan: &StructurePlan) -> NumericBindingPhiFacts {
    let mut bindings = vec![false; plan.phis().len()];
    let mut source_direct = vec![false; plan.phis().len()];
    for (phi, direct) in plan.loops().filter_map(|(_, loop_plan)| {
        let LoopSourceBindings::Numeric(binding) = loop_plan.source_bindings? else {
            return None;
        };
        let mut candidates = plan
            .phis_in_block(loop_plan.header)
            .iter()
            .filter_map(|&phi| plan.phi_plan(phi))
            .filter(|phi| phi.reg == binding);
        let phi = candidates.next()?.phi;
        if candidates.next().is_some() {
            return None;
        }
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
