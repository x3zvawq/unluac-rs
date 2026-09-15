//! 最终 CFG edge 的语义分类。输入 loop query、forward routes、syntax arms 与 residual evidence，为每条 edge 选择唯一 owner/transfer；不负责 phi copy。例如 VM-for exit 与祖先 single-pass break 共边时仍由内层 for owner发射外层 transfer；从 VM-for body 回到外层 retry header 的 residual edge 则保留显式 goto，不能降成祖先的隐式 loopback。

use super::*;

fn private_tail_owns_exit(partition: &LoopPartitions, edge: EdgeRef) -> bool {
    partition.normal_tail.as_ref().is_some_and(|tail| {
        tail.contract.in_exit_arm && tail.contract.normal_exits.binary_search(&edge).is_ok()
    })
}

impl EdgeSemantics {
    pub(super) fn new(
        proto: &LoweredProto,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
        arena: &RegionArena,
        input: &FinalPlanInput,
        partitions: &[LoopPartitions],
        forwarding: &ForwardingBoundaries,
    ) -> Result<Self, StructureError> {
        let mut residual_continue_entries_by_target = vec![Vec::new(); cfg.blocks.len()];
        for residual in &input.residual_transfers {
            if !matches!(
                residual.reason,
                crate::structure::GotoReason::UnstructuredContinueLike
                    | crate::structure::GotoReason::CrossLoopContinueLike
            ) {
                continue;
            }
            let edge = cfg.edges.get(residual.edge.index()).ok_or_else(|| {
                StructureError::invalid("residual continue entry is outside the CFG arena")
            })?;
            residual_continue_entries_by_target[edge.to.index()].push(residual.edge);
        }
        let layout_edges = layout_edge_facts(cfg, &arena.regions, &arena.navigation);
        let loops = LoopQueryIndex::build(cfg, arena, input, partitions, &layout_edges)?;
        let mut planned_breaks = vec![None; cfg.edges.len()];
        for (spec_index, spec) in arena.specs.iter().enumerate() {
            let ContainerKind::Loop(loop_id) = spec.kind else {
                continue;
            };
            let region = arena.slots[spec_index].region();
            let partition = partitions
                .get(loop_id.index())
                .ok_or_else(|| StructureError::invalid("selected loop has no frozen partitions"))?;
            for edge in partition.break_routes.keys().copied() {
                if private_tail_owns_exit(partition, edge) {
                    continue;
                }
                let slot = planned_breaks.get_mut(edge.index()).ok_or_else(|| {
                    StructureError::invalid("loop break route starts outside the CFG arena")
                })?;
                match *slot {
                    Some(owner) if arena.navigation.contains(owner, region) => {
                        *slot = Some(region);
                    }
                    Some(owner) if !arena.navigation.contains(region, owner) => {
                        return Err(StructureError::invalid(
                            "one CFG edge starts break routes for unrelated loops",
                        ));
                    }
                    Some(_) => {}
                    None => *slot = Some(region),
                }
            }
        }
        let mut semantics = Self {
            single_pass_breaks: vec![None; cfg.edges.len()],
            backedges: vec![None; cfg.edges.len()],
            breaks: planned_breaks,
            continues: vec![None; cfg.edges.len()],
            syntax_arms: vec![None; cfg.edges.len()],
            forced_gotos: vec![None; cfg.edges.len()],
            equal_loop_retry_gotos: vec![None; cfg.edges.len()],
            branch_by_header: vec![None; cfg.blocks.len()],
            loops,
            forward_routes: ForwardRouteBuilder::new(cfg.edges.len(), arena.regions.len()),
            early_continues: vec![false; cfg.edges.len()],
            internal_transitions: vec![None; cfg.edges.len()],
            preheader_edges: vec![false; cfg.edges.len()],
            for_syntax_edges: vec![false; cfg.edges.len()],
            normal_tail_edges: vec![false; cfg.edges.len()],
            layout_edges,
            value_decision_edges: vec![None; cfg.edges.len()],
        };
        for (index, spec) in arena.specs.iter().enumerate() {
            let region = arena.slots[index].region();
            match spec.kind {
                ContainerKind::SinglePass(id) => {
                    let branch = input.branches.get(id.index()).ok_or_else(|| {
                        StructureError::invalid("single-pass region references missing branch")
                    })?;
                    let fence = branch
                        .region
                        .as_ref()
                        .and_then(|region| region.single_pass_fence.as_ref())
                        .ok_or_else(|| {
                            StructureError::invalid(
                                "single-pass region has no frozen fence evidence",
                            )
                        })?;
                    for edge in &fence.escape_edges {
                        let slot = semantics
                            .single_pass_breaks
                            .get_mut(edge.index())
                            .ok_or_else(|| {
                                StructureError::invalid(
                                    "single-pass fence references an edge outside the CFG arena",
                                )
                            })?;
                        if slot.replace(region).is_some() {
                            return Err(StructureError::invalid(
                                "one CFG edge belongs to multiple single-pass fences",
                            ));
                        }
                    }
                }
                ContainerKind::Branch(id) => {
                    let branch = &input.branches[id.index()];
                    semantics.branch_by_header[branch.branch.header.index()] = Some(region);
                    if let Some(condition) = branch
                        .condition
                        .and_then(|condition| input.conditions.get(condition.index()))
                        && let ShortCircuitExit::BranchExit { truthy, falsy } =
                            condition.candidate.exit
                    {
                        for arc in &condition.arcs {
                            let internal_len = match arc.target {
                                crate::structure::ShortCircuitTarget::Node(_) => arc.edges.len(),
                                crate::structure::ShortCircuitTarget::Value(_)
                                | crate::structure::ShortCircuitTarget::TruthyExit
                                | crate::structure::ShortCircuitTarget::FalsyExit => {
                                    arc.edges.len().saturating_sub(1)
                                }
                            };
                            for &edge in arc.edges.iter().take(internal_len) {
                                let slot = semantics
                                        .internal_transitions
                                        .get_mut(edge.index())
                                        .ok_or_else(|| {
                                            StructureError::invalid(
                                                "condition route references an edge outside the CFG arena",
                                            )
                                        })?;
                                *slot = Some(region);
                            }
                        }
                        for block in &condition.candidate.blocks {
                            for edge in &cfg.succs[block.index()] {
                                let target = cfg.edges[edge.index()].to;
                                let arm = if target == truthy {
                                    Some(super::super::BranchArm::Truthy)
                                } else if target == falsy {
                                    Some(super::super::BranchArm::Falsy)
                                } else {
                                    None
                                };
                                if let Some(arm) = arm {
                                    semantics.syntax_arms[edge.index()] = Some((region, arm));
                                    let target_is_inside = arena.region_by_block[target.index()]
                                        .is_some_and(|target_region| {
                                            arena.navigation.contains(region, target_region)
                                        });
                                    if !target_is_inside && branch.branch.merge != Some(target) {
                                        // condition evidence 只能决定真假语义，不能把
                                        // 跳回 branch containment 外的边一律当空 arm；
                                        // 只有布局紧邻的 sibling 可以自然承接，其余仍
                                        // 由 forced-goto 保留显式 transfer。
                                        semantics.forced_gotos[edge.index()] =
                                            Some(crate::structure::GotoReason::IrreducibleFlow);
                                    }
                                }
                            }
                        }
                    }
                }
                ContainerKind::Loop(id) => {
                    let loop_ = &input.loops[id.index()].candidate;
                    let partition = partitions.get(id.index()).ok_or_else(|| {
                        StructureError::invalid("selected loop has no frozen partitions")
                    })?;
                    for edge in &loop_.backedges {
                        semantics.backedges[edge.index()] = Some(region);
                    }
                    for (edge, route) in &partition.break_routes {
                        if private_tail_owns_exit(partition, *edge) {
                            // 原私有尾已独占其 MOVE/phi 和完成边；不能再把同一路径
                            // 转发到条件入口，否则会提前消费尚未执行的尾部写入。
                            continue;
                        }
                        if route
                            .iter()
                            .any(|edge| semantics.single_pass_breaks[edge.index()].is_some())
                        {
                            // 同一路径先退出内层 loop、随后退出 single-pass fence 时，
                            // 两个词法 transfer 必须分别由各自 region 发射；forwarding
                            // 不能把后一个 break 吞进前一个 edge。
                            continue;
                        }
                        if let Some(route) = semantics.forward_routes.install(
                            cfg,
                            ForwardRouteKind::ExclusiveBreak,
                            region,
                            route,
                        )? {
                            semantics.forward_routes.bind(*edge, route)?;
                        }
                    }
                    let continue_reachable = loop_
                        .continue_target
                        .map(|target| body_blocks_reaching_target(cfg, &partition.body, target))
                        .unwrap_or_default();
                    let continue_forward_index = loop_
                        .continue_target
                        .map(|target| {
                            PureContinueForwardIndex::build(
                                cfg,
                                arena,
                                partition,
                                target,
                                &forwarding.barriers,
                                &forwarding.label_targets,
                            )
                        })
                        .transpose()?;
                    let direct_latch_edges = if let Some(target) = loop_.continue_target
                        && target != loop_.header
                        && !matches!(
                            loop_.kind_hint,
                            crate::structure::LoopKindHint::RepeatLike
                                | crate::structure::LoopKindHint::NumericForLike
                                | crate::structure::LoopKindHint::GenericForLike
                        )
                        && let Some(route) = direct_continue_latch_route(
                            cfg,
                            arena,
                            partition,
                            loop_.header,
                            target,
                            &forwarding.barriers,
                        ) {
                        Some(route)
                    } else {
                        None
                    };
                    let mut direct_latch_route = None;
                    let repeat_condition_route =
                        if loop_.kind_hint == crate::structure::LoopKindHint::RepeatLike {
                            loop_
                                .continue_target
                                .and_then(|target| {
                                    repeat_continue_forwarding_route(
                                        cfg,
                                        arena,
                                        partition,
                                        loop_,
                                        target,
                                        &forwarding.barriers,
                                        &forwarding.label_targets,
                                    )
                                })
                                .map(|route| {
                                    let kind = repeat_condition_route_kind(
                                        cfg,
                                        input,
                                        input.loops[id.index()].condition,
                                        &route,
                                    )?;
                                    Ok::<_, StructureError>(kind.map(|kind| (route, kind)))
                                })
                                .transpose()?
                                .flatten()
                        } else {
                            None
                        };
                    let mut repeat_condition_route_id = None;
                    for edge in &partition.continues {
                        if semantics.breaks[edge.index()].is_some_and(|owner| owner != region)
                            || semantics
                                .break_region(*edge)
                                .is_some_and(|owner| owner != region)
                        {
                            // 同一条物理边可以先退出内层 loop，再自然进入当前
                            // repeat 的尾条件。它的显式语义属于内层 break；不能再把
                            // 整条尾条件路径绑定成外层 continue forwarding route。
                            continue;
                        }
                        if semantics.forward_routes.contains_edge(*edge) {
                            continue;
                        }
                        let Some(target) = loop_.continue_target else {
                            continue;
                        };
                        let direct = cfg.edges[edge.index()].to == target;
                        let forwarding_route = (!direct)
                            .then(|| {
                                continue_forward_index
                                    .as_ref()
                                    .and_then(|index| index.route(cfg, *edge))
                            })
                            .flatten();
                        let reaches_target = direct || forwarding_route.is_some();
                        let source_edges = &cfg.succs[cfg.edges[edge.index()].from.index()];
                        let explicit_continue = source_edges.len() == 1
                            || source_edges.iter().any(|candidate| {
                                *candidate != *edge
                                    && continue_reachable.contains(&cfg.edges[candidate.index()].to)
                            });
                        let natural_repeat_tail = loop_.kind_hint
                            == crate::structure::LoopKindHint::RepeatLike
                            && direct
                            && semantics.layout_edges[edge.index()].natural;
                        if !natural_repeat_tail
                            && reaches_target
                            && explicit_continue
                            && (continue_edge_bypasses_body(cfg, partition, *edge)
                                || (loop_.continue_edges.contains(edge)
                                    || input.loops[id.index()]
                                        .semantic_continue_edges
                                        .contains(edge))
                                    && source_edges.len() == 1)
                        {
                            if let Some(route) = forwarding_route {
                                let installed =
                                    if let Some((suffix, kind)) = repeat_condition_route.as_ref() {
                                        semantics.forward_routes.install_functional_composed(
                                            cfg, *kind, region, route, suffix,
                                        )?
                                    } else {
                                        semantics.forward_routes.install_functional(
                                            cfg,
                                            ForwardRouteKind::ContinueToTarget,
                                            region,
                                            route,
                                        )?
                                    };
                                if let Some(route_id) = installed {
                                    semantics.forward_routes.bind(*edge, route_id)?;
                                }
                            }
                            if direct {
                                if loop_.kind_hint == crate::structure::LoopKindHint::RepeatLike {
                                    let Some((route, kind)) = repeat_condition_route.as_ref()
                                    else {
                                        continue;
                                    };
                                    let route_id = if let Some(route_id) = repeat_condition_route_id
                                    {
                                        route_id
                                    } else {
                                        let Some(route_id) = semantics
                                            .forward_routes
                                            .install(cfg, *kind, region, route)?
                                        else {
                                            continue;
                                        };
                                        repeat_condition_route_id = Some(route_id);
                                        route_id
                                    };
                                    semantics.forward_routes.bind(*edge, route_id)?;
                                } else if matches!(
                                    loop_.kind_hint,
                                    crate::structure::LoopKindHint::NumericForLike
                                        | crate::structure::LoopKindHint::GenericForLike
                                ) {
                                    // VM for 的 target 已由协议 lowering 吸收，不需要额外 route。
                                } else if target != loop_.header {
                                    let Some(edges) = direct_latch_edges.as_deref() else {
                                        continue;
                                    };
                                    let route = if let Some(route) = direct_latch_route {
                                        route
                                    } else {
                                        let Some(route) = semantics.forward_routes.install(
                                            cfg,
                                            ForwardRouteKind::ContinueLatch,
                                            region,
                                            edges,
                                        )?
                                        else {
                                            continue;
                                        };
                                        direct_latch_route = Some(route);
                                        route
                                    };
                                    semantics.forward_routes.bind(*edge, route)?;
                                }
                            }
                            semantics.continues[edge.index()] = Some(region);
                            semantics.early_continues[edge.index()] = true;
                        }
                    }
                    // 残余 continue 的入口本身不属于前面的 early-continue 候选；但它若
                    // 跳到纯 latch pad，pad 到 header 的 phi copy 仍是同一轮必须执行的
                    // 动作。按 target 索引签发 ContinueLatch route，使它成为内部过渡，
                    // 防止后续的 `goto -> continue` 快路径绕过 pad 的动作。
                    if let Some(target) = loop_.continue_target
                        && let Some(entries) =
                            residual_continue_entries_by_target.get(target.index())
                        && !entries.is_empty()
                        && let Some(edges) = direct_latch_edges.as_deref()
                    {
                        let eligible_entries = entries
                            .iter()
                            .copied()
                            .filter(|entry| {
                                cfg.edges.get(entry.index()).is_some_and(|edge| {
                                    edge.to == target
                                        && partition.body.contains(&edge.from)
                                        && semantics.continue_target_region(*entry) == Some(region)
                                })
                            })
                            .collect::<Vec<_>>();
                        if !eligible_entries.is_empty() {
                            let route = if let Some(route) = direct_latch_route {
                                route
                            } else {
                                let Some(route) = semantics.forward_routes.install(
                                    cfg,
                                    ForwardRouteKind::ContinueLatch,
                                    region,
                                    edges,
                                )?
                                else {
                                    return Err(StructureError::invalid(
                                        "eligible residual continue latch route was not installed",
                                    ));
                                };
                                route
                            };
                            for entry in eligible_entries {
                                semantics.forward_routes.bind(entry, route)?;
                            }
                        }
                    }
                    let forwarded_edges = std::mem::take(
                        &mut semantics.forward_routes.edges_by_owner[region.index()],
                    );
                    for forwarded in forwarded_edges {
                        if semantics.forward_routes.kind_by_edge[forwarded.index()]
                            == Some(ForwardRouteKind::ExclusiveBreak)
                        {
                            continue;
                        }
                        semantics.internal_transitions[forwarded.index()] = Some(region);
                        let pad = cfg.edges[forwarded.index()].from;
                        for incoming in &cfg.preds[pad.index()] {
                            let source = cfg.edges[incoming.index()].from;
                            if partition.body.contains(&source) {
                                semantics.internal_transitions[incoming.index()] = Some(region);
                            }
                        }
                    }
                    let ContainerSlots::Loop { body, .. } = arena.slots[index] else {
                        return Err(StructureError::invalid(
                            "loop container has no body region slot",
                        ));
                    };
                    for block in &partition.body {
                        let source = arena.region_by_block[block.index()].ok_or_else(|| {
                            StructureError::invalid("loop body block has no containment owner")
                        })?;
                        // 到达 latch 不代表已经走完源码 body：island [A, B] 中 A 的
                        // 条件边可能跳过 B 的 break，必须保留显式跳转到条件前缀。
                        if !arena
                            .navigation
                            .region_can_complete_from(body, source, *block)
                        {
                            continue;
                        }
                        for edge in &cfg.succs[block.index()] {
                            if partition.control.contains(&cfg.edges[edge.index()].to) {
                                semantics.internal_transitions[edge.index()] = Some(region);
                                // 完整 body 的词法尾已经到达 control，不能再被早期 branch
                                // continue 候选抢占；捕获局部的 Close/JMP 也属于该尾（regress_563）。
                                // 候选拒绝[SemanticBarrier:Lifetime]：repeat 的 staged condition
                                // 可能仍在 body 内求值；删 continue 会延迟捕获关闭（regress_457）。
                                if matches!(
                                    loop_.kind_hint,
                                    crate::structure::LoopKindHint::NumericForLike
                                        | crate::structure::LoopKindHint::GenericForLike
                                ) && semantics.continues[edge.index()] == Some(region)
                                {
                                    semantics.continues[edge.index()] = None;
                                    semantics.early_continues[edge.index()] = false;
                                }
                            }
                        }
                    }
                    for block in &partition.control {
                        for edge in &cfg.succs[block.index()] {
                            if partition.control.contains(&cfg.edges[edge.index()].to) {
                                semantics.internal_transitions[edge.index()] = Some(region);
                            }
                        }
                    }
                    if let Some(normal_tail) = &partition.normal_tail {
                        for block in &normal_tail.blocks {
                            for edge in &cfg.succs[block.index()] {
                                semantics.internal_transitions[edge.index()] = Some(region);
                                semantics.normal_tail_edges[edge.index()] = true;
                            }
                        }
                    }
                    let condition_terminals = input.loops[id.index()]
                        .condition
                        .and_then(|condition| input.conditions.get(condition.index()))
                        .map(|condition| freeze_condition(proto, cfg, dataflow, condition, None))
                        .transpose()?
                        .map(|condition| [condition.truthy, condition.falsy]);
                    let control_edges =
                        freeze_loop_control_edges(cfg, loop_, partition, condition_terminals)?;
                    for edge in [control_edges.preheader_body, control_edges.preheader_exit]
                        .into_iter()
                        .flatten()
                    {
                        semantics.preheader_edges[edge.index()] = true;
                    }
                    let is_for_loop = matches!(
                        loop_.kind_hint,
                        crate::structure::LoopKindHint::NumericForLike
                            | crate::structure::LoopKindHint::GenericForLike
                    );
                    for edge in control_edges
                        .preheader_body
                        .into_iter()
                        .chain(control_edges.body)
                    {
                        semantics.syntax_arms[edge.index()] =
                            Some((region, super::super::BranchArm::LoopBody));
                        semantics.for_syntax_edges[edge.index()] = is_for_loop;
                    }
                    for edge in control_edges
                        .preheader_exit
                        .into_iter()
                        .chain(control_edges.exit)
                    {
                        semantics.syntax_arms[edge.index()] =
                            Some((region, super::super::BranchArm::LoopExit));
                        semantics.for_syntax_edges[edge.index()] = is_for_loop;
                    }
                }
                ContainerKind::ValueDecision(id) => {
                    let decision = &input.value_decisions[id.index()].candidate;
                    let ShortCircuitExit::ValueMerge(continuation) = decision.exit else {
                        return Err(StructureError::invalid(
                            "selected value decision has no merge continuation",
                        ));
                    };
                    for block in &spec.blocks {
                        for edge in &cfg.succs[block.index()] {
                            let target = cfg.edges[edge.index()].to;
                            if !spec.blocks.contains(&target) && target != continuation {
                                return Err(StructureError::invalid(
                                    "value decision has an undeclared exit",
                                ));
                            }
                            let slot = &mut semantics.value_decision_edges[edge.index()];
                            if slot.replace(region).is_some() {
                                return Err(StructureError::invalid(
                                    "one CFG edge belongs to multiple value decisions",
                                ));
                            }
                        }
                    }
                }
                ContainerKind::Island(_) | ContainerKind::Residual(_) => {}
            }
        }
        Ok(semantics)
    }

    pub(super) fn install_equal_loop_retry_gotos(
        &mut self,
        cfg: &Cfg,
        arena: &RegionArena,
        input: &FinalPlanInput,
        residual_reason_by_edge: &[Option<crate::structure::GotoReason>],
    ) -> Result<(), StructureError> {
        for (index, spec) in arena.specs.iter().enumerate() {
            let (Some(parent), Some(retry_edge)) =
                (spec.equal_loop_parent, spec.equal_loop_retry_edge)
            else {
                continue;
            };
            let ContainerKind::Loop(_) = spec.kind else {
                return Err(StructureError::invalid(
                    "equal-domain relation points to a non-loop child",
                ));
            };
            let edge = cfg.edges.get(retry_edge.index()).ok_or_else(|| {
                StructureError::invalid("equal-domain retry edge is outside the CFG arena")
            })?;
            let child_region = arena.slots[index].region();
            let parent_region = *arena
                .loop_region_by_plan
                .get(parent.index())
                .ok_or_else(|| StructureError::invalid("equal-domain retry parent is missing"))?;
            let parent_loop = input
                .loops
                .get(parent.index())
                .ok_or_else(|| StructureError::invalid("equal-domain retry loop is missing"))?;
            if !arena.navigation.contains(parent_region, child_region)
                || parent_region == child_region
                || edge.to != parent_loop.candidate.header
                || !parent_loop.candidate.backedges.contains(&retry_edge)
                || self.loops.innermost(edge.from) != Some(child_region)
                || residual_reason_by_edge
                    .get(retry_edge.index())
                    .copied()
                    .flatten()
                    != Some(crate::structure::GotoReason::CrossLoopContinueLike)
            {
                return Err(StructureError::invalid(
                    "equal-domain retry edge lost its admitted loop relation",
                ));
            }
            let slot = self
                .equal_loop_retry_gotos
                .get_mut(retry_edge.index())
                .ok_or_else(|| StructureError::invalid("equal-domain retry edge is missing"))?;
            if slot
                .replace(crate::structure::GotoReason::CrossLoopContinueLike)
                .is_some()
            {
                return Err(StructureError::invalid(
                    "one retry edge belongs to multiple equal-domain loop relations",
                ));
            }
        }
        Ok(())
    }

    pub(super) fn classify(
        &self,
        cfg: &Cfg,
        edge_ref: EdgeRef,
        goto_reason: Option<crate::structure::GotoReason>,
        caps: ControlFlowCaps,
        default_owner: RegionId,
    ) -> (RegionId, EdgeTransfer) {
        let edge = cfg.edges[edge_ref.index()];
        if !cfg.reachable_blocks.contains(&edge.from) {
            return (default_owner, EdgeTransfer::Unreachable);
        }
        match edge.kind {
            EdgeKind::Return => return (default_owner, EdgeTransfer::Return),
            EdgeKind::TailCall => return (default_owner, EdgeTransfer::TailCall),
            EdgeKind::Fallthrough
            | EdgeKind::Jump
            | EdgeKind::BranchTrue
            | EdgeKind::BranchFalse
            | EdgeKind::LoopBody
            | EdgeKind::LoopExit => {}
        }
        if self.forward_routes.kind_by_edge[edge_ref.index()]
            == Some(ForwardRouteKind::ExclusiveBreak)
            && let Some(region) = self.forward_routes.owner_by_edge[edge_ref.index()]
        {
            // entry edge 已唯一持有语义 break；route 内部 jump 只承载 move/phi
            // forwarding。若末边同时是祖先 loop backedge，则只保留祖先的迭代
            // 语义，不能再次把同一条物理边解释成内层或 single-pass break。
            return match self.backedges[edge_ref.index()] {
                Some(ancestor) if ancestor != region => {
                    (ancestor, EdgeTransfer::LoopBack(ancestor))
                }
                _ => (region, EdgeTransfer::Fallthrough),
            };
        }
        if let Some(region) = self.single_pass_breaks[edge_ref.index()] {
            if self.for_syntax_edges[edge_ref.index()]
                && let Some((loop_region, super::super::BranchArm::LoopExit)) =
                    self.syntax_arms[edge_ref.index()]
            {
                // VM-for 的 exit 同时离开祖先 single-pass fence 时，物理边仍由
                // 最内层 for protocol 吸收；祖先 break 必须紧跟源码 for 发射。
                // 把 owner 提升到 fence 会让同一条 LoopExit 丢失唯一语法 owner。
                return (loop_region, EdgeTransfer::Break(region));
            }
            return (region, EdgeTransfer::Break(region));
        }
        if self.breaks[edge_ref.index()].is_none()
            && self.break_region(edge_ref).is_none()
            && !self.layout_edges[edge_ref.index()].natural
            && let Some(kind) = shared_pure_terminal_kind(cfg, edge.to)
        {
            return (
                default_owner,
                if kind == EdgeKind::Return {
                    EdgeTransfer::Return
                } else {
                    EdgeTransfer::TailCall
                },
            );
        }
        if let Some(region) = self.value_decision_edges[edge_ref.index()] {
            return (region, EdgeTransfer::Fallthrough);
        }
        if caps.continue_stmt
            && self.early_continues[edge_ref.index()]
            && let Some(region) = self.continues[edge_ref.index()]
            && !self.is_nested_loop_exit_to_ancestor(edge_ref, edge.from, region)
            && !self.exits_nested_loop_before_continue(cfg, edge_ref, edge.from, region)
            && (!self.layout_edges[edge_ref.index()].natural
                || self.loops.control_by_block[edge.to.index()] == Some(region))
        {
            // 显式 continue 可以同时是物理 backedge；语义 transfer 必须先于
            // natural-loop latch 分类，否则 HIR 会把条件 arm 静默吞成隐式回边。
            return (region, EdgeTransfer::Continue(region));
        }
        if let Some(reason) = self.equal_loop_retry_gotos[edge_ref.index()] {
            // admission 已把该 residual edge 绑定到唯一的等域 retry/VM-for 关系；
            // 它不能再降成祖先的隐式 LoopBack，否则条件重启会被吞掉。
            return (
                default_owner,
                EdgeTransfer::Goto(LabelPlanId(edge.to.index()), reason),
            );
        }
        if let Some(region) = self.backedges[edge_ref.index()] {
            let source_loop = self.loops.innermost(edge.from);
            if self.for_syntax_edges[edge_ref.index()]
                && let Some(source) = source_loop
                && source != region
                && self.syntax_arms[edge_ref.index()]
                    == Some((source, super::super::BranchArm::LoopExit))
            {
                // VM-for 的正常 exhaustion 可以和祖先 loop backedge 共用物理边。
                // child 语法先吸收 LoopExit；祖先迭代由外围 loop 隐式完成。
                return (
                    source,
                    EdgeTransfer::BranchArm(super::super::BranchArm::LoopExit),
                );
            }
            let propagated_break =
                source_loop
                    .filter(|source| *source != region)
                    .and_then(|source| {
                        self.loops
                            .propagated_break_by_region
                            .get(source.index())
                            .copied()
                            .flatten()
                    });
            if let Some(target) = propagated_break
                && !self.normal_tail_edges[edge_ref.index()]
                && self.break_region(edge_ref) == Some(target)
            {
                return (target, EdgeTransfer::Break(target));
            }
            // 同一条物理边可以先离开内层 loop，再自然落到祖先 loop 的 latch。
            // 源码在此必须先发射内层 break；祖先回边由外围 loop 语法隐式完成。
            // normal-tail 自身的出边已经位于内层 loop 之后，不能再次解释成 break。
            if !self.normal_tail_edges[edge_ref.index()]
                && let Some(inner) = self.break_region(edge_ref)
                && inner != region
                && self.loops.innermost(edge.from) == Some(inner)
            {
                return (inner, EdgeTransfer::Break(inner));
            }
            // Luau 可把内层空 generic-for 的 VM exit 与祖先 loop backedge 合并成
            // 同一条物理边；祖先回边负责最终 transfer，内层 VM protocol 隐式吸收语法边。
            return (region, EdgeTransfer::LoopBack(region));
        }
        if self.for_syntax_edges[edge_ref.index()]
            && let Some((region, arm)) = self.syntax_arms[edge_ref.index()]
        {
            // VM-for 的 body/exit edge 先由最内层语法 owner 吸收，不能再被外层
            // break/continue 推导抢占。离开 child 后的自然布局仍由 continuation 决定。
            if arm == super::super::BranchArm::LoopExit
                && self.loops.propagated_break_by_region[region.index()]
                    .is_some_and(|target| self.break_region(edge_ref) == Some(target))
            {
                // 全部语法出口已证明共享同一外层 break 时，物理 exit 只结束当前
                // VM-for；外层 transfer 由 loop completion 统一发射一次。
                return (region, EdgeTransfer::BranchArm(arm));
            }
            if arm == super::super::BranchArm::LoopExit
                && let Some(target) = self.break_region(edge_ref)
                && target != region
                && self.loops.innermost(edge.from) == Some(region)
                && !self.break_requires_island_goto(edge_ref, edge.to, target)
            {
                // VM-for 的正常 exit 可以同时结束包含它的外层 loop。VM 语法角色
                // 已冻结在 LoopControlEdges；最终源码 transfer 必须保留外层 break，
                // 否则 HIR 会在 for 后继续执行仅供其它 exit 使用的 sibling tail。
                return (region, EdgeTransfer::Break(target));
            }
            if arm == super::super::BranchArm::LoopExit
                && !self.layout_edges[edge_ref.index()].natural
                && self.breaks[edge_ref.index()].is_none()
                && (self.layout_edges[edge_ref.index()].crosses_island_layout
                    || self
                        .loops
                        .innermost_spec(edge.from)
                        .is_some_and(|(_, owner)| {
                            self.loops.continuation[owner.index()] != Some(edge.to)
                                && self.loops.normal_tail_entry[owner.index()] != Some(edge.to)
                        }))
            {
                return (
                    region,
                    EdgeTransfer::Goto(
                        LabelPlanId(edge.to.index()),
                        goto_reason.unwrap_or(crate::structure::GotoReason::IrreducibleFlow),
                    ),
                );
            }
            return (region, EdgeTransfer::BranchArm(arm));
        }
        if let Some(region) = self.breaks[edge_ref.index()] {
            if self.break_requires_island_goto(edge_ref, edge.to, region) {
                return (
                    region,
                    EdgeTransfer::Goto(
                        LabelPlanId(edge.to.index()),
                        goto_reason.unwrap_or(crate::structure::GotoReason::IrreducibleFlow),
                    ),
                );
            }
            return (region, EdgeTransfer::Break(region));
        }
        if !self.for_syntax_edges[edge_ref.index()]
            && !self.normal_tail_edges[edge_ref.index()]
            && !self.preheader_edges[edge_ref.index()]
            && let Some(region) = self.break_region(edge_ref)
        {
            let innermost = self.loops.innermost(edge.from);
            let exits_innermost_control = innermost != Some(region)
                && innermost.is_some()
                && self.loops.control_by_block[edge.from.index()] == innermost;
            if innermost != Some(region) && !exits_innermost_control {
                if self.loops.propagates_break(edge.from, region)
                    && !self.break_requires_island_goto(edge_ref, edge.to, region)
                {
                    return (region, EdgeTransfer::Break(region));
                }
                return (
                    default_owner,
                    EdgeTransfer::Goto(
                        LabelPlanId(edge.to.index()),
                        crate::structure::GotoReason::UnstructuredBreakLike,
                    ),
                );
            }
            if self.break_requires_island_goto(edge_ref, edge.to, region) {
                return (
                    region,
                    EdgeTransfer::Goto(
                        LabelPlanId(edge.to.index()),
                        goto_reason.unwrap_or(crate::structure::GotoReason::IrreducibleFlow),
                    ),
                );
            }
            return (region, EdgeTransfer::Break(region));
        }
        let branch_owner = self.branch_by_header[edge.from.index()];
        let loop_owner = self.loops.control_by_block[edge.from.index()];
        let structured_branch_arm = branch_owner.is_some()
            && matches!(edge.kind, EdgeKind::BranchTrue | EdgeKind::BranchFalse);
        let mut branch_around_continue = false;
        if let Some(region) = self.continues[edge_ref.index()]
            && self.early_continues[edge_ref.index()]
            && !self.is_nested_loop_exit_to_ancestor(edge_ref, edge.from, region)
            && !self.exits_nested_loop_before_continue(cfg, edge_ref, edge.from, region)
            && (!self.layout_edges[edge_ref.index()].natural
                || self.loops.control_by_block[edge.to.index()] == Some(region))
        {
            if caps.continue_stmt {
                return (region, EdgeTransfer::Continue(region));
            } else if structured_branch_arm {
                // 条件 continue 总能等价写成 branch-around-tail；即使目标支持
                // continue 不可用，也只允许已经有结构化 arm ownership 的 tail 改写。
                branch_around_continue = true;
            } else {
                return (
                    region,
                    EdgeTransfer::Goto(
                        LabelPlanId(edge.to.index()),
                        crate::structure::GotoReason::UnstructuredContinueLike,
                    ),
                );
            }
        }
        if let Some((_, region)) = self.loops.innermost_spec(edge.from)
            && !matches!(
                self.syntax_arms[edge_ref.index()],
                Some((owner, super::super::BranchArm::LoopBody | super::super::BranchArm::LoopExit))
                    if owner == region
            )
            && self.loops.leaves_innermost_loop[edge_ref.index()]
            && self.loops.continuation[region.index()] != Some(edge.to)
        {
            // island 的下一个 layout item 不等于结构化 loop body 内部 edge 的自然
            // fallthrough。离开 for child 且不去其声明 continuation 的边必须在 loop
            // 语法体内显式发射，否则条件 goto 会被静默吞掉。
            return (
                region,
                EdgeTransfer::Goto(
                    LabelPlanId(edge.to.index()),
                    goto_reason.unwrap_or(crate::structure::GotoReason::UnstructuredBreakLike),
                ),
            );
        }
        if let Some(reason) = self.forced_gotos[edge_ref.index()] {
            let natural_tail_to_latch =
                structured_branch_arm && self.continue_target_region(edge_ref).is_some();
            let natural_empty_arm = self.layout_edges[edge_ref.index()].natural
                && self.syntax_arms[edge_ref.index()].is_some();
            let selected_loop_arm = matches!(
                self.syntax_arms[edge_ref.index()],
                Some((
                    _,
                    super::super::BranchArm::LoopBody | super::super::BranchArm::LoopExit
                ))
            );
            let internal_transition = self.internal_transitions[edge_ref.index()].is_some();
            if !branch_around_continue
                && !natural_tail_to_latch
                && !natural_empty_arm
                && !selected_loop_arm
                && !internal_transition
            {
                return (
                    default_owner,
                    EdgeTransfer::Goto(LabelPlanId(edge.to.index()), reason),
                );
            }
        }
        if self.layout_edges[edge_ref.index()].crosses_island_layout
            && !self.layout_edges[edge_ref.index()].natural
        {
            return (
                default_owner,
                EdgeTransfer::Goto(
                    LabelPlanId(edge.to.index()),
                    goto_reason.unwrap_or(crate::structure::GotoReason::IrreducibleFlow),
                ),
            );
        }
        if let Some((region, arm)) = self.syntax_arms[edge_ref.index()] {
            return (region, EdgeTransfer::BranchArm(arm));
        }
        if let Some(region) = self.internal_transitions[edge_ref.index()] {
            return (region, EdgeTransfer::Fallthrough);
        }
        match (edge.kind, branch_owner, loop_owner) {
            (EdgeKind::BranchTrue, Some(owner), _) | (EdgeKind::BranchTrue, None, Some(owner)) => {
                return (
                    owner,
                    EdgeTransfer::BranchArm(super::super::BranchArm::Truthy),
                );
            }
            (EdgeKind::BranchFalse, Some(owner), _)
            | (EdgeKind::BranchFalse, None, Some(owner)) => {
                return (
                    owner,
                    EdgeTransfer::BranchArm(super::super::BranchArm::Falsy),
                );
            }
            (EdgeKind::LoopBody, _, Some(owner)) => {
                return (
                    owner,
                    EdgeTransfer::BranchArm(super::super::BranchArm::LoopBody),
                );
            }
            (EdgeKind::LoopExit, _, Some(owner)) => {
                return (
                    owner,
                    EdgeTransfer::BranchArm(super::super::BranchArm::LoopExit),
                );
            }
            _ => {}
        }
        if let Some(reason) = goto_reason {
            if caps.continue_stmt
                && matches!(
                    reason,
                    crate::structure::GotoReason::UnstructuredContinueLike
                        | crate::structure::GotoReason::CrossLoopContinueLike
                )
                && let Some(region) = self.continue_target_region(edge_ref)
            {
                return (region, EdgeTransfer::Continue(region));
            }
            return (
                default_owner,
                EdgeTransfer::Goto(LabelPlanId(edge.to.index()), reason),
            );
        }
        if matches!(
            edge.kind,
            EdgeKind::BranchTrue | EdgeKind::BranchFalse | EdgeKind::LoopBody | EdgeKind::LoopExit
        ) {
            if self.layout_edges[edge_ref.index()].natural {
                return (default_owner, EdgeTransfer::Fallthrough);
            }
            return (
                default_owner,
                EdgeTransfer::Goto(
                    LabelPlanId(edge.to.index()),
                    crate::structure::GotoReason::IrreducibleFlow,
                ),
            );
        }
        if self.layout_edges[edge_ref.index()].natural {
            (default_owner, EdgeTransfer::Fallthrough)
        } else {
            (
                default_owner,
                EdgeTransfer::Goto(
                    LabelPlanId(edge.to.index()),
                    crate::structure::GotoReason::IrreducibleFlow,
                ),
            )
        }
    }

    fn break_region(&self, edge_ref: EdgeRef) -> Option<RegionId> {
        // 多层循环可能共享同一个 continuation。直接边必须退出所有这些循环，因此
        // 选择覆盖最大的最外层 region；HIR 会逐层把该 transfer 物化成 break。
        self.loops
            .break_owner_by_edge
            .get(edge_ref.index())
            .copied()
            .flatten()
    }

    fn break_requires_island_goto(
        &self,
        edge_ref: EdgeRef,
        target: BlockRef,
        region: RegionId,
    ) -> bool {
        self.loops
            .continuation
            .get(region.index())
            .copied()
            .flatten()
            == Some(target)
            && self.layout_edges[edge_ref.index()].crosses_island_layout
            && !self.layout_edges[edge_ref.index()].natural
    }

    fn continue_target_region(&self, edge: EdgeRef) -> Option<RegionId> {
        self.loops
            .continue_owner_by_edge
            .get(edge.index())
            .copied()
            .flatten()
    }

    fn is_nested_loop_exit_to_ancestor(
        &self,
        edge: EdgeRef,
        source: BlockRef,
        target: RegionId,
    ) -> bool {
        matches!(
            self.syntax_arms.get(edge.index()).copied().flatten(),
            Some((owner, super::super::BranchArm::LoopExit))
                if owner != target
                    && self.loops.innermost(source) == Some(owner)
        )
    }

    fn exits_nested_loop_before_continue(
        &self,
        cfg: &Cfg,
        edge: EdgeRef,
        source: BlockRef,
        continue_target: RegionId,
    ) -> bool {
        let exits_nested = |edge| {
            self.break_region(edge).is_some_and(|break_target| {
                break_target != continue_target
                    && self.loops.innermost(source) == Some(break_target)
            })
        };
        if exits_nested(edge) {
            return true;
        }
        // 条件 arm 可以先落到仅含 jump 的 break pad，再由该 pad 退出最内层
        // loop。早期 continue 若只看 arm 本身，会把 `break` 变成外层 continue，
        // 从而错误执行 nested repeat 的 until 条件。
        let pad = cfg.edges[edge.index()].to;
        let [next] = cfg.succs[pad.index()].as_slice() else {
            return false;
        };
        cfg.blocks[pad.index()].instrs.len == 1
            && cfg.edges[next.index()].kind == EdgeKind::Jump
            && exits_nested(*next)
    }
}
