//! 循环分区构建。输入 LoopPlanInput、图事实与方言能力，输出 preheader/control/body/continuation 和 break/continue routes；不负责 HIR 语法选择。例如 repeat 会把安全 condition blocks 纳入 control，并把真实退出留在 owner 外。

use super::*;

pub(super) struct SelectedPayloads {
    pub(super) branches: Vec<super::super::BranchPlanData>,
    pub(super) loops: Vec<super::super::LoopPlanData>,
    pub(super) loop_regions: Vec<RegionId>,
    pub(super) conditions: Vec<super::super::ConditionPlan>,
    pub(super) condition_map: Vec<Option<super::super::ConditionPlanId>>,
    pub(super) value_decisions: Vec<super::super::ValueDecisionPlan>,
    pub(super) value_decision_regions: Vec<RegionId>,
}

pub(super) struct LoopExitTailIndex {
    pub(super) by_block: Vec<Option<super::super::LoopPlanId>>,
    pub(super) by_edge: Vec<Option<super::super::LoopPlanId>>,
    pub(super) by_cleanup_instr: Vec<Option<super::super::LoopPlanId>>,
}

pub(super) fn index_loop_exit_tails(
    cfg: &Cfg,
    loops: &[super::super::LoopPlanData],
) -> Result<LoopExitTailIndex, StructureError> {
    let mut by_block = vec![None; cfg.blocks.len()];
    let mut by_edge = vec![None; cfg.edges.len()];
    let mut by_cleanup_instr = vec![None; cfg.instr_to_block.len()];
    for (index, loop_) in loops.iter().enumerate() {
        let Some(tail) = &loop_.exit_tail else {
            continue;
        };
        let id = super::super::LoopPlanId(index);
        let block_slot = by_block.get_mut(tail.block.index()).ok_or_else(|| {
            StructureError::invalid("loop exit tail references a missing execution block")
        })?;
        if block_slot.replace(id).is_some() {
            return Err(StructureError::invalid(
                "one block is shared by multiple loop exit tails",
            ));
        }
        let edge_slot = by_edge.get_mut(tail.normal_exit.index()).ok_or_else(|| {
            StructureError::invalid("loop exit tail references a missing normal edge")
        })?;
        if edge_slot.replace(id).is_some() {
            return Err(StructureError::invalid(
                "one edge is shared by multiple loop exit tails",
            ));
        }
        for instr in &tail.cleanup {
            let cleanup_slot = by_cleanup_instr.get_mut(instr.index()).ok_or_else(|| {
                StructureError::invalid("loop exit tail cleanup is outside the instruction arena")
            })?;
            if cleanup_slot.replace(id).is_some() {
                return Err(StructureError::invalid(
                    "one cleanup instruction is shared by multiple loop exit tails",
                ));
            }
        }
    }
    Ok(LoopExitTailIndex {
        by_block,
        by_edge,
        by_cleanup_instr,
    })
}

pub(super) fn build_loop_partitions(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    caps: ControlFlowCaps,
    input: &FinalPlanInput,
) -> Result<Vec<LoopPartitions>, StructureError> {
    let forwarding_barriers = input
        .scopes
        .iter()
        .flat_map(|scope| {
            scope
                .exit
                .into_iter()
                .chain(std::iter::once(scope.entry))
                .chain(
                    scope
                        .close_points
                        .iter()
                        .filter_map(|close| cfg.instr_to_block.get(close.index()).copied()),
                )
        })
        .collect();
    let label_targets = input
        .residual_transfers
        .iter()
        .filter_map(|residual| cfg.edges.get(residual.edge.index()))
        .map(|edge| edge.to)
        .collect();
    let mut branch_merge_by_header = vec![None; cfg.blocks.len()];
    for branch in &input.branches {
        branch_merge_by_header[branch.branch.header.index()] = branch.branch.merge;
    }
    let mut reachable_by_block = vec![false; cfg.blocks.len()];
    for &block in &cfg.reachable_blocks {
        let slot = reachable_by_block.get_mut(block.index()).ok_or_else(|| {
            StructureError::invalid("reachable block is outside the CFG block arena")
        })?;
        *slot = true;
    }
    let mut unstructured_by_block = vec![false; cfg.blocks.len()];
    for island in &input.unstructured {
        let blocks = island
            .layout
            .as_ref()
            .map_or(&island.fact.blocks, |layout| &layout.blocks);
        for &block in blocks {
            let slot = unstructured_by_block
                .get_mut(block.index())
                .ok_or_else(|| {
                    StructureError::invalid("unstructured block is outside the CFG block arena")
                })?;
            *slot = true;
        }
    }
    let mut residual_incidents_by_block = vec![Vec::new(); cfg.blocks.len()];
    for residual in &input.residual_transfers {
        let edge = cfg.edges.get(residual.edge.index()).ok_or_else(|| {
            StructureError::invalid("residual transfer is outside the CFG edge arena")
        })?;
        residual_incidents_by_block[edge.from.index()].push(residual.edge);
        if edge.to != edge.from {
            residual_incidents_by_block[edge.to.index()].push(residual.edge);
        }
    }
    let context = LoopPartitionContext {
        forwarding_barriers,
        label_targets,
        branch_merge_by_header,
        reachable_by_block,
        unstructured_by_block,
        residual_incidents_by_block,
    };
    let inputs = LoopPartitionInputs {
        proto,
        cfg,
        graph_facts,
        caps,
        input,
    };
    let mut workspaces = LoopPartitionWorkspaces {
        exit_pad: LoopExitPadWorkspace::new(cfg.blocks.len()),
        while_break: WhileBreakArmWorkspace::new(cfg.blocks.len(), cfg.edges.len()),
    };
    let mut partitions = Vec::with_capacity(input.loops.len());
    for (index, loop_) in input.loops.iter().enumerate() {
        partitions.push(build_loop_partition(
            &inputs,
            &context,
            &mut workspaces,
            index,
            loop_,
        )?);
    }
    Ok(partitions)
}

pub(super) fn build_loop_partition(
    inputs: &LoopPartitionInputs<'_>,
    context: &LoopPartitionContext,
    workspaces: &mut LoopPartitionWorkspaces,
    index: usize,
    loop_: &super::super::LoopPlanInput,
) -> Result<LoopPartitions, StructureError> {
    use crate::structure::LoopKindHint;

    let proto = inputs.proto;
    let cfg = inputs.cfg;
    let graph_facts = inputs.graph_facts;
    let caps = inputs.caps;
    let input = inputs.input;
    let candidate = &loop_.candidate;
    let preheader = matches!(
        candidate.kind_hint,
        LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
    )
    .then_some(candidate.preheader)
    .flatten();
    let condition_blocks = loop_
        .condition
        .map(|id| {
            input
                .conditions
                .get(id.index())
                .map(|condition| condition.candidate.blocks.clone())
                .ok_or_else(|| {
                    StructureError::invalid(format!(
                        "loop #{index} references missing condition #{}",
                        id.index()
                    ))
                })
        })
        .transpose()?;
    let condition_entry = loop_
        .condition
        .and_then(|id| input.conditions.get(id.index()))
        .map(|condition| condition.candidate.header)
        .or(candidate.condition_header)
        .or_else(|| {
            (candidate.kind_hint == LoopKindHint::RepeatLike)
                .then_some(candidate.continue_target)
                .flatten()
        })
        .unwrap_or(candidate.header);
    let repeat_condition_exit = loop_
        .condition
        .and_then(|id| input.conditions.get(id.index()))
        .and_then(|condition| match condition.candidate.exit {
            ShortCircuitExit::BranchExit { truthy, falsy }
                if candidate.kind_hint == LoopKindHint::RepeatLike =>
            {
                match (truthy == candidate.header, falsy == candidate.header) {
                    (true, false) => Some(falsy),
                    (false, true) => Some(truthy),
                    _ => None,
                }
            }
            _ => None,
        });
    let repeat_prefix_is_movable = control_prefix_is_movable(proto, cfg, condition_entry);

    let has_vm_for_edges = |block: BlockRef| {
        let mut has_body = false;
        let mut has_exit = false;
        for edge in &cfg.succs[block.index()] {
            match cfg.edges[edge.index()].kind {
                EdgeKind::LoopBody => has_body = true,
                EdgeKind::LoopExit => has_exit = true,
                _ => {}
            }
        }
        has_body && has_exit
    };
    let vm_for_control = match candidate.kind_hint {
        LoopKindHint::NumericForLike => candidate.continue_target.into_iter(),
        LoopKindHint::GenericForLike => Some(candidate.header).into_iter(),
        _ => None.into_iter(),
    }
    .filter(|block| Some(*block) != preheader)
    .filter(|block| cfg.reachable_blocks.contains(block))
    .filter(|block| has_vm_for_edges(*block))
    .collect::<BTreeSet<_>>();
    let preheader_is_vm_control = preheader.is_some_and(has_vm_for_edges);

    let mut owned = candidate.blocks.clone();
    owned.extend(candidate.control_blocks.iter().copied());
    owned.insert(candidate.header);
    if let Some(blocks) = &condition_blocks {
        owned.extend(blocks.iter().copied());
    }
    if let Some(preheader) = preheader {
        owned.insert(preheader);
    }
    match candidate.kind_hint {
        LoopKindHint::RepeatLike => {
            // natural core 不包含只经 return/break 离开的 body arm；loops pass 已用
            // 支配与真实 LoopExit 边界冻结 lexical body scope。所有带明确 VM/尾条件
            // 边界的 repeat 必须保留该证据。
            owned.extend(candidate.body_scope_blocks.iter().copied());
            // repeat 的词法 body 扩张可以包含条件成功后进入的共享尾块；完整条件 DAG
            // 已把唯一回边出口规范化到 header，因此另一语义出口必须留在 loop 外。
            if let Some(exit) = repeat_condition_exit {
                owned.remove(&exit);
            }
        }
        LoopKindHint::NumericForLike | LoopKindHint::GenericForLike if !caps.goto_label => {
            // 无 goto 目标不能把首轮 body prefix 或 terminal arm 留成跨 loop 跳转；
            // goto-capable 目标则保留 mixed island，避免把不可规约 for 网格强压进树。
            owned.extend(candidate.body_scope_blocks.iter().copied());
        }
        LoopKindHint::WhileLike => {
            let natural = merged_natural_loop_domain(cfg, candidate);
            owned.retain(|block| natural.contains(block) || Some(*block) == preheader);
            owned.insert(candidate.header);
            let lexical_continuation = loop_.continuation.or_else(|| {
                let mut exits = condition_blocks
                    .as_ref()
                    .into_iter()
                    .flat_map(|blocks| blocks.iter().copied())
                    .chain(candidate.condition_header)
                    .chain(std::iter::once(candidate.header))
                    .flat_map(|block| cfg.succs[block.index()].iter().copied())
                    .map(|edge| cfg.edges[edge.index()].to)
                    .filter(|target| !natural.contains(target) && *target != cfg.exit_block)
                    .collect::<BTreeSet<_>>();
                (exits.len() == 1).then(|| exits.pop_first()).flatten()
            });
            let break_arms = verified_while_break_arms(
                cfg,
                graph_facts,
                context,
                WhileBreakArmDomain {
                    candidate,
                    natural: &natural,
                    condition_blocks: condition_blocks.as_ref(),
                    continuation: lexical_continuation,
                },
                &mut workspaces.while_break,
            )?;
            owned.extend(break_arms);
        }
        LoopKindHint::Unknown => {
            let terminal_condition_arm = loop_
                .condition
                .and_then(|id| input.conditions.get(id.index()))
                .and_then(|condition| match condition.candidate.exit {
                    ShortCircuitExit::BranchExit { truthy, falsy } => {
                        match (owned.contains(&truthy), owned.contains(&falsy)) {
                            (true, false) => Some(falsy),
                            (false, true) => Some(truthy),
                            (true, true) | (false, false) => None,
                        }
                    }
                    ShortCircuitExit::ValueMerge(_) => None,
                })
                .filter(|terminal| {
                    candidate.exits.contains(terminal)
                        && candidate
                            .exits
                            .iter()
                            .any(|exit| exit != terminal && *exit != cfg.exit_block)
                })
                .and_then(|terminal| closed_linear_terminal_arm(proto, cfg, terminal, &owned));
            if let Some(terminal) = terminal_condition_arm {
                // terminal arm 是 loop 内的早退，不是词法 continuation。把这个唯一入口
                // 的线性 return 链收进 body 后，Unknown loop 可稳定冻结为 `while true`
                // 加 guard，真正的 break 目标仍是唯一的非终止出口。
                owned.extend(terminal);
            }
        }
        _ => {}
    }
    if let Some(continuation) = loop_.continuation {
        // lexical body evidence 可能包含所有 break arm 汇入的共享 merge，Lua 5.5
        // 的 Close pad 尤其常见；但已声明 continuation 按合同一定在 loop 外，
        // 继续持有它只会制造虚假的多入口 loop。
        owned.remove(&continuation);
    }
    owned = reachable_nonempty_blocks(cfg, owned);
    let complete_unknown_condition = loop_
        .condition
        .and_then(|id| input.conditions.get(id.index()))
        .is_some_and(|condition| {
            let crate::structure::ShortCircuitExit::BranchExit { truthy, falsy } =
                condition.candidate.exit
            else {
                return false;
            };
            let is_body = |target| owned.contains(&target) && Some(target) != preheader;
            is_body(truthy) != is_body(falsy)
        });

    let mut control = match candidate.kind_hint {
        LoopKindHint::WhileLike => condition_blocks.unwrap_or_else(|| {
            BTreeSet::from([candidate.condition_header.unwrap_or(candidate.header)])
        }),
        LoopKindHint::RepeatLike => {
            if let Some(blocks) = condition_blocks {
                blocks
            } else {
                let loop_domain = owned
                    .iter()
                    .copied()
                    .filter(|block| Some(*block) != preheader)
                    .collect::<BTreeSet<_>>();
                let mut latches = BTreeSet::new();
                let mut frontier = candidate
                    .backedges
                    .iter()
                    .filter_map(|edge| cfg.edges.get(edge.index()))
                    .filter(|edge| edge.to == candidate.header)
                    .map(|edge| edge.from)
                    .collect::<BTreeSet<_>>();
                let mut visited = frontier.clone();
                while !frontier.is_empty() {
                    latches.extend(frontier.iter().copied().filter(|source| {
                        cfg.succs[source.index()].iter().any(|edge| {
                            let edge = cfg.edges[edge.index()];
                            edge.kind == EdgeKind::LoopExit || !loop_domain.contains(&edge.to)
                        })
                    }));
                    if !latches.is_empty() {
                        break;
                    }
                    let mut predecessors = BTreeSet::new();
                    for block in &frontier {
                        predecessors.extend(cfg.preds[block.index()].iter().filter_map(|edge| {
                            let source = cfg.edges[edge.index()].from;
                            (loop_domain.contains(&source) && visited.insert(source))
                                .then_some(source)
                        }));
                    }
                    frontier = predecessors;
                }
                if latches.is_empty() {
                    return Err(StructureError::invalid(format!(
                        "repeat loop #{index} has no condition latch on a backedge path to {}",
                        candidate.header
                    )));
                }
                latches
            }
        }
        LoopKindHint::NumericForLike | LoopKindHint::GenericForLike => {
            if vm_for_control.is_empty() && !preheader_is_vm_control {
                return Err(StructureError::invalid(format!(
                    "{:?} loop #{index} has no VM control block with LoopBody and LoopExit edges",
                    candidate.kind_hint
                )));
            }
            vm_for_control
        }
        LoopKindHint::WhileTrueLike => BTreeSet::new(),
        // Unknown 只在已经选出 loop condition 时冻结 control；没有条件证据时仍以
        // `while true` 降低，避免把普通 body branch 猜成源码 loop 条件。
        LoopKindHint::Unknown => condition_blocks
            .filter(|_| complete_unknown_condition)
            .unwrap_or_default(),
    };
    control = reachable_nonempty_blocks(cfg, control);
    if let Some(preheader) = preheader {
        control.remove(&preheader);
    }
    let exit_pads = verified_loop_exit_pads(
        cfg,
        candidate,
        loop_.continuation,
        &owned,
        &control,
        &mut workspaces.exit_pad,
    )?;
    owned.extend(exit_pads);
    if matches!(
        candidate.kind_hint,
        LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
    ) {
        control.extend(for_latch_exit_control_pads(proto, cfg, &control, &owned));
        control.extend(
            candidate
                .normalized_exit_aliases
                .iter()
                .map(|alias| alias.block),
        );
    }
    owned.extend(control.iter().copied());
    if matches!(
        candidate.kind_hint,
        LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
    ) && let Some(preheader) = preheader
    {
        for edge in &cfg.succs[preheader.index()] {
            let edge = cfg.edges[edge.index()];
            if edge.kind == EdgeKind::LoopExit {
                owned.remove(&edge.to);
            }
        }
    }
    let body = owned
        .iter()
        .copied()
        .filter(|block| Some(*block) != preheader && !control.contains(block))
        .collect::<BTreeSet<_>>();
    let is_own_branch_continuation = |edge: EdgeRef| {
        let edge = cfg.edges[edge.index()];
        context.branch_merge_by_header[edge.from.index()] == Some(edge.to)
    };
    let mut continues = candidate.continue_edges.clone();
    continues.extend(loop_.semantic_continue_edges.iter().copied());
    // branch continuation 只描述 containment 边界；带语句的 continue 也可能恰好是
    // natural backedge，只有 partition 证明它跳过同级 body tail 时才保留显式语义。
    continues.retain(|edge| {
        let source = cfg.edges[edge.index()].from;
        let proven_body_bypass =
            caps.continue_stmt && continue_edge_bypasses_body_parts(cfg, &body, *edge);
        !matches!(
            cfg.edges[edge.index()].kind,
            EdgeKind::Fallthrough | EdgeKind::LoopBody | EdgeKind::LoopExit
        ) && (!is_own_branch_continuation(*edge)
            || loop_.semantic_continue_edges.contains(edge)
            || proven_body_bypass
            || candidate.kind_hint == LoopKindHint::RepeatLike && repeat_prefix_is_movable)
            && (candidate.backedges.binary_search(edge).is_err()
                || cfg.succs[source.index()].len() > 1
                || proven_body_bypass
                || loop_.semantic_continue_edges.contains(edge))
    });
    let continue_target_carries_body_tail = candidate.kind_hint == LoopKindHint::NumericForLike
        && candidate
            .continue_target
            .is_some_and(|target| block_has_non_control_prefix(proto, cfg, target));
    if let Some(target) = candidate.continue_target
        && !continue_target_carries_body_tail
    {
        let reaches_target = body_blocks_reaching_target(cfg, &body, target);
        let forward_index = PureContinueForwardIndex::build_cfg(
            cfg,
            &body,
            target,
            &context.forwarding_barriers,
            &context.label_targets,
        )?;
        for block in &body {
            for edge in &cfg.succs[block.index()] {
                let own_branch_continuation = is_own_branch_continuation(*edge);
                let relaxed_own_continuation = caps.continue_stmt
                    && own_branch_continuation
                    && !(candidate.kind_hint == LoopKindHint::RepeatLike
                        && candidate.continue_target.is_some_and(|target| {
                            branch_conditions_share_subject(proto, cfg, *block, target)
                        }));
                if !matches!(
                    cfg.edges[edge.index()].kind,
                    EdgeKind::Fallthrough | EdgeKind::LoopBody | EdgeKind::LoopExit
                ) && candidate.backedges.binary_search(edge).is_err()
                    && (!own_branch_continuation || relaxed_own_continuation)
                    && continue_edge_bypasses_body_parts(cfg, &body, *edge)
                    && continue_pad_sibling_reaches_target(cfg, *edge, &reaches_target)
                    && (candidate.kind_hint != LoopKindHint::RepeatLike || repeat_prefix_is_movable)
                    && (cfg.edges[edge.index()].to == target
                        || forward_index.route(cfg, *edge).is_some())
                {
                    continues.insert(*edge);
                }
            }
        }
    }
    let exit_targets = owned
        .iter()
        .flat_map(|block| cfg.succs[block.index()].iter())
        .map(|edge| cfg.edges[edge.index()].to)
        .filter(|target| !owned.contains(target))
        .collect::<BTreeSet<_>>();
    let control_exit_targets = control
        .iter()
        .flat_map(|block| cfg.succs[block.index()].iter())
        .map(|edge| cfg.edges[edge.index()].to)
        .filter(|target| !owned.contains(target))
        .collect::<BTreeSet<_>>();
    let lexical_exit_targets = exit_targets
        .iter()
        .copied()
        .filter(|target| *target != cfg.exit_block)
        .collect::<Vec<_>>();
    let continuation = loop_
        .continuation
        .filter(|target| exit_targets.contains(target))
        .or_else(|| {
            (candidate.exits.len() == 1)
                .then(|| candidate.exits.first().copied())
                .flatten()
                .filter(|target| exit_targets.contains(target))
        })
        .or_else(|| {
            (control_exit_targets.len() == 1)
                .then(|| control_exit_targets.first().copied())
                .flatten()
        })
        // 终止型 body 可能让 VM latch/normal exit 不可达；synthetic exit 只表示
        // return/tailcall，不应和唯一的词法 break 目标竞争 continuation。
        .or_else(|| {
            (lexical_exit_targets.len() == 1)
                .then(|| lexical_exit_targets.first().copied())
                .flatten()
        })
        .or_else(|| {
            (exit_targets.len() == 1)
                .then(|| exit_targets.first().copied())
                .flatten()
        });
    let mut break_routes = BTreeMap::new();
    if let Some(target) = continuation {
        for block in &control {
            for edge in &cfg.succs[block.index()] {
                let cfg_edge = cfg.edges[edge.index()];
                if cfg_edge.kind != EdgeKind::LoopExit
                    && cfg_edge.to != target
                    && !owned.contains(&cfg_edge.to)
                    && let Some(route) = exclusive_break_forwarding_route(
                        proto,
                        cfg,
                        *edge,
                        target,
                        &context.forwarding_barriers,
                        &context.label_targets,
                    )
                {
                    break_routes.insert(*edge, route);
                }
            }
        }
    }
    let normal_tail = detect_normal_loop_tail(
        proto,
        cfg,
        NormalLoopTailDomain {
            candidate,
            preheader,
            control: &control,
            body: &body,
            owned: &owned,
            continuation,
        },
    );

    Ok(LoopPartitions {
        preheader,
        control,
        body,
        owned,
        continuation,
        continues,
        break_routes,
        normal_tail,
    })
}
