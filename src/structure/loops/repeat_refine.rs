//! 用安全短路条件证据细化 repeat 候选及嵌套 for 出口；依赖候选集合和 CFG，
//! 不负责初始 natural-loop 发现；例如把伪 while header 恢复为 repeat 尾条件。
//! 多叶条件保留完整 DAG 根与候选末叶，最终分区再按完整条件冻结 continue 入口。

use super::*;

pub(in crate::structure) struct RepeatRefinementInput<'a> {
    pub(in crate::structure) proto: &'a LoweredProto,
    pub(in crate::structure) cfg: &'a Cfg,
    pub(in crate::structure) graph_facts: &'a GraphFacts,
    pub(in crate::structure) dataflow: &'a DataflowFacts,
    pub(in crate::structure) branches: &'a [BranchCandidate],
    pub(in crate::structure) supplements: &'a [ShortCircuitCandidate],
}

pub(in crate::structure) fn refine_short_circuit_repeat_candidates(
    input: RepeatRefinementInput<'_>,
    short_circuits: &mut Vec<ShortCircuitCandidate>,
    candidates: &mut [LoopCandidate],
) {
    let RepeatRefinementInput {
        proto,
        cfg,
        graph_facts,
        dataflow,
        branches,
        supplements,
    } = input;
    let current_by_exit = short_circuits_by_exit(cfg.blocks.len(), short_circuits);
    let supplements_by_exit = short_circuits_by_exit(cfg.blocks.len(), supplements);
    let mut branch_by_header = vec![None; cfg.blocks.len()];
    for branch in branches {
        let slot = &mut branch_by_header[branch.header.index()];
        if slot.is_none() {
            *slot = Some(branch);
        }
    }
    let mut repeat_wrapper_by_header = vec![None; cfg.blocks.len()];
    for (index, candidate) in candidates.iter().enumerate() {
        if candidate.kind_hint != LoopKindHint::RepeatLike {
            continue;
        }
        let slot = &mut repeat_wrapper_by_header[candidate.header.index()];
        if slot
            .is_none_or(|current: usize| candidates[current].blocks.len() < candidate.blocks.len())
        {
            *slot = Some(index);
        }
    }
    let nested_under_same_header_repeat = candidates
        .iter()
        .enumerate()
        .map(|(index, candidate)| {
            repeat_wrapper_by_header[candidate.header.index()].is_some_and(|wrapper| {
                wrapper != index
                    && candidate.blocks.len() < candidates[wrapper].blocks.len()
                    && candidates[wrapper]
                        .continue_target
                        .is_some_and(|target| candidate.exits.contains(&target))
            })
        })
        .collect::<Vec<_>>();
    let mut accepted_supplements = Vec::new();
    let mut shared_exit_workspace = SharedExitWorkspace::new(cfg.blocks.len());

    for (index, candidate) in candidates.iter_mut().enumerate() {
        // 初始 RepeatLike 也可能只从 jump latch 识别到尾条件的最后一项。
        // 完整 DAG 的入口仍须参与精化，否则跳入前置条件的 continue 会落成正文合流。
        if !matches!(
            candidate.kind_hint,
            LoopKindHint::Unknown
                | LoopKindHint::WhileLike
                | LoopKindHint::WhileTrueLike
                | LoopKindHint::RepeatLike
        ) {
            continue;
        }
        let backedge_sources = candidate
            .backedges
            .iter()
            .map(|edge| cfg.edges[edge.index()].from)
            .collect::<Vec<_>>();
        let match_at = |backedge_target: BlockRef, owned_sources: Option<&[BlockRef]>| {
            repeat_short_circuit_match(
                proto,
                cfg,
                graph_facts,
                candidate,
                &current_by_exit[backedge_target.index()],
                backedge_target,
                owned_sources,
            )
            .map(|(target, short)| {
                (
                    target,
                    Some(short.header),
                    Some(short.header),
                    Option::<ShortCircuitCandidate>::None,
                    Option::<BlockRef>::None,
                )
            })
            .or_else(|| {
                repeat_short_circuit_match(
                    proto,
                    cfg,
                    graph_facts,
                    candidate,
                    &supplements_by_exit[backedge_target.index()],
                    backedge_target,
                    owned_sources,
                )
                .map(|(target, short)| {
                    (
                        target,
                        Some(short.header),
                        Some(short.header),
                        Some(short.clone()),
                        None,
                    )
                })
            })
        };
        let grouped = match_at(candidate.header, Some(&backedge_sources));
        let single = (backedge_sources.len() == 1).then(|| {
            let backedge_source = backedge_sources[0];
            let jump_backedge = matches!(
                cfg.terminator(&proto.instrs, backedge_source),
                Some(LowInstr::Jump(jump))
                    if cfg.instr_to_block[jump.target.index()] == candidate.header
            );
            jump_backedge
                .then(|| match_at(backedge_source, None))
                .flatten()
                .or_else(|| {
                    if nested_under_same_header_repeat[index] {
                        // 同 header 的外层 repeat 已唯一拥有该尾条件时，内层
                        // WhileLike 的 body-break 也会呈现为“分支后汇入尾条件”。
                        // 这里保留 header 的 while 证据，避免同一尾条件被两个 loop
                        // 重复解释成 repeat。
                        return None;
                    }
                    direct_branch_repeat_continue_target(
                        proto,
                        cfg,
                        graph_facts,
                        &branch_by_header,
                        candidate,
                        backedge_source,
                    )
                    .map(|(target, exit_merge)| (target, None, None, None, Some(exit_merge)))
                })
        });
        let Some((continue_target, condition_header, dominance_entry, supplement, exit_merge)) =
            grouped.or_else(|| single.flatten())
        else {
            continue;
        };
        // repeat 的条件入口必须支配最终回边源；否则存在不经过该条件就回到 header 的
        // 路径，它只能是 while/while-true 中的提前 continue。把这种形状精化成 repeat
        // 会让 continue 错误执行原本应跳过的尾条件。
        // 单回边经共享 jump pad 时，最终 condition node 不支配 pad，但完整短路
        // condition 的 header 必须支配它。最终冻结也必须从这个 header 消费同一张
        // DAG；若只记录末尾 node，前置短路项会退化成无行为的 body branch。
        let condition_entry = dominance_entry
            .or(condition_header)
            .unwrap_or(continue_target);
        if backedge_sources
            .iter()
            .any(|source| !graph_facts.dominates(condition_entry, *source))
        {
            continue;
        }
        if let Some(supplement) = supplement {
            accepted_supplements.push(supplement);
        }

        candidate.kind_hint = LoopKindHint::RepeatLike;
        candidate.continue_target = Some(continue_target);
        candidate.condition_header = condition_header;
        let shared_exit =
            shared_exit_continuation(proto, &candidate.exits, cfg, &mut shared_exit_workspace);
        candidate.body_scope_blocks = loop_body_scope(
            (candidate.kind_hint, candidate.continue_target),
            &candidate.blocks,
            &candidate.exits,
            shared_exit.as_ref(),
            candidate.header,
            cfg,
            graph_facts,
        );
        if let Some(exit_merge) = exit_merge {
            install_refined_repeat_exit_merge(dataflow, candidate, exit_merge);
        }
    }

    short_circuits.extend(accepted_supplements);
    let mut unique = std::mem::take(short_circuits)
        .into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    unique.sort_by_key(|candidate| {
        (
            candidate.header,
            candidate.blocks.len(),
            candidate.nodes.len(),
            candidate.result_reg.map(Reg::index),
        )
    });
    *short_circuits = unique;
}

pub(super) fn install_refined_repeat_exit_merge(
    dataflow: &DataflowFacts,
    candidate: &mut LoopCandidate,
    exit_merge: BlockRef,
) {
    let mut ownership_blocks = candidate.body_scope_blocks.clone();
    ownership_blocks.extend(candidate.exits.iter().copied());
    ownership_blocks.remove(&exit_merge);
    let Some(exit_value_merge) =
        loop_exit_value_merge_in_block(dataflow, exit_merge, &ownership_blocks)
    else {
        return;
    };
    candidate
        .exit_value_merges
        .retain(|candidate| candidate.exit != exit_merge);
    candidate.exit_value_merges.push(exit_value_merge);
    candidate
        .exit_value_merges
        .sort_by_key(|candidate| candidate.exit);
}

pub(super) fn repeat_short_circuit_match<'a>(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    candidate: &LoopCandidate,
    shorts: &[&'a ShortCircuitCandidate],
    backedge_target: BlockRef,
    owned_backedge_sources: Option<&[BlockRef]>,
) -> Option<(BlockRef, &'a ShortCircuitCandidate)> {
    let backedge_sources =
        owned_backedge_sources.unwrap_or_else(|| std::slice::from_ref(&backedge_target));
    shorts
        .iter()
        .copied()
        .filter_map(|short| {
            if candidate.kind_hint == LoopKindHint::RepeatLike {
                let tail = candidate.condition_header.or(candidate.continue_target)?;
                // 已识别的 repeat 只能补齐原尾条件，不能用正文 break guard 替换它。
                // 新入口须在正文 header 之后且无独立前缀；带 CALL/写入的尾 guard
                // 仍由原 body/condition owner 保持求值位置，交给后续有序条件折叠。
                if short.header == candidate.header
                    || short.header == tail
                    || !short.blocks.contains(&tail)
                    || backedge_has_non_cleanup_prefix(proto, cfg, short.header)
                {
                    return None;
                }
            }
            ((owned_backedge_sources.is_none()
                || backedge_sources
                    .iter()
                    .all(|source| short.blocks.contains(source)))
                && backedge_sources
                    .iter()
                    .all(|source| graph_facts.dominates(short.header, *source)))
            .then(|| {
                repeat_short_circuit_continue_target(
                    proto,
                    cfg,
                    graph_facts,
                    short,
                    candidate,
                    backedge_target,
                    backedge_sources,
                )
                .map(|target| (target, short))
            })
            .flatten()
        })
        .max_by_key(|(_, short)| (short.nodes.len(), short.blocks.len()))
}

pub(super) fn short_circuits_by_exit(
    block_count: usize,
    short_circuits: &[ShortCircuitCandidate],
) -> Vec<Vec<&ShortCircuitCandidate>> {
    let mut by_exit = vec![Vec::new(); block_count];
    for short in short_circuits {
        if let ShortCircuitExit::BranchExit { truthy, falsy } = short.exit {
            by_exit[truthy.index()].push(short);
            by_exit[falsy.index()].push(short);
        }
    }
    by_exit
}

pub(super) fn repeat_short_circuit_continue_target(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    short: &ShortCircuitCandidate,
    candidate: &LoopCandidate,
    backedge_target: BlockRef,
    backedge_sources: &[BlockRef],
) -> Option<BlockRef> {
    let ShortCircuitExit::BranchExit { truthy, falsy } = short.exit else {
        return None;
    };
    let loop_exit = if truthy == backedge_target {
        falsy
    } else if falsy == backedge_target {
        truthy
    } else {
        return None;
    };
    let header_exit_rejoins_tail =
        while_header_exit_rejoins_repeat_exit(proto, cfg, graph_facts, candidate, loop_exit);
    if !short.reducible
        || !candidate.blocks.contains(&short.header)
        // while true 的 header 可以同时承载本轮正文和提前 break guard。若它经一条
        // 非 cleanup 正文路径到 jump latch，不能把这条路径反推成 repeat 尾条件；
        // Close 仍可作为 goto/repeat 的词法清理 pad，由后续 scope owner 接管。
        || backedge_sources.iter().any(|source| {
            (short.header == candidate.header || !short.blocks.contains(source))
                && backedge_has_non_cleanup_prefix(proto, cfg, *source)
        })
        || (candidate.kind_hint == LoopKindHint::WhileLike && !header_exit_rejoins_tail)
        || (short.nodes.len() == 1 && candidate.exits.len() != 1 && !header_exit_rejoins_tail)
        || !short.blocks.is_subset(&candidate.blocks)
        || !candidate.exits.contains(&loop_exit)
    {
        return None;
    }

    let mut final_nodes = short.nodes.iter().filter(|node| {
        matches!(
            node.truthy,
            ShortCircuitTarget::TruthyExit | ShortCircuitTarget::FalsyExit
        ) && matches!(
            node.falsy,
            ShortCircuitTarget::TruthyExit | ShortCircuitTarget::FalsyExit
        )
    });
    let final_node = final_nodes.next()?;
    final_nodes.next().is_none().then_some(final_node.header)
}

pub(super) fn backedge_has_non_cleanup_prefix(
    proto: &LoweredProto,
    cfg: &Cfg,
    block: BlockRef,
) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    let end = range.last().map_or(range.end(), |last| last.index());
    (range.start.index()..end)
        .any(|instr_index| !matches!(proto.instrs[instr_index], LowInstr::Close(_)))
}

pub(super) fn while_header_exit_rejoins_repeat_exit(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    candidate: &LoopCandidate,
    repeat_exit: BlockRef,
) -> bool {
    if candidate.kind_hint != LoopKindHint::WhileLike {
        return false;
    }
    let Some((then_edge, else_edge)) = cfg.branch_edges(candidate.header) else {
        return false;
    };
    let mut header_exits = [then_edge, else_edge]
        .into_iter()
        .map(|edge| cfg.edges[edge.index()].to)
        .filter(|target| !candidate.blocks.contains(target));
    let Some(header_exit) = header_exits.next() else {
        return false;
    };
    if graph_facts.dominates(header_exit, candidate.header) {
        // 候选拒绝[SemanticBarrier:ControlFlow]：goto_06 的内层 while 出口是外层
        // 回边；最终出口虽然后支配它，却不是本轮尾合流，不能将该路径吸收到 repeat。
        return false;
    }

    header_exits.next().is_none()
        && candidate.exits.contains(&header_exit)
        && ((candidate.backedges.len() > 1
            && (header_exit == repeat_exit
                || matches!(
                    cfg.terminator(&proto.instrs, header_exit),
                    Some(LowInstr::Return(_) | LowInstr::TailCall(_))
                )))
            || (header_exit != repeat_exit && graph_facts.post_dominates(repeat_exit, header_exit)))
}

pub(super) fn direct_branch_repeat_continue_target(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    branch_by_header: &[Option<&BranchCandidate>],
    candidate: &LoopCandidate,
    backedge_source: BlockRef,
) -> Option<(BlockRef, BlockRef)> {
    if candidate.kind_hint != LoopKindHint::WhileLike {
        return None;
    }
    let condition = cfg.branch_edges(backedge_source).map_or_else(
        || repeat_continue_target_via_backedge_pad(proto, cfg, backedge_source, &candidate.blocks),
        |_| Some(backedge_source),
    )?;
    let loop_target = if condition == backedge_source {
        candidate.header
    } else {
        backedge_source
    };
    let (then_edge, else_edge) = cfg.branch_edges(condition)?;
    let (then_target, else_target) = (
        cfg.edges[then_edge.index()].to,
        cfg.edges[else_edge.index()].to,
    );
    let repeat_exit = match (then_target == loop_target, else_target == loop_target) {
        (true, false) => else_target,
        (false, true) => then_target,
        _ => return None,
    };
    if !candidate.exits.contains(&repeat_exit) {
        return None;
    }

    let mut header_exits = cfg
        .branch_edges(candidate.header)
        .into_iter()
        .flat_map(|(then_edge, else_edge)| [then_edge, else_edge])
        .map(|edge| cfg.edges[edge.index()].to)
        .filter(|target| !candidate.blocks.contains(target));
    let header_exit = header_exits.next()?;
    if header_exits.next().is_some()
        || header_exit == repeat_exit
        || !candidate.exits.contains(&header_exit)
    {
        return None;
    }
    // 标准 Lua 会让尾条件 exit 直接跳过 body 的 break pad；两条路径只在该 pad
    // 已确认的 merge 重新汇合。分支臂消费候选的 merge，其余臂要求完整后支配证书。
    let exit_merge = branch_by_header[header_exit.index()]
        .and_then(|branch| branch.merge)
        .and_then(|merge| {
            repeat_exit_merge_after_guard(proto, cfg, graph_facts, repeat_exit, merge)
        })
        .or_else(|| {
            // 候选拒绝[LayerBoundary]：纯转发 pad 没有待认领的正文，继续由既有
            // loop 出口值协议处理；不能仅因后支配关系改选并行快照的结构。
            if cfg
                .non_control_instr_range(&proto.instrs, header_exit)
                .is_empty()
            {
                return None;
            }
            // 展开的退出臂未必有 BranchCandidate；共用短路 repeat 的后支配证明，
            // 由 body scope 与最终分区保留臂内操作，不把它们移到带标记的循环外尾部。
            while_header_exit_rejoins_repeat_exit(proto, cfg, graph_facts, candidate, repeat_exit)
                .then_some(repeat_exit)
        })?;
    if exit_merge == cfg.exit_block || candidate.blocks.contains(&exit_merge) {
        return None;
    }

    Some((condition, exit_merge))
}

pub(super) fn repeat_exit_merge_after_guard(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    repeat_exit: BlockRef,
    early_exit_merge: BlockRef,
) -> Option<BlockRef> {
    if repeat_exit == early_exit_merge {
        return Some(early_exit_merge);
    }
    let repeat_continuation = transparent_loop_exit_target(proto, cfg, repeat_exit)
        .or_else(|| cfg.unique_reachable_successor(repeat_exit))?;
    (repeat_continuation == early_exit_merge
        || graph_facts.post_dominates(repeat_continuation, early_exit_merge))
    .then_some(repeat_continuation)
}

pub(super) fn refine_ambiguous_repeat_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    shared_exit_workspace: &mut SharedExitWorkspace,
    candidates: &mut [LoopCandidate],
) {
    // repeat body 若进入 nested loop，natural-loop core 会把该入口误看成 header exit；
    // 独立尾条件与 header 分支读取同一主体，或尾条件直接完成祖先 for 的本轮迭代时，
    // header 的另一臂可仍属于 repeat 正文；不能把尾条件出口当作内层 while 的空操作。
    // repeat 后再 break 外层 for 时，条件出口又会像 while true 的 terminal exit。
    // 两者都只能等候选齐全后用关系证据消歧，不能全局提高 repeat 启发式优先级。
    let mut for_owners = vec![Vec::new(); cfg.blocks.len()];
    let mut for_backedges = vec![false; cfg.edges.len()];
    for (index, candidate) in candidates.iter().enumerate() {
        if !matches!(
            candidate.kind_hint,
            LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
        ) {
            continue;
        }
        for block in &candidate.body_scope_blocks {
            for_owners[block.index()].push(index);
        }
        for edge in &candidate.backedges {
            for_backedges[edge.index()] = true;
        }
    }
    let mut loop_entries = vec![Vec::new(); cfg.blocks.len()];
    for (index, candidate) in candidates.iter().enumerate() {
        loop_entries[candidate.header.index()].push(index);
        if let Some(preheader) = candidate.preheader {
            loop_entries[preheader.index()].push(index);
        }
    }

    for index in 0..candidates.len() {
        let candidate = &candidates[index];
        if !matches!(
            candidate.kind_hint,
            LoopKindHint::WhileLike | LoopKindHint::WhileTrueLike
        ) || candidate.backedges.len() != 1
        {
            continue;
        }
        let source = cfg.edges[candidate.backedges[0].index()].from;
        let Some(continue_target) =
            branch_has_header_and_exit(cfg, source, candidate.header, &candidate.blocks)
                .then_some(source)
                .or_else(|| {
                    repeat_continue_target_via_backedge_pad(proto, cfg, source, &candidate.blocks)
                })
        else {
            continue;
        };
        let shared_exit =
            shared_exit_continuation(proto, &candidate.exits, cfg, shared_exit_workspace);
        let repeat_body_scope = loop_body_scope(
            (LoopKindHint::RepeatLike, Some(continue_target)),
            &candidate.blocks,
            &candidate.exits,
            shared_exit.as_ref(),
            candidate.header,
            cfg,
            graph_facts,
        );
        let is_repeat = match candidate.kind_hint {
            LoopKindHint::WhileLike => {
                continue_target != candidate.header
                    && (branch_conditions_share_subject(
                        proto,
                        cfg,
                        candidate.header,
                        continue_target,
                    ) || cfg.succs[continue_target.index()].iter().any(|edge| {
                        let target = cfg.edges[edge.index()].to;
                        // 该原边属于祖先 for 的回边，且确实离开当前 core。
                        // 结合下方 nested body 的完整包含证明，按 repeat 保留两种出口：
                        // 正常尾条件完成本轮，header 另一臂先执行嵌套正文再退出。
                        for_backedges[edge.index()]
                            && !candidate.blocks.contains(&target)
                            && graph_facts.dominates(target, candidate.header)
                    }))
                    && cfg
                        .branch_edges(candidate.header)
                        .into_iter()
                        .flat_map(|(then_edge, else_edge)| [then_edge, else_edge])
                        .map(|edge| cfg.edges[edge.index()].to)
                        .filter(|target| !candidate.blocks.contains(target))
                        .flat_map(|target| loop_entries[target.index()].iter())
                        .copied()
                        .filter(|nested| *nested != index)
                        .any(|nested| {
                            // 立即 break 的 for 仍保留不可达 latch 以证明 VM 协议，
                            // 词法正文包含关系只约束可执行块，不把该 latch 当作额外出口。
                            candidates[nested]
                                .blocks
                                .iter()
                                .filter(|block| cfg.reachable_blocks.contains(block))
                                .all(|block| repeat_body_scope.contains(block))
                        })
            }
            LoopKindHint::WhileTrueLike => for_owners[candidate.header.index()]
                .iter()
                .copied()
                .filter(|owner| *owner != index)
                .any(|owner| !candidate.exits.is_disjoint(&candidates[owner].exits)),
            _ => false,
        };
        if is_repeat {
            candidates[index].kind_hint = LoopKindHint::RepeatLike;
            candidates[index].continue_target = Some(continue_target);
            candidates[index].body_scope_blocks = repeat_body_scope;
        }
    }
}

pub(super) fn refine_nested_for_exit_loops(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    candidates: &mut [LoopCandidate],
) {
    let mut nested_for_by_exit = vec![Vec::new(); cfg.blocks.len()];
    for (index, candidate) in candidates.iter().enumerate() {
        if matches!(
            candidate.kind_hint,
            LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
        ) && let Some(exit) = for_normal_exit(proto, cfg, candidate)
        {
            nested_for_by_exit[exit.index()].push(index);
        }
    }
    let demoted = candidates
        .iter()
        .enumerate()
        .filter(|(_, outer)| {
            if outer.kind_hint != LoopKindHint::WhileTrueLike || outer.exits.len() != 1 {
                return false;
            }
            let Some(post_loop) = outer.exits.iter().next().copied() else {
                return false;
            };
            nested_for_by_exit[post_loop.index()]
                .iter()
                .map(|index| &candidates[*index])
                .any(|nested| {
                    nested.blocks.len() < outer.blocks.len()
                        && nested.blocks.is_subset(&outer.body_scope_blocks)
                })
        })
        .map(|(index, _)| index)
        .collect::<Vec<_>>();

    for index in demoted {
        let candidate = &mut candidates[index];
        // nested for 的正常完成边已经证明 post-loop 可达；它不能因为该块恰好
        // 以 return 结束，就把外层 retry loop 伪装成没有普通出口的 while true。
        candidate.kind_hint = LoopKindHint::Unknown;
        candidate.body_scope_blocks = loop_body_scope(
            (candidate.kind_hint, candidate.continue_target),
            &candidate.blocks,
            &candidate.exits,
            None,
            candidate.header,
            cfg,
            graph_facts,
        );
    }
}

pub(super) fn for_normal_exit(
    proto: &LoweredProto,
    cfg: &Cfg,
    candidate: &LoopCandidate,
) -> Option<BlockRef> {
    let target = match candidate.kind_hint {
        LoopKindHint::NumericForLike => {
            let preheader = candidate.preheader?;
            let LowInstr::NumericForInit(instr) = cfg.terminator(&proto.instrs, preheader)? else {
                return None;
            };
            instr.exit_target
        }
        LoopKindHint::GenericForLike => {
            let LowInstr::GenericForLoop(instr) =
                cfg.terminator(&proto.instrs, candidate.header)?
            else {
                return None;
            };
            instr.exit_target
        }
        _ => return None,
    };
    Some(cfg.instr_to_block[target.index()])
}
