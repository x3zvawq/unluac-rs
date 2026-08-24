//! 用安全短路条件证据细化 repeat 候选及嵌套 for 出口；依赖候选集合和 CFG，
//! 不负责初始 natural-loop 发现；例如把伪 while header 恢复为 repeat 尾条件。
//! 多叶条件必须同时冻结完整 DAG 根；最终叶只作为 continue target，不能替代完整条件。

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
        if !matches!(
            candidate.kind_hint,
            LoopKindHint::Unknown | LoopKindHint::WhileLike | LoopKindHint::WhileTrueLike
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
    // 已确认的 merge 重新汇合，因此这里消费 branch 候选关系，不按裸可达性猜测。
    let merge = branch_by_header[header_exit.index()]?.merge?;
    let exit_merge = repeat_exit_merge_after_guard(proto, cfg, graph_facts, repeat_exit, merge)?;
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
    // 只有独立尾条件与 header 分支读取同一主体时，才能排除“真实 while + 尾部 break”。
    // repeat 后再 break 外层 for 时，条件出口又会像 while true 的 terminal exit。
    // 两者都只能等候选齐全后用关系证据消歧，不能全局提高 repeat 启发式优先级。
    let mut for_owners = vec![Vec::new(); cfg.blocks.len()];
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
            repeat_continue_target_via_backedge_pad(proto, cfg, source, &candidate.blocks)
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
                    && branch_conditions_share_subject(
                        proto,
                        cfg,
                        candidate.header,
                        continue_target,
                    )
                    && cfg
                        .branch_edges(candidate.header)
                        .into_iter()
                        .flat_map(|(then_edge, else_edge)| [then_edge, else_edge])
                        .map(|edge| cfg.edges[edge.index()].to)
                        .filter(|target| !candidate.blocks.contains(target))
                        .flat_map(|target| loop_entries[target.index()].iter())
                        .copied()
                        .filter(|nested| *nested != index)
                        .any(|nested| candidates[nested].blocks.is_subset(&repeat_body_scope))
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
