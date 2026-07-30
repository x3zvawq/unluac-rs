//! 这个文件实现共享循环候选提取。
//!
//! 这个 pass 只消费 CFG / GraphFacts / Dataflow / low-IR terminator，产出“循环形态 hint +
//! 可直接复用的源码绑定证据 + loop merge incoming 事实”，不会越权决定最终
//! `while/repeat/for` 语法。
//!
//! 例子：
//! - `NumericForInit/Loop` 会产出 `LoopKindHint::NumericForLike`，并把源码绑定寄存器
//!   记录成 `LoopSourceBindings::Numeric`
//! - `GenericForCall/Loop` 会产出 `LoopKindHint::GenericForLike`，并把源码绑定区间
//!   记录成 `LoopSourceBindings::Generic`
//! - 无自身回边的 generic-for 以 body target 支配区域恢复完整语义 owner，零次迭代
//!   出口仍保持在 body 外侧
//! - `while ... do ... end` 的 header/exit phi 会被整理成 `inside/outside` 两臂的
//!   incoming facts，后续 HIR 直接消费这些结构事实，不再自己回头拆 `phi.incoming`
//! - 普通 `while/repeat` 只保留形态 hint，不会伪造额外 binding 证据
//! - branch 经共享 backedge pad 提前进入下一轮时，会在 branch 候选齐备后记录唯一
//!   `continue_edges` owner，HIR 不再按 jump 形状猜测归属
//! - 多条 loop-exclusive exit 可先写回 live-out 再直接汇入同一 continuation；需要跨越
//!   中间 pad 时仍只接受 `Close + Jump` 或 `Close-only + fallthrough`
//! - for binding 的提前退出域在多个物理 exit 的共同后继前结束，不会穿过
//!   cleanup pad 把循环变量身份带到 post-loop
//! - repeat body 的首个条件可能让 natural-loop 暂时呈现为 while；若该 header 的局部
//!   break pad 严格汇入独立尾条件出口，则由 Structure 恢复真正的 repeat 形态
//! - 同一 header 的全部 natural backedge 只形成一个候选；源码里的重叠循环写法若
//!   编译成同一控制身份，由这个 region 内的 branch/break/continue 表达，不在后层
//!   重新按回边拆候选
//! - 全部出口都直接终止时，多条 sibling latch 共同归一个 while-true owner，header
//!   作为它们共享的下一轮入口
//! - `WhileLike` 的 header 前缀必须属于 branch 条件的数据依赖链，或是可丢弃的
//!   无副作用残留；带副作用但不参与条件的语句应保守留给 repeat/unknown/goto 形态

use std::collections::{BTreeMap, BTreeSet};

use crate::structure::{BlockRef, Cfg, DataflowFacts, EdgeKind, EdgeRef, GraphFacts};
use crate::transformer::{LowInstr, LoweredProto, Reg};

use super::common::{
    BranchCandidate, BranchKind, LoopCandidate, LoopExitAlias, LoopExitValueMergeCandidate,
    LoopKindHint, LoopSourceBindings, LoopValueMerge, ShortCircuitCandidate, ShortCircuitExit,
    ShortCircuitTarget,
};
use super::helpers::{
    block_has_non_control_prefix, collect_forward_region_blocks, collect_region_exits,
    equivalent_single_return_targets, is_reducible_region, same_or_transparent_jump_target,
};
use super::phi_facts::loop_value_merges_in_block;

#[derive(Clone, Copy)]
struct LoopAnalysisContext<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    graph_facts: &'a GraphFacts,
    dataflow: &'a DataflowFacts,
}

pub(super) fn analyze_loops(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
) -> Vec<LoopCandidate> {
    let context = LoopAnalysisContext {
        proto,
        cfg,
        graph_facts,
        dataflow,
    };
    let mut shared_exit_workspace = SharedExitWorkspace::new(cfg.blocks.len());
    let mut domain_workspace = NaturalLoopDomainWorkspace::new(cfg.blocks.len());
    let mut loop_candidates = Vec::with_capacity(graph_facts.natural_loops.len());
    for natural_loop in &graph_facts.natural_loops {
        if let Some(partition) = reachable_numeric_for_loop(
            &context,
            &mut shared_exit_workspace,
            &mut domain_workspace,
            natural_loop,
        ) {
            loop_candidates.extend(partition);
        } else if let Some(partition) = partition_repeat_like_natural_loop(
            &context,
            &mut shared_exit_workspace,
            &mut domain_workspace,
            natural_loop,
        ) {
            loop_candidates.extend(partition);
        } else {
            loop_candidates.push(build_loop_candidate(
                &context,
                &mut shared_exit_workspace,
                natural_loop.header,
                natural_loop.blocks.clone(),
                natural_loop.backedges.clone(),
            ));
        }
    }
    let mut grouped_headers = vec![false; cfg.blocks.len()];
    let mut numeric_headers = vec![false; cfg.blocks.len()];
    for candidate in &loop_candidates {
        grouped_headers[candidate.header.index()] = true;
        if candidate.kind_hint == LoopKindHint::NumericForLike {
            numeric_headers[candidate.header.index()] = true;
        }
    }

    let degenerate_generic_for_loops = analyze_degenerate_generic_for_loops(
        proto,
        cfg,
        dataflow,
        graph_facts,
        &grouped_headers,
        &mut shared_exit_workspace,
    );
    loop_candidates.extend(degenerate_generic_for_loops);
    let numeric_for_latches = index_numeric_for_latches(proto, cfg);
    loop_candidates.extend(
        cfg.reachable_blocks
            .iter()
            .copied()
            .filter_map(|preheader| {
                degenerate_numeric_for_loop(
                    &context,
                    &numeric_headers,
                    &numeric_for_latches,
                    &mut shared_exit_workspace,
                    preheader,
                )
            }),
    );
    loop_candidates.sort_by_key(|candidate| (candidate.header, candidate.blocks.len()));
    refine_nested_for_exit_loops(proto, cfg, graph_facts, &mut loop_candidates);
    refine_ambiguous_repeat_candidates(
        proto,
        cfg,
        graph_facts,
        &mut shared_exit_workspace,
        &mut loop_candidates,
    );
    loop_candidates
}

pub(super) fn assign_continue_edge_ownership(
    proto: &LoweredProto,
    cfg: &Cfg,
    branches: &[BranchCandidate],
    candidates: &mut [LoopCandidate],
) {
    let mut owners_by_entry = vec![Vec::new(); cfg.blocks.len()];
    let mut owners_by_block = vec![Vec::new(); cfg.blocks.len()];
    for (index, candidate) in candidates.iter().enumerate() {
        for block in &candidate.blocks {
            owners_by_block[block.index()].push(index);
        }
        if numeric_continue_target_carries_body_tail(proto, cfg, candidate) {
            continue;
        }
        let Some(target) = candidate.continue_target else {
            continue;
        };
        owners_by_entry[target.index()].push(index);
        for source in candidate
            .backedges
            .iter()
            .map(|edge| cfg.edges[edge.index()].from)
            .filter(|source| *source != target && jump_only_to(proto, cfg, *source, target))
        {
            owners_by_entry[source.index()].push(index);
        }
    }
    for owners in &mut owners_by_entry {
        owners.sort_unstable();
        owners.dedup();
    }

    for branch in branches {
        let Some((then_edge, else_edge)) = cfg.branch_edges(branch.header) else {
            continue;
        };
        if cfg.edges[then_edge.index()].to == cfg.edges[else_edge.index()].to {
            continue;
        }
        for edge_ref in [then_edge, else_edge] {
            let edge = cfg.edges[edge_ref.index()];
            let owners = &owners_by_entry[edge.to.index()];
            if owners.is_empty() {
                continue;
            }
            let eligible = || {
                owners.iter().copied().filter(|index| {
                    let candidate = &candidates[*index];
                    // repeat 的 backedge pad 还承载条件求值，不能仅凭 jump 形状认作 continue。
                    candidate.kind_hint != LoopKindHint::RepeatLike
                        && candidate.continue_target != Some(branch.header)
                        && candidate.blocks.contains(&branch.header)
                        && (candidate.backedges.binary_search(&edge_ref).is_err()
                            || branch.kind == BranchKind::Guard
                                && branch.then_entry == edge.to
                                && branch.merge != Some(edge.to))
                })
            };
            let Some(owner) = eligible().min_by_key(|index| {
                let candidate = &candidates[*index];
                (candidate.body_scope_blocks.len(), candidate.blocks.len())
            }) else {
                continue;
            };
            let owner_scope = (
                candidates[owner].body_scope_blocks.len(),
                candidates[owner].blocks.len(),
            );
            if eligible().filter(|index| *index != owner).any(|index| {
                let candidate = &candidates[index];
                (candidate.body_scope_blocks.len(), candidate.blocks.len()) == owner_scope
            }) {
                continue;
            }
            candidates[owner].continue_edges.insert(edge_ref);
        }

        if branch.else_entry.is_some() {
            continue;
        }
        for index in owners_by_block[branch.header.index()].iter().copied() {
            let candidate = &mut candidates[index];
            if candidate.kind_hint == LoopKindHint::RepeatLike
                || numeric_continue_target_carries_body_tail(proto, cfg, candidate)
                || !candidate.blocks.contains(&branch.then_entry)
            {
                continue;
            }
            let Some(target) = candidate.continue_target else {
                continue;
            };
            let Some(edge_ref) = linear_arm_continue_edge(
                cfg,
                &candidate.blocks,
                branch.then_entry,
                branch.merge,
                target,
            ) else {
                continue;
            };
            candidate.continue_edges.insert(edge_ref);
        }
    }
}

fn numeric_continue_target_carries_body_tail(
    proto: &LoweredProto,
    cfg: &Cfg,
    candidate: &LoopCandidate,
) -> bool {
    candidate.kind_hint == LoopKindHint::NumericForLike
        && candidate
            .continue_target
            .is_some_and(|target| block_has_non_control_prefix(proto, cfg, target))
}

fn linear_arm_continue_edge(
    cfg: &Cfg,
    loop_blocks: &BTreeSet<BlockRef>,
    start: BlockRef,
    merge: Option<BlockRef>,
    target: BlockRef,
) -> Option<EdgeRef> {
    // 单臂 branch 的 continuation 本身就是 VM latch 时，then arm 自然落回 merge；
    // 这条边没有跳过任何源码 tail，不能因为目标恰好等于 continue target 就升级为
    // continue（Lua 5.1 会因此被迫生成非法 goto）。真正的 continue 会在到达 branch
    // continuation 之前先跳到 target。
    if merge == Some(target) {
        return None;
    }
    let mut current = start;
    let mut visited = BTreeSet::new();
    while current != target && Some(current) != merge && visited.insert(current) {
        if !loop_blocks.contains(&current) {
            return None;
        }
        let [edge_ref] = cfg.succs[current.index()].as_slice() else {
            return None;
        };
        let edge = cfg.edges[edge_ref.index()];
        if edge.to == target {
            return Some(*edge_ref);
        }
        current = edge.to;
    }
    None
}

fn jump_only_to(proto: &LoweredProto, cfg: &Cfg, block: BlockRef, target: BlockRef) -> bool {
    cfg.blocks[block.index()].instrs.len == 1
        && matches!(
            cfg.terminator(&proto.instrs, block),
            Some(LowInstr::Jump(jump))
                if cfg.instr_to_block[jump.target.index()] == target
        )
}

pub(super) struct RepeatRefinementInput<'a> {
    pub(super) proto: &'a LoweredProto,
    pub(super) cfg: &'a Cfg,
    pub(super) graph_facts: &'a GraphFacts,
    pub(super) dataflow: &'a DataflowFacts,
    pub(super) branches: &'a [BranchCandidate],
    pub(super) supplements: &'a [ShortCircuitCandidate],
}

pub(super) fn refine_short_circuit_repeat_candidates(
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
                    owned_sources.map(|_| short.header),
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
                        owned_sources.map(|_| short.header),
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
        // condition 的 header 必须支配它。这个 header 只用于证明，不能同时写回
        // `condition_header`，否则冻结时会把同一 connector 重复纳入 condition node。
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

fn install_refined_repeat_exit_merge(
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

fn repeat_short_circuit_match<'a>(
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

fn short_circuits_by_exit(
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

fn repeat_short_circuit_continue_target(
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

fn backedge_has_non_cleanup_prefix(proto: &LoweredProto, cfg: &Cfg, block: BlockRef) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    let end = range.last().map_or(range.end(), |last| last.index());
    (range.start.index()..end)
        .any(|instr_index| !matches!(proto.instrs[instr_index], LowInstr::Close(_)))
}

fn while_header_exit_rejoins_repeat_exit(
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

fn direct_branch_repeat_continue_target(
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

fn repeat_exit_merge_after_guard(
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

fn refine_ambiguous_repeat_candidates(
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

fn refine_nested_for_exit_loops(
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

fn for_normal_exit(proto: &LoweredProto, cfg: &Cfg, candidate: &LoopCandidate) -> Option<BlockRef> {
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

pub(super) fn branch_conditions_share_subject(
    proto: &LoweredProto,
    cfg: &Cfg,
    left: BlockRef,
    right: BlockRef,
) -> bool {
    let (Some(LowInstr::Branch(left)), Some(LowInstr::Branch(right))) = (
        cfg.terminator(&proto.instrs, left),
        cfg.terminator(&proto.instrs, right),
    ) else {
        return false;
    };
    left.cond.subject == right.cond.subject
}

fn reachable_numeric_for_loop(
    context: &LoopAnalysisContext<'_>,
    shared_exit_workspace: &mut SharedExitWorkspace,
    domain_workspace: &mut NaturalLoopDomainWorkspace,
    natural_loop: &crate::structure::NaturalLoop,
) -> Option<Vec<LoopCandidate>> {
    let LoopAnalysisContext {
        proto,
        cfg,
        graph_facts,
        dataflow,
    } = *context;
    let natural_header = natural_loop.header;
    let mut matches = natural_loop
        .backedges
        .iter()
        .copied()
        .filter_map(|backedge| {
            let latch = cfg.edges[backedge.index()].from;
            let LowInstr::NumericForLoop(loop_instr) = cfg.terminator(&proto.instrs, latch)? else {
                return None;
            };
            numeric_for_owner(proto, cfg, natural_header, loop_instr)
                .map(|(header, preheader)| (backedge, header, preheader))
        });
    let (protocol_backedge, header, preheader) = matches.next()?;
    if matches.next().is_some() {
        // 同一控制身份出现多个互相冲突的 VM numeric latch 时，不能任选其一后
        // 静默丢掉其余回边；保守交回普通 merged loop，让最终 plan 决定结构或 island。
        return None;
    }
    let LowInstr::NumericForInit(init) = cfg.terminator(&proto.instrs, preheader)? else {
        return None;
    };
    let exit = cfg.instr_to_block[init.exit_target.index()];
    let latch = cfg.edges[protocol_backedge.index()].from;
    let LowInstr::NumericForLoop(loop_instr) = cfg.terminator(&proto.instrs, latch)? else {
        return None;
    };
    let latch_exit = cfg.instr_to_block[loop_instr.exit_target.index()];
    let duplicated_terminal_exit = latch_exit != exit
        && equivalent_single_return_targets(proto, cfg, loop_instr.exit_target, init.exit_target);

    let mut blocks = collect_forward_region_blocks(
        cfg,
        [header],
        Some(exit),
        Some((header, &graph_facts.dominator_tree)),
    );
    if duplicated_terminal_exit {
        blocks.remove(&latch_exit);
    }
    blocks.insert(latch);
    if !natural_loop.blocks.is_subset(&blocks) || !is_reducible_region(cfg, header, &blocks) {
        return None;
    }

    let residual_backedges = natural_loop
        .backedges
        .iter()
        .copied()
        .filter(|backedge| *backedge != protocol_backedge)
        .collect::<Vec<_>>();
    let residual_blocks = if residual_backedges.is_empty() {
        None
    } else {
        Some(natural_loop_domain_for_backedges(
            cfg,
            natural_loop,
            &residual_backedges,
            domain_workspace,
        )?)
    };
    if residual_blocks.as_ref().is_some_and(|residual| {
        !residual_cycle_is_nested(cfg, natural_loop, residual, &residual_backedges)
    }) {
        // residual cycle 与 VM latch 无法形成严格的 containment 分区时，不能任选一个
        // 回边当 numeric-for；交回 merged candidate，最终 plan 会结构化或形成 island。
        return None;
    }

    let mut candidate = build_loop_candidate(
        context,
        shared_exit_workspace,
        header,
        blocks,
        vec![protocol_backedge],
    );
    if duplicated_terminal_exit {
        candidate.exits.insert(exit);
        candidate.control_blocks.insert(latch_exit);
        candidate.normalized_exit_aliases.push(LoopExitAlias {
            block: latch_exit,
            continuation: exit,
        });
        let shared_exit =
            shared_exit_continuation(proto, &candidate.exits, cfg, shared_exit_workspace);
        candidate.exit_value_merges = analyze_loop_exit_value_merges(
            cfg,
            dataflow,
            &candidate.exits,
            shared_exit.as_ref(),
            &candidate.blocks,
            &candidate.blocks,
        );
    }
    if candidate.kind_hint != LoopKindHint::NumericForLike
        || candidate.preheader != Some(preheader)
        || !candidate.exits.contains(&exit)
    {
        return None;
    }
    if latch_exit != exit && !duplicated_terminal_exit {
        candidate.control_blocks.insert(latch_exit);
    }
    let mut partition = Vec::with_capacity(1 + usize::from(residual_blocks.is_some()));
    if let Some(residual_blocks) = residual_blocks {
        let mut child = build_loop_candidate(
            context,
            shared_exit_workspace,
            natural_header,
            residual_blocks,
            residual_backedges,
        );
        // header phi 同时可见于 wrapper 与 child，但 canonical loop-carried owner 只能是
        // VM-for wrapper；child 只负责 residual control cycle。
        child.header_value_merges.clear();
        partition.push(child);
    }
    partition.push(candidate);
    Some(partition)
}

fn partition_repeat_like_natural_loop(
    context: &LoopAnalysisContext<'_>,
    shared_exit_workspace: &mut SharedExitWorkspace,
    domain_workspace: &mut NaturalLoopDomainWorkspace,
    natural_loop: &crate::structure::NaturalLoop,
) -> Option<Vec<LoopCandidate>> {
    let LoopAnalysisContext {
        proto,
        cfg,
        graph_facts: _,
        dataflow: _,
    } = *context;
    if natural_loop.backedges.len() < 2 {
        return None;
    }
    let header = natural_loop.header;
    let (outer_backedges, residual_backedges): (Vec<_>, Vec<_>) = natural_loop
        .backedges
        .iter()
        .copied()
        .partition(|backedge| {
            let source = cfg.edges[backedge.index()].from;
            branch_has_header_and_exit(cfg, source, header, &natural_loop.blocks)
                || repeat_continue_target_via_backedge_pad(proto, cfg, source, &natural_loop.blocks)
                    .is_some()
        });
    if outer_backedges.is_empty() || residual_backedges.is_empty() {
        return None;
    }

    let residual_blocks = natural_loop_domain_for_backedges(
        cfg,
        natural_loop,
        &residual_backedges,
        domain_workspace,
    )?;
    if !residual_cycle_is_nested(cfg, natural_loop, &residual_blocks, &residual_backedges) {
        return None;
    }

    let mut child = build_loop_candidate(
        context,
        shared_exit_workspace,
        header,
        residual_blocks,
        residual_backedges,
    );
    child.header_value_merges.clear();
    let outer = build_loop_candidate(
        context,
        shared_exit_workspace,
        header,
        natural_loop.blocks.clone(),
        outer_backedges,
    );
    Some(vec![child, outer])
}

struct NaturalLoopDomainWorkspace {
    marks: Vec<usize>,
    next_mark: usize,
}

impl NaturalLoopDomainWorkspace {
    fn new(block_count: usize) -> Self {
        Self {
            marks: vec![0; block_count],
            next_mark: 0,
        }
    }

    fn begin(&mut self) -> usize {
        self.next_mark = self.next_mark.wrapping_add(1);
        if self.next_mark == 0 {
            self.marks.fill(0);
            self.next_mark = 1;
        }
        self.next_mark
    }
}

fn natural_loop_domain_for_backedges(
    cfg: &Cfg,
    natural_loop: &crate::structure::NaturalLoop,
    backedges: &[EdgeRef],
    workspace: &mut NaturalLoopDomainWorkspace,
) -> Option<BTreeSet<BlockRef>> {
    let mark = workspace.begin();
    let header = natural_loop.header;
    let mut blocks = BTreeSet::from([header]);
    let mut worklist = Vec::with_capacity(backedges.len());
    workspace.marks[header.index()] = mark;

    for backedge in backedges {
        let edge = cfg.edges.get(backedge.index())?;
        if edge.to != header || !natural_loop.blocks.contains(&edge.from) {
            return None;
        }
        if workspace.marks[edge.from.index()] != mark {
            workspace.marks[edge.from.index()] = mark;
            blocks.insert(edge.from);
            worklist.push(edge.from);
        }
    }

    while let Some(block) = worklist.pop() {
        for pred_edge in &cfg.preds[block.index()] {
            let pred = cfg.edges[pred_edge.index()].from;
            if !natural_loop.blocks.contains(&pred) || workspace.marks[pred.index()] == mark {
                continue;
            }
            workspace.marks[pred.index()] = mark;
            blocks.insert(pred);
            worklist.push(pred);
        }
    }
    Some(blocks)
}

fn residual_cycle_is_nested(
    cfg: &Cfg,
    natural_loop: &crate::structure::NaturalLoop,
    residual: &BTreeSet<BlockRef>,
    residual_backedges: &[EdgeRef],
) -> bool {
    if residual == &natural_loop.blocks
        || residual.len() <= 1
        || !is_reducible_region(cfg, natural_loop.header, residual)
        || !collect_region_exits(cfg, residual).is_subset(&natural_loop.blocks)
    {
        return false;
    }

    let successors = cfg.succs[natural_loop.header.index()]
        .iter()
        .map(|edge| cfg.edges[edge.index()].to)
        .collect::<BTreeSet<_>>();
    if successors.len() <= 1 {
        return true;
    }
    if successors.len() != 2
        || successors
            .iter()
            .filter(|block| residual.contains(block))
            .count()
            != 1
    {
        return false;
    }
    let Some(outer_only_start) = successors
        .iter()
        .copied()
        .find(|block| !residual.contains(block))
        .map(|block| cfg.blocks[block.index()].instrs.start.index())
    else {
        return false;
    };

    // 两条 sibling latch 也可能各自带“回 header / 离开循环”的局部分支。真正的
    // nested residual 在布局上先完成内层回边，再进入 outer-only arm；若 residual
    // latch 已位于 outer arm 之后，它只是同一轮的另一条 sibling 路径。
    residual_backedges.iter().all(|backedge| {
        let source = cfg.edges[backedge.index()].from;
        cfg.blocks[source.index()].instrs.end() <= outer_only_start
    })
}

fn numeric_for_owner(
    proto: &LoweredProto,
    cfg: &Cfg,
    natural_header: BlockRef,
    loop_instr: &crate::transformer::NumericForLoopInstr,
) -> Option<(BlockRef, BlockRef)> {
    let mut body_entries = BTreeSet::from([natural_header]);
    body_entries.extend(
        cfg.reachable_predecessors(natural_header)
            .into_iter()
            .filter(|body| {
                *body != natural_header
                    && matches!(
                        cfg.terminator(&proto.instrs, *body),
                        Some(LowInstr::Jump(jump))
                            if cfg.instr_to_block[jump.target.index()] == natural_header
                    )
            }),
    );

    let mut owners = body_entries.into_iter().flat_map(|header| {
        cfg.reachable_predecessors(header)
            .into_iter()
            .filter_map(
                move |preheader| match cfg.terminator(&proto.instrs, preheader) {
                    Some(LowInstr::NumericForInit(init))
                        if numeric_for_instrs_match(proto, cfg, init, loop_instr) =>
                    {
                        Some((header, preheader))
                    }
                    _ => None,
                },
            )
    });
    let owner = owners.next()?;
    owners.next().is_none().then_some(owner)
}

fn numeric_for_instrs_match(
    proto: &LoweredProto,
    cfg: &Cfg,
    init: &crate::transformer::NumericForInitInstr,
    loop_instr: &crate::transformer::NumericForLoopInstr,
) -> bool {
    numeric_for_state_matches(init, loop_instr)
        && (loop_instr.body_target == init.body_target
            || matches!(
                cfg.terminator(&proto.instrs, cfg.instr_to_block[init.body_target.index()]),
                Some(LowInstr::Jump(jump))
                    if cfg.instr_to_block[jump.target.index()]
                        == cfg.instr_to_block[loop_instr.body_target.index()]
            ))
        && same_or_equivalent_exit_target(proto, cfg, loop_instr.exit_target, init.exit_target)
}

fn numeric_for_state_matches(
    init: &crate::transformer::NumericForInitInstr,
    loop_instr: &crate::transformer::NumericForLoopInstr,
) -> bool {
    numeric_for_init_state(init) == numeric_for_loop_state(loop_instr)
}

type NumericForState = (Reg, Reg, Reg, Reg);
type NumericForLatchIndex<'a> =
    BTreeMap<NumericForState, Vec<(BlockRef, &'a crate::transformer::NumericForLoopInstr)>>;

fn numeric_for_init_state(instr: &crate::transformer::NumericForInitInstr) -> NumericForState {
    (instr.index, instr.limit, instr.step, instr.binding)
}

fn numeric_for_loop_state(instr: &crate::transformer::NumericForLoopInstr) -> NumericForState {
    (instr.index, instr.limit, instr.step, instr.binding)
}

fn index_numeric_for_latches<'a>(proto: &'a LoweredProto, cfg: &Cfg) -> NumericForLatchIndex<'a> {
    let mut latches = NumericForLatchIndex::new();
    for (instr_index, instr) in proto.instrs.iter().enumerate() {
        let LowInstr::NumericForLoop(loop_instr) = instr else {
            continue;
        };
        latches
            .entry(numeric_for_loop_state(loop_instr))
            .or_default()
            .push((cfg.instr_to_block[instr_index], loop_instr));
    }
    latches
}

fn build_loop_candidate(
    context: &LoopAnalysisContext<'_>,
    shared_exit_workspace: &mut SharedExitWorkspace,
    header: BlockRef,
    blocks: BTreeSet<BlockRef>,
    mut backedges: Vec<EdgeRef>,
) -> LoopCandidate {
    let LoopAnalysisContext {
        proto,
        cfg,
        graph_facts,
        dataflow,
    } = *context;
    backedges.sort();
    backedges.dedup();
    let preheader = unique_loop_preheader(cfg, header, &blocks);
    let exits = collect_region_exits(cfg, &blocks);
    let header_value_merges = analyze_loop_header_value_merges(dataflow, header, &blocks);
    let (kind_hint, continue_target, source_bindings) = infer_loop_shape(LoopShapeInput {
        proto,
        cfg,
        dataflow,
        header,
        blocks: &blocks,
        backedges: &backedges,
        exits: &exits,
        preheader,
        header_value_merges: &header_value_merges,
    });
    let shared_exit = shared_exit_continuation(proto, &exits, cfg, shared_exit_workspace);
    let body_scope_blocks = loop_body_scope(
        (kind_hint, continue_target),
        &blocks,
        &exits,
        shared_exit.as_ref(),
        header,
        cfg,
        graph_facts,
    );
    let exit_value_merges = analyze_loop_exit_value_merges(
        cfg,
        dataflow,
        &exits,
        shared_exit.as_ref(),
        &blocks,
        &blocks,
    );

    LoopCandidate {
        header,
        preheader,
        blocks,
        body_scope_blocks,
        control_blocks: BTreeSet::new(),
        normalized_exit_aliases: Vec::new(),
        backedges,
        exits,
        continue_target,
        continue_edges: BTreeSet::new(),
        condition_header: None,
        kind_hint,
        source_bindings,
        header_value_merges,
        exit_value_merges,
    }
}

fn degenerate_numeric_for_loop(
    context: &LoopAnalysisContext<'_>,
    numeric_headers: &[bool],
    numeric_for_latches: &NumericForLatchIndex<'_>,
    shared_exit_workspace: &mut SharedExitWorkspace,
    preheader: BlockRef,
) -> Option<LoopCandidate> {
    let LoopAnalysisContext {
        proto,
        cfg,
        graph_facts,
        dataflow,
    } = *context;
    let Some(LowInstr::NumericForInit(init)) = cfg.terminator(&proto.instrs, preheader) else {
        return None;
    };
    let header = cfg.instr_to_block[init.body_target.index()];
    let exit = cfg.instr_to_block[init.exit_target.index()];
    if numeric_headers[header.index()] || header == exit {
        return None;
    }

    let latch = numeric_for_latches
        .get(&numeric_for_init_state(init))?
        .iter()
        .find_map(|(latch, loop_instr)| {
            // Luau 会把不可达 latch 的 body edge 直接改指向 loop exit。立即 break
            // 还会把 latch exit 留在不可达 jump pad，但仍共享同一个数值循环身份。
            ((loop_instr.body_target == init.body_target
                || loop_instr.body_target == init.exit_target)
                && same_or_equivalent_exit_target(
                    proto,
                    cfg,
                    loop_instr.exit_target,
                    init.exit_target,
                ))
            .then_some(*latch)
        })?;
    if cfg.reachable_blocks.contains(&latch)
        || latch == preheader
        || latch == header
        || latch == exit
    {
        return None;
    }

    let mut blocks = collect_forward_region_blocks(
        cfg,
        [header],
        Some(exit),
        Some((header, &graph_facts.dominator_tree)),
    );
    blocks.insert(latch);
    let mut exits = collect_region_exits(cfg, &blocks);
    // 立即 break/return 的 body 不会物理抵达零迭代出口；preheader 的 LoopExit
    // 仍是源码 numeric-for 的唯一正常 continuation，必须显式保留。
    exits.insert(exit);
    if !is_reducible_region(cfg, header, &blocks) {
        return None;
    }
    let shared_exit = shared_exit_continuation(proto, &exits, cfg, shared_exit_workspace);
    let body_scope_blocks = loop_body_scope(
        (LoopKindHint::NumericForLike, Some(latch)),
        &blocks,
        &exits,
        shared_exit.as_ref(),
        header,
        cfg,
        graph_facts,
    );

    Some(LoopCandidate {
        header,
        preheader: Some(preheader),
        body_scope_blocks,
        control_blocks: BTreeSet::new(),
        normalized_exit_aliases: Vec::new(),
        backedges: Vec::new(),
        exits: exits.clone(),
        continue_target: Some(latch),
        continue_edges: BTreeSet::new(),
        condition_header: None,
        kind_hint: LoopKindHint::NumericForLike,
        source_bindings: Some(LoopSourceBindings::Numeric(init.binding)),
        header_value_merges: analyze_loop_header_value_merges(dataflow, header, &blocks),
        exit_value_merges: analyze_loop_exit_value_merges(
            cfg,
            dataflow,
            &exits,
            shared_exit.as_ref(),
            &blocks,
            &blocks,
        ),
        blocks,
    })
}

fn same_or_equivalent_exit_target(
    proto: &LoweredProto,
    cfg: &Cfg,
    actual: crate::transformer::InstrRef,
    expected: crate::transformer::InstrRef,
) -> bool {
    same_or_transparent_jump_target(proto, cfg, actual, expected)
        || equivalent_single_return_targets(proto, cfg, actual, expected)
}

fn analyze_degenerate_generic_for_loops(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    graph_facts: &GraphFacts,
    grouped_headers: &[bool],
    shared_exit_workspace: &mut SharedExitWorkspace,
) -> Vec<LoopCandidate> {
    cfg.reachable_blocks
        .iter()
        .copied()
        .filter(|header| !grouped_headers[header.index()])
        .filter_map(|header| {
            degenerate_generic_for_loop(
                proto,
                cfg,
                dataflow,
                graph_facts,
                shared_exit_workspace,
                header,
            )
        })
        .collect()
}

fn degenerate_generic_for_loop(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    graph_facts: &GraphFacts,
    shared_exit_workspace: &mut SharedExitWorkspace,
    header: BlockRef,
) -> Option<LoopCandidate> {
    let Some(LowInstr::GenericForLoop(instr)) = cfg.terminator(&proto.instrs, header) else {
        return None;
    };
    let body = cfg.instr_to_block[instr.body_target.index()];
    let exit = cfg.instr_to_block[instr.exit_target.index()];
    // Luau 会把 `for ... do break end` 编译成 body/exit 同目标，或让 exit 先经过
    // 单条 jump pad 再汇入 body；这不是“没有循环”，候选只需让 header 持有控制结构。
    let immediate_break = body == exit
        || same_or_transparent_jump_target(proto, cfg, instr.exit_target, instr.body_target);
    let mut blocks = BTreeSet::from([header]);
    if !immediate_break {
        blocks.extend(collect_forward_region_blocks(
            cfg,
            [body],
            Some(exit),
            Some((body, &graph_facts.dominator_tree)),
        ));
    }
    if body == header
        || exit == header
        || (!immediate_break && blocks.contains(&exit))
        || !generic_for_has_loop_body_and_exit(proto, cfg, header, instr, &blocks)
    {
        return None;
    }

    let exits = collect_region_exits(cfg, &blocks);
    if !exits.contains(&exit) || !is_reducible_region(cfg, header, &blocks) {
        return None;
    }
    let shared_exit = shared_exit_continuation(proto, &exits, cfg, shared_exit_workspace);
    let body_scope_blocks = loop_body_scope(
        (LoopKindHint::GenericForLike, Some(header)),
        &blocks,
        &exits,
        shared_exit.as_ref(),
        header,
        cfg,
        graph_facts,
    );

    let preheader = unique_loop_preheader(cfg, header, &blocks);
    let header_value_merges = analyze_loop_header_value_merges(dataflow, header, &blocks);
    // 退化 generic-for 没有自身回边：header -> exit 表示零次迭代，语义上属于
    // 循环外初值；只有被 body 支配的完整区域到 exit 的边才是循环内写回。
    let mut body_blocks = blocks.clone();
    body_blocks.remove(&header);
    let exit_value_merges = analyze_loop_exit_value_merges(
        cfg,
        dataflow,
        &exits,
        shared_exit.as_ref(),
        &body_blocks,
        &blocks,
    );

    Some(LoopCandidate {
        header,
        preheader,
        blocks,
        body_scope_blocks,
        control_blocks: BTreeSet::new(),
        normalized_exit_aliases: Vec::new(),
        backedges: Vec::new(),
        exits,
        continue_target: Some(header),
        continue_edges: BTreeSet::new(),
        condition_header: None,
        kind_hint: LoopKindHint::GenericForLike,
        source_bindings: generic_for_source_bindings(proto, cfg, header),
        header_value_merges,
        exit_value_merges,
    })
}

struct LoopShapeInput<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    dataflow: &'a DataflowFacts,
    header: BlockRef,
    blocks: &'a BTreeSet<BlockRef>,
    backedges: &'a [EdgeRef],
    exits: &'a BTreeSet<BlockRef>,
    preheader: Option<BlockRef>,
    header_value_merges: &'a [LoopValueMerge],
}

fn infer_loop_shape(
    input: LoopShapeInput<'_>,
) -> (LoopKindHint, Option<BlockRef>, Option<LoopSourceBindings>) {
    let LoopShapeInput {
        proto,
        cfg,
        dataflow,
        header,
        blocks,
        backedges,
        exits,
        preheader,
        header_value_merges,
    } = input;
    let backedge_sources = backedges
        .iter()
        .map(|edge_ref| cfg.edges[edge_ref.index()].from)
        .collect::<BTreeSet<_>>();

    if let Some(source) = numeric_for_latch_for_preheader(
        proto,
        cfg,
        header,
        preheader,
        backedge_sources.iter().copied(),
    ) {
        return (
            LoopKindHint::NumericForLike,
            Some(source),
            numeric_for_source_bindings(proto, cfg, preheader),
        );
    }

    // generic-for 的 header 本身就携带了比普通回边更强的形状证据。
    // 如果这里先按“回边源是 branch”去判断，很容易把正常的 generic-for
    // 误认成 repeat-like，后面 HIR 就只能回到 unresolved 的 VM 级控制块。
    if matches!(
        cfg.terminator(&proto.instrs, header),
        Some(LowInstr::GenericForLoop(instr))
            if generic_for_has_loop_body_and_exit(proto, cfg, header, instr, blocks)
    ) {
        return (
            LoopKindHint::GenericForLike,
            Some(header),
            generic_for_source_bindings(proto, cfg, header),
        );
    }

    // dialect lowering 往往会把 while 条件需要的临时准备也塞进 header block，再接 branch。
    // 这些前缀仍然属于“每轮先算条件、再决定进不进 body”的源码语义；如果这里只接受
    // 纯常量加载，像 `while i <= #values do`、`while (x & mask) ~= 0 do` 这类最普通的
    // 条件都会被误打成 repeat/unknown，后面整片 loop state 恢复就只能回退成 label/goto。
    if block_is_while_header_like(proto, cfg, dataflow, header, header_value_merges)
        && branch_has_loop_body_and_exit(cfg, header, blocks)
    {
        return (LoopKindHint::WhileLike, Some(header), None);
    }

    if backedge_sources.len() > 1
        && exits.len() > 1
        && matches!(
            cfg.terminator(&proto.instrs, header),
            Some(LowInstr::Branch(_))
        )
        && !region_has_scope_cleanup(proto, cfg, blocks)
        && exits_are_terminal(proto, cfg, exits)
    {
        // 多个 sibling latch 只是把同一轮尾部短路条件拆成多条回 header 的边；
        // 没有普通 continuation 时，header 本身就是这些回边共同拥有的下一轮入口。
        return (LoopKindHint::WhileTrueLike, Some(header), None);
    }

    if let Some(source) = (backedge_sources.len() == 1)
        .then(|| backedge_sources.iter().next().copied())
        .flatten()
    {
        if matches!(
            cfg.terminator(&proto.instrs, source),
            Some(LowInstr::Jump(jump))
                if cfg.instr_to_block[jump.target.index()] == header
        ) && let Some(continue_target) =
            repeat_continue_target_via_backedge_pad(proto, cfg, source, blocks)
        {
            // 先消费“条件 branch -> 纯 backedge pad”的 repeat 协议；若先按
            // terminal exits 把纯 jump latch 判成 while-true，这条更强的尾条件
            // 证据会永久丢失，continue 也只能退化成残余 goto。
            return (LoopKindHint::RepeatLike, Some(continue_target), None);
        }

        if matches!(
            cfg.terminator(&proto.instrs, source),
            Some(LowInstr::Jump(jump)) if cfg.instr_to_block[jump.target.index()] == header
        ) && !region_has_scope_cleanup(proto, cfg, blocks)
            && exits_are_terminal(proto, cfg, exits)
        {
            return (LoopKindHint::WhileTrueLike, Some(source), None);
        }

        if matches!(
            cfg.terminator(&proto.instrs, source),
            Some(LowInstr::Branch(_instr)) if branch_has_header_and_exit(cfg, source, header, blocks)
        ) {
            return (LoopKindHint::RepeatLike, Some(source), None);
        }
    }

    let continue_target = if backedge_sources.len() == 1 {
        backedge_sources.iter().next().copied()
    } else {
        None
    };

    (LoopKindHint::Unknown, continue_target, None)
}

fn numeric_for_latch_for_preheader(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: BlockRef,
    preheader: Option<BlockRef>,
    sources: impl IntoIterator<Item = BlockRef>,
) -> Option<BlockRef> {
    let preheader = preheader?;
    let LowInstr::NumericForInit(init) = cfg.terminator(&proto.instrs, preheader)? else {
        return None;
    };
    if cfg.instr_to_block[init.body_target.index()] != header {
        return None;
    }

    let mut matches = sources.into_iter().filter(|source| {
        matches!(
            cfg.terminator(&proto.instrs, *source),
            Some(LowInstr::NumericForLoop(loop_instr))
                if numeric_for_instrs_match(proto, cfg, init, loop_instr)
        )
    });
    let source = matches.next()?;
    matches.next().is_none().then_some(source)
}

fn region_has_scope_cleanup(proto: &LoweredProto, cfg: &Cfg, blocks: &BTreeSet<BlockRef>) -> bool {
    blocks.iter().copied().any(|block| {
        let range = cfg.blocks[block.index()].instrs;
        (range.start.index()..range.end()).any(|instr_index| {
            matches!(
                proto.instrs[instr_index],
                LowInstr::Close(_) | LowInstr::Tbc(_)
            )
        })
    })
}

fn exits_are_terminal(proto: &LoweredProto, cfg: &Cfg, exits: &BTreeSet<BlockRef>) -> bool {
    exits.iter().copied().all(|exit| {
        let Some(instr_ref) = cfg.blocks[exit.index()].instrs.last() else {
            return exit == cfg.exit_block;
        };
        matches!(
            proto.instrs[instr_ref.index()],
            LowInstr::Return(_) | LowInstr::TailCall(_)
        )
    })
}

fn numeric_for_source_bindings(
    proto: &LoweredProto,
    cfg: &Cfg,
    preheader: Option<BlockRef>,
) -> Option<LoopSourceBindings> {
    let preheader = preheader?;
    let instr_ref = cfg.blocks[preheader.index()].instrs.last()?;

    match proto.instrs.get(instr_ref.index())? {
        LowInstr::NumericForInit(instr) => Some(LoopSourceBindings::Numeric(instr.binding)),
        _ => None,
    }
}

fn generic_for_source_bindings(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: BlockRef,
) -> Option<LoopSourceBindings> {
    let instr_ref = cfg.blocks[header.index()].instrs.last()?;

    match proto.instrs.get(instr_ref.index())? {
        LowInstr::GenericForLoop(instr) => Some(LoopSourceBindings::Generic(instr.bindings)),
        _ => None,
    }
}

/// 计算源码 loop body 的词法作用域块集合。
///
/// natural loop 拓扑只包含能回到 header 的 body 块，不含通过 return/break
/// 提前离开循环的块；repeat 的条件前分支还可能先进入 nested loop，再回到尾条件。
///
/// 策略：在 candidate.blocks 基础上，追加被 header 严格支配的提前退出区域。
/// for 的 LoopExit 与 repeat 尾条件的循环外后继都是词法边界。while/while-true 不做
/// 扩张，避免把普通 post-loop 和后续 sibling loop 误纳入当前 body。
fn loop_body_scope(
    shape: (LoopKindHint, Option<BlockRef>),
    body_blocks: &BTreeSet<BlockRef>,
    exits: &BTreeSet<BlockRef>,
    shared_exit: Option<&SharedExitContinuation>,
    header: BlockRef,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
) -> BTreeSet<BlockRef> {
    let (kind_hint, continue_target) = shape;
    if !matches!(
        kind_hint,
        LoopKindHint::NumericForLike | LoopKindHint::GenericForLike | LoopKindHint::RepeatLike
    ) {
        return body_blocks.clone();
    }

    let mut scope = body_blocks.clone();
    let mut scope_boundaries = exits
        .iter()
        .copied()
        .filter(|exit| {
            cfg.preds[exit.index()].iter().any(|edge_ref| {
                let edge = &cfg.edges[edge_ref.index()];
                body_blocks.contains(&edge.from) && edge.kind == EdgeKind::LoopExit
            })
        })
        .collect::<BTreeSet<_>>();
    if kind_hint == LoopKindHint::RepeatLike
        && let Some(continue_target) = continue_target
    {
        scope_boundaries.extend(
            cfg.succs[continue_target.index()]
                .iter()
                .map(|edge_ref| cfg.edges[edge_ref.index()].to)
                .filter(|target| !body_blocks.contains(target)),
        );
    }
    if let Some(shared_exit) = shared_exit {
        scope_boundaries.insert(shared_exit.merge);
    }

    for &exit in exits {
        if exit == header || !graph_facts.dominator_tree.dominates(header, exit) {
            continue;
        }
        let reached_via_loop_exit = cfg.preds[exit.index()].iter().any(|edge_ref| {
            let edge = &cfg.edges[edge_ref.index()];
            body_blocks.contains(&edge.from) && edge.kind == EdgeKind::LoopExit
        });
        if !reached_via_loop_exit {
            scope.extend(loop_binding_early_exit_scope(
                exit,
                header,
                &scope_boundaries,
                cfg,
                graph_facts,
            ));
        }
    }
    scope
}

struct SharedExitContinuation {
    merge: BlockRef,
    path_blocks: BTreeSet<BlockRef>,
}

struct SharedExitWorkspace {
    seen_marks: Vec<usize>,
    next_path_mark: usize,
    path_counts: Vec<usize>,
    counted_blocks: Vec<BlockRef>,
}

impl SharedExitWorkspace {
    fn new(block_count: usize) -> Self {
        Self {
            seen_marks: vec![0; block_count],
            next_path_mark: 0,
            path_counts: vec![0; block_count],
            counted_blocks: Vec::new(),
        }
    }

    fn begin_path(&mut self) -> usize {
        self.next_path_mark = self.next_path_mark.wrapping_add(1);
        if self.next_path_mark == 0 {
            self.seen_marks.fill(0);
            self.next_path_mark = 1;
        }
        self.next_path_mark
    }

    fn clear_path_counts(&mut self) {
        for block in self.counted_blocks.drain(..) {
            self.path_counts[block.index()] = 0;
        }
    }

    fn count_path_block(&mut self, block: BlockRef) {
        let count = &mut self.path_counts[block.index()];
        if *count == 0 {
            self.counted_blocks.push(block);
        }
        *count += 1;
    }
}

fn shared_exit_continuation(
    proto: &LoweredProto,
    exits: &BTreeSet<BlockRef>,
    cfg: &Cfg,
    workspace: &mut SharedExitWorkspace,
) -> Option<SharedExitContinuation> {
    if exits.len() < 2 {
        return None;
    }
    let mut paths = Vec::with_capacity(exits.len());
    for exit in exits.iter().copied() {
        let path_mark = workspace.begin_path();
        paths.push(loop_exit_continuation_path(
            proto,
            cfg,
            exit,
            &mut workspace.seen_marks,
            path_mark,
        ));
    }
    workspace.clear_path_counts();
    for path in &paths {
        for block in path {
            workspace.count_path_block(*block);
        }
    }
    let merge = paths.first()?.iter().copied().find(|block| {
        *block != cfg.exit_block && workspace.path_counts[block.index()] == paths.len()
    })?;
    let path_blocks = paths
        .iter()
        .flat_map(|path| path.iter().copied().take_while(|block| *block != merge))
        .collect();
    Some(SharedExitContinuation { merge, path_blocks })
}

fn loop_exit_continuation_path(
    proto: &LoweredProto,
    cfg: &Cfg,
    exit: BlockRef,
    seen_marks: &mut [usize],
    path_mark: usize,
) -> Vec<BlockRef> {
    let mut path = vec![exit];
    seen_marks[exit.index()] = path_mark;
    let Some(mut cursor) = cfg.unique_reachable_successor(exit) else {
        return path;
    };
    while seen_marks[cursor.index()] != path_mark {
        seen_marks[cursor.index()] = path_mark;
        path.push(cursor);
        let Some(next) = transparent_loop_exit_target(proto, cfg, cursor) else {
            break;
        };
        cursor = next;
    }
    path
}

fn loop_binding_early_exit_scope(
    exit: BlockRef,
    header: BlockRef,
    scope_boundaries: &BTreeSet<BlockRef>,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
) -> BTreeSet<BlockRef> {
    let mut scope = BTreeSet::new();
    let mut stack = vec![exit];

    while let Some(block) = stack.pop() {
        if block == cfg.exit_block
            || scope_boundaries.contains(&block)
            || !graph_facts.dominator_tree.dominates(header, block)
            || !scope.insert(block)
        {
            continue;
        }

        for edge_ref in &cfg.succs[block.index()] {
            let successor = cfg.edges[edge_ref.index()].to;
            if !scope_boundaries.contains(&successor) {
                stack.push(successor);
            }
        }
    }

    scope
}

fn analyze_loop_header_value_merges(
    dataflow: &DataflowFacts,
    header: BlockRef,
    loop_blocks: &BTreeSet<BlockRef>,
) -> Vec<LoopValueMerge> {
    loop_value_merges_in_block(dataflow, header, loop_blocks)
        .into_iter()
        .filter(loop_value_has_inside_and_outside_incoming)
        .collect()
}

fn analyze_loop_exit_value_merges(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    exits: &BTreeSet<BlockRef>,
    shared_exit: Option<&SharedExitContinuation>,
    value_inside_blocks: &BTreeSet<BlockRef>,
    exit_owner_blocks: &BTreeSet<BlockRef>,
) -> Vec<LoopExitValueMergeCandidate> {
    let shared_merge = shared_loop_exit_merge(cfg, shared_exit, exit_owner_blocks);
    let shared_merge_block = shared_merge.map(|continuation| continuation.merge);
    let mut candidates = exits
        .iter()
        .copied()
        .filter(|exit| Some(*exit) != shared_merge_block)
        .filter_map(|exit| loop_exit_value_merge_in_block(dataflow, exit, value_inside_blocks))
        .collect::<Vec<_>>();

    if let Some(shared_merge) = shared_merge {
        let mut ownership_blocks = value_inside_blocks.clone();
        ownership_blocks.extend(shared_merge.path_blocks.iter().copied());
        if let Some(candidate) =
            loop_exit_value_merge_in_block(dataflow, shared_merge.merge, &ownership_blocks)
        {
            candidates.push(candidate);
        }
    }
    candidates.sort_by_key(|candidate| candidate.exit);
    candidates
}

fn loop_exit_value_merge_in_block(
    dataflow: &DataflowFacts,
    exit: BlockRef,
    ownership_blocks: &BTreeSet<BlockRef>,
) -> Option<LoopExitValueMergeCandidate> {
    let values = loop_value_merges_in_block(dataflow, exit, ownership_blocks)
        .into_iter()
        .filter(|value| !value.inside_arm.is_empty())
        .collect::<Vec<_>>();
    (!values.is_empty()).then_some(LoopExitValueMergeCandidate { exit, values })
}

fn shared_loop_exit_merge<'a>(
    cfg: &Cfg,
    continuation: Option<&'a SharedExitContinuation>,
    exit_owner_blocks: &BTreeSet<BlockRef>,
) -> Option<&'a SharedExitContinuation> {
    // 出口块自身可以写回 live-out；只要它们直接汇入同一 block，merge 的 incoming
    // 仍完整对应这些出口。透明性只约束继续跨越的中间 pad，不能反过来丢掉直接合流。
    let continuation = continuation?;
    let path_blocks = &continuation.path_blocks;

    // ownership_blocks 会把这些 predecessor 的完整输出视为 loop 内值；只要某个块还能
    // 从循环外进入，它的输出就可能已经混合外部路径，不能再整项交给 loop owner。
    path_blocks
        .iter()
        .all(|block| {
            cfg.preds[block.index()].iter().all(|edge| {
                let pred = cfg.edges[edge.index()].from;
                !cfg.reachable_blocks.contains(&pred)
                    || exit_owner_blocks.contains(&pred)
                    || path_blocks.contains(&pred)
            })
        })
        .then_some(continuation)
}

pub(super) fn transparent_loop_exit_target(
    proto: &LoweredProto,
    cfg: &Cfg,
    block: BlockRef,
) -> Option<BlockRef> {
    if let Some(target) = transparent_jump_target(proto, cfg, block) {
        return Some(target);
    }
    let range = cfg.blocks[block.index()].instrs;
    if range.is_empty()
        || (range.start.index()..range.end())
            .any(|instr_index| !matches!(proto.instrs[instr_index], LowInstr::Close(_)))
    {
        return None;
    }
    cfg.unique_reachable_successor(block)
}

fn loop_value_has_inside_and_outside_incoming(value: &LoopValueMerge) -> bool {
    !value.inside_arm.is_empty() && !value.outside_arm.is_empty()
}

fn unique_loop_preheader(
    cfg: &Cfg,
    header: BlockRef,
    loop_blocks: &BTreeSet<BlockRef>,
) -> Option<BlockRef> {
    cfg.unique_reachable_predecessor_matching(header, |pred| !loop_blocks.contains(&pred))
}

fn branch_has_loop_body_and_exit(cfg: &Cfg, header: BlockRef, blocks: &BTreeSet<BlockRef>) -> bool {
    let Some((then_edge_ref, else_edge_ref)) = cfg.branch_edges(header) else {
        return false;
    };
    let then_block = cfg.edges[then_edge_ref.index()].to;
    let else_block = cfg.edges[else_edge_ref.index()].to;

    (blocks.contains(&then_block) && !blocks.contains(&else_block))
        || (!blocks.contains(&then_block) && blocks.contains(&else_block))
}

fn branch_has_header_and_exit(
    cfg: &Cfg,
    block: BlockRef,
    header: BlockRef,
    blocks: &BTreeSet<BlockRef>,
) -> bool {
    let Some((then_edge_ref, else_edge_ref)) = cfg.branch_edges(block) else {
        return false;
    };
    let then_block = cfg.edges[then_edge_ref.index()].to;
    let else_block = cfg.edges[else_edge_ref.index()].to;

    (then_block == header && !blocks.contains(&else_block))
        || (else_block == header && !blocks.contains(&then_block))
}

fn block_is_while_header_like(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    block: BlockRef,
    header_value_merges: &[LoopValueMerge],
) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    if !matches!(
        cfg.terminator(&proto.instrs, block),
        Some(LowInstr::Branch(_))
    ) {
        return false;
    }
    if range.len == 1 {
        return true;
    }

    let carried_regs = header_value_merges
        .iter()
        .map(|value| value.reg)
        .collect::<BTreeSet<_>>();
    let terminator_index = range.end() - 1;
    let Some(branch_effect) = dataflow.instr_effects.get(terminator_index) else {
        return false;
    };
    let mut needed_regs = branch_effect.fixed_uses.clone();

    (range.start.index()..terminator_index)
        .rev()
        .all(|instr_index| {
            let instr = &proto.instrs[instr_index];
            let Some(effect) = dataflow.instr_effects.get(instr_index) else {
                return false;
            };
            if carried_regs.iter().any(|reg| effect.must_define(*reg))
                || !instr_is_while_header_prefix(instr)
            {
                return false;
            }
            let writes_needed = needed_regs.iter().any(|reg| effect.must_define(*reg));
            if !writes_needed {
                return dataflow
                    .effect_summaries
                    .get(instr_index)
                    .is_some_and(|summary| summary.tags.is_empty());
            }

            for reg in &effect.fixed_must_defs {
                needed_regs.remove(reg);
            }
            if let Some(open_def) = effect.open_must_def {
                needed_regs.retain(|reg| reg.index() < open_def.index());
            }
            needed_regs.extend(effect.fixed_uses.iter().copied());
            if let Some(open_use) = effect.open_use {
                needed_regs.insert(open_use);
            }
            true
        })
}

/// while 条件求值中不可能出现的指令。这些指令要么是控制流终结指令（已由
/// terminator 位置单独处理），要么是纯副作用写出指令（SetUpvalue / SetTable /
/// SetList），要么是 scope 管理指令（Close / Tbc），不可能出现在 Lua 编译器
/// 为 expression 上下文生成的条件求值序列里。
///
/// 使用排除列表而非允许列表，避免新增 LowInstr 变体时遗漏导致合法的 while
/// 条件被误判为 repeat/unknown。
fn instr_is_while_header_prefix(instr: &LowInstr) -> bool {
    !matches!(
        instr,
        LowInstr::SetUpvalue(_)
            | LowInstr::SetTable(_)
            | LowInstr::SetList(_)
            | LowInstr::TailCall(_)
            | LowInstr::Return(_)
            | LowInstr::Close(_)
            | LowInstr::Tbc(_)
            | LowInstr::NumericForInit(_)
            | LowInstr::NumericForLoop(_)
            | LowInstr::GenericForPrep(_)
            | LowInstr::GenericForCall(_)
            | LowInstr::GenericForLoop(_)
            | LowInstr::Jump(_)
            | LowInstr::Branch(_)
    )
}

fn repeat_continue_target_via_backedge_pad(
    proto: &LoweredProto,
    cfg: &Cfg,
    backedge_source: BlockRef,
    blocks: &BTreeSet<BlockRef>,
) -> Option<BlockRef> {
    // 条件 branch 后的纯 jump/close pad 可以属于 repeat 控制；普通赋值或调用则仍是
    // while/retry body 的尾部，若把它当条件 pad，HIR 会跳过本轮副作用。
    transparent_jump_target(proto, cfg, backedge_source)?;
    let continue_target =
        cfg.unique_reachable_predecessor_matching(backedge_source, |pred| blocks.contains(&pred))?;

    if !matches!(
        cfg.terminator(&proto.instrs, continue_target),
        Some(LowInstr::Branch(_))
    ) {
        return None;
    }

    let (then_edge_ref, else_edge_ref) = cfg.branch_edges(continue_target)?;
    let then_block = cfg.edges[then_edge_ref.index()].to;
    let else_block = cfg.edges[else_edge_ref.index()].to;

    if (then_block == backedge_source && !blocks.contains(&else_block))
        || (else_block == backedge_source && !blocks.contains(&then_block))
    {
        Some(continue_target)
    } else {
        None
    }
}

fn transparent_jump_target(proto: &LoweredProto, cfg: &Cfg, block: BlockRef) -> Option<BlockRef> {
    let range = cfg.blocks[block.index()].instrs;
    let last = range.last()?;
    let LowInstr::Jump(jump) = &proto.instrs[last.index()] else {
        return None;
    };
    if (range.start.index()..last.index())
        .any(|instr_index| !matches!(proto.instrs[instr_index], LowInstr::Close(_)))
    {
        return None;
    }
    Some(cfg.instr_to_block[jump.target.index()])
}

fn generic_for_has_loop_body_and_exit(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: BlockRef,
    instr: &crate::transformer::GenericForLoopInstr,
    blocks: &BTreeSet<BlockRef>,
) -> bool {
    let range = cfg.blocks[header.index()].instrs;
    if range.len < 2 {
        return false;
    }
    let Some(call_instr_index) = range.end().checked_sub(2) else {
        return false;
    };
    let Some(LowInstr::GenericForCall(call)) = proto.instrs.get(call_instr_index) else {
        return false;
    };
    let body_block = cfg.instr_to_block[instr.body_target.index()];
    let exit_block = cfg.instr_to_block[instr.exit_target.index()];

    call.control == instr.control_target
        && matches!(call.results, crate::transformer::ResultPack::Fixed(range) if range == instr.bindings)
        && (body_block == exit_block
            || same_or_transparent_jump_target(proto, cfg, instr.exit_target, instr.body_target)
            || blocks.contains(&body_block))
        && !blocks.contains(&exit_block)
}
