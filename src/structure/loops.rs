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
//! - `while ... do ... end` 的 header/exit phi 会被整理成 `inside/outside` 两臂的
//!   incoming facts，后续 HIR 直接消费这些结构事实，不再自己回头拆 `phi.incoming`
//! - 普通 `while/repeat` 只保留形态 hint，不会伪造额外 binding 证据
//! - branch 经共享 backedge pad 提前进入下一轮时，会在 branch 候选齐备后记录唯一
//!   `continue_edges` owner，HIR 不再按 jump 形状猜测归属
//! - 多条 break exit 若仅经 `Close + Jump` 或 `Close-only + fallthrough` pad 汇入同一
//!   continuation，该处 live-out phi 仍归 loop owner；带赋值或调用的路径不透明
//! - for binding 的提前退出域在多个物理 exit 的共同后继前结束，不会穿过
//!   cleanup pad 把循环变量身份带到 post-loop
//! - repeat body 的首个条件可能让 natural-loop 暂时呈现为 while；若该 header 的局部
//!   break pad 严格汇入独立尾条件出口，则由 Structure 恢复真正的 repeat 形态
//! - 普通内外循环可能共享 header；只有 successor 分区、内层出口归属和真实
//!   body/exit 都能证明层级时才拆成多个候选，避免把 sibling latch 或无出口循环误拆
//! - 全部出口都直接终止时，多条 sibling latch 仍共同归一个 while-true owner，header
//!   作为它们共享的下一轮入口
//! - `WhileLike` 的 header 前缀必须属于 branch 条件的数据依赖链，或是可丢弃的
//!   无副作用残留；带副作用但不参与条件的语句应保守留给 repeat/unknown/goto 形态

use std::collections::{BTreeMap, BTreeSet};

use crate::structure::{BlockRef, Cfg, DataflowFacts, EdgeKind, EdgeRef, GraphFacts};
use crate::transformer::{LowInstr, LoweredProto, Reg, ResultPack};

use super::common::{
    BranchCandidate, LoopCandidate, LoopExitValueMergeCandidate, LoopKindHint, LoopSourceBindings,
    LoopValueMerge, ShortCircuitCandidate, ShortCircuitExit, ShortCircuitTarget,
};
use super::helpers::{
    block_has_non_control_prefix, collect_forward_region_blocks, collect_region_exits,
    is_reducible_region,
};
use super::phi_facts::loop_value_merges_in_block;

pub(super) fn analyze_loops(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
) -> Vec<LoopCandidate> {
    let mut natural_loops_by_header = BTreeMap::<BlockRef, Vec<_>>::new();
    for natural_loop in &graph_facts.natural_loops {
        natural_loops_by_header
            .entry(natural_loop.header)
            .or_default()
            .push(natural_loop);
    }
    let mut claimed_backedges = BTreeSet::new();
    let mut loop_candidates = natural_loops_by_header
        .values()
        .filter_map(|natural_loops| {
            reachable_numeric_for_loop(
                proto,
                cfg,
                dataflow,
                graph_facts,
                natural_loops,
                &mut claimed_backedges,
            )
        })
        .collect::<Vec<_>>();

    for (header, natural_loops) in natural_loops_by_header {
        let remaining = natural_loops
            .into_iter()
            .filter(|natural_loop| !claimed_backedges.contains(&natural_loop.backedge))
            .collect::<Vec<_>>();
        loop_candidates.extend(
            group_same_header_natural_loops(proto, cfg, header, remaining)
                .into_iter()
                .map(|(blocks, backedges)| {
                    build_loop_candidate(
                        proto,
                        cfg,
                        graph_facts,
                        dataflow,
                        header,
                        blocks,
                        backedges,
                    )
                }),
        );
    }
    let grouped_headers = loop_candidates
        .iter()
        .map(|candidate| candidate.header)
        .collect::<BTreeSet<_>>();
    let numeric_headers = loop_candidates
        .iter()
        .filter(|candidate| candidate.kind_hint == LoopKindHint::NumericForLike)
        .map(|candidate| candidate.header)
        .collect::<BTreeSet<_>>();

    let degenerate_generic_for_loops = analyze_degenerate_generic_for_loops(
        proto,
        cfg,
        dataflow,
        graph_facts,
        &grouped_headers,
        &loop_candidates,
    );
    loop_candidates.extend(degenerate_generic_for_loops);
    loop_candidates.extend(
        cfg.reachable_blocks
            .iter()
            .copied()
            .filter_map(|preheader| {
                degenerate_numeric_for_loop(
                    proto,
                    cfg,
                    dataflow,
                    graph_facts,
                    &numeric_headers,
                    preheader,
                )
            }),
    );
    loop_candidates.sort_by_key(|candidate| (candidate.header, candidate.blocks.len()));
    refine_ambiguous_repeat_candidates(proto, cfg, &mut loop_candidates);
    assign_same_header_merge_ownership(&mut loop_candidates);
    loop_candidates
}

fn group_same_header_natural_loops(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: BlockRef,
    mut natural_loops: Vec<&crate::structure::NaturalLoop>,
) -> Vec<(BTreeSet<BlockRef>, Vec<EdgeRef>)> {
    natural_loops.sort_by_key(|natural_loop| (natural_loop.blocks.len(), natural_loop.backedge));
    let mut groups = Vec::<(BTreeSet<BlockRef>, Vec<EdgeRef>)>::new();

    for natural_loop in natural_loops {
        if groups.is_empty() {
            groups.push((natural_loop.blocks.clone(), vec![natural_loop.backedge]));
            continue;
        }
        if let Some(outer_blocks) = groups.last().and_then(|(inner_blocks, _)| {
            same_header_nested_outer_blocks(proto, cfg, header, inner_blocks, natural_loop)
        }) {
            groups.push((outer_blocks, vec![natural_loop.backedge]));
            continue;
        }

        let group = groups
            .last_mut()
            .expect("first same-header natural loop starts a group");
        group.0.extend(natural_loop.blocks.iter().copied());
        group.1.push(natural_loop.backedge);
    }

    groups
}

fn same_header_nested_outer_blocks(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: BlockRef,
    inner: &BTreeSet<BlockRef>,
    next: &crate::structure::NaturalLoop,
) -> Option<BTreeSet<BlockRef>> {
    let outer = inner.union(&next.blocks).copied().collect::<BTreeSet<_>>();
    // 单块自回边也可能只是同一 retry loop 的条件短路；无出口组合则常见于
    // `while true + if/else`。两者拆层都缺少源码边界证据。
    if inner.len() <= 1
        || inner.len() >= outer.len()
        || collect_region_exits(cfg, &outer).is_empty()
        || !collect_region_exits(cfg, inner).is_subset(&outer)
    {
        return None;
    }
    let successors = cfg.succs[header.index()]
        .iter()
        .map(|edge| cfg.edges[edge.index()].to)
        .collect::<BTreeSet<_>>();
    if successors.len() != 2
        || successors
            .iter()
            .filter(|block| inner.contains(block))
            .count()
            != 1
    {
        return None;
    }
    let mut outer_only_successors = successors
        .iter()
        .copied()
        .filter(|block| outer.contains(block) && !inner.contains(block));
    let outer_only_successor = outer_only_successors.next()?;
    if outer_only_successors.next().is_some() {
        return None;
    }

    // outer body 可以包含任意语句；层级证据来自尾条件自身拥有回 header
    // 和退出 outer 的两条边。条件后的 Close/jump pad 仍属于这个控制边界。
    let backedge_source = cfg.edges[next.backedge.index()].from;
    (backedge_source == outer_only_successor
        || branch_has_header_and_exit(cfg, backedge_source, header, &outer)
        || repeat_continue_target_via_backedge_pad(proto, cfg, backedge_source, &outer).is_some())
    .then_some(outer)
}

pub(super) fn assign_continue_edge_ownership(
    proto: &LoweredProto,
    cfg: &Cfg,
    branches: &[BranchCandidate],
    candidates: &mut [LoopCandidate],
) {
    let mut owners_by_entry = BTreeMap::<BlockRef, BTreeSet<usize>>::new();
    for (index, candidate) in candidates.iter().enumerate() {
        if numeric_continue_target_carries_body_tail(proto, cfg, candidate) {
            continue;
        }
        let Some(target) = candidate.continue_target else {
            continue;
        };
        owners_by_entry.entry(target).or_default().insert(index);
        for source in candidate
            .backedges
            .iter()
            .map(|edge| cfg.edges[edge.index()].from)
            .filter(|source| *source != target && jump_only_to(proto, cfg, *source, target))
        {
            owners_by_entry.entry(source).or_default().insert(index);
        }
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
            let Some(owners) = owners_by_entry.get(&edge.to) else {
                continue;
            };
            let eligible = || {
                owners.iter().copied().filter(|index| {
                    let candidate = &candidates[*index];
                    // repeat 的 backedge pad 还承载条件求值，不能仅凭 jump 形状认作 continue。
                    candidate.kind_hint != LoopKindHint::RepeatLike
                        && candidate.continue_target != Some(branch.header)
                        && candidate.blocks.contains(&branch.header)
                        && !candidate.backedges.contains(&edge_ref)
                })
            };
            let Some(owner) = eligible().min_by_key(|index| {
                let candidate = &candidates[*index];
                (candidate.binding_scope_blocks.len(), candidate.blocks.len())
            }) else {
                continue;
            };
            let owner_scope = (
                candidates[owner].binding_scope_blocks.len(),
                candidates[owner].blocks.len(),
            );
            if eligible().filter(|index| *index != owner).any(|index| {
                let candidate = &candidates[index];
                (candidate.binding_scope_blocks.len(), candidate.blocks.len()) == owner_scope
            }) {
                continue;
            }
            candidates[owner].continue_edges.insert(edge_ref);
        }

        if branch.else_entry.is_some() {
            continue;
        }
        for candidate in candidates.iter_mut().filter(|candidate| {
            candidate.kind_hint != LoopKindHint::RepeatLike
                && !numeric_continue_target_carries_body_tail(proto, cfg, candidate)
                && candidate.blocks.contains(&branch.header)
                && candidate.blocks.contains(&branch.then_entry)
        }) {
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

pub(super) fn refine_short_circuit_repeat_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    branches: &[BranchCandidate],
    short_circuits: &mut Vec<ShortCircuitCandidate>,
    supplements: &[ShortCircuitCandidate],
    candidates: &mut [LoopCandidate],
) {
    let current_by_exit = short_circuits_by_exit(short_circuits);
    let supplements_by_exit = short_circuits_by_exit(supplements);
    let mut accepted_supplements = Vec::new();

    for candidate in candidates {
        if !matches!(
            candidate.kind_hint,
            LoopKindHint::Unknown | LoopKindHint::WhileLike | LoopKindHint::WhileTrueLike
        ) || candidate.backedges.len() != 1
        {
            continue;
        }
        let backedge_source = cfg.edges[candidate.backedges[0].index()].from;
        let jump_backedge = matches!(
            cfg.terminator(&proto.instrs, backedge_source),
            Some(LowInstr::Jump(jump))
                if cfg.instr_to_block[jump.target.index()] == candidate.header
        );

        let matched = jump_backedge
            .then(|| {
                current_by_exit
                    .get(&backedge_source)
                    .into_iter()
                    .flatten()
                    .find_map(|short| {
                        repeat_short_circuit_continue_target(
                            proto,
                            cfg,
                            graph_facts,
                            short,
                            candidate,
                            backedge_source,
                        )
                        .filter(|_| graph_facts.dominates(short.header, backedge_source))
                        .map(|target| (target, None, None, short.header))
                    })
                    .or_else(|| {
                        supplements_by_exit
                            .get(&backedge_source)
                            .into_iter()
                            .flatten()
                            .find_map(|short| {
                                repeat_short_circuit_continue_target(
                                    proto,
                                    cfg,
                                    graph_facts,
                                    short,
                                    candidate,
                                    backedge_source,
                                )
                                .filter(|_| graph_facts.dominates(short.header, backedge_source))
                                .map(|target| {
                                    (
                                        target,
                                        Some(short.header),
                                        Some((*short).clone()),
                                        short.header,
                                    )
                                })
                            })
                    })
            })
            .flatten()
            .or_else(|| {
                direct_branch_repeat_continue_target(cfg, branches, candidate, backedge_source)
                    .map(|target| (target, None, None, target))
            });
        let Some((continue_target, condition_header, supplement, condition_entry)) = matched else {
            continue;
        };
        // repeat 的条件入口必须支配最终回边源；否则存在不经过该条件就回到 header 的
        // 路径，它只能是 while/while-true 中的提前 continue。把这种形状精化成 repeat
        // 会让 continue 错误执行原本应跳过的尾条件。
        if !graph_facts.dominates(condition_entry, backedge_source) {
            continue;
        }
        if let Some(supplement) = supplement {
            accepted_supplements.push(supplement);
        }

        candidate.kind_hint = LoopKindHint::RepeatLike;
        candidate.continue_target = Some(continue_target);
        candidate.condition_header = condition_header;
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

fn short_circuits_by_exit(
    short_circuits: &[ShortCircuitCandidate],
) -> BTreeMap<BlockRef, Vec<&ShortCircuitCandidate>> {
    let mut by_exit = BTreeMap::<BlockRef, Vec<_>>::new();
    for short in short_circuits {
        if let ShortCircuitExit::BranchExit { truthy, falsy } = short.exit {
            by_exit.entry(truthy).or_default().push(short);
            by_exit.entry(falsy).or_default().push(short);
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
    backedge_source: BlockRef,
) -> Option<BlockRef> {
    let ShortCircuitExit::BranchExit { truthy, falsy } = short.exit else {
        return None;
    };
    let loop_exit = if truthy == backedge_source {
        falsy
    } else if falsy == backedge_source {
        truthy
    } else {
        return None;
    };
    let header_exit_rejoins_tail =
        while_header_exit_rejoins_repeat_exit(cfg, graph_facts, candidate, loop_exit);
    if !short.reducible
        || !candidate.blocks.contains(&short.header)
        // while true 的 header 可以同时承载本轮正文和提前 break guard。若它经一条
        // 非 cleanup 正文路径到 jump latch，不能把这条路径反推成 repeat 尾条件；
        // Close 仍可作为 goto/repeat 的词法清理 pad，由后续 scope owner 接管。
        || (short.header == candidate.header
            && backedge_has_non_cleanup_prefix(proto, cfg, backedge_source))
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
        && header_exit != repeat_exit
        && candidate.exits.contains(&header_exit)
        && graph_facts.post_dominates(repeat_exit, header_exit)
}

fn direct_branch_repeat_continue_target(
    cfg: &Cfg,
    branches: &[BranchCandidate],
    candidate: &LoopCandidate,
    backedge_source: BlockRef,
) -> Option<BlockRef> {
    if candidate.kind_hint != LoopKindHint::WhileLike {
        return None;
    }
    let (then_edge, else_edge) = cfg.branch_edges(backedge_source)?;
    let (then_target, else_target) = (
        cfg.edges[then_edge.index()].to,
        cfg.edges[else_edge.index()].to,
    );
    let repeat_exit = match (
        then_target == candidate.header,
        else_target == candidate.header,
    ) {
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
    let merge = branches
        .iter()
        .find(|branch| branch.header == header_exit)?
        .merge?;
    if merge == cfg.exit_block
        || candidate.blocks.contains(&merge)
        || (repeat_exit != merge && cfg.unique_reachable_successor(repeat_exit) != Some(merge))
    {
        return None;
    }

    Some(backedge_source)
}

fn refine_ambiguous_repeat_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    candidates: &mut [LoopCandidate],
) {
    // repeat body 若进入 nested loop，natural-loop core 会把该入口误看成 header exit；
    // 只有独立尾条件与 header 分支读取同一主体时，才能排除“真实 while + 尾部 break”。
    // repeat 后再 break 外层 for 时，条件出口又会像 while true 的 terminal exit。
    // 两者都只能等候选齐全后用关系证据消歧，不能全局提高 repeat 启发式优先级。
    let for_owners = candidates
        .iter()
        .enumerate()
        .filter(|(_, candidate)| {
            matches!(
                candidate.kind_hint,
                LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
            )
        })
        .flat_map(|(index, candidate)| {
            candidate
                .binding_scope_blocks
                .iter()
                .copied()
                .map(move |block| (block, index))
        })
        .fold(
            BTreeMap::<BlockRef, Vec<usize>>::new(),
            |mut owners, (block, index)| {
                owners.entry(block).or_default().push(index);
                owners
            },
        );
    let mut loop_entries = BTreeMap::<BlockRef, Vec<usize>>::new();
    for (index, candidate) in candidates.iter().enumerate() {
        loop_entries
            .entry(candidate.header)
            .or_default()
            .push(index);
        if let Some(preheader) = candidate.preheader {
            loop_entries.entry(preheader).or_default().push(index);
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
                        .flat_map(|target| loop_entries.get(&target).into_iter().flatten())
                        .copied()
                        .filter(|nested| *nested != index)
                        .any(|nested| {
                            candidates[nested]
                                .blocks
                                .is_subset(&candidate.binding_scope_blocks)
                        })
            }
            LoopKindHint::WhileTrueLike => for_owners
                .get(&candidate.header)
                .into_iter()
                .flatten()
                .copied()
                .filter(|owner| *owner != index)
                .any(|owner| !candidate.exits.is_disjoint(&candidates[owner].exits)),
            _ => false,
        };
        if is_repeat {
            candidates[index].kind_hint = LoopKindHint::RepeatLike;
            candidates[index].continue_target = Some(continue_target);
        }
    }
}

fn branch_conditions_share_subject(
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
    left.cond.predicate == right.cond.predicate && left.cond.operands == right.cond.operands
}

fn reachable_numeric_for_loop(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    graph_facts: &GraphFacts,
    natural_loops: &[&crate::structure::NaturalLoop],
    claimed_backedges: &mut BTreeSet<EdgeRef>,
) -> Option<LoopCandidate> {
    let natural_header = natural_loops.first()?.header;
    let mut matches = natural_loops.iter().filter_map(|natural_loop| {
        let latch = cfg.edges[natural_loop.backedge.index()].from;
        let LowInstr::NumericForLoop(loop_instr) = cfg.terminator(&proto.instrs, latch)? else {
            return None;
        };
        numeric_for_owner(proto, cfg, natural_header, loop_instr)
            .map(|(header, preheader)| (*natural_loop, header, preheader))
    });
    let (natural_loop, header, preheader) = matches.next()?;
    if matches.next().is_some() {
        return None;
    }
    let LowInstr::NumericForInit(init) = cfg.terminator(&proto.instrs, preheader)? else {
        return None;
    };
    let exit = cfg.instr_to_block[init.exit_target.index()];
    let latch = cfg.edges[natural_loop.backedge.index()].from;
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
    blocks.insert(cfg.edges[natural_loop.backedge.index()].from);
    if !natural_loops
        .iter()
        .all(|candidate| candidate.blocks.is_subset(&blocks))
        || !is_reducible_region(cfg, header, &blocks)
    {
        return None;
    }

    let mut candidate = build_loop_candidate(
        proto,
        cfg,
        graph_facts,
        dataflow,
        header,
        blocks,
        vec![natural_loop.backedge],
    );
    if duplicated_terminal_exit {
        candidate.exits.insert(exit);
        candidate.control_blocks.insert(latch_exit);
        candidate.exit_value_merges = analyze_loop_exit_value_merges(
            proto,
            cfg,
            dataflow,
            &candidate.exits,
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
    claimed_backedges.insert(natural_loop.backedge);
    Some(candidate)
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
    loop_instr.index == init.index
        && loop_instr.limit == init.limit
        && loop_instr.step == init.step
        && loop_instr.binding == init.binding
}

fn assign_same_header_merge_ownership(candidates: &mut [LoopCandidate]) {
    let mut start = 0;
    while start < candidates.len() {
        let header = candidates[start].header;
        let end = candidates[start..]
            .iter()
            .position(|candidate| candidate.header != header)
            .map_or(candidates.len(), |offset| start + offset);
        if candidates[start..end]
            .windows(2)
            .all(|pair| pair[0].blocks.is_subset(&pair[1].blocks))
        {
            for candidate in &mut candidates[start..end.saturating_sub(1)] {
                candidate.header_value_merges.clear();
            }
        }
        start = end;
    }
}

fn build_loop_candidate(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    header: BlockRef,
    blocks: BTreeSet<BlockRef>,
    mut backedges: Vec<EdgeRef>,
) -> LoopCandidate {
    backedges.sort();
    backedges.dedup();
    let preheader = unique_loop_preheader(cfg, header, &blocks);
    let exits = collect_region_exits(cfg, &blocks);
    let binding_scope_blocks = loop_binding_scope(&blocks, &exits, header, cfg, graph_facts);
    let header_value_merges = analyze_loop_header_value_merges(dataflow, header, &blocks);
    let (kind_hint, continue_target, source_bindings) = infer_loop_shape(LoopShapeInput {
        proto,
        cfg,
        dataflow,
        header,
        blocks: &blocks,
        backedges: &backedges,
        preheader,
        header_value_merges: &header_value_merges,
    });
    let exit_value_merges = analyze_loop_exit_value_merges(proto, cfg, dataflow, &exits, &blocks);

    LoopCandidate {
        header,
        preheader,
        blocks,
        binding_scope_blocks,
        control_blocks: BTreeSet::new(),
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
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    graph_facts: &GraphFacts,
    numeric_headers: &BTreeSet<BlockRef>,
    preheader: BlockRef,
) -> Option<LoopCandidate> {
    let Some(LowInstr::NumericForInit(init)) = cfg.terminator(&proto.instrs, preheader) else {
        return None;
    };
    let header = cfg.instr_to_block[init.body_target.index()];
    let exit = cfg.instr_to_block[init.exit_target.index()];
    if numeric_headers.contains(&header) || header == exit {
        return None;
    }

    let latch = proto
        .instrs
        .iter()
        .enumerate()
        .find_map(|(index, instr)| match instr {
            LowInstr::NumericForLoop(loop_instr)
                if numeric_for_state_matches(init, loop_instr)
                    // Luau 会把不可达 latch 的 body edge 直接改指向 loop exit。
                    && (loop_instr.body_target == init.body_target
                        || loop_instr.body_target == init.exit_target)
                    // 立即 break 的空循环还会把 latch exit 留在不可达 jump pad；
                    // pad 与 init exit 汇合时仍属于同一个数值循环身份。
                    && same_or_transparent_jump_target(
                        proto,
                        cfg,
                        loop_instr.exit_target,
                        init.exit_target,
                    ) =>
            {
                Some(cfg.instr_to_block[index])
            }
            _ => None,
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
    let exits = collect_region_exits(cfg, &blocks);
    if !exits.contains(&exit) || !is_reducible_region(cfg, header, &blocks) {
        return None;
    }
    let binding_scope_blocks = loop_binding_scope(&blocks, &exits, header, cfg, graph_facts);

    Some(LoopCandidate {
        header,
        preheader: Some(preheader),
        binding_scope_blocks,
        control_blocks: BTreeSet::new(),
        backedges: Vec::new(),
        exits: exits.clone(),
        continue_target: Some(latch),
        continue_edges: BTreeSet::new(),
        condition_header: None,
        kind_hint: LoopKindHint::NumericForLike,
        source_bindings: Some(LoopSourceBindings::Numeric(init.binding)),
        header_value_merges: analyze_loop_header_value_merges(dataflow, header, &blocks),
        exit_value_merges: analyze_loop_exit_value_merges(proto, cfg, dataflow, &exits, &blocks),
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

fn same_or_transparent_jump_target(
    proto: &LoweredProto,
    cfg: &Cfg,
    actual: crate::transformer::InstrRef,
    expected: crate::transformer::InstrRef,
) -> bool {
    if actual == expected {
        return true;
    }
    let block = cfg.instr_to_block[actual.index()];
    let range = cfg.blocks[block.index()].instrs;
    range.len == 1
        && matches!(
            cfg.terminator(&proto.instrs, block),
            Some(LowInstr::Jump(jump))
                if cfg.instr_to_block[jump.target.index()]
                    == cfg.instr_to_block[expected.index()]
        )
}

fn equivalent_single_return_targets(
    proto: &LoweredProto,
    cfg: &Cfg,
    actual: crate::transformer::InstrRef,
    expected: crate::transformer::InstrRef,
) -> bool {
    let block = cfg.instr_to_block[actual.index()];
    let range = cfg.blocks[block.index()].instrs;
    let expected_block = cfg.instr_to_block[expected.index()];
    cfg.blocks[expected_block.index()].instrs.len == 1
        && range.len == 1
        && matches!(
            (
                cfg.terminator(&proto.instrs, block),
                cfg.terminator(&proto.instrs, expected_block),
            ),
            (Some(LowInstr::Return(actual)), Some(LowInstr::Return(expected)))
                if actual == expected
        )
}

fn analyze_degenerate_generic_for_loops(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    graph_facts: &GraphFacts,
    grouped_headers: &BTreeSet<BlockRef>,
    nested_loops: &[LoopCandidate],
) -> Vec<LoopCandidate> {
    cfg.reachable_blocks
        .iter()
        .copied()
        .filter(|header| !grouped_headers.contains(header))
        .filter_map(|header| {
            degenerate_generic_for_loop(proto, cfg, dataflow, graph_facts, nested_loops, header)
        })
        .collect()
}

fn degenerate_generic_for_loop(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    graph_facts: &GraphFacts,
    nested_loops: &[LoopCandidate],
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
        blocks.insert(body);
    }
    let mut owned_nested_loops = nested_loops
        .iter()
        .filter(|candidate| candidate.header == body && candidate.preheader == Some(header));
    if let Some(nested) = owned_nested_loops.next() {
        if owned_nested_loops.next().is_some() {
            return None;
        }
        blocks.extend(nested.blocks.iter().copied());
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
    let binding_scope_blocks = loop_binding_scope(&blocks, &exits, header, cfg, graph_facts);

    let preheader = unique_loop_preheader(cfg, header, &blocks);
    let header_value_merges = analyze_loop_header_value_merges(dataflow, header, &blocks);
    // 退化 generic-for 没有自身回边：header -> exit 表示零次迭代，语义上属于
    // 循环外初值；只有 body（含直属 nested loop）到 exit 的边才是循环内写回。
    let mut body_blocks = blocks.clone();
    body_blocks.remove(&header);
    let exit_value_merges =
        analyze_loop_exit_value_merges(proto, cfg, dataflow, &exits, &body_blocks);

    Some(LoopCandidate {
        header,
        preheader,
        blocks,
        binding_scope_blocks,
        control_blocks: BTreeSet::new(),
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

    let exits = collect_region_exits(cfg, blocks);
    if backedge_sources.len() > 1
        && exits.len() > 1
        && matches!(
            cfg.terminator(&proto.instrs, header),
            Some(LowInstr::Branch(_))
        )
        && !region_has_scope_cleanup(proto, cfg, blocks)
        && exits_are_terminal(proto, cfg, &exits)
    {
        // 多个 sibling latch 只是把同一轮尾部短路条件拆成多条回 header 的边；
        // 没有普通 continuation 时，header 本身就是这些回边共同拥有的下一轮入口。
        return (LoopKindHint::WhileTrueLike, Some(header), None);
    }

    if backedge_sources.len() == 1 {
        let source = *backedge_sources
            .iter()
            .next()
            .expect("set length already checked");
        if matches!(
            cfg.terminator(&proto.instrs, source),
            Some(LowInstr::Jump(jump)) if cfg.instr_to_block[jump.target.index()] == header
        ) && !region_has_scope_cleanup(proto, cfg, blocks)
            && exits_are_terminal(proto, cfg, &exits)
        {
            return (LoopKindHint::WhileTrueLike, Some(source), None);
        }

        if matches!(
            cfg.terminator(&proto.instrs, source),
            Some(LowInstr::Branch(_instr)) if branch_has_header_and_exit(cfg, source, header, blocks)
        ) {
            return (LoopKindHint::RepeatLike, Some(source), None);
        }

        if matches!(
            cfg.terminator(&proto.instrs, source),
            Some(LowInstr::Jump(jump))
                if cfg.instr_to_block[jump.target.index()] == header
        ) && let Some(continue_target) =
            repeat_continue_target_via_backedge_pad(proto, cfg, source, blocks)
        {
            return (LoopKindHint::RepeatLike, Some(continue_target), None);
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

/// 计算 for-loop binding 的可见作用域块集合。
///
/// natural loop 拓扑只包含能回到 header 的 body 块，不含通过 return/break
/// 提前离开循环的块。但在 Lua 语义下，这些提前退出的块仍处于 for-binding
/// 的词法作用域中（如 `for i = 1, n do if cond then return i end end`）。
///
/// 策略：在 candidate.blocks 基础上，追加被 header 严格支配的提前退出区域。
/// 只有不是通过 LoopExit 边到达的出口块才被视为提前退出；LoopExit 边的目标是循环
/// 正常结束后的后继块，for-binding 在那里已失效。
fn loop_binding_scope(
    body_blocks: &BTreeSet<BlockRef>,
    exits: &BTreeSet<BlockRef>,
    header: BlockRef,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
) -> BTreeSet<BlockRef> {
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
    if let Some(shared_successor) = shared_unique_exit_successor(exits, cfg) {
        scope_boundaries.insert(shared_successor);
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

fn shared_unique_exit_successor(exits: &BTreeSet<BlockRef>, cfg: &Cfg) -> Option<BlockRef> {
    if exits.len() < 2 {
        return None;
    }
    let mut exits = exits.iter().copied();
    let shared = cfg.unique_reachable_successor(exits.next()?)?;
    exits
        .all(|exit| cfg.unique_reachable_successor(exit) == Some(shared))
        .then_some(shared)
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
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    exits: &BTreeSet<BlockRef>,
    loop_blocks: &BTreeSet<BlockRef>,
) -> Vec<LoopExitValueMergeCandidate> {
    let shared_merge = shared_transparent_loop_exit_merge(proto, cfg, exits);
    let mut candidates = exits
        .iter()
        .copied()
        .filter(|exit| Some(*exit) != shared_merge)
        .filter_map(|exit| loop_exit_value_merge_in_block(dataflow, exit, loop_blocks))
        .collect::<Vec<_>>();

    if let Some(shared_merge) = shared_merge {
        let mut ownership_blocks = loop_blocks.clone();
        ownership_blocks.extend(exits.iter().copied().filter(|exit| *exit != shared_merge));
        if let Some(candidate) =
            loop_exit_value_merge_in_block(dataflow, shared_merge, &ownership_blocks)
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

fn shared_transparent_loop_exit_merge(
    proto: &LoweredProto,
    cfg: &Cfg,
    exits: &BTreeSet<BlockRef>,
) -> Option<BlockRef> {
    if exits.len() < 2 {
        return None;
    }

    let mut common = None::<BTreeSet<BlockRef>>;
    for exit in exits.iter().copied() {
        let mut reachable = BTreeSet::from([exit]);
        if let Some(target) = transparent_loop_exit_target(proto, cfg, exit) {
            reachable.insert(target);
        }
        common = Some(match common {
            Some(common) => common.intersection(&reachable).copied().collect(),
            None => reachable,
        });
    }

    let mut common = common?.into_iter().filter(|block| *block != cfg.exit_block);
    let merge = common.next()?;
    common.next().is_none().then_some(merge)
}

fn transparent_loop_exit_target(
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
            if instr_writes_any_reg(instr, &carried_regs) || !instr_is_while_header_prefix(instr) {
                return false;
            }

            let Some(effect) = dataflow.instr_effects.get(instr_index) else {
                return false;
            };
            let writes_needed = instr_writes_any_reg_set(effect, &needed_regs);
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
            | LowInstr::GenericForCall(_)
            | LowInstr::GenericForLoop(_)
            | LowInstr::Jump(_)
            | LowInstr::Branch(_)
    )
}

fn instr_writes_any_reg(instr: &LowInstr, regs: &BTreeSet<Reg>) -> bool {
    match instr {
        LowInstr::Move(instr) => regs.contains(&instr.dst),
        LowInstr::LoadNil(instr) => (0..instr.dst.len)
            .map(|offset| Reg(instr.dst.start.index() + offset))
            .any(|reg| regs.contains(&reg)),
        LowInstr::LoadBool(instr) => regs.contains(&instr.dst),
        LowInstr::LoadConst(instr) => regs.contains(&instr.dst),
        LowInstr::LoadInteger(instr) => regs.contains(&instr.dst),
        LowInstr::LoadNumber(instr) => regs.contains(&instr.dst),
        LowInstr::UnaryOp(instr) => regs.contains(&instr.dst),
        LowInstr::BinaryOp(instr) => regs.contains(&instr.dst),
        LowInstr::Concat(instr) => regs.contains(&instr.dst),
        LowInstr::GetUpvalue(instr) => regs.contains(&instr.dst),
        LowInstr::GetTable(instr) => regs.contains(&instr.dst),
        LowInstr::NewTable(instr) => regs.contains(&instr.dst),
        LowInstr::Closure(instr) => regs.contains(&instr.dst),
        LowInstr::Call(instr) => result_pack_writes_any_reg(&instr.results, regs),
        LowInstr::VarArg(instr) => result_pack_writes_any_reg(&instr.results, regs),
        // ErrNil 只读 subject 不写寄存器。
        LowInstr::ErrNil(_) => false,
        // 以下指令要么不写寄存器，要么已被 instr_is_while_header_prefix 排除。
        LowInstr::SetUpvalue(_)
        | LowInstr::SetTable(_)
        | LowInstr::SetList(_)
        | LowInstr::TailCall(_)
        | LowInstr::Return(_)
        | LowInstr::Close(_)
        | LowInstr::Tbc(_)
        | LowInstr::NumericForInit(_)
        | LowInstr::NumericForLoop(_)
        | LowInstr::GenericForCall(_)
        | LowInstr::GenericForLoop(_)
        | LowInstr::Jump(_)
        | LowInstr::Branch(_) => false,
    }
}

fn instr_writes_any_reg_set(effect: &crate::structure::InstrEffect, regs: &BTreeSet<Reg>) -> bool {
    effect.fixed_must_defs.iter().any(|reg| regs.contains(reg))
        || effect
            .open_must_def
            .is_some_and(|start| regs.iter().any(|reg| reg.index() >= start.index()))
}

fn result_pack_writes_any_reg(results: &ResultPack, regs: &BTreeSet<Reg>) -> bool {
    match results {
        ResultPack::Fixed(range) => (0..range.len)
            .map(|offset| Reg(range.start.index() + offset))
            .any(|reg| regs.contains(&reg)),
        // Open result pack 从 start 开始向高位扩展，保守地检查 start 本身。
        // 实际 while 条件求值中 open pack 极少出现，但如果出现则 start 之后的
        // 所有寄存器理论上都可能被写入——这里保守处理即可，因为 carried_regs
        // 通常只包含少量低位循环变量。
        ResultPack::Open(start) => regs.iter().any(|reg| reg.index() >= start.index()),
        ResultPack::Ignore => false,
    }
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

    matches!(call.results, crate::transformer::ResultPack::Fixed(range) if range == instr.bindings)
        && (body_block == exit_block
            || same_or_transparent_jump_target(proto, cfg, instr.exit_target, instr.body_target)
            || blocks.contains(&body_block))
        && !blocks.contains(&exit_block)
}
