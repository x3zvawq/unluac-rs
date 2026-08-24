//! 重叠 loop evidence 的规范化。输入同 header 或嵌套候选，输出无重复的最终 loop inputs 与必要 residual islands；不负责 region 物化。例如同一控制身份的候选会合并 backedge、value merge 与 continuation 事实。

use super::*;

pub(super) fn canonicalize_loops(
    cfg: &Cfg,
    mut loops: Vec<super::super::LoopPlanInput>,
) -> (
    Vec<super::super::LoopPlanInput>,
    Vec<super::super::UnstructuredPlanData>,
) {
    for loop_ in &mut loops {
        normalize_break_only_while_body(cfg, loop_);
    }
    let mut by_header = BTreeMap::<BlockRef, Vec<super::super::LoopPlanInput>>::new();
    for loop_ in loops {
        by_header
            .entry(loop_.candidate.header)
            .or_default()
            .push(loop_);
    }

    let mut selected_loops = Vec::new();
    let mut residuals = Vec::new();
    for candidates in by_header.into_values() {
        let distinct_blocks = candidates
            .iter()
            .map(|candidate| &candidate.candidate.blocks)
            .collect::<BTreeSet<_>>();
        let mut block_sets = distinct_blocks.iter().copied().collect::<Vec<_>>();
        block_sets.sort_by_key(|blocks| blocks.len());
        // 同 header 的候选若构成包含链，按大小排序后只需检查相邻集合；传递性保证
        // 其余任意两项也嵌套，避免候选较多时做全对集合比较。
        let nested_chain = block_sets.windows(2).all(|pair| pair[0].is_subset(pair[1]));
        let candidate_groups = if block_sets.len() > 1 && nested_chain {
            let mut by_blocks = BTreeMap::<BTreeSet<BlockRef>, Vec<_>>::new();
            for candidate in candidates {
                by_blocks
                    .entry(candidate.candidate.blocks.clone())
                    .or_default()
                    .push(candidate);
            }
            by_blocks.into_values().collect::<Vec<_>>()
        } else {
            vec![candidates]
        };

        for mut candidates in candidate_groups {
            let kinds = candidates
                .iter()
                .map(|candidate| candidate.candidate.kind_hint)
                .filter(|kind| *kind != crate::structure::LoopKindHint::Unknown)
                .collect::<BTreeSet<_>>();
            let mut bindings = Vec::new();
            for binding in candidates
                .iter()
                .filter_map(|candidate| candidate.candidate.source_bindings)
            {
                if !bindings.contains(&binding) {
                    bindings.push(binding);
                }
            }
            let conditions = candidates
                .iter()
                .filter_map(|candidate| candidate.condition)
                .collect::<BTreeSet<_>>();
            if kinds.len() > 1 || bindings.len() > 1 || conditions.len() > 1 {
                let Some(first) = candidates.first() else {
                    continue;
                };
                let header = first.candidate.header;
                let mut blocks = BTreeSet::from([header]);
                let mut exits = BTreeSet::new();
                for candidate in candidates {
                    blocks.extend(candidate.candidate.blocks);
                    blocks.extend(candidate.candidate.body_scope_blocks);
                    blocks.extend(candidate.candidate.control_blocks);
                    exits.extend(candidate.candidate.exits);
                }
                residuals.push(super::super::UnstructuredPlanData {
                    fact: crate::structure::RegionFact {
                        blocks,
                        entry: header,
                        exits,
                    },
                    layout: None,
                });
                continue;
            }
            let selected = candidates
                .iter()
                .enumerate()
                .max_by_key(|(index, candidate)| {
                    (
                        candidate.candidate.source_bindings.is_some(),
                        candidate.candidate.kind_hint != crate::structure::LoopKindHint::Unknown,
                        candidate.candidate.blocks.len(),
                        Reverse(*index),
                    )
                })
                .map(|(index, _)| index);
            let Some(selected) = selected else {
                continue;
            };
            let mut selected = candidates.swap_remove(selected);
            for candidate in candidates {
                selected
                    .candidate
                    .blocks
                    .extend(candidate.candidate.blocks.iter().copied());
                selected
                    .candidate
                    .body_scope_blocks
                    .extend(candidate.candidate.body_scope_blocks.iter().copied());
                selected
                    .candidate
                    .control_blocks
                    .extend(candidate.candidate.control_blocks.iter().copied());
                selected
                    .candidate
                    .normalized_exit_aliases
                    .extend(candidate.candidate.normalized_exit_aliases);
                selected.candidate.exits.extend(candidate.candidate.exits);
                selected
                    .candidate
                    .continue_edges
                    .extend(candidate.candidate.continue_edges);
                selected
                    .semantic_continue_edges
                    .extend(candidate.semantic_continue_edges);
                extend_edges(
                    &mut selected.candidate.backedges,
                    candidate.candidate.backedges,
                );
                extend_value_merges(
                    &mut selected.candidate.header_value_merges,
                    candidate.candidate.header_value_merges,
                );
                for exit_merge in candidate.candidate.exit_value_merges {
                    if let Some(existing) = selected
                        .candidate
                        .exit_value_merges
                        .iter_mut()
                        .find(|existing| existing.exit == exit_merge.exit)
                    {
                        extend_value_merges(&mut existing.values, exit_merge.values);
                    } else {
                        selected.candidate.exit_value_merges.push(exit_merge);
                    }
                }
                extend_value_merges(&mut selected.carried_values, candidate.carried_values);
                if selected.condition.is_none() {
                    selected.condition = candidate.condition;
                }
                if selected.continuation != candidate.continuation {
                    selected.continuation = None;
                }
            }
            selected
                .candidate
                .backedges
                .sort_by_key(|edge| edge.index());
            selected.candidate.normalize_control_blocks();
            selected.candidate.normalized_exit_aliases.sort();
            selected.candidate.normalized_exit_aliases.dedup();
            selected_loops.push(selected);
        }
    }
    (selected_loops, residuals)
}

pub(super) fn normalize_break_only_while_body(cfg: &Cfg, loop_: &mut super::super::LoopPlanInput) {
    use crate::structure::LoopKindHint;

    let candidate = &loop_.candidate;
    if candidate.kind_hint != LoopKindHint::WhileLike
        || candidate.body_scope_blocks.is_subset(&candidate.blocks)
    {
        return;
    }
    let Some(continuation) = loop_.continuation else {
        return;
    };
    let mut lexical = reachable_nonempty_blocks(cfg, candidate.body_scope_blocks.clone());
    lexical.insert(candidate.header);
    lexical.remove(&continuation);
    let Some((truthy, falsy)) = cfg.branch_edges(candidate.header) else {
        return;
    };
    if ![truthy, falsy]
        .into_iter()
        .map(|edge| cfg.edges[edge.index()].to)
        .all(|target| lexical.contains(&target))
        || !candidate.blocks.is_subset(&lexical)
        || !single_entry(cfg, &lexical, candidate.header)
    {
        return;
    }
    let mut has_break = false;
    for block in &lexical {
        for edge in &cfg.succs[block.index()] {
            let target = cfg.edges[edge.index()].to;
            if lexical.contains(&target) {
                continue;
            }
            if target == continuation {
                has_break = true;
            } else if target != cfg.exit_block {
                return;
            }
        }
    }
    if !has_break {
        return;
    }

    let candidate = &mut loop_.candidate;
    candidate.kind_hint = LoopKindHint::WhileTrueLike;
    candidate.condition_header = None;
    candidate.blocks = lexical.clone();
    candidate.body_scope_blocks = lexical;
    candidate.exits = candidate
        .blocks
        .iter()
        .flat_map(|block| cfg.succs[block.index()].iter().copied())
        .map(|edge| cfg.edges[edge.index()].to)
        .filter(|target| !candidate.blocks.contains(target))
        .collect();
    loop_.condition = None;
}

pub(super) fn extend_edges(target: &mut Vec<EdgeRef>, source: Vec<EdgeRef>) {
    let mut merged = std::mem::take(target).into_iter().collect::<BTreeSet<_>>();
    merged.extend(source);
    target.extend(merged);
}

pub(super) fn extend_value_merges(
    target: &mut Vec<crate::structure::LoopValueMerge>,
    source: Vec<crate::structure::LoopValueMerge>,
) {
    let mut by_value = target
        .iter()
        .enumerate()
        .map(|(index, merge)| ((merge.phi_id, merge.reg), index))
        .collect::<BTreeMap<_, _>>();
    for merge in source {
        if let Some(index) = by_value.get(&(merge.phi_id, merge.reg)).copied() {
            let existing = &mut target[index];
            extend_value_incomings(
                &mut existing.inside_arm.incomings,
                merge.inside_arm.incomings,
            );
            extend_value_incomings(
                &mut existing.outside_arm.incomings,
                merge.outside_arm.incomings,
            );
        } else {
            by_value.insert((merge.phi_id, merge.reg), target.len());
            target.push(merge);
        }
    }
}

pub(super) fn extend_value_incomings(
    target: &mut Vec<crate::structure::LoopValueIncoming>,
    source: Vec<crate::structure::LoopValueIncoming>,
) {
    let mut known = target
        .iter()
        .map(|incoming| (incoming.pred, incoming.value))
        .collect::<BTreeSet<_>>();
    for incoming in source {
        if known.insert((incoming.pred, incoming.value)) {
            target.push(incoming);
        }
    }
}
