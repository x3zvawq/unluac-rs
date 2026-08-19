//! effectful unknown-loop 条件的结构归一化。输入 loop partition 与 branch evidence，输出可冻结的 guard/body 边界；不负责后层 HIR 兜底。例如带副作用的 header guard 会改写为 loop body 内的一臂 branch。

use super::*;

pub(super) fn normalize_effectful_unknown_loop_conditions(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    input: &mut FinalPlanInput,
    partitions: &[LoopPartitions],
) -> Result<bool, StructureError> {
    let mut while_true_guards = Vec::new();
    let mut loop_header_guards = Vec::new();
    let mut rewrites = Vec::new();
    for (loop_index, loop_) in input.loops.iter().enumerate() {
        let partition = partitions
            .get(loop_index)
            .ok_or_else(|| StructureError::invalid("selected loop has no frozen partitions"))?;
        if loop_.candidate.kind_hint == crate::structure::LoopKindHint::WhileTrueLike
            && partition.control.is_empty()
            && let Some(continuation) = partition.continuation
            && let Some((branch, condition)) =
                input
                    .branches
                    .iter()
                    .enumerate()
                    .find_map(|(index, branch)| {
                        (branch.branch.header == loop_.candidate.header)
                            .then_some(branch.condition)
                            .flatten()
                            .and_then(|condition| {
                                input
                                    .conditions
                                    .get(condition.index())
                                    .map(|condition| (index, condition))
                            })
                    })
            && let ShortCircuitExit::BranchExit { truthy, falsy } = condition.candidate.exit
        {
            let body = match (truthy == continuation, falsy == continuation) {
                (true, false) if partition.body.contains(&falsy) => Some(falsy),
                (false, true) if partition.body.contains(&truthy) => Some(truthy),
                (true, true) | (false, false) | (true, false) | (false, true) => None,
            };
            if let Some(body) = body {
                // `while true; if condition then break end` 的编译结果会把整个短路 DAG
                // 绑定到 header 上的早期 local-join candidate。最终 condition 出口已经
                // 明确给出 break/body，直接冻结为包住 body tail 的单臂 guard。
                while_true_guards.push((branch, continuation, body));
                continue;
            }
        }
        if loop_.candidate.kind_hint != crate::structure::LoopKindHint::Unknown
            || !partition.control.is_empty()
        {
            continue;
        }
        let Some(condition_id) = loop_.condition else {
            continue;
        };
        let condition = input.conditions.get(condition_id.index()).ok_or_else(|| {
            StructureError::invalid(format!(
                "loop #{loop_index} references missing condition #{}",
                condition_id.index()
            ))
        })?;
        let ShortCircuitExit::BranchExit { truthy, falsy } = condition.candidate.exit else {
            continue;
        };
        if truthy == condition.candidate.header || falsy == condition.candidate.header {
            let remainder = if truthy == condition.candidate.header {
                falsy
            } else {
                truthy
            };
            if partition.body.contains(&remainder)
                && let Some(branch) = input.branches.iter().position(|branch| {
                    branch.branch.header == condition.candidate.header
                        && branch.condition == Some(condition_id)
                })
            {
                loop_header_guards.push((branch, remainder));
            }
            continue;
        }
        if !partition.body.contains(&truthy) || !partition.body.contains(&falsy) {
            continue;
        }

        let Some(prefix_branch) = input.branches.iter().position(|branch| {
            branch.branch.header == condition.candidate.header
                && branch.condition == Some(condition_id)
        }) else {
            continue;
        };
        let branch = &input.branches[prefix_branch].branch;
        if branch.else_entry.is_some() {
            continue;
        }
        // Unknown 条件的两个出口都还在 natural loop 内时，真正的 body 出口必须支配
        // 某条已冻结 backedge。这个 dominator interval 查询等价于旧的“能否到达
        // latch”探测，但不会为每个 loop 重跑图搜索；local join 仅作为直接边界证据。
        let reaches_backedge = |target| {
            loop_.candidate.backedges.iter().any(|edge| {
                cfg.edges
                    .get(edge.index())
                    .is_some_and(|edge| graph_facts.dominates(target, edge.from))
            })
        };
        let (remainder, body) = match (reaches_backedge(truthy), reaches_backedge(falsy)) {
            (true, false) => (falsy, truthy),
            (false, true) => (truthy, falsy),
            (true, true) | (false, false) => match branch.merge {
                Some(merge) if merge == truthy => (falsy, truthy),
                Some(merge) if merge == falsy => (truthy, falsy),
                Some(_) | None => continue,
            },
        };
        if !loop_.candidate.backedges.iter().any(|edge| {
            cfg.edges
                .get(edge.index())
                .is_some_and(|edge| graph_facts.dominates(body, edge.from))
        }) {
            continue;
        }
        let terminal_branches = partition
            .continuation
            .into_iter()
            .flat_map(|continuation| {
                input
                    .branches
                    .iter()
                    .enumerate()
                    .filter_map(move |(index, branch)| {
                        let header = branch.branch.header;
                        if header == condition.candidate.header
                            || !graph_facts.dominates(remainder, header)
                            || graph_facts.dominates(body, header)
                        {
                            return None;
                        }
                        let (truthy_edge, falsy_edge) = cfg.branch_edges(header)?;
                        let truthy_target = cfg.edges[truthy_edge.index()].to;
                        let falsy_target = cfg.edges[falsy_edge.index()].to;
                        match (truthy_target, falsy_target) {
                            (target, inside) | (inside, target)
                                if target == continuation && inside == body =>
                            {
                                Some((index, target, inside))
                            }
                            _ => None,
                        }
                    })
            })
            .collect::<Vec<_>>();
        rewrites.push((prefix_branch, remainder, body, terminal_branches));
    }

    let changed =
        !while_true_guards.is_empty() || !loop_header_guards.is_empty() || !rewrites.is_empty();
    for (branch, escape, body) in while_true_guards {
        rewrite_one_arm_branch(graph_facts, &mut input.branches[branch], escape, body);
    }
    for (branch, remainder) in loop_header_guards {
        rewrite_loop_header_guard(&mut input.branches[branch], remainder);
    }
    for (prefix_branch, remainder, body, terminal_branches) in rewrites {
        rewrite_one_arm_branch(
            graph_facts,
            &mut input.branches[prefix_branch],
            remainder,
            body,
        );
        for (index, exit, continuation) in terminal_branches {
            rewrite_one_arm_branch(graph_facts, &mut input.branches[index], exit, continuation);
        }
    }
    Ok(changed)
}

pub(super) fn rewrite_loop_header_guard(
    branch: &mut super::super::BranchPlanInput,
    then_entry: BlockRef,
) {
    branch.branch.then_entry = then_entry;
    branch.branch.else_entry = None;
    branch.branch.merge = None;
    branch.branch.kind = BranchKind::IfThen;
    branch.branch.invert_hint = false;
    branch.value_merge = None;
    branch.region = None;
}

pub(super) fn rewrite_one_arm_branch(
    graph_facts: &GraphFacts,
    branch: &mut super::super::BranchPlanInput,
    then_entry: BlockRef,
    merge: BlockRef,
) {
    branch.branch.then_entry = then_entry;
    branch.branch.else_entry = None;
    branch.branch.merge = Some(merge);
    branch.branch.kind = BranchKind::IfThen;
    branch.branch.invert_hint = false;
    branch.value_merge = None;
    branch.region = Some(BranchRegionFact::new(
        graph_facts,
        branch.branch.header,
        merge,
        BranchKind::IfThen,
        None,
    ));
}
