//! 等域 retry/VM-for 的共享关系证明。输入最终 loop partitions、residual evidence 与
//! branch condition 出口，输出唯一外层 retry、内层 VM-for 及条件重启 arm；不负责容器
//! 插入或 edge 分类。例如 `::retry:: for value in iter do if again then goto retry end end`
//! 中，外层 normal exit、内层 VM control 和条件重启必须作为一个事务被后续阶段消费。

use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct EqualLoopNesting {
    pub(super) parent: super::super::LoopPlanId,
    pub(super) child: super::super::LoopPlanId,
    pub(super) guard: super::super::BranchPlanId,
    pub(super) retry_edge: EdgeRef,
    pub(super) retry_entry: BlockRef,
    pub(super) vm_control: BlockRef,
    pub(super) invert_guard: bool,
}

pub(super) struct LoopRegionSnapshot<'a> {
    pub(super) partitions: &'a [LoopPartitions],
    pub(super) domains: &'a [BTreeSet<BlockRef>],
    pub(super) equal_nestings: &'a [EqualLoopNesting],
}

pub(super) fn loop_container_domains(
    cfg: &Cfg,
    partitions: &[LoopPartitions],
) -> Vec<BTreeSet<BlockRef>> {
    partitions
        .iter()
        .map(|partition| {
            let mut blocks = partition.owned.clone();
            if let Some(normal_tail) = &partition.normal_tail {
                blocks.extend(normal_tail.blocks.iter().copied());
            }
            reachable_nonempty_blocks(cfg, blocks)
        })
        .collect()
}

pub(super) fn analyze_equal_loop_nestings(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    input: &FinalPlanInput,
    partitions: &[LoopPartitions],
    domains: &[BTreeSet<BlockRef>],
) -> Result<Vec<EqualLoopNesting>, StructureError> {
    use crate::structure::{GotoReason, LoopKindHint};

    type EqualLoopKey = (BTreeSet<BlockRef>, BlockRef, BlockRef);

    let cross_loop_edges = input
        .residual_transfers
        .iter()
        .filter(|transfer| transfer.reason == GotoReason::CrossLoopContinueLike)
        .map(|transfer| transfer.edge)
        .collect::<BTreeSet<_>>();
    let mut retry_parents = BTreeMap::<EqualLoopKey, Vec<super::super::LoopPlanId>>::new();
    let mut vm_for_children = BTreeMap::<EqualLoopKey, Vec<super::super::LoopPlanId>>::new();
    for (index, loop_) in input.loops.iter().enumerate() {
        let id = super::super::LoopPlanId(index);
        let Some(partition) = partitions.get(index) else {
            continue;
        };
        let Some(blocks) = domains.get(index) else {
            continue;
        };
        let Some(continuation) = partition.continuation else {
            continue;
        };
        let candidate = &loop_.candidate;
        if candidate.kind_hint == LoopKindHint::Unknown
            && loop_.condition.is_none()
            && partition.preheader.is_none()
            && partition.control.is_empty()
            && !candidate.backedges.is_empty()
            && candidate.backedges.iter().all(|edge_ref| {
                cross_loop_edges.contains(edge_ref)
                    && cfg.edges.get(edge_ref.index()).is_some_and(|edge| {
                        edge.to == candidate.header && blocks.contains(&edge.from)
                    })
            })
            && loop_part_for_blocks(partition, blocks)? == Some(LoopPart::Body)
        {
            retry_parents
                .entry((blocks.clone(), candidate.header, continuation))
                .or_default()
                .push(id);
        }
        if matches!(
            candidate.kind_hint,
            LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
        ) && let Some(preheader) = partition.preheader
            && preheader != candidate.header
        {
            vm_for_children
                .entry((blocks.clone(), preheader, continuation))
                .or_default()
                .push(id);
        }
    }

    type RetryRelation = (super::super::LoopPlanId, super::super::LoopPlanId, EdgeRef);
    let mut relation_by_retry_entry = BTreeMap::<BlockRef, Option<RetryRelation>>::new();
    for (key, parents) in &retry_parents {
        let Some(children) = vm_for_children.get(key) else {
            continue;
        };
        let ([parent], [child]) = (parents.as_slice(), children.as_slice()) else {
            continue;
        };
        for &retry_edge in &input.loops[parent.index()].candidate.backedges {
            let retry_entry = cfg.edges[retry_edge.index()].from;
            let relation = (*parent, *child, retry_edge);
            relation_by_retry_entry
                .entry(retry_entry)
                .and_modify(|present| {
                    if *present != Some(relation) {
                        *present = None;
                    }
                })
                .or_insert(Some(relation));
        }
    }

    type GuardKey = (
        super::super::LoopPlanId,
        super::super::LoopPlanId,
        EdgeRef,
        BlockRef,
        BlockRef,
    );
    let mut guards_by_relation =
        BTreeMap::<GuardKey, Vec<(super::super::BranchPlanId, bool)>>::new();
    for (index, branch) in input.branches.iter().enumerate() {
        let condition_matches = branch.condition.is_some_and(|condition_id| {
            input
                .conditions
                .get(condition_id.index())
                .is_some_and(|condition| condition.candidate.header == branch.branch.header)
        });
        if !condition_matches
            || branch.branch.else_entry.is_some()
            || !matches!(branch.branch.kind, BranchKind::Guard | BranchKind::IfThen)
        {
            continue;
        }
        let Some(merge) = branch.branch.merge else {
            continue;
        };
        let guard = (super::super::BranchPlanId(index), branch.branch.invert_hint);
        for (relation, retry_entry, vm_control) in [
            (
                relation_by_retry_entry
                    .get(&branch.branch.then_entry)
                    .copied()
                    .flatten(),
                branch.branch.then_entry,
                merge,
            ),
            (
                relation_by_retry_entry.get(&merge).copied().flatten(),
                merge,
                branch.branch.then_entry,
            ),
        ] {
            let Some((parent, child, retry_edge)) = relation else {
                continue;
            };
            if !partitions[child.index()].control.contains(&vm_control)
                || !partitions[child.index()]
                    .body
                    .contains(&branch.branch.header)
            {
                continue;
            }
            guards_by_relation
                .entry((parent, child, retry_edge, retry_entry, vm_control))
                .or_default()
                .push(guard);
        }
    }

    let mut nestings = Vec::new();
    for ((parent, child, retry_edge, retry_entry, vm_control), guards) in guards_by_relation {
        let min_depth = guards
            .iter()
            .filter_map(|(guard, _)| {
                graph_facts.dominator_tree.depth
                    [input.branches[guard.index()].branch.header.index()]
            })
            .min();
        let Some(min_depth) = min_depth else {
            continue;
        };
        let mut outermost = guards.iter().filter(|(guard, _)| {
            graph_facts.dominator_tree.depth[input.branches[guard.index()].branch.header.index()]
                == Some(min_depth)
        });
        let Some(&(guard, invert_guard)) = outermost.next() else {
            continue;
        };
        if outermost.next().is_some() {
            continue;
        }
        let guard_header = input.branches[guard.index()].branch.header;
        if !guards.iter().all(|(candidate, _)| {
            graph_facts.dominates(
                guard_header,
                input.branches[candidate.index()].branch.header,
            )
        }) {
            continue;
        }
        nestings.push(EqualLoopNesting {
            parent,
            child,
            guard,
            retry_edge,
            retry_entry,
            vm_control,
            invert_guard,
        });
    }
    Ok(nestings)
}

pub(super) fn normalize_equal_loop_retry_guards(
    graph_facts: &GraphFacts,
    input: &mut FinalPlanInput,
    nestings: &[EqualLoopNesting],
) -> Result<bool, StructureError> {
    let mut changed = false;
    for nesting in nestings {
        let branch = input
            .branches
            .get_mut(nesting.guard.index())
            .ok_or_else(|| {
                StructureError::invalid("equal-domain loop guard references a missing branch")
            })?;
        let already_normalized = branch.branch.then_entry == nesting.retry_entry
            && branch.branch.else_entry.is_none()
            && branch.branch.merge == Some(nesting.vm_control)
            && branch.branch.kind == BranchKind::IfThen
            && branch.branch.invert_hint == nesting.invert_guard;
        if already_normalized {
            continue;
        }
        rewrite_one_arm_branch(graph_facts, branch, nesting.retry_entry, nesting.vm_control);
        branch.branch.invert_hint = nesting.invert_guard;
        changed = true;
    }
    Ok(changed)
}
