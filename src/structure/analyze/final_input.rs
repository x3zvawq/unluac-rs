//! 汇总冻结最终 StructurePlan 所需的候选与边界；依赖各专题选择结果，不负责构建区域 arena；例如为 branch、loop 和 condition 建立稳定输入。
//! 候选在最后一次选择查询后移交载荷；branch 提取保证 header 唯一，因此对应边界和值合流事实各消费一次。

use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn final_plan_input(
    branches: Vec<BranchCandidate>,
    branch_regions: Vec<BranchRegionFact>,
    branch_value_merges: Vec<BranchValueMergeCandidate>,
    loops: Vec<LoopCandidate>,
    condition_candidates: &[ShortCircuitCandidate],
    value_candidates: &[ShortCircuitCandidate],
    closed_control_dags: &[ClosedControlDagEvidence],
    residual_transfers: Vec<ResidualTransferEvidence>,
    regions: Vec<RegionFact>,
    scopes: Vec<ScopePlan>,
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    graph_facts: &GraphFacts,
    exit_block: super::super::BlockRef,
    caps: ControlFlowCaps,
) -> Result<FinalPlanInput, StructureError> {
    let mut branch_regions = unique_branch_regions(branch_regions)?;
    let mut branch_value_merges = unique_branch_value_merges(branch_value_merges)?;
    let (conditions, condition_by_header) = selected_conditions(ConditionSelectionInput {
        proto,
        cfg,
        dataflow,
        loops: &loops,
        caps,
        branches: &branches,
        candidates: condition_candidates,
        value_candidates,
        closed_control_dags,
        residual_transfers: &residual_transfers,
    })?;
    let value_decisions = selected_value_decisions(
        proto,
        cfg,
        dataflow,
        &loops,
        &residual_transfers,
        value_candidates,
    );

    let branch_index = branches::BranchIndex::new(cfg, graph_facts, &loops);
    let branches = branches
        .into_iter()
        .map(|mut branch| {
            let condition = condition_by_header.get(&branch.header).copied();
            let condition_ref = condition.and_then(|id| conditions.get(id.index()));
            let frozen_region = branch_regions.remove(&branch.header);
            let boundary_changed = frozen_region
                .as_ref()
                .is_none_or(|region| region.single_pass_fence.is_none())
                && normalize_branch_condition_boundary(
                    cfg,
                    graph_facts,
                    &loops,
                    &branch_index,
                    &mut branch,
                    condition_ref,
                );
            let value_merge = branch
                .merge
                .and_then(|merge| branch_value_merges.remove(&(branch.header, merge)));
            let region = frozen_region
                .filter(|region| !boundary_changed || Some(region.merge) == branch.merge)
                .or_else(|| {
                    branch.merge.map(|merge| {
                        BranchRegionFact::new(graph_facts, branch.header, merge, branch.kind, None)
                    })
                });
            BranchPlanInput {
                region,
                condition,
                value_merge,
                branch,
            }
        })
        .collect();
    let loops = loops
        .into_iter()
        .map(|loop_| {
            let condition = required_loop_condition_header(cfg, &loop_)
                .and_then(|header| condition_by_header.get(&header).copied());
            let (continuation, private_exit_tail) = loop_continuation(
                proto,
                &loop_,
                condition.and_then(|id| conditions.get(id.index())),
                cfg,
                graph_facts,
                exit_block,
            );
            LoopPlanInput {
                condition,
                continuation,
                private_exit_tail,
                candidate: loop_,
                semantic_continue_edges: BTreeSet::new(),
            }
        })
        .collect();
    let unstructured = regions
        .into_iter()
        .map(|fact| UnstructuredPlanData { fact, layout: None })
        .collect();

    Ok(FinalPlanInput {
        branches,
        loops,
        conditions,
        value_decisions,
        scopes,
        unstructured,
        residual_transfers,
    })
}

pub(super) fn normalize_branch_condition_boundary(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    loops: &[LoopCandidate],
    branch_index: &branches::BranchIndex<'_>,
    branch: &mut BranchCandidate,
    condition: Option<&ConditionPlanInput>,
) -> bool {
    let Some(condition) = condition.filter(|condition| condition.candidate.nodes.len() > 1) else {
        return false;
    };
    let ShortCircuitExit::BranchExit { truthy, falsy } = condition.candidate.exit else {
        return false;
    };
    if let Some((then_entry, continuation)) =
        loop_guard_boundary(branch.header, truthy, falsy, loops)
    {
        branch.then_entry = then_entry;
        branch.else_entry = None;
        branch.merge = Some(continuation);
        branch.kind = BranchKind::Guard;
        branch.invert_hint = false;
        return true;
    }
    if let Some((then_entry, continuation)) = branch_endpoint_boundary(graph_facts, truthy, falsy) {
        branch.then_entry = then_entry;
        branch.else_entry = None;
        branch.merge = Some(continuation);
        branch.kind = BranchKind::Guard;
        branch.invert_hint = false;
        return true;
    }
    // 短路条件吸收了原合流块后，旧边界已经变成条件内部节点。
    // 重新消费既有 loop-exit/frontier 证明，保留 break 臂和本轮共享 tail 的归属；
    // 不能把共享 tail 留成跳出外层 if 的 residual goto。
    if branch
        .merge
        .is_some_and(|merge| condition.candidate.blocks.contains(&merge))
        && let Some(normalized) = branch_index.loop_exit_boundary(cfg, branch.header, truthy, falsy)
    {
        *branch = normalized;
        return true;
    }
    let Some(merge) = branches::find_soft_merge(cfg, graph_facts, branch.header, truthy, falsy)
    else {
        return false;
    };
    if merge == truthy
        || merge == falsy
        || condition.candidate.blocks.contains(&merge)
        || branch.merge.is_some_and(|current| {
            current != truthy && current != falsy && !graph_facts.dominates(merge, current)
        })
    {
        return false;
    }
    branch.then_entry = truthy;
    branch.else_entry = Some(falsy);
    branch.merge = Some(merge);
    branch.kind = BranchKind::IfElse;
    branch.invert_hint = false;
    true
}

pub(super) fn branch_endpoint_boundary(
    graph_facts: &GraphFacts,
    truthy: super::super::BlockRef,
    falsy: super::super::BlockRef,
) -> Option<(super::super::BlockRef, super::super::BlockRef)> {
    let truthy_joins_falsy = graph_facts
        .dominance_frontier
        .get(truthy.index())
        .is_some_and(|frontier| frontier.contains(&falsy));
    let falsy_joins_truthy = graph_facts
        .dominance_frontier
        .get(falsy.index())
        .is_some_and(|frontier| frontier.contains(&truthy));
    match (truthy_joins_falsy, falsy_joins_truthy) {
        (true, false) => Some((truthy, falsy)),
        (false, true) => Some((falsy, truthy)),
        (true, true) | (false, false) => None,
    }
}

pub(super) fn loop_guard_boundary(
    header: super::super::BlockRef,
    truthy: super::super::BlockRef,
    falsy: super::super::BlockRef,
    loops: &[LoopCandidate],
) -> Option<(super::super::BlockRef, super::super::BlockRef)> {
    loops
        .iter()
        .filter(|loop_| {
            loop_.condition_header != Some(header)
                && (loop_.kind_hint == super::super::LoopKindHint::RepeatLike
                    || loop_.header != header)
                && (loop_.blocks.contains(&header) || loop_.body_scope_blocks.contains(&header))
        })
        .filter_map(|loop_| {
            let is_iteration_boundary = |block| {
                block == loop_.header
                    || loop_.continue_target == Some(block)
                    || loop_.control_blocks.contains(&block)
            };
            match (is_iteration_boundary(truthy), is_iteration_boundary(falsy)) {
                (true, false) => Some((
                    (loop_.body_scope_blocks.len(), loop_.blocks.len()),
                    (falsy, truthy),
                )),
                (false, true) => Some((
                    (loop_.body_scope_blocks.len(), loop_.blocks.len()),
                    (truthy, falsy),
                )),
                (true, true) | (false, false) => None,
            }
        })
        .min_by_key(|(score, _)| *score)
        .map(|(_, boundary)| boundary)
}
