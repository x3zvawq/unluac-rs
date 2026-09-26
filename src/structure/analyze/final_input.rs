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
    let value_decisions = selected_value_decisions(
        proto,
        cfg,
        dataflow,
        graph_facts,
        &loops,
        &residual_transfers,
        value_candidates,
    );
    let (conditions, condition_by_header) = selected_conditions(ConditionSelectionInput {
        proto,
        cfg,
        graph: graph_facts,
        dataflow,
        loops: &loops,
        caps,
        branches: &branches,
        candidates: condition_candidates,
        value_candidates,
        selected_values: &value_decisions,
        closed_control_dags,
        residual_transfers: &residual_transfers,
    })?;

    let branch_index = branches::BranchIndex::new(cfg, graph_facts, &loops);
    let mut value_owner = vec![None::<usize>; cfg.blocks.len()];
    for (index, value) in value_decisions.iter().enumerate() {
        for block in &value.candidate.blocks {
            if value_owner[block.index()].is_none_or(|current| {
                value_decisions[current].candidate.blocks.len() < value.candidate.blocks.len()
            }) {
                value_owner[block.index()] = Some(index);
            }
        }
    }
    let consumed_fences = branch_regions
        .values()
        .filter(|region| {
            let Some(fence) = &region.single_pass_fence else {
                return false;
            };
            // 值 DAG 可以接管整个 fence（包括内部取值操作数），不能同时给同一批
            // block 冻结 ValueDecision 和 SinglePass 两个 containment owner。
            value_owner[region.header.index()].is_some_and(|index| {
                let candidate = &value_decisions[index].candidate;
                candidate.blocks.contains(&region.merge)
                    && (candidate.blocks.contains(&fence.exit)
                        || candidate.exit == ShortCircuitExit::ValueMerge(fence.exit))
            }) || condition_consumes_single_pass(
                region,
                condition_by_header
                    .get(&region.header)
                    .and_then(|id| conditions.get(id.index())),
                &conditions,
                &condition_by_header,
                graph_facts,
                cfg,
                &branch_index,
            )
        })
        .map(|region| region.header)
        .collect::<BTreeSet<_>>();
    let mut branches_by_merge = BTreeMap::<_, Vec<_>>::new();
    for branch in &branches {
        if let Some(merge) = branch.merge {
            branches_by_merge
                .entry(merge)
                .or_default()
                .push(branch.header);
        }
    }
    let mut restored_merges = BTreeMap::new();
    // fence 消费是整个边界事务：早期为它收紧的子 branch 也回到原出口，
    // 否则会留下指向另一臂 tail 的过期 continuation。按 tail 索引分组，
    // 每个 tail 的唯一后继确定原出口，不逐 fence 扫描全部分支。
    for header in &consumed_fences {
        let region = &branch_regions[header];
        let exit = region.single_pass_fence.as_ref().unwrap().exit;
        if let Some(headers) = branches_by_merge.remove(&region.merge) {
            for header in headers {
                if graph_facts.dominates(region.header, header) {
                    restored_merges.insert(header, exit);
                }
            }
        }
    }
    let branches = branches
        .into_iter()
        .map(|mut branch| {
            let condition = condition_by_header.get(&branch.header).copied();
            let condition_ref = condition.and_then(|id| conditions.get(id.index()));
            let frozen_region = branch_regions.remove(&branch.header);
            let consumes_fence = consumed_fences.contains(&branch.header);
            let restored = restored_merges.get(&branch.header).copied();
            if let Some(merge) = restored {
                branch.merge = Some(merge);
            }
            // 普通单节点沿用 branch owner 已证明的循环/合流边界；只有已消费
            // 旧 fence 的单节点才需重算，否则会把 loop body 的首语句误当 continuation。
            let normalized = (consumes_fence
                || condition_ref.is_some_and(|condition| condition.candidate.nodes.len() > 1))
                && (consumes_fence
                    || frozen_region
                        .as_ref()
                        .is_none_or(|region| region.single_pass_fence.is_none()))
                && normalize_branch_condition_boundary(
                    cfg,
                    graph_facts,
                    &loops,
                    &branch_index,
                    &mut branch,
                    condition_ref,
                );
            // 宽常量池的 RK/LOADK 布局依赖发射顺序；双臂仍按原指令顺序排布。
            // 极性由最终 condition 出口重新匹配，不能用 truthy 端点替代源码 then。
            if proto.constants.len() >= 256
                && let Some(other) = branch.else_entry
                && cfg.blocks[other.index()].instrs.start
                    < cfg.blocks[branch.then_entry.index()].instrs.start
            {
                branch.else_entry = Some(branch.then_entry);
                branch.then_entry = other;
                branch.invert_hint = !branch.invert_hint;
            }
            let boundary_changed = restored.is_some() || normalized;
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

/// 已选条件接管 escape 或将 tail/escape 分入两臂后，重算普通 branch 边界；
/// 不让早期图形候选的 repeat 包装入口前缀，使出口后的定义落入假作用域。
fn condition_consumes_single_pass(
    region: &BranchRegionFact,
    condition: Option<&ConditionPlanInput>,
    conditions: &[ConditionPlanInput],
    by_header: &BTreeMap<super::super::BlockRef, ConditionPlanId>,
    graph: &GraphFacts,
    cfg: &Cfg,
    branch_index: &branches::BranchIndex<'_>,
) -> bool {
    let Some(fence) = &region.single_pass_fence else {
        return false;
    };
    let Some(condition) = condition else {
        return false;
    };
    let ShortCircuitExit::BranchExit { truthy, falsy } = condition.candidate.exit else {
        return false;
    };
    if condition.candidate.header != region.header {
        return false;
    }
    let opposite = if truthy == region.merge {
        Some(falsy)
    } else if falsy == region.merge {
        Some(truthy)
    } else {
        None
    };
    if let Some(opposite) = opposite
        && condition.candidate.nodes.len() > 1
        && cfg.unique_reachable_successor(region.merge) == Some(fence.exit)
        && branch_index.has_single_local_join(opposite, fence.exit)
        && fence.escape_edges.iter().all(|edge| {
            let edge = cfg.edges[edge.index()];
            edge.to == fence.exit && graph.dominates(opposite, edge.from)
        })
    {
        // 短路折叠后，原共享 tail 已成为完整的一臂，所有 escape 则由另一臂拥有。
        // 两臂的正常路径只在旧 fence 出口合流；提前 RETURN 保留原退出，不再需要
        // 包住条件前缀的单次循环。这里消费支配/唯一局部合流，而非只比较出口编号。
        return true;
    }
    let matches_exit = |truthy, falsy| {
        (truthy == region.merge && falsy == fence.exit)
            || (falsy == region.merge && truthy == fence.exit)
    };
    let nested = if matches_exit(truthy, falsy) {
        None
    } else {
        // 声明将外层 guard 与其短路 body 分开；两个已选条件共同拥有原出口，
        // 无须用单次循环包住声明。只消费直接子条件及其完整边证书，不猜共享 tail。
        if condition.candidate.nodes.len() != 1 {
            return false;
        }
        let body = if truthy == fence.exit {
            falsy
        } else if falsy == fence.exit {
            truthy
        } else {
            return false;
        };
        let Some(nested) = by_header
            .get(&body)
            .and_then(|id| conditions.get(id.index()))
        else {
            return false;
        };
        let ShortCircuitExit::BranchExit { truthy, falsy } = nested.candidate.exit else {
            return false;
        };
        if nested.candidate.nodes.len() < 2
            || !matches_exit(truthy, falsy)
            || !nested
                .candidate
                .blocks
                .iter()
                .all(|&block| region.domain.contains(graph, block))
        {
            return false;
        }
        Some(nested)
    };
    // 消费已通过 connector、escaping-def 和边动作验证的 arc，不重新猜测短路边。
    // 未被 DAG 认领的 break 仍属于 SinglePass，不能仅凭两个出口相同就去掉 fence。
    let edges = std::iter::once(condition)
        .chain(nested)
        .flat_map(|condition| &condition.arcs)
        .flat_map(|arc| arc.edges.iter().copied())
        .collect::<BTreeSet<_>>();
    fence.escape_edges.is_subset(&edges)
}

pub(super) fn normalize_branch_condition_boundary(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    loops: &[LoopCandidate],
    branch_index: &branches::BranchIndex<'_>,
    branch: &mut BranchCandidate,
    condition: Option<&ConditionPlanInput>,
) -> bool {
    // 声明边界可把已选 DAG 截成单节点；它的真实出口仍可能不同于早期
    // branch 的软合流点，不能因节点数为一而沿用旧 containment。
    let Some(condition) = condition else {
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
    if let Some((then_entry, continuation)) =
        branch_endpoint_boundary(graph_facts, branch_index, truthy, falsy)
    {
        branch.then_entry = then_entry;
        branch.else_entry = None;
        branch.merge = Some(continuation);
        branch.kind = BranchKind::Guard;
        branch.invert_hint = false;
        return true;
    }
    // 有 break 的臂同时汇入本轮 tail 和 loop exit，不满足单一局部 frontier。
    // 对短路条件的新端点重新消费 loop-exit 证明；即使旧 merge 未被条件吸收，
    // 也不能让旧边界把共享 tail 留成 residual goto。
    if let Some(normalized) = branch_index.loop_exit_boundary(cfg, branch.header, truthy, falsy) {
        *branch = normalized;
        return true;
    }
    // 已选条件可能吞掉原局部 join 的全部测试。一个端点仍由本分支支配，
    // 另一个则由外层 guard 的跳过路径共享时，后者才是词法 continuation；
    // 沿用旧 join 会把真正的 return 臂放到尾部，并迫使正常路径 goto 越过它。
    // 回到支配当前 header 的端点属于循环边界，已由上面的循环协议处理。
    let owned_then = graph_facts.dominates(branch.header, truthy);
    let owned_else = graph_facts.dominates(branch.header, falsy);
    if owned_then != owned_else {
        let (body, continuation) = if owned_then {
            (truthy, falsy)
        } else {
            (falsy, truthy)
        };
        if !graph_facts.dominates(continuation, branch.header) {
            branch.then_entry = body;
            branch.else_entry = None;
            branch.merge = Some(continuation);
            branch.kind = BranchKind::Guard;
            branch.invert_hint = false;
            return true;
        }
    }
    // 完整条件确定的两臂都只正常到达外层共享出口时，旧软 merge 可能只是
    // 条件的一个端点。用已索引的局部 frontier 恢复 IfElse；提前 RETURN 不参与合流。
    if owned_then
        && owned_else
        && let Some(merge) = branch_index.common_local_join(truthy, falsy)
        && !graph_facts.dominates(merge, branch.header)
    {
        branch.then_entry = truthy;
        branch.else_entry = Some(falsy);
        branch.merge = Some(merge);
        branch.kind = BranchKind::IfElse;
        branch.invert_hint = false;
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
    branch_index: &branches::BranchIndex<'_>,
    truthy: super::super::BlockRef,
    falsy: super::super::BlockRef,
) -> Option<(super::super::BlockRef, super::super::BlockRef)> {
    // 一条边汇入另一端点不代表整臂在此结束；内嵌值选择还可能绕过它，
    // 在更后的共同出口合流。复用原 branch 的单臂证明，避免吞入共享 tail。
    let truthy_joins_falsy = graph_facts.post_dominates(falsy, truthy)
        || branch_index.has_single_local_join(truthy, falsy);
    let falsy_joins_truthy = graph_facts.post_dominates(truthy, falsy)
        || branch_index.has_single_local_join(falsy, truthy);
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
