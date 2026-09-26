//! 枚举闭合 branch/loop 控制分量并形成 DAG 候选入口；依赖 CFG、支配与 branch 索引，不负责弧细化；例如合并共享 connector 的闭合分支分量。

use super::*;

/// 从 raw CFG decision headers 提取完整 control DAG。
///
/// 这条路径只为 short-circuit evidence 服务，不把 raw header 伪装成最终 branch。
/// connector 必须是唯一线性 successor、无副作用且定义不逃出候选；不可规约 SCC 中
/// 的 block 在入口即被排除。普通 branch 继续走既有 analyzer，raw roots 只来自可能
/// 消费 condition 的 loop owner。
///
/// 先按最小 loop domain 建立互不重叠的 dense owner，再为每条 decision edge 只计算一次
/// connector route；每个 decision、connector 和 edge 最多被登记常数次。复杂度为
/// `O(B + E + I + output_membership)`。
pub(in crate::structure::short_circuit) fn analyze_closed_control_dag_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    irreducible_regions: &[IrreducibleRegion],
    loops: &[LoopCandidate],
) -> Vec<ClosedControlDagEvidence> {
    let index = build_raw_condition_index(
        proto,
        cfg,
        graph_facts,
        dataflow,
        irreducible_regions,
        loops,
    );
    let mut workspace = DenseConditionWorkspace {
        raw: DenseMarks::new(cfg.blocks.len()),
        blocked: DenseMarks::new(cfg.blocks.len()),
        retained: DenseMarks::new(cfg.blocks.len()),
        node_refs: vec![None; cfg.blocks.len()],
    };
    let mut candidates = index
        .roots
        .iter()
        .copied()
        .filter(|root| !index.owner_conflicts[root.owner])
        .filter_map(|root| {
            build_closed_control_dag(cfg, graph_facts, dataflow, &index, root, &mut workspace)
        })
        .collect::<Vec<_>>();
    candidates.sort_by_key(|evidence| {
        (
            evidence.candidate.header,
            evidence.candidate.blocks.len(),
            evidence.candidate.nodes.len(),
        )
    });
    candidates
}

/// 把经单入口 connector 相连、最终只有两个源码 arm 的 branch component 冻结成条件 DAG。
///
/// 普通 branch 候选会把共享 continuation 的复合条件拆成多个同层 `if`。这里先排除
/// loop、不可规约区域和值 decision，再对剩余 branch 图做一次弱连通分量扫描；每个
/// block/edge 只登记一次。只有单入口、无环、恰好两个出口的分量才成为 evidence。
pub(in crate::structure::short_circuit) fn analyze_closed_branch_components(
    context: super::super::ClosedControlDagContext<'_>,
    irreducible_regions: &[IrreducibleRegion],
    loops: &[LoopCandidate],
    value_decision_blocks: &BTreeSet<BlockRef>,
) -> Vec<ClosedControlDagEvidence> {
    let super::super::ClosedControlDagContext {
        proto,
        cfg,
        graph_facts,
        dataflow,
        source_initializer_blocks,
    } = context;
    let mut blocked = vec![false; cfg.blocks.len()];
    for block in irreducible_regions
        .iter()
        .flat_map(|region| region.blocks.iter())
        .chain(value_decision_blocks)
    {
        blocked[block.index()] = true;
    }
    let mut loop_owner = vec![None; cfg.blocks.len()];
    let mut loop_order = (0..loops.len()).collect::<Vec<_>>();
    loop_order.sort_by_key(|index| {
        (
            loops[*index].body_scope_blocks.len(),
            loops[*index].blocks.len(),
            *index,
        )
    });
    for index in loop_order {
        for block in &loops[index].body_scope_blocks {
            if loop_owner[block.index()].is_none() {
                loop_owner[block.index()] = Some(index);
            }
        }
    }
    let mut loop_control = vec![false; cfg.blocks.len()];
    for candidate in loops {
        let has_distinct_branch_latch = candidate.backedges.iter().any(|edge| {
            cfg.edges.get(edge.index()).is_some_and(|edge| {
                edge.from != candidate.header && cfg.branch_edges(edge.from).is_some()
            })
        });
        if !matches!(
            candidate.kind_hint,
            crate::structure::LoopKindHint::WhileTrueLike | crate::structure::LoopKindHint::Unknown
        ) {
            for block in &candidate.control_blocks {
                loop_control[block.index()] = true;
            }
        }
        for block in candidate
            .condition_header
            .filter(|header| {
                *header != candidate.header
                    || !matches!(
                        candidate.kind_hint,
                        crate::structure::LoopKindHint::WhileTrueLike
                            | crate::structure::LoopKindHint::Unknown
                    )
            })
            .into_iter()
        {
            loop_control[block.index()] = true;
        }
        for edge in &candidate.backedges {
            let Some(mut cursor) = cfg.edges.get(edge.index()).map(|edge| edge.from) else {
                continue;
            };
            loop {
                loop_control[cursor.index()] = true;
                if cfg.branch_edges(cursor).is_some()
                    || !connector_block_is_safe(proto, cfg, dataflow, cursor)
                {
                    break;
                }
                let Some(predecessor) = cfg.unique_reachable_predecessor_matching(cursor, |_| true)
                else {
                    break;
                };
                cursor = predecessor;
            }
        }
        if matches!(
            candidate.kind_hint,
            crate::structure::LoopKindHint::NumericForLike
                | crate::structure::LoopKindHint::GenericForLike
        ) || candidate.kind_hint == crate::structure::LoopKindHint::WhileLike
            && !has_distinct_branch_latch
        {
            loop_control[candidate.header.index()] = true;
        }
    }
    let eligible = cfg
        .blocks
        .iter()
        .enumerate()
        .map(|(index, _)| {
            let block = BlockRef(index);
            cfg.reachable_blocks.contains(&block)
                && !blocked[index]
                && !loop_control[index]
                && cfg.branch_edges(block).is_some()
        })
        .collect::<Vec<_>>();
    let mut arcs_by_header = vec![None; cfg.blocks.len()];
    let mut neighbors = vec![Vec::new(); cfg.blocks.len()];
    for block in cfg
        .block_order
        .iter()
        .copied()
        .filter(|block| eligible[block.index()])
    {
        let Some((truthy, falsy)) = cfg.predicate_edges(&proto.instrs, block) else {
            continue;
        };
        let make_arc = |truthy: bool, edge: EdgeRef| {
            let mut target = cfg.edges[edge.index()].to;
            let mut edges = vec![edge];
            let mut connector_blocks = Vec::new();
            // 单前驱 connector 只属于一条 decision arc，遍历成本不随候选数量放大。
            // 共享判断则不能按前驱数量截断；完整分量仍需通过单入口、无环和两出口证明。
            while target != cfg.exit_block
                && !blocked[target.index()]
                && !loop_control[target.index()]
                && loop_owner[target.index()] == loop_owner[block.index()]
                && !eligible[target.index()]
                && reachable_predecessor_count(cfg, target) == 1
                && super::super::shared::block_is_passthrough(proto, cfg, target)
            {
                let [next] = cfg.succs[target.index()].as_slice() else {
                    break;
                };
                connector_blocks.push(target);
                edges.push(*next);
                target = cfg.edges[next.index()].to;
            }
            RawConditionArc {
                source: block,
                truthy,
                edges,
                connector_blocks,
                target: if eligible.get(target.index()).copied().unwrap_or(false)
                    // 声明属于新条件的入口，不能被前一个条件吞入同一分量。
                    // 在建连通分量前切边，入口之后的共享短路 DAG 才仍有独立候选。
                    && !source_initializer_blocks[target.index()]
                    && loop_owner[target.index()] == loop_owner[block.index()]
                    // 计数/迭代循环的 control 与 body 已有独立协议；body 内的共享
                    // 判断仍由完整 DAG 验证。while/repeat 的共享节点可能同时承担
                    // break 和尾条件，继续要求 loop owner 的专门边界证据。
                    && (loop_owner[target.index()].is_none()
                        || reachable_predecessor_count(cfg, target) == 1
                        || loop_owner[target.index()].is_some_and(|owner| matches!(loops[owner].kind_hint,
                            crate::structure::LoopKindHint::NumericForLike | crate::structure::LoopKindHint::GenericForLike)))
                {
                    RawConditionTarget::Node(target)
                } else {
                    RawConditionTarget::Exit(target)
                },
            }
        };
        let arcs = [make_arc(true, truthy), make_arc(false, falsy)];
        for arc in &arcs {
            if let RawConditionTarget::Node(target) = arc.target {
                neighbors[block.index()].push(target);
                neighbors[target.index()].push(block);
            }
        }
        arcs_by_header[block.index()] = Some(arcs);
    }

    let mut visited = vec![false; cfg.blocks.len()];
    let mut evidence = Vec::new();
    let mut indegree = vec![0usize; cfg.blocks.len()];
    for start in cfg.block_order.iter().copied() {
        if !eligible[start.index()] || visited[start.index()] {
            continue;
        }
        let mut headers = BTreeSet::new();
        let mut pending = vec![start];
        visited[start.index()] = true;
        while let Some(block) = pending.pop() {
            headers.insert(block);
            for next in &neighbors[block.index()] {
                if !visited[next.index()] {
                    visited[next.index()] = true;
                    pending.push(*next);
                }
            }
        }
        if headers.len() < 2 {
            continue;
        }
        for block in &headers {
            indegree[block.index()] = 0;
        }
        let mut raw_arcs = Vec::with_capacity(headers.len() * 2);
        let mut exits = BTreeSet::new();
        for block in &headers {
            let Some(arcs) = arcs_by_header[block.index()].as_ref() else {
                continue;
            };
            for arc in arcs {
                match arc.target {
                    RawConditionTarget::Node(target) => indegree[target.index()] += 1,
                    RawConditionTarget::Exit(exit) => {
                        exits.insert(exit);
                    }
                }
                raw_arcs.push(arc.clone());
            }
        }
        let mut roots = headers
            .iter()
            .copied()
            .filter(|block| indegree[block.index()] == 0);
        let Some(root) = roots.next() else { continue };
        // 多入口弱连通分量可由先前的取值区域或独立分支汇合而成。
        // 分割后的每段仍须独立通过 finalize 的单入口证明，不能整组丢弃。
        if roots.next().is_some() || exits.len() != 2 {
            evidence.extend(partition_condition_chain(
                cfg,
                graph_facts,
                dataflow,
                &headers,
                &arcs_by_header,
            ));
            continue;
        }
        let mut exits = exits.into_iter();
        let Some(first) = exits.next() else { continue };
        let Some(second) = exits.next() else { continue };
        let Some((truthy, falsy)) =
            classify_guard_branch_exits(cfg, &graph_facts.post_dominator_tree, first, second)
        else {
            continue;
        };
        if let Some(candidate) =
            finalize_closed_control_dag(cfg, dataflow, root, headers, raw_arcs, truthy, falsy)
        {
            evidence.push(candidate);
        }
    }
    evidence.sort_by_key(|candidate| candidate.candidate.header);
    evidence
}

/// 连续 elseif 的条件也是弱连通的，但每段拥有自己的两个出口。
/// 逆拓扑传播出口对；只有子段出口包含另一臂入口，或两子段出口相同，才吸收它。
/// 否则把该子段入口保留为边界。随后按相同出口对分组，完整单入口/边动作证明仍
/// 由 finalize 完成。每个节点和边只处理常数次，不为每个 header 重扫后缀。
fn partition_condition_chain(
    cfg: &Cfg,
    graph: &GraphFacts,
    dataflow: &DataflowFacts,
    headers: &BTreeSet<BlockRef>,
    arcs: &[Option<[RawConditionArc; 2]>],
) -> Vec<ClosedControlDagEvidence> {
    let mut indegrees = BTreeMap::new();
    for header in headers {
        indegrees.insert(*header, 0usize);
    }
    for header in headers {
        for arc in arcs[header.index()].as_ref().into_iter().flatten() {
            if let RawConditionTarget::Node(target) = arc.target {
                *indegrees.get_mut(&target).unwrap() += 1;
            }
        }
    }
    let mut pending = indegrees
        .iter()
        .filter_map(|(block, degree)| (*degree == 0).then_some(*block))
        .collect::<Vec<_>>();
    let mut order = Vec::with_capacity(headers.len());
    while let Some(block) = pending.pop() {
        order.push(block);
        for arc in arcs[block.index()].as_ref().into_iter().flatten() {
            if let RawConditionTarget::Node(target) = arc.target {
                let degree = indegrees.get_mut(&target).unwrap();
                *degree -= 1;
                if *degree == 0 {
                    pending.push(target);
                }
            }
        }
    }
    if order.len() != headers.len() {
        return Vec::new();
    }
    let mut pairs = BTreeMap::<BlockRef, [BlockRef; 2]>::new();
    let target = |arc: &RawConditionArc| match arc.target {
        RawConditionTarget::Node(block) | RawConditionTarget::Exit(block) => block,
    };
    for header in order.iter().rev() {
        let Some([left, right]) = arcs[header.index()].as_ref() else {
            continue;
        };
        let (left, right) = (target(left), target(right));
        let (a, b) = (pairs.get(&left), pairs.get(&right));
        let pair = if let Some(pair) = a.filter(|pair| Some(*pair) == b || pair.contains(&right)) {
            *pair
        } else if let Some(pair) = b.filter(|pair| pair.contains(&left)) {
            *pair
        } else if left != right {
            [left.min(right), left.max(right)]
        } else {
            continue;
        };
        pairs.insert(*header, pair);
    }
    let mut claimed = BTreeSet::new();
    let mut evidence = Vec::new();
    for root in order {
        if claimed.contains(&root) {
            continue;
        }
        let Some(&[first, second]) = pairs.get(&root) else {
            continue;
        };
        let mut nodes = BTreeSet::new();
        let mut raw = Vec::new();
        let mut pending = vec![root];
        while let Some(block) = pending.pop() {
            if !nodes.insert(block) {
                continue;
            }
            claimed.insert(block);
            for arc in arcs[block.index()].as_ref().into_iter().flatten() {
                let mut arc = arc.clone();
                let next = target(&arc);
                if next != first && next != second && pairs.get(&next) == Some(&[first, second]) {
                    arc.target = RawConditionTarget::Node(next);
                    pending.push(next);
                } else {
                    arc.target = RawConditionTarget::Exit(next);
                }
                raw.push(arc);
            }
        }
        if nodes.len() < 2 {
            continue;
        }
        let (truthy, falsy) = if graph.post_dominator_tree.dominates(first, second) {
            (second, first)
        } else {
            (first, second)
        };
        if let Some(candidate) =
            finalize_closed_control_dag(cfg, dataflow, root, nodes, raw, truthy, falsy)
        {
            evidence.push(candidate);
        }
    }
    evidence
}

/// 提取“条件路径与源码 body 共享入口”的普通 branch DAG。
///
/// 这类 CFG 的严格后支配点是整个 `if` 的 continuation，而条件为真时会先汇入一个
/// soft merge。若仍按每个物理 branch 分别建 region，同一个 body 会同时属于多条臂；
/// 这里先把 soft/strict merge 之间的纯 decision DAG 冻结成一个条件，再交给唯一的
/// outer branch owner。已接受候选的 decision block 不再作为后续 root，因而每个节点
/// 和 connector 只会进入一个最终 evidence。
pub(in crate::structure::short_circuit) fn analyze_closed_branch_control_dag_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    branches: &[BranchCandidate],
) -> Vec<ClosedControlDagEvidence> {
    struct Job {
        root: BlockRef,
        then_entry: BlockRef,
        else_entry: BlockRef,
        body: BlockRef,
        continuation: BlockRef,
        reaches_body: bool,
    }

    let mut jobs = Vec::new();
    let mut jobs_by_body = vec![Vec::new(); cfg.blocks.len()];
    for branch in branches {
        if branch.kind != BranchKind::IfElse {
            continue;
        }
        let (Some(continuation), Some(else_entry)) = (branch.merge, branch.else_entry) else {
            continue;
        };
        let Some(body) = super::super::super::branches::find_soft_merge(
            cfg,
            graph_facts,
            branch.header,
            branch.then_entry,
            else_entry,
        ) else {
            continue;
        };
        if body == continuation {
            continue;
        }
        let index = jobs.len();
        jobs.push(Job {
            root: branch.header,
            then_entry: branch.then_entry,
            else_entry,
            body,
            continuation,
            reaches_body: false,
        });
        let Some(group) = jobs_by_body.get_mut(body.index()) else {
            continue;
        };
        group.push(index);
    }
    let mut reachability = ReverseReachability::new(cfg);
    for (body_index, job_indexes) in jobs_by_body.into_iter().enumerate() {
        if job_indexes.is_empty() {
            continue;
        }
        let body = BlockRef(body_index);
        let epoch = reachability.mark_reaching(cfg, body);
        for index in job_indexes {
            let job = &mut jobs[index];
            job.reaches_body = reachability.reaches(job.then_entry, epoch)
                && reachability.reaches(job.else_entry, epoch);
        }
    }

    let mut claimed = vec![false; cfg.blocks.len()];
    let mut candidates = Vec::new();
    for job in jobs {
        if claimed[job.root.index()] || !job.reaches_body {
            continue;
        }
        let Some(evidence) = build_closed_branch_control_dag(
            proto,
            cfg,
            dataflow,
            job.root,
            job.body,
            job.continuation,
            &claimed,
        ) else {
            continue;
        };
        for node in &evidence.candidate.nodes {
            claimed[node.header.index()] = true;
        }
        candidates.push(evidence);
    }
    candidates
}
