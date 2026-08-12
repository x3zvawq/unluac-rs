//! 这个文件负责“条件出口型”短路候选提取。
//!
//! 它解决的是 `if a and b then ... end`、`if a or b then ... end`，以及
//! `if a or b then ... else ... end` 这类最终直接流向“整体为真/整体为假”两个出口的
//! 形状。这里特意不碰 value merge，让“条件出口识别”和“值合流 DAG 提取”各自拥有
//! 单一职责。
//!
//! 它依赖 branch 候选、支配/后支配关系和共享线性跟随规则，只负责回答
//! “这一串判断是不是一个纯条件出口短路”；它不会越权去拆 phi，也不会替 value merge
//! 做值来源分类。
//!
//! 例子：
//! - `if a and b then return end` 会产出“整体真时流向 then、整体假时流向 fallthrough”的
//!   短路候选
//! - `if a or b then body() end` 会产出“整体真时进入 body、整体假时直接跳过”的候选
//!
//! `IfElse` 链的每个 root 都可能看到同一条长后缀，因此前缀选择只前向扫描一次：
//! 增量维护当前前缀的外部出口计数和严格真假出口约束，仍保留最长候选及其原始
//! strict-before-relaxed 优先级，最后才构造 nodes/blocks。

use std::collections::{BTreeMap, BTreeSet};

use crate::structure::{BlockRef, Cfg, DataflowFacts, EdgeRef, GraphFacts, PostDominatorTree};
use crate::transformer::{LowInstr, LoweredProto};

use super::super::common::{
    BranchCandidate, BranchKind, IrreducibleRegion, LoopCandidate, ShortCircuitCandidate,
    ShortCircuitExit, ShortCircuitNode, ShortCircuitNodeRef, ShortCircuitTarget,
};
use super::ReverseReachability;
use super::shared::{
    LinearFollowCtx, LinearFollowTarget, is_reducible_candidate, prefer_short_circuit_candidate,
    short_circuit_nodes_are_acyclic, truthy_falsy_targets,
};

/// raw CFG condition arc 的物理路径证据。
///
/// `source`/`target` 描述逻辑 decision DAG，`edges` 则保留两者之间实际执行的 CFG
/// 路径。connector 只能是无可观察副作用的单后继 block；后续 final plan 必须冻结并
/// 消费这条路径，不能只凭逻辑 target 跳过其中的 value action。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::structure) struct ConditionArcEvidence {
    pub(in crate::structure) source: ShortCircuitNodeRef,
    pub(in crate::structure) truthy: bool,
    pub(in crate::structure) edges: Vec<EdgeRef>,
    pub(in crate::structure) connector_blocks: Vec<BlockRef>,
    pub(in crate::structure) target: ShortCircuitTarget,
}

/// 不依赖最终 `BranchCandidate` 的 closed control DAG evidence。
///
/// 只有单入口、无环、恰好两个出口的完整候选会到达这里。`candidate.blocks` 同时包含
/// decision 与 connector blocks，`arcs` 保存每条逻辑边对应的物理 CFG route；raw
/// evidence 本身不会创建 branch owner。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::structure) struct ClosedControlDagEvidence {
    pub(in crate::structure) candidate: ShortCircuitCandidate,
    pub(in crate::structure) arcs: Vec<ConditionArcEvidence>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RawConditionArc {
    source: BlockRef,
    truthy: bool,
    edges: Vec<EdgeRef>,
    connector_blocks: Vec<BlockRef>,
    target: RawConditionTarget,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RawConditionTarget {
    Node(BlockRef),
    Exit(BlockRef),
}

#[derive(Debug, Clone, Copy)]
struct RawConditionRoot {
    owner: usize,
    header: BlockRef,
}

#[derive(Debug, Clone, Copy)]
struct ConnectorClaim {
    owner: usize,
}

struct RawConditionIndex {
    roots: Vec<RawConditionRoot>,
    owner_by_block: Vec<Option<usize>>,
    arcs_by_header: Vec<Option<[RawConditionArc; 2]>>,
    owner_conflicts: Vec<bool>,
}

struct DenseConditionWorkspace {
    raw: DenseMarks,
    blocked: DenseMarks,
    retained: DenseMarks,
    node_refs: Vec<Option<ShortCircuitNodeRef>>,
}

struct DenseMarks {
    values: Vec<u32>,
    next_epoch: u32,
}

struct DenseNodeRefs {
    epochs: Vec<u32>,
    refs: Vec<ShortCircuitNodeRef>,
    next_epoch: u32,
}

impl DenseMarks {
    fn new(len: usize) -> Self {
        Self {
            values: vec![0; len],
            next_epoch: 1,
        }
    }

    fn begin(&mut self) -> u32 {
        if self.next_epoch == u32::MAX {
            self.values.fill(0);
            self.next_epoch = 1;
        }
        let epoch = self.next_epoch;
        self.next_epoch += 1;
        epoch
    }

    fn insert(&mut self, block: BlockRef, epoch: u32) -> bool {
        let slot = &mut self.values[block.index()];
        if *slot == epoch {
            false
        } else {
            *slot = epoch;
            true
        }
    }

    fn contains(&self, block: BlockRef, epoch: u32) -> bool {
        self.values.get(block.index()).copied() == Some(epoch)
    }
}

impl DenseNodeRefs {
    fn new(len: usize) -> Self {
        Self {
            epochs: vec![0; len],
            refs: vec![ShortCircuitNodeRef(0); len],
            next_epoch: 1,
        }
    }

    fn begin(&mut self) -> u32 {
        if self.next_epoch == u32::MAX {
            self.epochs.fill(0);
            self.next_epoch = 1;
        }
        let epoch = self.next_epoch;
        self.next_epoch += 1;
        epoch
    }

    fn get(&self, block: BlockRef, epoch: u32) -> Option<ShortCircuitNodeRef> {
        (self.epochs.get(block.index()).copied() == Some(epoch)).then(|| self.refs[block.index()])
    }

    fn insert(&mut self, block: BlockRef, node_ref: ShortCircuitNodeRef, epoch: u32) {
        self.epochs[block.index()] = epoch;
        self.refs[block.index()] = node_ref;
    }
}

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
pub(super) fn analyze_closed_control_dag_candidates(
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

/// 把互相直连、最终只有两个源码 arm 的 branch component 冻结成一个条件 DAG。
///
/// 普通 branch 候选会把共享 continuation 的复合条件拆成多个同层 `if`。这里先排除
/// loop、不可规约区域和值 decision，再对剩余 branch 图做一次弱连通分量扫描；每个
/// block/edge 只登记一次。只有单入口、无环、恰好两个出口的分量才成为 evidence。
pub(super) fn analyze_closed_branch_components(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    irreducible_regions: &[IrreducibleRegion],
    loops: &[LoopCandidate],
    value_decision_blocks: &BTreeSet<BlockRef>,
) -> Vec<ClosedControlDagEvidence> {
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
        let Some((truthy, falsy)) = truthy_falsy_edges(proto, cfg, block) else {
            continue;
        };
        let make_arc = |truthy: bool, edge: EdgeRef| {
            let target = cfg.edges[edge.index()].to;
            RawConditionArc {
                source: block,
                truthy,
                edges: vec![edge],
                connector_blocks: Vec::new(),
                target: if eligible.get(target.index()).copied().unwrap_or(false)
                    && loop_owner[target.index()] == loop_owner[block.index()]
                    && reachable_predecessor_count(cfg, target) == 1
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
        if roots.next().is_some() || exits.len() != 2 {
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

/// 提取“条件路径与源码 body 共享入口”的普通 branch DAG。
///
/// 这类 CFG 的严格后支配点是整个 `if` 的 continuation，而条件为真时会先汇入一个
/// soft merge。若仍按每个物理 branch 分别建 region，同一个 body 会同时属于多条臂；
/// 这里先把 soft/strict merge 之间的纯 decision DAG 冻结成一个条件，再交给唯一的
/// outer branch owner。已接受候选的 decision block 不再作为后续 root，因而每个节点
/// 和 connector 只会进入一个最终 evidence。
pub(super) fn analyze_closed_branch_control_dag_candidates(
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
        let Some(body) = super::super::branches::find_soft_merge(
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

fn build_closed_branch_control_dag(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    root: BlockRef,
    truthy_exit: BlockRef,
    falsy_exit: BlockRef,
    claimed: &[bool],
) -> Option<ClosedControlDagEvidence> {
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    let mut raw_arcs = Vec::new();
    while let Some(header) = pending.pop() {
        if !seen.insert(header) {
            continue;
        }
        if header != root && claimed.get(header.index()).copied().unwrap_or(true) {
            return None;
        }
        let (truthy_edge, falsy_edge) = truthy_falsy_edges(proto, cfg, header)?;
        for (truthy, edge) in [(true, truthy_edge), (false, falsy_edge)] {
            let arc = follow_closed_branch_arc(
                proto,
                cfg,
                dataflow,
                header,
                truthy,
                edge,
                truthy_exit,
                falsy_exit,
            )?;
            if let RawConditionTarget::Node(target) = arc.target {
                pending.push(target);
            }
            raw_arcs.push(arc);
        }
    }
    finalize_closed_control_dag(cfg, dataflow, root, seen, raw_arcs, truthy_exit, falsy_exit)
}

fn finalize_closed_control_dag(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    root: BlockRef,
    headers: BTreeSet<BlockRef>,
    raw_arcs: Vec<RawConditionArc>,
    truthy_exit: BlockRef,
    falsy_exit: BlockRef,
) -> Option<ClosedControlDagEvidence> {
    if headers.len() < 2 {
        return None;
    }
    let mut blocks = headers.clone();
    for arc in &raw_arcs {
        blocks.extend(arc.connector_blocks.iter().copied());
    }
    let exits = raw_arcs
        .iter()
        .filter_map(|arc| match arc.target {
            RawConditionTarget::Exit(exit) => Some(exit),
            RawConditionTarget::Node(_) => None,
        })
        .collect::<BTreeSet<_>>();
    if exits != BTreeSet::from([truthy_exit, falsy_exit])
        || headers
            .iter()
            .copied()
            .filter(|header| *header != root)
            .any(|header| block_defs_escape(cfg, dataflow, header, &blocks))
        || !connector_defs_stay_inside(cfg, dataflow, &raw_arcs, &blocks)
        || !is_reducible_candidate(cfg, root, &blocks)
    {
        return None;
    }

    let mut headers = headers.into_iter().collect::<Vec<_>>();
    headers.retain(|header| *header != root);
    headers.insert(0, root);
    let refs = headers
        .iter()
        .copied()
        .enumerate()
        .map(|(index, header)| (header, ShortCircuitNodeRef(index)))
        .collect::<BTreeMap<_, _>>();
    let mut nodes = headers
        .iter()
        .copied()
        .enumerate()
        .map(|(index, header)| ShortCircuitNode {
            id: ShortCircuitNodeRef(index),
            header,
            truthy: ShortCircuitTarget::TruthyExit,
            falsy: ShortCircuitTarget::FalsyExit,
        })
        .collect::<Vec<_>>();
    let mut arcs = Vec::with_capacity(raw_arcs.len());
    for raw in raw_arcs {
        let source = refs[&raw.source];
        let target = match raw.target {
            RawConditionTarget::Node(header) => ShortCircuitTarget::Node(refs[&header]),
            RawConditionTarget::Exit(exit) if exit == truthy_exit => ShortCircuitTarget::TruthyExit,
            RawConditionTarget::Exit(exit) if exit == falsy_exit => ShortCircuitTarget::FalsyExit,
            RawConditionTarget::Exit(_) => return None,
        };
        let node = nodes.get_mut(source.index())?;
        if raw.truthy {
            node.truthy = target.clone();
        } else {
            node.falsy = target.clone();
        }
        arcs.push(ConditionArcEvidence {
            source,
            truthy: raw.truthy,
            edges: raw.edges,
            connector_blocks: raw.connector_blocks,
            target,
        });
    }
    let entry = ShortCircuitNodeRef(0);
    if !short_circuit_nodes_are_acyclic(&nodes, entry) {
        return None;
    }
    Some(ClosedControlDagEvidence {
        candidate: ShortCircuitCandidate {
            header: root,
            blocks,
            entry,
            nodes,
            exit: ShortCircuitExit::BranchExit {
                truthy: truthy_exit,
                falsy: falsy_exit,
            },
            result_reg: None,
            result_phi_id: None,
            entry_value: None,
            value_incomings: Vec::new(),
            reducible: true,
        },
        arcs,
    })
}

#[allow(clippy::too_many_arguments)]
fn follow_closed_branch_arc(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    source: BlockRef,
    truthy: bool,
    first_edge: EdgeRef,
    truthy_exit: BlockRef,
    falsy_exit: BlockRef,
) -> Option<RawConditionArc> {
    let mut edges = vec![first_edge];
    let mut connector_blocks = Vec::new();
    let mut target = cfg.edges.get(first_edge.index())?.to;
    loop {
        if target == truthy_exit || target == falsy_exit {
            break;
        }
        if cfg.branch_edges(target).is_some() {
            return Some(RawConditionArc {
                source,
                truthy,
                edges,
                connector_blocks,
                target: RawConditionTarget::Node(target),
            });
        }
        if reachable_predecessor_count(cfg, target) != 1
            || !connector_block_is_safe(proto, cfg, dataflow, target)
        {
            return None;
        }
        let [next] = cfg.succs[target.index()].as_slice() else {
            return None;
        };
        connector_blocks.push(target);
        edges.push(*next);
        target = cfg.edges[next.index()].to;
    }
    Some(RawConditionArc {
        source,
        truthy,
        edges,
        connector_blocks,
        target: RawConditionTarget::Exit(target),
    })
}

fn build_raw_condition_index(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    irreducible_regions: &[IrreducibleRegion],
    loops: &[LoopCandidate],
) -> RawConditionIndex {
    let mut selected_by_header = vec![None::<usize>; cfg.blocks.len()];
    for (index, candidate) in loops.iter().enumerate() {
        let header = closed_control_root(cfg, graph_facts, candidate);
        if header.index() >= cfg.blocks.len()
            || !cfg.reachable_blocks.contains(&header)
            || cfg.branch_edges(header).is_none()
        {
            continue;
        }
        let slot = &mut selected_by_header[header.index()];
        let replace = slot.is_none_or(|current| {
            (candidate.blocks.len(), index) < (loops[current].blocks.len(), current)
        });
        if replace {
            *slot = Some(index);
        }
    }
    let mut selected = selected_by_header.into_iter().flatten().collect::<Vec<_>>();
    selected.sort_by_key(|index| {
        let candidate = &loops[*index];
        (
            candidate.blocks.len(),
            closed_control_root(cfg, graph_facts, candidate),
        )
    });

    let mut roots = Vec::with_capacity(selected.len());
    let mut loop_headers = Vec::with_capacity(selected.len());
    let mut owner_by_block = vec![None; cfg.blocks.len()];
    let mut owner_conflicts = Vec::with_capacity(selected.len());
    for index in selected {
        let candidate = &loops[index];
        let header = closed_control_root(cfg, graph_facts, candidate);
        let owner = roots.len();
        for block in candidate.blocks.iter().copied() {
            if let Some(slot) = owner_by_block.get_mut(block.index())
                && slot.is_none()
            {
                *slot = Some(owner);
            }
        }
        if owner_by_block[header.index()].is_none() {
            owner_by_block[header.index()] = Some(owner);
        }
        owner_conflicts.push(owner_by_block[header.index()] != Some(owner));
        roots.push(RawConditionRoot { owner, header });
        loop_headers.push(candidate.header);
    }

    let mut irreducible = vec![false; cfg.blocks.len()];
    for block in irreducible_regions
        .iter()
        .flat_map(|region| region.blocks.iter().copied())
    {
        irreducible[block.index()] = true;
    }
    let mut decision = vec![false; cfg.blocks.len()];
    for header in cfg.block_order.iter().copied() {
        decision[header.index()] = cfg.reachable_blocks.contains(&header)
            && !irreducible[header.index()]
            && owner_by_block[header.index()].is_some()
            && cfg.branch_edges(header).is_some();
    }

    let root_by_owner = roots.iter().map(|root| root.header).collect::<Vec<_>>();
    let mut connector_claims = vec![None::<ConnectorClaim>; cfg.blocks.len()];
    let mut arcs_by_header = vec![None; cfg.blocks.len()];
    for header in cfg.block_order.iter().copied() {
        if !decision[header.index()] {
            continue;
        }
        let Some(owner) = owner_by_block[header.index()] else {
            continue;
        };
        let Some((truthy_edge, falsy_edge)) = truthy_falsy_edges(proto, cfg, header) else {
            owner_conflicts[owner] = true;
            continue;
        };
        let truthy = follow_indexed_condition_arc(
            proto,
            cfg,
            dataflow,
            &owner_by_block,
            &decision,
            &root_by_owner,
            &loop_headers,
            &mut connector_claims,
            &mut owner_conflicts,
            owner,
            header,
            true,
            truthy_edge,
        );
        let falsy = follow_indexed_condition_arc(
            proto,
            cfg,
            dataflow,
            &owner_by_block,
            &decision,
            &root_by_owner,
            &loop_headers,
            &mut connector_claims,
            &mut owner_conflicts,
            owner,
            header,
            false,
            falsy_edge,
        );
        if let (Some(truthy), Some(falsy)) = (truthy, falsy) {
            arcs_by_header[header.index()] = Some([truthy, falsy]);
        } else {
            owner_conflicts[owner] = true;
        }
    }

    RawConditionIndex {
        roots,
        owner_by_block,
        arcs_by_header,
        owner_conflicts,
    }
}

fn closed_control_root(cfg: &Cfg, graph_facts: &GraphFacts, candidate: &LoopCandidate) -> BlockRef {
    let declared = candidate.condition_header.unwrap_or(candidate.header);
    if declared != candidate.header || candidate.backedges.len() < 2 {
        return declared;
    }
    let mut sources = candidate
        .backedges
        .iter()
        .filter_map(|edge| cfg.edges.get(edge.index()).map(|edge| edge.from));
    let Some(first) = sources.next() else {
        return declared;
    };
    let Some(common) = sources.try_fold(first, |common, source| {
        graph_facts
            .dominator_tree
            .nearest_common_ancestor(common, source)
    }) else {
        return declared;
    };
    if common != candidate.header && cfg.branch_edges(common).is_some() {
        common
    } else {
        declared
    }
}

#[allow(clippy::too_many_arguments)]
fn follow_indexed_condition_arc(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    owner_by_block: &[Option<usize>],
    decision: &[bool],
    root_by_owner: &[BlockRef],
    loop_header_by_owner: &[BlockRef],
    connector_claims: &mut [Option<ConnectorClaim>],
    owner_conflicts: &mut [bool],
    owner: usize,
    source: BlockRef,
    truthy: bool,
    first_edge: EdgeRef,
) -> Option<RawConditionArc> {
    let mut edges = vec![first_edge];
    let mut connector_blocks = Vec::new();
    let mut target = cfg.edges.get(first_edge.index())?.to;

    loop {
        if target == cfg.exit_block
            || owner_by_block.get(target.index()).copied().flatten() != Some(owner)
        {
            break;
        }
        if decision[target.index()] {
            let target = if target == root_by_owner[owner] || target == loop_header_by_owner[owner]
            {
                RawConditionTarget::Exit(target)
            } else {
                RawConditionTarget::Node(target)
            };
            return Some(RawConditionArc {
                source,
                truthy,
                edges,
                connector_blocks,
                target,
            });
        }
        if reachable_predecessor_count(cfg, target) != 1
            || !connector_block_is_safe(proto, cfg, dataflow, target)
        {
            break;
        }
        if let Some(claim) = connector_claims[target.index()] {
            owner_conflicts[owner] = true;
            owner_conflicts[claim.owner] = true;
            return None;
        }
        connector_claims[target.index()] = Some(ConnectorClaim { owner });
        let [next_edge] = cfg.succs[target.index()].as_slice() else {
            break;
        };
        connector_blocks.push(target);
        edges.push(*next_edge);
        target = cfg.edges[next_edge.index()].to;
    }

    Some(RawConditionArc {
        source,
        truthy,
        edges,
        connector_blocks,
        target: RawConditionTarget::Exit(target),
    })
}

fn build_closed_control_dag(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    index: &RawConditionIndex,
    root: RawConditionRoot,
    workspace: &mut DenseConditionWorkspace,
) -> Option<ClosedControlDagEvidence> {
    if index.owner_by_block[root.header.index()] != Some(root.owner) {
        return None;
    }
    let raw_epoch = workspace.raw.begin();
    let mut pending = vec![root.header];
    let mut raw_nodes = Vec::new();
    let mut raw_blocks = BTreeSet::new();

    while let Some(header) = pending.pop() {
        if !workspace.raw.insert(header, raw_epoch) {
            continue;
        }
        if index.owner_by_block[header.index()] != Some(root.owner) {
            return None;
        }
        raw_nodes.push(header);
        raw_blocks.insert(header);
        let arcs = index.arcs_by_header[header.index()].as_ref()?;
        for arc in arcs {
            raw_blocks.extend(arc.connector_blocks.iter().copied());
            if let RawConditionTarget::Node(next) = arc.target {
                pending.push(next);
            }
        }
    }

    // decision prefix 若把定义带到候选外，它已经属于 body/continuation，而不是条件。
    // 把该 decision 当作边界，再从 root 重建可达子图，避免吸收 loop body 的首个判断。
    let blocked_epoch = workspace.blocked.begin();
    for header in raw_nodes
        .iter()
        .copied()
        .filter(|header| *header != root.header)
    {
        if block_defs_escape(cfg, dataflow, header, &raw_blocks) {
            workspace.blocked.insert(header, blocked_epoch);
        }
    }
    let retained_epoch = workspace.retained.begin();
    let mut pending = vec![root.header];
    let mut node_headers = Vec::new();
    let mut raw_arcs = Vec::new();
    while let Some(header) = pending.pop() {
        if !workspace.retained.insert(header, retained_epoch) {
            continue;
        }
        node_headers.push(header);
        for raw in index.arcs_by_header[header.index()].as_ref()? {
            let mut arc = raw.clone();
            if let RawConditionTarget::Node(target) = arc.target {
                if workspace.blocked.contains(target, blocked_epoch) {
                    arc.target = RawConditionTarget::Exit(target);
                } else {
                    pending.push(target);
                }
            }
            raw_arcs.push(arc);
        }
    }
    if node_headers.len() < 2 {
        return None;
    }

    let mut blocks = node_headers.iter().copied().collect::<BTreeSet<_>>();
    for arc in &raw_arcs {
        blocks.extend(arc.connector_blocks.iter().copied());
    }
    if !connector_defs_stay_inside(cfg, dataflow, &raw_arcs, &blocks)
        || !is_reducible_candidate(cfg, root.header, &blocks)
    {
        return None;
    }

    let mut exits = raw_arcs.iter().filter_map(|arc| match arc.target {
        RawConditionTarget::Exit(exit) => Some(exit),
        RawConditionTarget::Node(_) => None,
    });
    let first_exit = exits.next()?;
    let second_exit = exits.find(|exit| *exit != first_exit)?;
    if exits.any(|exit| exit != first_exit && exit != second_exit) {
        return None;
    }
    let (truthy_exit, falsy_exit) = classify_guard_branch_exits(
        cfg,
        &graph_facts.post_dominator_tree,
        first_exit,
        second_exit,
    )?;

    node_headers.sort();
    node_headers.retain(|header| *header != root.header);
    node_headers.insert(0, root.header);
    for (position, header) in node_headers.iter().copied().enumerate() {
        workspace.node_refs[header.index()] = Some(ShortCircuitNodeRef(position));
    }
    let entry = ShortCircuitNodeRef(0);
    let mut nodes = node_headers
        .iter()
        .copied()
        .enumerate()
        .map(|(index, header)| ShortCircuitNode {
            id: ShortCircuitNodeRef(index),
            header,
            truthy: ShortCircuitTarget::TruthyExit,
            falsy: ShortCircuitTarget::FalsyExit,
        })
        .collect::<Vec<_>>();
    let mut arcs = Vec::with_capacity(raw_arcs.len());
    for raw in raw_arcs {
        let source = workspace.node_refs[raw.source.index()]?;
        let target = match raw.target {
            RawConditionTarget::Node(header) => {
                ShortCircuitTarget::Node(workspace.node_refs[header.index()]?)
            }
            RawConditionTarget::Exit(exit) if exit == truthy_exit => ShortCircuitTarget::TruthyExit,
            RawConditionTarget::Exit(exit) if exit == falsy_exit => ShortCircuitTarget::FalsyExit,
            RawConditionTarget::Exit(_) => return None,
        };
        let node = nodes.get_mut(source.index())?;
        if raw.truthy {
            node.truthy = target.clone();
        } else {
            node.falsy = target.clone();
        }
        arcs.push(ConditionArcEvidence {
            source,
            truthy: raw.truthy,
            edges: raw.edges,
            connector_blocks: raw.connector_blocks,
            target,
        });
    }
    if !short_circuit_nodes_are_acyclic(&nodes, entry) {
        return None;
    }

    Some(ClosedControlDagEvidence {
        candidate: ShortCircuitCandidate {
            header: root.header,
            blocks,
            entry,
            nodes,
            exit: ShortCircuitExit::BranchExit {
                truthy: truthy_exit,
                falsy: falsy_exit,
            },
            result_reg: None,
            result_phi_id: None,
            entry_value: None,
            value_incomings: Vec::new(),
            reducible: true,
        },
        arcs,
    })
}

fn truthy_falsy_edges(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: BlockRef,
) -> Option<(EdgeRef, EdgeRef)> {
    let (then_edge, else_edge) = cfg.branch_edges(header)?;
    match cfg.terminator(&proto.instrs, header) {
        Some(LowInstr::Branch(branch)) if branch.cond.negated => Some((else_edge, then_edge)),
        Some(LowInstr::Branch(_)) => Some((then_edge, else_edge)),
        _ => None,
    }
}

fn connector_block_is_safe(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    block: BlockRef,
) -> bool {
    let [edge] = cfg.succs[block.index()].as_slice() else {
        return false;
    };
    let range = cfg.blocks[block.index()].instrs;
    if cfg.edges[edge.index()].to == block {
        return false;
    }
    (range.start.index()..range.end()).all(|index| {
        let Some(instr) = proto.instrs.get(index) else {
            return false;
        };
        if instr.is_control_terminator() && index + 1 != range.end() {
            return false;
        }
        dataflow
            .effect_summaries
            .get(index)
            .is_some_and(|summary| summary.tags.is_empty())
    })
}

fn block_defs_escape(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    block: BlockRef,
    allowed_blocks: &BTreeSet<BlockRef>,
) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    (range.start.index()..range.end()).any(|instr| {
        dataflow.instr_defs[instr]
            .iter()
            .copied()
            .any(|def| dataflow.def_has_use_outside(cfg, def, allowed_blocks))
    })
}

fn connector_defs_stay_inside(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    arcs: &[RawConditionArc],
    allowed_blocks: &BTreeSet<BlockRef>,
) -> bool {
    arcs.iter()
        .flat_map(|arc| arc.connector_blocks.iter().copied())
        .all(|block| !block_defs_escape(cfg, dataflow, block, allowed_blocks))
}

fn reachable_predecessor_count(cfg: &Cfg, block: BlockRef) -> usize {
    cfg.preds[block.index()]
        .iter()
        .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
        .take(2)
        .count()
}

pub(super) fn analyze_guard_branch_exit_dag_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    branch_candidates: &[BranchCandidate],
    closed_linear_interiors: &BTreeSet<BlockRef>,
    value_decision_headers: &BTreeSet<BlockRef>,
) -> Vec<ShortCircuitCandidate> {
    let mut best_by_header = BTreeMap::<BlockRef, ShortCircuitCandidate>::new();
    let mut node_refs = DenseNodeRefs::new(cfg.blocks.len());
    let context = GuardBranchExitDagContext {
        proto,
        cfg,
        graph_facts,
        branch_by_header,
        value_decision_headers,
    };

    for root in branch_candidates {
        if closed_linear_interiors.contains(&root.header) {
            continue;
        }
        let candidate =
            GuardBranchExitDagBuilder::new(&context, root.header, true, &mut node_refs).build();
        let candidate = match candidate {
            Some(candidate) => Some(candidate),
            None => {
                GuardBranchExitDagBuilder::new(&context, root.header, false, &mut node_refs).build()
            }
        };
        let Some(candidate) = candidate else {
            continue;
        };

        match best_by_header.get(&root.header) {
            Some(existing) if !prefer_short_circuit_candidate(proto, cfg, &candidate, existing) => {
            }
            _ => {
                best_by_header.insert(root.header, candidate);
            }
        }
    }

    best_by_header.into_values().collect()
}

pub(super) fn analyze_linear_branch_exit_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    branch_candidates: &[BranchCandidate],
) -> Vec<ShortCircuitCandidate> {
    let chains =
        LinearChainIndex::branch_then(cfg.blocks.len(), branch_by_header, branch_candidates);
    analyze_linear_branch_exit_candidates_with(
        proto,
        cfg,
        branch_by_header,
        branch_candidates,
        &chains,
    )
}

pub(super) fn analyze_cfg_linear_branch_exit_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    branch_candidates: &[BranchCandidate],
) -> Vec<ShortCircuitCandidate> {
    let chains = LinearChainIndex::cfg(proto, cfg, branch_by_header, branch_candidates);
    analyze_linear_branch_exit_candidates_with(
        proto,
        cfg,
        branch_by_header,
        branch_candidates,
        &chains,
    )
}

fn analyze_linear_branch_exit_candidates_with(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    branch_candidates: &[BranchCandidate],
    chains: &LinearChainIndex,
) -> Vec<ShortCircuitCandidate> {
    let mut candidates = Vec::new();
    let mut closed_linear_interiors = BTreeSet::new();
    let mut visited = DenseMarks::new(cfg.blocks.len());
    for candidate in branch_candidates {
        if candidate.kind != BranchKind::IfThen
            || closed_linear_interiors.contains(&candidate.header)
        {
            continue;
        }

        let visited_epoch = visited.begin();
        let mut headers = Vec::new();
        let mut current = candidate.header;

        loop {
            if !visited.insert(current, visited_epoch) {
                break;
            }
            headers.push(current);

            let Some(next) = chains.next(current, &visited, visited_epoch) else {
                break;
            };
            current = next;
        }

        // If the full chain fails at `infer_linear_branch_exit`, the last block
        // might be a body block mistakenly included because it is also a branch
        // candidate. Detect this by checking whether every preceding header has
        // the last header as one of its truthy/falsy targets (i.e. it is the
        // common short-circuit exit). Only trim in that case to avoid producing
        // spurious candidates elsewhere.
        let mut exit = infer_linear_branch_exit(proto, cfg, &headers);
        if exit.is_none() && headers.len() >= 3 {
            let Some(last) = headers.last().copied() else {
                continue;
            };
            let is_common_exit = headers[..headers.len() - 1].iter().all(|h| {
                truthy_falsy_targets(proto, cfg, *h).is_some_and(|(t, f)| t == last || f == last)
            });
            if is_common_exit {
                headers.pop();
                exit = infer_linear_branch_exit(proto, cfg, &headers);
            }
        }
        // `a or b` 沿 falsy 边进入下一判断；其 truthy body 若也以 branch 开头，
        // 线性跟随会越过条件链。AND 链可由嵌套 if 自然表达，不在证据不足时扩候选。
        if exit.is_none()
            && headers
                .first()
                .zip(headers.get(1))
                .is_some_and(|(header, next)| {
                    truthy_falsy_targets(proto, cfg, *header)
                        .is_some_and(|(_, falsy)| falsy == *next)
                })
            && let Some((prefix_len, prefix_exit)) =
                infer_longest_linear_branch_exit(proto, cfg, &headers)
        {
            headers.truncate(prefix_len);
            exit = Some(prefix_exit);
        }
        let Some(exit) = exit else {
            continue;
        };
        let Some(nodes) = build_linear_branch_exit_nodes(proto, cfg, &headers, &exit) else {
            continue;
        };

        let blocks = headers.iter().copied().collect::<BTreeSet<_>>();
        let reducible = is_reducible_candidate(cfg, candidate.header, &blocks);
        let candidate = ShortCircuitCandidate {
            header: candidate.header,
            blocks,
            entry: ShortCircuitNodeRef(0),
            nodes,
            exit,
            result_reg: None,
            result_phi_id: None,
            entry_value: None,
            value_incomings: Vec::new(),
            reducible,
        };
        if candidate.reducible
            && let Some(interiors) =
                closed_single_entry_linear_interiors(cfg, branch_by_header, &candidate)
        {
            closed_linear_interiors.extend(interiors);
        }
        candidates.push(candidate);
    }

    candidates.sort_by_key(|candidate| candidate.header);
    candidates.dedup_by(|left, right| {
        left.header == right.header
            && left.exit == right.exit
            && left.blocks == right.blocks
            && left.nodes == right.nodes
    });
    candidates
}

pub(super) fn closed_linear_interior_headers(
    cfg: &Cfg,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    candidates: &[ShortCircuitCandidate],
) -> BTreeSet<BlockRef> {
    candidates
        .iter()
        .filter(|candidate| candidate.reducible)
        .filter_map(|candidate| {
            closed_single_entry_linear_interiors(cfg, branch_by_header, candidate)
        })
        .flatten()
        .collect()
}

fn closed_single_entry_linear_interiors(
    cfg: &Cfg,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    candidate: &ShortCircuitCandidate,
) -> Option<Vec<BlockRef>> {
    let ShortCircuitExit::BranchExit { truthy, falsy } = candidate.exit else {
        return None;
    };
    if branch_by_header.contains_key(&truthy) || branch_by_header.contains_key(&falsy) {
        return None;
    }

    let interiors = candidate
        .blocks
        .iter()
        .copied()
        .filter(|block| *block != candidate.header)
        .collect::<Vec<_>>();
    interiors
        .iter()
        .all(|block| cfg.reachable_predecessors(*block).len() == 1)
        .then_some(interiors)
}

pub(super) fn analyze_if_else_branch_exit_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    branch_candidates: &[BranchCandidate],
) -> Vec<ShortCircuitCandidate> {
    let mut candidates = Vec::new();
    let mut visited = DenseMarks::new(cfg.blocks.len());
    let chains = LinearChainIndex::cfg(proto, cfg, branch_by_header, branch_candidates);

    for candidate in branch_candidates {
        if candidate.kind != BranchKind::IfElse {
            continue;
        }

        let headers = collect_if_else_branch_exit_chain(candidate, &chains, &mut visited);
        if headers.len() < 2 {
            continue;
        }

        let Some((prefix_len, exit)) = infer_longest_if_else_branch_exit(proto, cfg, &headers)
        else {
            continue;
        };
        let prefix = &headers[..prefix_len];
        let Some(nodes) = build_linear_branch_exit_nodes(proto, cfg, prefix, &exit) else {
            continue;
        };
        let blocks = prefix.iter().copied().collect::<BTreeSet<_>>();
        let reducible = is_reducible_candidate(cfg, candidate.header, &blocks);
        candidates.push(ShortCircuitCandidate {
            header: candidate.header,
            blocks,
            entry: ShortCircuitNodeRef(0),
            nodes,
            exit,
            result_reg: None,
            result_phi_id: None,
            entry_value: None,
            value_incomings: Vec::new(),
            reducible,
        });
    }

    candidates.sort_by_key(|candidate| candidate.header);
    candidates.dedup_by(|left, right| {
        left.header == right.header
            && left.exit == right.exit
            && left.blocks == right.blocks
            && left.nodes == right.nodes
    });
    candidates
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct GuardExitTempNode {
    id: ShortCircuitNodeRef,
    header: BlockRef,
    truthy: GuardExitTempTarget,
    falsy: GuardExitTempTarget,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum GuardExitTempTarget {
    Node(ShortCircuitNodeRef),
    Exit(BlockRef),
}

struct GuardBranchExitDagContext<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    graph_facts: &'a GraphFacts,
    branch_by_header: &'a BTreeMap<BlockRef, &'a BranchCandidate>,
    value_decision_headers: &'a BTreeSet<BlockRef>,
}

struct GuardBranchExitDagBuilder<'a, 'w> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    branch_by_header: &'a BTreeMap<BlockRef, &'a BranchCandidate>,
    dom_tree: &'a crate::structure::DominatorTree,
    post_dom_tree: &'a PostDominatorTree,
    root: BlockRef,
    allow_shared_headers: bool,
    value_decision_headers: &'a BTreeSet<BlockRef>,
    included_shared_header: bool,
    nodes: Vec<GuardExitTempNode>,
    branch_targets: Vec<(BlockRef, BlockRef)>,
    node_refs: &'w mut DenseNodeRefs,
    node_epoch: u32,
    blocks: BTreeSet<BlockRef>,
    exits: BTreeSet<BlockRef>,
}

impl<'a, 'w> GuardBranchExitDagBuilder<'a, 'w> {
    fn new(
        context: &GuardBranchExitDagContext<'a>,
        root: BlockRef,
        allow_shared_headers: bool,
        node_refs: &'w mut DenseNodeRefs,
    ) -> Self {
        let node_epoch = node_refs.begin();
        Self {
            proto: context.proto,
            cfg: context.cfg,
            branch_by_header: context.branch_by_header,
            dom_tree: &context.graph_facts.dominator_tree,
            post_dom_tree: &context.graph_facts.post_dominator_tree,
            root,
            allow_shared_headers,
            value_decision_headers: context.value_decision_headers,
            included_shared_header: false,
            nodes: Vec::new(),
            branch_targets: Vec::new(),
            node_refs,
            node_epoch,
            blocks: BTreeSet::new(),
            exits: BTreeSet::new(),
        }
    }

    fn build(mut self) -> Option<ShortCircuitCandidate> {
        let _root_candidate = *self.branch_by_header.get(&self.root)?;

        let entry = self.build_nodes()?;
        if entry != ShortCircuitNodeRef(0) || self.nodes.len() < 2 || self.exits.len() != 2 {
            return None;
        }
        if self.included_shared_header
            && !self
                .exits
                .iter()
                .any(|exit| *exit != self.root && self.dom_tree.dominates(self.root, *exit))
        {
            return None;
        }

        let mut exits = self.exits.iter().copied().collect::<Vec<_>>();
        exits.sort();
        let [first_exit, second_exit] = exits.as_slice() else {
            return None;
        };
        let (truthy_exit, falsy_exit) =
            classify_guard_branch_exits(self.cfg, self.post_dom_tree, *first_exit, *second_exit)?;

        let nodes = self
            .nodes
            .into_iter()
            .map(|node| {
                Some(ShortCircuitNode {
                    id: node.id,
                    header: node.header,
                    truthy: finalize_guard_exit_target(node.truthy, truthy_exit, falsy_exit)?,
                    falsy: finalize_guard_exit_target(node.falsy, truthy_exit, falsy_exit)?,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        if !short_circuit_nodes_are_acyclic(&nodes, entry) {
            return None;
        }

        let reducible = is_reducible_candidate(self.cfg, self.root, &self.blocks);
        // 共享节点的前驱数不能替代区域入口校验；扩展后的 DAG 必须仍由 root
        // 单入口控制。普通保守候选继续保留 reducible 事实交给既有消费者判断。
        if self.included_shared_header && !reducible {
            return None;
        }
        Some(ShortCircuitCandidate {
            header: self.root,
            blocks: self.blocks,
            entry,
            nodes,
            exit: ShortCircuitExit::BranchExit {
                truthy: truthy_exit,
                falsy: falsy_exit,
            },
            result_reg: None,
            result_phi_id: None,
            entry_value: None,
            value_incomings: Vec::new(),
            reducible,
        })
    }

    fn reserve_node(&mut self, header: BlockRef) -> Option<(ShortCircuitNodeRef, bool)> {
        if let Some(node_ref) = self.node_refs.get(header, self.node_epoch) {
            return Some((node_ref, false));
        }
        if !self.should_include_header(header) {
            return None;
        }

        let (truthy_block, falsy_block) = truthy_falsy_targets(self.proto, self.cfg, header)?;
        let id = ShortCircuitNodeRef(self.nodes.len());
        self.node_refs.insert(header, id, self.node_epoch);
        self.blocks.insert(header);
        self.nodes.push(GuardExitTempNode {
            id,
            header,
            truthy: GuardExitTempTarget::Exit(header),
            falsy: GuardExitTempTarget::Exit(header),
        });
        self.branch_targets.push((truthy_block, falsy_block));

        Some((id, true))
    }

    fn build_nodes(&mut self) -> Option<ShortCircuitNodeRef> {
        let (entry, _) = self.reserve_node(self.root)?;
        // CFG 深度来自用户输入，不能用 Rust 递归栈承载；arm 顺序仍保持 truthy-first，
        // 因而 node id 和候选排序合同不变。
        let mut pending = vec![(entry, 0u8)];

        while !pending.is_empty() {
            let frame_index = pending.len() - 1;
            let (node_ref, arm) = pending[frame_index];
            if arm == 2 {
                pending.pop();
                continue;
            }
            pending[frame_index].1 += 1;

            let (truthy_block, falsy_block) = *self.branch_targets.get(node_ref.index())?;
            let target = if arm == 0 { truthy_block } else { falsy_block };
            let resolved = self.resolve_target(target)?;
            let target = match resolved {
                ResolvedGuardTarget::Final(target) => target,
                ResolvedGuardTarget::Header(header) => {
                    let (child, is_new) = self.reserve_node(header)?;
                    if is_new {
                        pending.push((child, 0));
                    }
                    GuardExitTempTarget::Node(child)
                }
            };

            let node = self.nodes.get_mut(node_ref.index())?;
            if arm == 0 {
                node.truthy = target;
            } else {
                node.falsy = target;
            }
        }

        Some(entry)
    }

    fn resolve_target(&mut self, target: BlockRef) -> Option<ResolvedGuardTarget> {
        let original_target = target;
        if target != self.root && self.value_decision_headers.contains(&target) {
            self.exits.insert(target);
            return Some(ResolvedGuardTarget::Final(GuardExitTempTarget::Exit(
                target,
            )));
        }
        if !self.allow_shared_headers
            && target != self.root
            && self.cfg.preds[target.index()].len() > 1
        {
            self.exits.insert(target);
            return Some(ResolvedGuardTarget::Final(GuardExitTempTarget::Exit(
                target,
            )));
        }
        // 回到候选 root 的严格支配祖先表示条件已经离开无环 DAG（典型是 repeat
        // 回到 loop header），它是语义出口而不是后续条件节点。共享 descendant 则可有
        // 多个前驱，不能在这里按前驱数一并截断。
        if target != self.root && self.dom_tree.dominates(target, self.root) {
            self.exits.insert(target);
            return Some(ResolvedGuardTarget::Final(GuardExitTempTarget::Exit(
                target,
            )));
        }
        let followed = LinearFollowCtx {
            proto: self.proto,
            cfg: self.cfg,
            branch_by_header: self.branch_by_header,
            dom_tree: self.dom_tree,
            root: self.root,
        }
        .follow(target, |_| true, |_, _| false);
        let target = match followed.map(|followed| followed.target) {
            Some(LinearFollowTarget::Header(target)) => target,
            Some(LinearFollowTarget::Terminal(target)) => {
                if self.is_exit_target(target) {
                    self.exits.insert(target);
                    return Some(ResolvedGuardTarget::Final(GuardExitTempTarget::Exit(
                        target,
                    )));
                }
                return None;
            }
            None => {
                if self.is_exit_target(original_target) {
                    self.exits.insert(original_target);
                    return Some(ResolvedGuardTarget::Final(GuardExitTempTarget::Exit(
                        original_target,
                    )));
                }
                return None;
            }
        };
        if target != self.root && self.value_decision_headers.contains(&target) {
            self.exits.insert(target);
            return Some(ResolvedGuardTarget::Final(GuardExitTempTarget::Exit(
                target,
            )));
        }
        if !self.allow_shared_headers
            && target != self.root
            && self.cfg.preds[target.index()].len() > 1
        {
            self.exits.insert(target);
            return Some(ResolvedGuardTarget::Final(GuardExitTempTarget::Exit(
                target,
            )));
        }
        if self.should_include_header(target) {
            self.included_shared_header |=
                target != self.root && self.cfg.preds[target.index()].len() > 1;
            Some(ResolvedGuardTarget::Header(target))
        } else {
            self.exits.insert(target);
            Some(ResolvedGuardTarget::Final(GuardExitTempTarget::Exit(
                target,
            )))
        }
    }

    fn is_exit_target(&self, target: BlockRef) -> bool {
        target != self.cfg.exit_block
            && self.cfg.reachable_blocks.contains(&target)
            && (self.dom_tree.dominates(self.root, target)
                || self.post_dom_tree.dominates(target, self.root))
    }

    fn should_include_header(&self, header: BlockRef) -> bool {
        let Some(candidate) = self.branch_by_header.get(&header) else {
            return false;
        };

        let _candidate = candidate;
        header == self.root || !self.post_dom_tree.dominates(header, self.root)
    }
}

enum ResolvedGuardTarget {
    Final(GuardExitTempTarget),
    Header(BlockRef),
}

#[derive(Clone, Copy, Default)]
enum LinearChainNext {
    #[default]
    End,
    One(BlockRef),
    Two(BlockRef, BlockRef),
}

struct LinearChainIndex {
    next_by_header: Vec<LinearChainNext>,
}

impl LinearChainIndex {
    fn branch_then(
        block_count: usize,
        branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
        candidates: &[BranchCandidate],
    ) -> Self {
        let mut next_by_header = vec![LinearChainNext::End; block_count];
        for candidate in candidates {
            if candidate.kind == BranchKind::IfThen
                && let Some(next) = branch_by_header.get(&candidate.then_entry)
            {
                next_by_header[candidate.header.index()] = LinearChainNext::One(next.header);
            }
        }
        Self { next_by_header }
    }

    fn cfg(
        proto: &LoweredProto,
        cfg: &Cfg,
        branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
        candidates: &[BranchCandidate],
    ) -> Self {
        let mut next_by_header = vec![LinearChainNext::End; cfg.blocks.len()];
        for candidate in candidates {
            let Some((truthy, falsy)) = truthy_falsy_targets(proto, cfg, candidate.header) else {
                continue;
            };
            let mut first = None;
            let mut second = None;
            for target in [truthy, falsy] {
                if !branch_by_header.contains_key(&target)
                    || cfg.preds[target.index()].len() > 1
                    || first == Some(target)
                {
                    continue;
                }
                if first.is_none() {
                    first = Some(target);
                } else {
                    second = Some(target);
                }
            }
            next_by_header[candidate.header.index()] = match (first, second) {
                (Some(first), Some(second)) if first < second => {
                    LinearChainNext::Two(first, second)
                }
                (Some(first), Some(second)) => LinearChainNext::Two(second, first),
                (Some(next), None) => LinearChainNext::One(next),
                (None, _) => LinearChainNext::End,
            };
        }
        Self { next_by_header }
    }

    fn next(&self, header: BlockRef, visited: &DenseMarks, epoch: u32) -> Option<BlockRef> {
        match self.next_by_header.get(header.index()).copied()? {
            LinearChainNext::End => None,
            LinearChainNext::One(next) => (!visited.contains(next, epoch)).then_some(next),
            LinearChainNext::Two(first, second) => match (
                visited.contains(first, epoch),
                visited.contains(second, epoch),
            ) {
                (false, true) => Some(first),
                (true, false) => Some(second),
                (false, false) | (true, true) => None,
            },
        }
    }
}

fn collect_if_else_branch_exit_chain(
    root: &BranchCandidate,
    chains: &LinearChainIndex,
    visited: &mut DenseMarks,
) -> Vec<BlockRef> {
    let mut headers = Vec::new();
    let visited_epoch = visited.begin();
    let mut current = root.header;

    while visited.insert(current, visited_epoch) {
        headers.push(current);
        let Some(next) = chains.next(current, visited, visited_epoch) else {
            break;
        };
        current = next;
    }

    headers
}

fn infer_linear_branch_exit(
    proto: &LoweredProto,
    cfg: &Cfg,
    headers: &[BlockRef],
) -> Option<ShortCircuitExit> {
    let mut truthy_exit = None;
    let mut falsy_exit = None;

    for (index, header) in headers.iter().enumerate() {
        let next = headers.get(index + 1).copied();
        let (truthy_target, falsy_target) = truthy_falsy_targets(proto, cfg, *header)?;

        match next {
            Some(next_header) if truthy_target == next_header => {
                falsy_exit.get_or_insert(falsy_target);
                if falsy_exit != Some(falsy_target) {
                    return None;
                }
            }
            Some(next_header) if falsy_target == next_header => {
                truthy_exit.get_or_insert(truthy_target);
                if truthy_exit != Some(truthy_target) {
                    return None;
                }
            }
            Some(_) => return None,
            None => {
                truthy_exit.get_or_insert(truthy_target);
                falsy_exit.get_or_insert(falsy_target);
                if truthy_exit != Some(truthy_target) || falsy_exit != Some(falsy_target) {
                    return None;
                }
            }
        }
    }

    Some(ShortCircuitExit::BranchExit {
        truthy: truthy_exit?,
        falsy: falsy_exit?,
    })
}

fn infer_longest_linear_branch_exit(
    proto: &LoweredProto,
    cfg: &Cfg,
    headers: &[BlockRef],
) -> Option<(usize, ShortCircuitExit)> {
    let mut truthy_exit = None;
    let mut falsy_exit = None;
    let mut best = None;

    for (index, header) in headers.iter().copied().enumerate() {
        let Some((truthy_target, falsy_target)) = truthy_falsy_targets(proto, cfg, header) else {
            break;
        };
        if index >= 1
            && truthy_exit.is_none_or(|exit| exit == truthy_target)
            && falsy_exit.is_none_or(|exit| exit == falsy_target)
        {
            best = Some((
                index + 1,
                ShortCircuitExit::BranchExit {
                    truthy: truthy_target,
                    falsy: falsy_target,
                },
            ));
        }

        let Some(next) = headers.get(index + 1).copied() else {
            break;
        };
        let valid = if truthy_target == next {
            constrain_linear_exit(&mut falsy_exit, falsy_target)
        } else if falsy_target == next {
            constrain_linear_exit(&mut truthy_exit, truthy_target)
        } else {
            false
        };
        if !valid {
            break;
        }
    }

    best
}

fn infer_longest_if_else_branch_exit(
    proto: &LoweredProto,
    cfg: &Cfg,
    headers: &[BlockRef],
) -> Option<(usize, ShortCircuitExit)> {
    let (&first_header, remaining_headers) = headers.split_first()?;
    let mut previous_targets = truthy_falsy_targets(proto, cfg, first_header)?;
    let mut external_targets = BTreeMap::<BlockRef, usize>::new();
    for target in [previous_targets.0, previous_targets.1] {
        *external_targets.entry(target).or_default() += 1;
    }
    let mut strict_truthy_exit = None;
    let mut strict_falsy_exit = None;
    let mut strict_possible = true;
    let mut best = None;

    for (index, header) in remaining_headers.iter().copied().enumerate() {
        let Some(targets) = truthy_falsy_targets(proto, cfg, header) else {
            break;
        };
        for target in [previous_targets.0, previous_targets.1] {
            if target == header && !decrement_target_count(&mut external_targets, target) {
                return best;
            }
        }

        if previous_targets.0 == header {
            strict_possible = strict_possible
                && constrain_linear_exit(&mut strict_falsy_exit, previous_targets.1);
        } else if previous_targets.1 == header {
            strict_possible = strict_possible
                && constrain_linear_exit(&mut strict_truthy_exit, previous_targets.0);
        } else {
            strict_possible = false;
        }

        for target in [targets.0, targets.1] {
            *external_targets.entry(target).or_default() += 1;
        }
        previous_targets = targets;

        let strict_exit = (strict_possible
            && strict_truthy_exit.is_none_or(|exit| exit == targets.0)
            && strict_falsy_exit.is_none_or(|exit| exit == targets.1))
        .then_some(ShortCircuitExit::BranchExit {
            truthy: targets.0,
            falsy: targets.1,
        });
        let relaxed_exit = || {
            let mut exits = external_targets.keys().copied();
            let (Some(truthy), Some(falsy), None) = (exits.next(), exits.next(), exits.next())
            else {
                return None;
            };
            Some(ShortCircuitExit::BranchExit { truthy, falsy })
        };

        if let Some(exit) = strict_exit.or_else(relaxed_exit) {
            best = Some((index + 2, exit));
        }
    }

    best
}

fn constrain_linear_exit(exit: &mut Option<BlockRef>, target: BlockRef) -> bool {
    match *exit {
        Some(existing) => existing == target,
        None => {
            *exit = Some(target);
            true
        }
    }
}

fn decrement_target_count(targets: &mut BTreeMap<BlockRef, usize>, target: BlockRef) -> bool {
    let Some(count) = targets.get_mut(&target) else {
        return false;
    };
    *count -= 1;
    if *count == 0 {
        targets.remove(&target);
    }
    true
}

fn build_linear_branch_exit_nodes(
    proto: &LoweredProto,
    cfg: &Cfg,
    headers: &[BlockRef],
    exit: &ShortCircuitExit,
) -> Option<Vec<ShortCircuitNode>> {
    let ShortCircuitExit::BranchExit { truthy, falsy } = *exit else {
        return None;
    };

    let node_ids = headers
        .iter()
        .enumerate()
        .map(|(index, header)| (*header, ShortCircuitNodeRef(index)))
        .collect::<BTreeMap<_, _>>();

    headers
        .iter()
        .enumerate()
        .map(|(index, header)| {
            let next = headers.get(index + 1).and_then(|header| {
                node_ids
                    .get(header)
                    .copied()
                    .map(|node_ref| (*header, node_ref))
            });
            let (truthy_target, falsy_target) = truthy_falsy_targets(proto, cfg, *header)?;

            Some(ShortCircuitNode {
                id: ShortCircuitNodeRef(index),
                header: *header,
                truthy: classify_linear_target(truthy_target, next, truthy, falsy)?,
                falsy: classify_linear_target(falsy_target, next, truthy, falsy)?,
            })
        })
        .collect()
}

fn classify_linear_target(
    block: BlockRef,
    next: Option<(BlockRef, ShortCircuitNodeRef)>,
    truthy_exit: BlockRef,
    falsy_exit: BlockRef,
) -> Option<ShortCircuitTarget> {
    match next {
        Some((next_block, next_ref)) if block == next_block => {
            Some(ShortCircuitTarget::Node(next_ref))
        }
        _ if block == truthy_exit => Some(ShortCircuitTarget::TruthyExit),
        _ if block == falsy_exit => Some(ShortCircuitTarget::FalsyExit),
        _ => None,
    }
}

fn classify_guard_branch_exits(
    cfg: &Cfg,
    post_dom_tree: &PostDominatorTree,
    first_exit: BlockRef,
    second_exit: BlockRef,
) -> Option<(BlockRef, BlockRef)> {
    match (
        post_dom_tree.dominates(first_exit, second_exit),
        post_dom_tree.dominates(second_exit, first_exit),
    ) {
        (true, false) => return Some((second_exit, first_exit)),
        (false, true) => return Some((first_exit, second_exit)),
        _ => {}
    }

    match (
        cfg.can_reach(first_exit, second_exit),
        cfg.can_reach(second_exit, first_exit),
    ) {
        (true, false) => Some((first_exit, second_exit)),
        (false, true) => Some((second_exit, first_exit)),
        (false, false) => Some((first_exit, second_exit)),
        (true, true) => Some((first_exit, second_exit)),
    }
}

fn finalize_guard_exit_target(
    target: GuardExitTempTarget,
    truthy_exit: BlockRef,
    falsy_exit: BlockRef,
) -> Option<ShortCircuitTarget> {
    match target {
        GuardExitTempTarget::Node(node_ref) => Some(ShortCircuitTarget::Node(node_ref)),
        GuardExitTempTarget::Exit(block) if block == truthy_exit => {
            Some(ShortCircuitTarget::TruthyExit)
        }
        GuardExitTempTarget::Exit(block) if block == falsy_exit => {
            Some(ShortCircuitTarget::FalsyExit)
        }
        GuardExitTempTarget::Exit(_) => None,
    }
}
