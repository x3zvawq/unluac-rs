//! 这个文件实现短路候选提取。
//!
//! 当前实现分两部分：
//! 1. 条件出口型短路继续沿用保守的线性识别，优先保证 `if a and b then ...` 这类
//!    条件链稳定可用；
//! 2. 值合流型短路改成受控 DAG 提取，允许普通 Lua 源码里常见的共享 continuation，
//!    例如 `(a and b) or (c and d)`。
//!
//! 这样做的原因是：值型短路的 CFG 更容易出现“多个失败路径汇到同一后续表达式”的
//! 共享形状，如果继续强行压成线性链，HIR 只能看到残缺证据，后面就会被迫回退。

use std::collections::{BTreeMap, BTreeSet};

use crate::cfg::{BlockRef, Cfg, DataflowFacts, GraphFacts};
use crate::transformer::{LowInstr, LoweredProto, Reg};

use super::common::{
    BranchCandidate, BranchKind, ShortCircuitCandidate, ShortCircuitExit, ShortCircuitNode,
    ShortCircuitNodeRef, ShortCircuitTarget,
};
use super::helpers::{branch_edges, can_reach, dominates};

pub(super) fn analyze_short_circuits(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    branch_candidates: &[BranchCandidate],
) -> Vec<ShortCircuitCandidate> {
    let branch_by_header = branch_candidates
        .iter()
        .map(|candidate| (candidate.header, candidate))
        .collect::<BTreeMap<_, _>>();

    let mut candidates = analyze_linear_branch_exit_candidates(proto, cfg, branch_candidates);
    candidates.extend(analyze_guard_branch_exit_dag_candidates(
        proto,
        cfg,
        graph_facts,
        &branch_by_header,
        branch_candidates,
    ));
    candidates.extend(analyze_value_merge_candidates(
        proto,
        cfg,
        graph_facts,
        dataflow,
        &branch_by_header,
        branch_candidates,
    ));
    candidates.sort_by_key(|candidate| {
        (
            candidate.header,
            candidate.blocks.len(),
            candidate.nodes.len(),
            candidate.result_reg.map(Reg::index),
        )
    });
    candidates
}

fn analyze_guard_branch_exit_dag_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    branch_candidates: &[BranchCandidate],
) -> Vec<ShortCircuitCandidate> {
    let mut best_by_header = BTreeMap::<BlockRef, ShortCircuitCandidate>::new();

    for root in branch_candidates {
        let Some(candidate) =
            GuardBranchExitDagBuilder::new(proto, cfg, graph_facts, branch_by_header, root.header)
                .build()
        else {
            continue;
        };

        match best_by_header.get(&root.header) {
            Some(existing) if !prefer_guard_exit_candidate(&candidate, existing) => {}
            _ => {
                best_by_header.insert(root.header, candidate);
            }
        }
    }

    best_by_header.into_values().collect()
}

fn prefer_guard_exit_candidate(
    candidate: &ShortCircuitCandidate,
    existing: &ShortCircuitCandidate,
) -> bool {
    let candidate_score = (
        candidate.blocks.len(),
        candidate.nodes.len(),
        usize::MAX - candidate.header.index(),
    );
    let existing_score = (
        existing.blocks.len(),
        existing.nodes.len(),
        usize::MAX - existing.header.index(),
    );
    candidate_score > existing_score
}

fn analyze_linear_branch_exit_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch_candidates: &[BranchCandidate],
) -> Vec<ShortCircuitCandidate> {
    let branch_by_header = branch_candidates
        .iter()
        .map(|candidate| (candidate.header, candidate))
        .collect::<BTreeMap<_, _>>();

    let mut candidates = Vec::new();
    for candidate in branch_candidates {
        if candidate.kind != BranchKind::IfThen {
            continue;
        }

        let Some(mut current) = branch_by_header.get(&candidate.header).copied() else {
            continue;
        };
        let mut visited = BTreeSet::new();
        let mut headers = Vec::new();

        loop {
            if !visited.insert(current.header) {
                break;
            }
            headers.push(current.header);

            let Some(next) = next_chain_header(&branch_by_header, current, &visited) else {
                break;
            };
            current = next;
        }

        let Some(exit) = infer_linear_branch_exit(proto, cfg, &headers) else {
            continue;
        };
        let Some(nodes) = build_linear_branch_exit_nodes(proto, cfg, &headers, &exit) else {
            continue;
        };

        let blocks = headers.iter().copied().collect::<BTreeSet<_>>();
        let reducible = is_reducible_candidate(cfg, candidate.header, &blocks);
        candidates.push(ShortCircuitCandidate {
            header: candidate.header,
            blocks,
            entry: ShortCircuitNodeRef(0),
            nodes,
            exit,
            result_reg: None,
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

fn analyze_value_merge_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    branch_candidates: &[BranchCandidate],
) -> Vec<ShortCircuitCandidate> {
    let mut best_by_merge = BTreeMap::<(BlockRef, Reg), ShortCircuitCandidate>::new();

    for phi in &dataflow.phi_candidates {
        if phi.incoming.len() < 2 {
            continue;
        }

        for root in branch_candidates {
            let Some(candidate) = ValueMergeDagBuilder::new(
                proto,
                cfg,
                graph_facts,
                dataflow,
                branch_by_header,
                ValueMergeSeed {
                    root: root.header,
                    merge: phi.block,
                    reg: phi.reg,
                },
            )
            .build() else {
                continue;
            };

            let key = (phi.block, phi.reg);
            match best_by_merge.get(&key) {
                Some(existing) if !prefer_value_candidate(&candidate, existing) => {}
                _ => {
                    best_by_merge.insert(key, candidate);
                }
            }
        }
    }

    best_by_merge.into_values().collect()
}

fn prefer_value_candidate(
    candidate: &ShortCircuitCandidate,
    existing: &ShortCircuitCandidate,
) -> bool {
    let candidate_score = (
        candidate.blocks.len(),
        candidate.nodes.len(),
        usize::MAX - candidate.header.index(),
    );
    let existing_score = (
        existing.blocks.len(),
        existing.nodes.len(),
        usize::MAX - existing.header.index(),
    );
    candidate_score > existing_score
}

fn next_chain_header<'a>(
    branch_by_header: &BTreeMap<BlockRef, &'a BranchCandidate>,
    candidate: &'a BranchCandidate,
    visited: &BTreeSet<BlockRef>,
) -> Option<&'a BranchCandidate> {
    if candidate.kind != BranchKind::IfThen {
        return None;
    }

    let next = branch_by_header.get(&candidate.then_entry).copied()?;
    if visited.contains(&next.header) {
        None
    } else {
        Some(next)
    }
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

struct ValueMergeDagBuilder<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    dataflow: &'a DataflowFacts,
    branch_by_header: &'a BTreeMap<BlockRef, &'a BranchCandidate>,
    dom_parent: &'a [Option<BlockRef>],
    root: BlockRef,
    merge: BlockRef,
    reg: Reg,
    nodes: Vec<ShortCircuitNode>,
    node_by_header: BTreeMap<BlockRef, ShortCircuitNodeRef>,
    visiting: BTreeSet<BlockRef>,
    blocks: BTreeSet<BlockRef>,
    value_leaves: BTreeSet<BlockRef>,
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

struct GuardBranchExitDagBuilder<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    branch_by_header: &'a BTreeMap<BlockRef, &'a BranchCandidate>,
    dom_parent: &'a [Option<BlockRef>],
    post_dom_parent: &'a [Option<BlockRef>],
    root: BlockRef,
    nodes: Vec<GuardExitTempNode>,
    node_by_header: BTreeMap<BlockRef, ShortCircuitNodeRef>,
    visiting: BTreeSet<BlockRef>,
    blocks: BTreeSet<BlockRef>,
    exits: BTreeSet<BlockRef>,
}

#[derive(Debug, Clone, Copy)]
struct ValueMergeSeed {
    root: BlockRef,
    merge: BlockRef,
    reg: Reg,
}

impl<'a> ValueMergeDagBuilder<'a> {
    fn new(
        proto: &'a LoweredProto,
        cfg: &'a Cfg,
        graph_facts: &'a GraphFacts,
        dataflow: &'a DataflowFacts,
        branch_by_header: &'a BTreeMap<BlockRef, &'a BranchCandidate>,
        seed: ValueMergeSeed,
    ) -> Self {
        Self {
            proto,
            cfg,
            dataflow,
            branch_by_header,
            dom_parent: &graph_facts.dominator_tree.parent,
            root: seed.root,
            merge: seed.merge,
            reg: seed.reg,
            nodes: Vec::new(),
            node_by_header: BTreeMap::new(),
            visiting: BTreeSet::new(),
            blocks: BTreeSet::new(),
            value_leaves: BTreeSet::new(),
        }
    }

    fn build(mut self) -> Option<ShortCircuitCandidate> {
        if !self.branch_by_header.contains_key(&self.root)
            || self.merge == self.root
            || !dominates(self.dom_parent, self.root, self.merge)
        {
            return None;
        }

        let entry = self.build_node(self.root)?;
        if entry != ShortCircuitNodeRef(0) {
            return None;
        }
        if self.value_leaves.len() < 2 {
            return None;
        }
        let has_header_leaf = self
            .value_leaves
            .iter()
            .any(|leaf| self.node_by_header.contains_key(leaf));
        if self.nodes.len() == 1 && !has_header_leaf {
            return None;
        }
        if !self.value_leaves_feed_phi() {
            return None;
        }

        let reducible = is_reducible_candidate(self.cfg, self.root, &self.blocks);
        Some(ShortCircuitCandidate {
            header: self.root,
            blocks: self.blocks,
            entry,
            nodes: self.nodes,
            exit: ShortCircuitExit::ValueMerge(self.merge),
            result_reg: Some(self.reg),
            reducible,
        })
    }

    fn build_node(&mut self, header: BlockRef) -> Option<ShortCircuitNodeRef> {
        if let Some(node_ref) = self.node_by_header.get(&header).copied() {
            return Some(node_ref);
        }
        if !self.visiting.insert(header) {
            return None;
        }

        let _candidate = self.branch_by_header.get(&header)?;
        if !dominates(self.dom_parent, self.root, header)
            || !can_reach(self.cfg, header, self.merge)
        {
            self.visiting.remove(&header);
            return None;
        }

        let (truthy_block, falsy_block) = truthy_falsy_targets(self.proto, self.cfg, header)?;
        let id = ShortCircuitNodeRef(self.nodes.len());
        self.node_by_header.insert(header, id);
        self.blocks.insert(header);
        self.nodes.push(ShortCircuitNode {
            id,
            header,
            truthy: ShortCircuitTarget::Value(header),
            falsy: ShortCircuitTarget::Value(header),
        });

        let truthy = self.resolve_value_target(header, truthy_block)?;
        let falsy = self.resolve_value_target(header, falsy_block)?;
        self.nodes[id.index()] = ShortCircuitNode {
            id,
            header,
            truthy,
            falsy,
        };

        self.visiting.remove(&header);
        Some(id)
    }

    fn resolve_value_target(
        &mut self,
        from_header: BlockRef,
        target: BlockRef,
    ) -> Option<ShortCircuitTarget> {
        if target == self.merge {
            self.value_leaves.insert(from_header);
            return Some(ShortCircuitTarget::Value(from_header));
        }
        if target == self.cfg.exit_block
            || !self.cfg.reachable_blocks.contains(&target)
            || !dominates(self.dom_parent, self.root, target)
            || !can_reach(self.cfg, target, self.merge)
        {
            return None;
        }

        if self.branch_by_header.contains_key(&target) {
            return Some(ShortCircuitTarget::Node(self.build_node(target)?));
        }

        match self.follow_linear_value_target(target)? {
            LinearValueTarget::Node(header) => {
                Some(ShortCircuitTarget::Node(self.build_node(header)?))
            }
            LinearValueTarget::Value(block) => {
                self.blocks.insert(block);
                self.value_leaves.insert(block);
                Some(ShortCircuitTarget::Value(block))
            }
        }
    }

    fn follow_linear_value_target(&self, start: BlockRef) -> Option<LinearValueTarget> {
        let mut current = start;
        let mut visited = BTreeSet::new();

        loop {
            if current == self.merge
                || current == self.cfg.exit_block
                || !self.cfg.reachable_blocks.contains(&current)
                || !dominates(self.dom_parent, self.root, current)
                || !visited.insert(current)
            {
                return None;
            }

            if self.branch_by_header.contains_key(&current) {
                return Some(LinearValueTarget::Node(current));
            }

            let succs = reachable_successors(self.cfg, current);
            match succs.as_slice() {
                [succ] if *succ == self.merge => {
                    return block_writes_reg(
                        self.proto,
                        self.dataflow,
                        self.cfg,
                        current,
                        self.reg,
                    )
                    .then_some(LinearValueTarget::Value(current));
                }
                [succ] if block_is_passthrough(self.proto, self.cfg, current) => {
                    current = *succ;
                }
                _ => return None,
            }
        }
    }

    fn value_leaves_feed_phi(&self) -> bool {
        let mut incoming_preds = self
            .dataflow
            .phi_candidates
            .iter()
            .find(|phi| phi.block == self.merge && phi.reg == self.reg)
            .into_iter()
            .flat_map(|phi| phi.incoming.iter().map(|incoming| incoming.pred))
            .collect::<Vec<_>>();
        incoming_preds.sort();
        incoming_preds.dedup();

        let mut leaves = self.value_leaves.iter().copied().collect::<Vec<_>>();
        leaves.sort();
        leaves == incoming_preds
    }
}

impl<'a> GuardBranchExitDagBuilder<'a> {
    fn new(
        proto: &'a LoweredProto,
        cfg: &'a Cfg,
        graph_facts: &'a GraphFacts,
        branch_by_header: &'a BTreeMap<BlockRef, &'a BranchCandidate>,
        root: BlockRef,
    ) -> Self {
        Self {
            proto,
            cfg,
            branch_by_header,
            dom_parent: &graph_facts.dominator_tree.parent,
            post_dom_parent: &graph_facts.post_dominator_tree.parent,
            root,
            nodes: Vec::new(),
            node_by_header: BTreeMap::new(),
            visiting: BTreeSet::new(),
            blocks: BTreeSet::new(),
            exits: BTreeSet::new(),
        }
    }

    fn build(mut self) -> Option<ShortCircuitCandidate> {
        let root_candidate = *self.branch_by_header.get(&self.root)?;
        if root_candidate.kind == BranchKind::IfElse {
            return None;
        }

        let entry = self.build_node(self.root)?;
        if entry != ShortCircuitNodeRef(0) || self.nodes.len() < 2 || self.exits.len() != 2 {
            return None;
        }

        let mut exits = self.exits.iter().copied().collect::<Vec<_>>();
        exits.sort();
        let [first_exit, second_exit] = exits.as_slice() else {
            return None;
        };
        let (truthy_exit, falsy_exit) =
            classify_guard_branch_exits(self.cfg, *first_exit, *second_exit)?;

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

        let reducible = is_reducible_candidate(self.cfg, self.root, &self.blocks);
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
            reducible,
        })
    }

    fn build_node(&mut self, header: BlockRef) -> Option<ShortCircuitNodeRef> {
        if let Some(node_ref) = self.node_by_header.get(&header).copied() {
            return Some(node_ref);
        }
        if !self.visiting.insert(header) {
            return None;
        }
        if !self.should_include_header(header) {
            self.visiting.remove(&header);
            return None;
        }

        let (truthy_block, falsy_block) = truthy_falsy_targets(self.proto, self.cfg, header)?;
        let id = ShortCircuitNodeRef(self.nodes.len());
        self.node_by_header.insert(header, id);
        self.blocks.insert(header);
        self.nodes.push(GuardExitTempNode {
            id,
            header,
            truthy: GuardExitTempTarget::Exit(header),
            falsy: GuardExitTempTarget::Exit(header),
        });

        let truthy = self.resolve_target(truthy_block)?;
        let falsy = self.resolve_target(falsy_block)?;
        self.nodes[id.index()] = GuardExitTempNode {
            id,
            header,
            truthy,
            falsy,
        };

        self.visiting.remove(&header);
        Some(id)
    }

    fn resolve_target(&mut self, target: BlockRef) -> Option<GuardExitTempTarget> {
        let target = self.follow_linear_target(target)?;
        if self.should_include_header(target) {
            Some(GuardExitTempTarget::Node(self.build_node(target)?))
        } else {
            self.exits.insert(target);
            Some(GuardExitTempTarget::Exit(target))
        }
    }

    fn follow_linear_target(&self, start: BlockRef) -> Option<BlockRef> {
        let mut current = start;
        let mut visited = BTreeSet::new();

        loop {
            if current == self.cfg.exit_block
                || !self.cfg.reachable_blocks.contains(&current)
                || !dominates(self.dom_parent, self.root, current)
                || !visited.insert(current)
            {
                return None;
            }

            if self.branch_by_header.contains_key(&current) {
                return Some(current);
            }

            let succs = reachable_successors(self.cfg, current);
            match succs.as_slice() {
                [succ] if block_is_passthrough(self.proto, self.cfg, current) => {
                    current = *succ;
                }
                _ => return None,
            }
        }
    }

    fn should_include_header(&self, header: BlockRef) -> bool {
        let Some(candidate) = self.branch_by_header.get(&header) else {
            return false;
        };

        candidate.kind != BranchKind::IfElse
            && (header == self.root || !dominates(self.post_dom_parent, header, self.root))
    }
}

fn classify_guard_branch_exits(
    cfg: &Cfg,
    first_exit: BlockRef,
    second_exit: BlockRef,
) -> Option<(BlockRef, BlockRef)> {
    match (
        can_reach(cfg, first_exit, second_exit),
        can_reach(cfg, second_exit, first_exit),
    ) {
        (true, false) => Some((first_exit, second_exit)),
        (false, true) => Some((second_exit, first_exit)),
        _ => None,
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

enum LinearValueTarget {
    Node(BlockRef),
    Value(BlockRef),
}

fn truthy_falsy_targets(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: BlockRef,
) -> Option<(BlockRef, BlockRef)> {
    let (then_edge_ref, else_edge_ref) = branch_edges(cfg, header)?;
    let then_target = cfg.edges[then_edge_ref.index()].to;
    let else_target = cfg.edges[else_edge_ref.index()].to;

    match cfg.terminator(&proto.instrs, header) {
        Some(LowInstr::Branch(instr)) if instr.cond.negated => Some((else_target, then_target)),
        Some(LowInstr::Branch(_)) => Some((then_target, else_target)),
        _ => None,
    }
}

fn block_writes_reg(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    cfg: &Cfg,
    block: BlockRef,
    reg: Reg,
) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    let end = range
        .last()
        .and_then(|last| {
            matches!(proto.instrs.get(last.index()), Some(LowInstr::Jump(_)))
                .then_some(range.end().saturating_sub(1))
        })
        .unwrap_or_else(|| range.end());

    (range.start.index()..end).any(|instr_index| {
        dataflow.instr_defs[instr_index]
            .iter()
            .any(|def_id| dataflow.defs[def_id.index()].reg == reg)
    })
}

fn block_is_passthrough(proto: &LoweredProto, cfg: &Cfg, block: BlockRef) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    match range.len {
        0 => true,
        1 => matches!(
            proto.instrs.get(range.start.index()),
            Some(LowInstr::Jump(_))
        ),
        _ => false,
    }
}

fn reachable_successors(cfg: &Cfg, block: BlockRef) -> Vec<BlockRef> {
    let mut succs = cfg.succs[block.index()]
        .iter()
        .map(|edge_ref| cfg.edges[edge_ref.index()].to)
        .filter(|succ| cfg.reachable_blocks.contains(succ))
        .collect::<Vec<_>>();
    succs.sort();
    succs.dedup();
    succs
}

fn is_reducible_candidate(cfg: &Cfg, header: BlockRef, blocks: &BTreeSet<BlockRef>) -> bool {
    blocks.iter().all(|block| {
        if *block == header {
            true
        } else {
            cfg.preds[block.index()].iter().all(|edge_ref| {
                let pred = cfg.edges[edge_ref.index()].from;
                !cfg.reachable_blocks.contains(&pred) || blocks.contains(&pred)
            })
        }
    })
}
