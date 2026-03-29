//! 这个文件负责“条件出口型”短路候选提取。
//!
//! 它解决的是 `if a and b then ... end`、`if a or b then ... end` 这类最终直接流向
//! “整体为真/整体为假”两个出口的形状。这里特意不碰 value merge，让“条件出口识别”
//! 和“值合流 DAG 提取”各自拥有单一职责。
//!
//! 它依赖 branch 候选、支配/后支配关系和共享线性跟随规则，只负责回答
//! “这一串判断是不是一个纯条件出口短路”；它不会越权去拆 phi，也不会替 value merge
//! 做值来源分类。
//!
//! 例子：
//! - `if a and b then return end` 会产出“整体真时流向 then、整体假时流向 fallthrough”的
//!   短路候选
//! - `if a or b then body() end` 会产出“整体真时进入 body、整体假时直接跳过”的候选

use std::collections::{BTreeMap, BTreeSet};

use crate::cfg::{BlockRef, Cfg, GraphFacts, PostDominatorTree};
use crate::transformer::LoweredProto;

use super::super::common::{
    BranchCandidate, BranchKind, ShortCircuitCandidate, ShortCircuitExit, ShortCircuitNode,
    ShortCircuitNodeRef, ShortCircuitTarget,
};
use super::shared::{
    LinearFollowCtx, LinearFollowTarget, is_reducible_candidate, prefer_short_circuit_candidate,
    short_circuit_nodes_are_acyclic, truthy_falsy_targets,
};

pub(super) fn analyze_guard_branch_exit_dag_candidates(
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
            Some(existing) if !prefer_short_circuit_candidate(&candidate, existing) => {}
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

            let Some(next) = next_chain_header(branch_by_header, current, &visited) else {
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
            result_phi_id: None,
            entry_defs: BTreeSet::new(),
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

struct GuardBranchExitDagBuilder<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    branch_by_header: &'a BTreeMap<BlockRef, &'a BranchCandidate>,
    dom_tree: &'a crate::cfg::DominatorTree,
    post_dom_tree: &'a PostDominatorTree,
    root: BlockRef,
    nodes: Vec<GuardExitTempNode>,
    node_by_header: BTreeMap<BlockRef, ShortCircuitNodeRef>,
    visiting: BTreeSet<BlockRef>,
    blocks: BTreeSet<BlockRef>,
    exits: BTreeSet<BlockRef>,
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
            dom_tree: &graph_facts.dominator_tree,
            post_dom_tree: &graph_facts.post_dominator_tree,
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
        if !short_circuit_nodes_are_acyclic(&nodes, entry) {
            return None;
        }

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
            result_phi_id: None,
            entry_defs: BTreeSet::new(),
            value_incomings: Vec::new(),
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
        let LinearFollowTarget::Header(target) = LinearFollowCtx {
            proto: self.proto,
            cfg: self.cfg,
            branch_by_header: self.branch_by_header,
            dom_tree: self.dom_tree,
            root: self.root,
        }
        .follow(target, |_| true, |_, _| false)?
        else {
            return None;
        };
        if self.should_include_header(target) {
            Some(GuardExitTempTarget::Node(self.build_node(target)?))
        } else {
            self.exits.insert(target);
            Some(GuardExitTempTarget::Exit(target))
        }
    }

    fn should_include_header(&self, header: BlockRef) -> bool {
        let Some(candidate) = self.branch_by_header.get(&header) else {
            return false;
        };

        candidate.kind != BranchKind::IfElse
            && (header == self.root || !self.post_dom_tree.dominates(header, self.root))
    }
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

fn classify_guard_branch_exits(
    cfg: &Cfg,
    first_exit: BlockRef,
    second_exit: BlockRef,
) -> Option<(BlockRef, BlockRef)> {
    match (
        cfg.can_reach(first_exit, second_exit),
        cfg.can_reach(second_exit, first_exit),
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
