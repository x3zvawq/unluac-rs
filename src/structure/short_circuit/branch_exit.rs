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

use crate::structure::{BlockRef, Cfg, GraphFacts, PostDominatorTree};
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
    closed_linear_interiors: &BTreeSet<BlockRef>,
) -> Vec<ShortCircuitCandidate> {
    let mut best_by_header = BTreeMap::<BlockRef, ShortCircuitCandidate>::new();

    for root in branch_candidates {
        if closed_linear_interiors.contains(&root.header) {
            continue;
        }
        let Some(candidate) = GuardBranchExitDagBuilder::new(
            proto,
            cfg,
            graph_facts,
            branch_by_header,
            root.header,
            true,
        )
        .build()
        .or_else(|| {
            GuardBranchExitDagBuilder::new(
                proto,
                cfg,
                graph_facts,
                branch_by_header,
                root.header,
                false,
            )
            .build()
        }) else {
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
    analyze_linear_branch_exit_candidates_with(
        proto,
        cfg,
        branch_by_header,
        branch_candidates,
        |candidate, visited| {
            next_chain_header(branch_by_header, candidate, visited).map(|next| next.header)
        },
    )
}

pub(super) fn analyze_cfg_linear_branch_exit_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    branch_candidates: &[BranchCandidate],
) -> Vec<ShortCircuitCandidate> {
    analyze_linear_branch_exit_candidates_with(
        proto,
        cfg,
        branch_by_header,
        branch_candidates,
        |candidate, visited| {
            next_cfg_chain_header(proto, cfg, branch_by_header, candidate.header, visited)
        },
    )
}

fn analyze_linear_branch_exit_candidates_with<'a>(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch_by_header: &BTreeMap<BlockRef, &'a BranchCandidate>,
    branch_candidates: &'a [BranchCandidate],
    mut next_header: impl FnMut(&'a BranchCandidate, &BTreeSet<BlockRef>) -> Option<BlockRef>,
) -> Vec<ShortCircuitCandidate> {
    let mut candidates = Vec::new();
    let mut closed_linear_interiors = BTreeSet::new();
    for candidate in branch_candidates {
        if candidate.kind != BranchKind::IfThen
            || closed_linear_interiors.contains(&candidate.header)
        {
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

            let Some(next) = next_header(current, &visited)
                .and_then(|header| branch_by_header.get(&header).copied())
            else {
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
            let last = *headers.last().unwrap();
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
            && let Some((prefix_len, prefix_exit)) = (2..headers.len()).rev().find_map(|len| {
                infer_linear_branch_exit(proto, cfg, &headers[..len]).map(|exit| (len, exit))
            })
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

    for candidate in branch_candidates {
        if candidate.kind != BranchKind::IfElse {
            continue;
        }

        let headers = collect_if_else_branch_exit_chain(proto, cfg, branch_by_header, candidate);
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

struct GuardBranchExitDagBuilder<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    branch_by_header: &'a BTreeMap<BlockRef, &'a BranchCandidate>,
    dom_tree: &'a crate::structure::DominatorTree,
    post_dom_tree: &'a PostDominatorTree,
    root: BlockRef,
    allow_shared_headers: bool,
    included_shared_header: bool,
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
        allow_shared_headers: bool,
    ) -> Self {
        Self {
            proto,
            cfg,
            branch_by_header,
            dom_tree: &graph_facts.dominator_tree,
            post_dom_tree: &graph_facts.post_dominator_tree,
            root,
            allow_shared_headers,
            included_shared_header: false,
            nodes: Vec::new(),
            node_by_header: BTreeMap::new(),
            visiting: BTreeSet::new(),
            blocks: BTreeSet::new(),
            exits: BTreeSet::new(),
        }
    }

    fn build(mut self) -> Option<ShortCircuitCandidate> {
        let _root_candidate = *self.branch_by_header.get(&self.root)?;

        let entry = self.build_node(self.root)?;
        if entry != ShortCircuitNodeRef(0) || self.nodes.len() < 2 || self.exits.len() != 2 {
            return None;
        }
        if self.included_shared_header
            && !self
                .exits
                .iter()
                .any(|exit| *exit != self.root && self.dom_tree.dominates(*exit, self.root))
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
        let original_target = target;
        if !self.allow_shared_headers
            && target != self.root
            && self.cfg.preds[target.index()].len() > 1
        {
            self.exits.insert(target);
            return Some(GuardExitTempTarget::Exit(target));
        }
        // 回到候选 root 的严格支配祖先表示条件已经离开无环 DAG（典型是 repeat
        // 回到 loop header），它是语义出口而不是后续条件节点。共享 descendant 则可有
        // 多个前驱，不能在这里按前驱数一并截断。
        if target != self.root && self.dom_tree.dominates(target, self.root) {
            self.exits.insert(target);
            return Some(GuardExitTempTarget::Exit(target));
        }
        let followed = LinearFollowCtx {
            proto: self.proto,
            cfg: self.cfg,
            branch_by_header: self.branch_by_header,
            dom_tree: self.dom_tree,
            root: self.root,
        }
        .follow(target, |_| true, |_, _| false);
        let target = match followed {
            Some(LinearFollowTarget::Header(target)) => target,
            Some(LinearFollowTarget::Terminal(target)) => {
                if self.is_exit_target(target) {
                    self.exits.insert(target);
                    return Some(GuardExitTempTarget::Exit(target));
                }
                return None;
            }
            None => {
                if self.is_exit_target(original_target) {
                    self.exits.insert(original_target);
                    return Some(GuardExitTempTarget::Exit(original_target));
                }
                return None;
            }
        };
        if !self.allow_shared_headers
            && target != self.root
            && self.cfg.preds[target.index()].len() > 1
        {
            self.exits.insert(target);
            return Some(GuardExitTempTarget::Exit(target));
        }
        if self.should_include_header(target) {
            self.included_shared_header |=
                target != self.root && self.cfg.preds[target.index()].len() > 1;
            Some(GuardExitTempTarget::Node(self.build_node(target)?))
        } else {
            self.exits.insert(target);
            Some(GuardExitTempTarget::Exit(target))
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

fn collect_if_else_branch_exit_chain(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    root: &BranchCandidate,
) -> Vec<BlockRef> {
    let mut headers = Vec::new();
    let mut visited = BTreeSet::new();
    let mut current = root.header;

    while visited.insert(current) {
        headers.push(current);
        let Some(next) = next_cfg_chain_header(proto, cfg, branch_by_header, current, &visited)
        else {
            break;
        };
        current = next;
    }

    headers
}

fn next_cfg_chain_header(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    header: BlockRef,
    visited: &BTreeSet<BlockRef>,
) -> Option<BlockRef> {
    let (truthy_target, falsy_target) = truthy_falsy_targets(proto, cfg, header)?;
    let mut next_headers = [truthy_target, falsy_target]
        .into_iter()
        .filter(|target| {
            branch_by_header.contains_key(target)
                && !visited.contains(target)
                && cfg.preds[target.index()].len() <= 1
        })
        .collect::<Vec<_>>();
    next_headers.sort();
    next_headers.dedup();

    match next_headers.as_slice() {
        [next] => Some(*next),
        _ => None,
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
            if target == header {
                decrement_target_count(&mut external_targets, target);
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

fn decrement_target_count(targets: &mut BTreeMap<BlockRef, usize>, target: BlockRef) {
    let count = targets
        .get_mut(&target)
        .expect("previous branch target must remain counted");
    *count -= 1;
    if *count == 0 {
        targets.remove(&target);
    }
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
