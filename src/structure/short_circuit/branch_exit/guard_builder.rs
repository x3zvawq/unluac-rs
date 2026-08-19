//! 用显式任务状态构建 guard branch-exit DAG；依赖 CFG/branch candidates 与稠密节点索引，不负责线性链推断；例如解析嵌套 guard 的真假出口。

use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct GuardExitTempNode {
    id: ShortCircuitNodeRef,
    header: BlockRef,
    truthy: GuardExitTempTarget,
    falsy: GuardExitTempTarget,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum GuardExitTempTarget {
    Node(ShortCircuitNodeRef),
    Exit(BlockRef),
}

pub(super) struct GuardBranchExitDagContext<'a> {
    pub(super) proto: &'a LoweredProto,
    pub(super) cfg: &'a Cfg,
    pub(super) graph_facts: &'a GraphFacts,
    pub(super) branch_by_header: &'a BTreeMap<BlockRef, &'a BranchCandidate>,
    pub(super) value_decision_headers: &'a BTreeSet<BlockRef>,
}

pub(super) struct GuardBranchExitDagBuilder<'a, 'w> {
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
    pub(super) fn new(
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

    pub(super) fn build(mut self) -> Option<ShortCircuitCandidate> {
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

    pub(super) fn reserve_node(&mut self, header: BlockRef) -> Option<(ShortCircuitNodeRef, bool)> {
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

    pub(super) fn build_nodes(&mut self) -> Option<ShortCircuitNodeRef> {
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

    pub(super) fn resolve_target(&mut self, target: BlockRef) -> Option<ResolvedGuardTarget> {
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

    pub(super) fn is_exit_target(&self, target: BlockRef) -> bool {
        target != self.cfg.exit_block
            && self.cfg.reachable_blocks.contains(&target)
            && (self.dom_tree.dominates(self.root, target)
                || self.post_dom_tree.dominates(target, self.root))
    }

    pub(super) fn should_include_header(&self, header: BlockRef) -> bool {
        let Some(candidate) = self.branch_by_header.get(&header) else {
            return false;
        };

        let _candidate = candidate;
        header == self.root || !self.post_dom_tree.dominates(header, self.root)
    }
}
