//! 提取在 merge block 合成结果值的短路 DAG，并发布叶值来源。
//!
//! 消费 branch 骨架、Dataflow phi 与共享图规则，将 incoming 关系前移为
//! StructureFacts；最终表达式或赋值语法仍由 HIR 决定。
//! 例如 (a and b) or (c and d) 可以共享 continuation，无须压成线性条件链；
//! 递归 phi 的身份由 Dataflow 提供，不在本层重算。

use std::collections::{BTreeMap, BTreeSet};

use crate::structure::{
    BlockRef, Cfg, DataflowFacts, DominatorTree, GraphFacts, PhiCandidate, PostDominatorTree,
    SsaValue,
};
use crate::transformer::LoweredProto;

use super::super::common::{
    BranchCandidate, ShortCircuitCandidate, ShortCircuitExit, ShortCircuitNode,
    ShortCircuitNodeRef, ShortCircuitTarget,
};
use super::super::phi_facts::short_circuit_phi_facts;
use super::shared::{
    LinearFollowCtx, LinearFollowTarget, block_has_ignore_call, block_is_passthrough,
    is_reducible_candidate, short_circuit_nodes_are_acyclic, truthy_falsy_targets,
};

pub(super) fn analyze_value_merge_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
) -> Vec<ShortCircuitCandidate> {
    let dom_tree = &graph_facts.dominator_tree;
    let build_ctx = ValueMergeBuildCtx {
        proto,
        cfg,
        dataflow,
        branch_by_header,
        dom_tree,
        postdom_tree: &graph_facts.post_dominator_tree,
    };
    let mut candidates = Vec::new();
    let mut node_refs = DenseNodeRefs::new(cfg.blocks.len());
    for phi in &dataflow.phi_candidates {
        if phi.incoming.len() < 2 {
            continue;
        }
        let Some(root) = value_merge_root(dom_tree, branch_by_header, phi) else {
            continue;
        };
        let Some(builder) = ValueMergeDagBuilder::new(&build_ctx, root.header, phi, &mut node_refs)
        else {
            continue;
        };
        let Some(candidate) = builder.build() else {
            continue;
        };
        candidates.push(candidate);
    }
    candidates
}

fn value_merge_root<'a>(
    dom_tree: &DominatorTree,
    branch_by_header: &'a BTreeMap<BlockRef, &'a BranchCandidate>,
    phi: &PhiCandidate,
) -> Option<&'a BranchCandidate> {
    phi.incoming
        .iter()
        .all(|incoming| incoming.pred.is_some())
        .then_some(())?;
    let root = dom_tree.parent[phi.block.index()]?;
    branch_by_header.get(&root).copied()
}

struct ValueMergeBuildCtx<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    dataflow: &'a DataflowFacts,
    branch_by_header: &'a BTreeMap<BlockRef, &'a BranchCandidate>,
    dom_tree: &'a DominatorTree,
    postdom_tree: &'a PostDominatorTree,
}

struct DenseNodeRefs {
    epochs: Vec<u32>,
    refs: Vec<ShortCircuitNodeRef>,
    next_epoch: u32,
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

struct ValueMergeDagBuilder<'a, 'w> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    dataflow: &'a DataflowFacts,
    branch_by_header: &'a BTreeMap<BlockRef, &'a BranchCandidate>,
    dom_tree: &'a DominatorTree,
    postdom_tree: &'a PostDominatorTree,
    root: BlockRef,
    phi: &'a PhiCandidate,
    nodes: Vec<ShortCircuitNode>,
    branch_targets: Vec<(BlockRef, BlockRef)>,
    node_refs: &'w mut DenseNodeRefs,
    node_epoch: u32,
    blocks: BTreeSet<BlockRef>,
    value_leaves: BTreeSet<BlockRef>,
    value_leaf_predecessors: BTreeSet<BlockRef>,
    phi_predecessors: BTreeSet<BlockRef>,
    value_leaf_values: BTreeMap<BlockRef, Option<SsaValue>>,
}

impl<'a, 'w> ValueMergeDagBuilder<'a, 'w> {
    fn new(
        ctx: &'a ValueMergeBuildCtx<'a>,
        root: BlockRef,
        phi: &'a PhiCandidate,
        node_refs: &'w mut DenseNodeRefs,
    ) -> Option<Self> {
        // root 已由 value_merge_root 选为 merge 的严格支配父分支，并排除了 Entry 输入。
        if ctx.dataflow.phi_graph.is_recursive(phi.id)
            && !phi
                .incoming
                .iter()
                .any(|incoming| incoming.value == SsaValue::Phi(phi.id))
        {
            return None;
        }
        let decision_incomings = phi
            .incoming
            .iter()
            .filter(|incoming| incoming.value != SsaValue::Phi(phi.id));
        if decision_incomings.clone().count() < 2 {
            return None;
        }
        let phi_predecessors = decision_incomings
            .filter_map(|incoming| incoming.pred)
            .collect();
        let node_epoch = node_refs.begin();

        Some(Self {
            proto: ctx.proto,
            cfg: ctx.cfg,
            dataflow: ctx.dataflow,
            branch_by_header: ctx.branch_by_header,
            dom_tree: ctx.dom_tree,
            postdom_tree: ctx.postdom_tree,
            root,
            phi,
            nodes: Vec::new(),
            branch_targets: Vec::new(),
            node_refs,
            node_epoch,
            blocks: BTreeSet::new(),
            value_leaves: BTreeSet::new(),
            value_leaf_predecessors: BTreeSet::new(),
            phi_predecessors,
            value_leaf_values: BTreeMap::new(),
        })
    }

    fn build(mut self) -> Option<ShortCircuitCandidate> {
        let entry = self.build_nodes()?;
        if entry != ShortCircuitNodeRef(0) {
            return None;
        }
        if self.value_leaves.len() < 2 {
            return None;
        }

        let has_header_leaf = self
            .value_leaves
            .iter()
            .any(|leaf| self.node_refs.get(*leaf, self.node_epoch).is_some());
        if self.nodes.len() == 1 && !has_header_leaf {
            return None;
        }
        if !self.value_leaves_feed_phi() || !short_circuit_nodes_are_acyclic(&self.nodes, entry) {
            return None;
        }

        let phi_facts =
            short_circuit_phi_facts(self.dataflow, self.root, self.phi.reg, &self.value_leaves);
        let reducible = is_reducible_candidate(self.cfg, self.root, &self.blocks);
        Some(ShortCircuitCandidate {
            header: self.root,
            blocks: self.blocks,
            entry,
            nodes: self.nodes,
            exit: ShortCircuitExit::ValueMerge(self.phi.block),
            result_reg: Some(self.phi.reg),
            result_phi_id: Some(self.phi.id),
            entry_value: Some(phi_facts.entry_value),
            value_incomings: phi_facts.value_incomings,
            reducible,
        })
    }

    fn reserve_node(&mut self, header: BlockRef) -> Option<(ShortCircuitNodeRef, bool)> {
        if let Some(node_ref) = self.node_refs.get(header, self.node_epoch) {
            return Some((node_ref, false));
        }

        let _candidate = self.branch_by_header.get(&header)?;
        if !self.dom_tree.dominates(self.root, header)
            || !self.postdom_tree.dominates(self.phi.block, header)
        {
            return None;
        }

        let (truthy_block, falsy_block) = truthy_falsy_targets(self.proto, self.cfg, header)?;
        let id = ShortCircuitNodeRef(self.nodes.len());
        self.node_refs.insert(header, id, self.node_epoch);
        self.blocks.insert(header);
        self.nodes.push(ShortCircuitNode {
            id,
            header,
            truthy: ShortCircuitTarget::Value(header),
            falsy: ShortCircuitTarget::Value(header),
        });
        self.branch_targets.push((truthy_block, falsy_block));

        Some((id, true))
    }

    fn build_nodes(&mut self) -> Option<ShortCircuitNodeRef> {
        let (entry, _) = self.reserve_node(self.root)?;
        // 显式 frame 保留旧实现 truthy-first 的编号顺序，同时让 DAG 深度不再占用
        // Rust 调用栈；共享节点在 reserve 时直接复用稠密 node id。
        let mut pending = vec![(entry, 0u8)];

        while !pending.is_empty() {
            let frame_index = pending.len() - 1;
            let (node_ref, arm) = pending[frame_index];
            if arm == 2 {
                pending.pop();
                continue;
            }
            pending[frame_index].1 += 1;
            let header = self.nodes.get(node_ref.index())?.header;
            let (truthy_block, falsy_block) = *self.branch_targets.get(node_ref.index())?;
            let target = if arm == 0 { truthy_block } else { falsy_block };
            let resolved = self.resolve_value_target(header, target)?;
            let target = match resolved {
                ResolvedValueTarget::Final(target) => target,
                ResolvedValueTarget::Header(header) => {
                    let (child, is_new) = self.reserve_node(header)?;
                    if is_new {
                        pending.push((child, 0));
                    }
                    ShortCircuitTarget::Node(child)
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

    fn resolve_value_target(
        &mut self,
        from_header: BlockRef,
        target: BlockRef,
    ) -> Option<ResolvedValueTarget> {
        if target == self.phi.block {
            let incoming = self.decision_incoming_from(from_header)?;
            if matches!(incoming.value, crate::structure::SsaValue::Entry(_)) {
                return None;
            }
            self.record_value_leaf(from_header, from_header);
            return Some(ResolvedValueTarget::Final(ShortCircuitTarget::Value(
                from_header,
            )));
        }

        let mut terminal = None;
        let followed = (LinearFollowCtx {
            proto: self.proto,
            cfg: self.cfg,
            branch_by_header: self.branch_by_header,
            dom_tree: self.dom_tree,
            root: self.root,
        })
        .follow(
            target,
            |block| block != self.phi.block && self.postdom_tree.dominates(self.phi.block, block),
            |block| {
                terminal = self.value_leaf_carrier(block);
                terminal.is_some()
            },
        )?;
        self.blocks.extend(followed.traversed);
        match followed.target {
            LinearFollowTarget::Header(header) => Some(ResolvedValueTarget::Header(header)),
            LinearFollowTarget::Terminal(block) => {
                let (carriers, predecessor) = terminal?;
                self.blocks.extend(carriers);
                self.blocks.insert(block);
                self.record_value_leaf(block, predecessor);
                Some(ResolvedValueTarget::Final(ShortCircuitTarget::Value(block)))
            }
        }
    }

    /// 允许值叶先经过只携带同一 SSA 值的 jump/phi pad，再进入最终 merge。
    /// carrier 必须是唯一后继、无普通写入的透明块；最终 incoming 还要确实包含
    /// 当前叶值，不能仅凭 CFG 可达性把中途已被覆盖的 def 算进候选。
    fn value_leaf_carrier(&self, leaf: BlockRef) -> Option<(BTreeSet<BlockRef>, BlockRef)> {
        let range = self.cfg.blocks[leaf.index()].instrs;
        if self
            .dataflow
            .last_fixed_def_in_range(self.phi.reg, range.start.index()..range.end())
            .is_none()
            || block_has_ignore_call(self.proto, self.cfg, leaf)
        {
            return None;
        }

        let leaf_value = self.dataflow.block_exit_value(leaf, self.phi.reg);
        let mut current = leaf;
        let mut carriers = BTreeSet::new();
        loop {
            let successor = self.cfg.unique_reachable_successor(current)?;
            if successor == self.phi.block {
                let incoming = self.decision_incoming_from(current)?;
                return self
                    .dataflow
                    .value_contains(incoming.value, leaf_value)
                    .then_some((carriers, current));
            }
            if successor == self.cfg.exit_block
                || !self.dom_tree.dominates(self.root, successor)
                || self.branch_by_header.contains_key(&successor)
                || !block_is_passthrough(self.proto, self.cfg, successor)
                || !carriers.insert(successor)
            {
                return None;
            }
            current = successor;
        }
    }

    fn value_leaves_feed_phi(&self) -> bool {
        if self.value_leaf_predecessors != self.phi_predecessors {
            return false;
        }

        if self.decision_incomings().all(|incoming| {
            incoming
                .pred
                .and_then(|pred| self.value_leaf_values.get(&pred).copied().flatten())
                == Some(incoming.value)
        }) {
            return true;
        }

        let phi_leaf_values = self
            .decision_incomings()
            .flat_map(|incoming| self.dataflow.leaf_values(incoming.value))
            .collect::<BTreeSet<_>>();
        let leaf_values = self
            .value_leaves
            .iter()
            .flat_map(|leaf| {
                self.dataflow
                    .leaf_values(self.dataflow.block_exit_value(*leaf, self.phi.reg))
            })
            .collect::<BTreeSet<_>>();
        leaf_values == phi_leaf_values
    }

    fn record_value_leaf(&mut self, leaf: BlockRef, predecessor: BlockRef) {
        let value = self.dataflow.block_exit_value(leaf, self.phi.reg);
        self.value_leaves.insert(leaf);
        self.value_leaf_predecessors.insert(predecessor);
        self.value_leaf_values
            .entry(predecessor)
            .and_modify(|known| {
                if *known != Some(value) {
                    *known = None;
                }
            })
            .or_insert(Some(value));
    }

    fn decision_incomings(&self) -> impl Iterator<Item = &crate::structure::PhiIncoming> {
        self.phi
            .incoming
            .iter()
            .filter(|incoming| incoming.value != SsaValue::Phi(self.phi.id))
    }

    fn decision_incoming_from(&self, pred: BlockRef) -> Option<&crate::structure::PhiIncoming> {
        // CFG 两侧邻接表保留同一 edge 追加顺序；平行边仍选 phi 中首个非 self 输入。
        self.cfg.succs[pred.index()]
            .iter()
            .filter_map(|&edge| self.dataflow.phi_incoming_for_edge(self.phi.id, edge))
            .find(|incoming| incoming.value != SsaValue::Phi(self.phi.id))
    }
}

enum ResolvedValueTarget {
    Final(ShortCircuitTarget),
    Header(BlockRef),
}
