//! 这个文件负责“值合流型”短路 DAG 提取。
//!
//! 它解决的是 `local x = a and b or c`、`local y = (a and b) or (c and d)` 这类
//! 最终在 merge block 合成一个值的短路形状。这里会把 `phi -> 叶子 defs` 的来源
//! 直接前移成 `StructureFacts`，避免 HIR 再回头拆 `phi.incoming`。
//!
//! 它依赖 branch 骨架、Dataflow phi 和共享短路跟随规则，只负责产出值合流候选与
//! merge 前的来源事实；它不会越权决定最终是 `a and b or c`、`if + assign` 还是
//! generic phi 物化。
//!
//! 例子：
//! - `local x = a and b or c` 会产出一个 `merge=#... result_reg=x` 的 value-merge 候选
//! - `local y = (a and b) or (c and d)` 会允许多个失败路径汇到同一 merge，而不是强行
//!   压回线性链
//! - 如果某个判断链里存在回边或 merge 不受 root 支配，这里会直接放弃候选
//! - 候选 root 只从 merge 的严格支配祖先中枚举，并在构建完整 DAG 前排除首跳
//!   已不可能汇入当前 phi 的分支，避免大函数中的交叉扫描

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
    block_writes_reg, is_reducible_candidate, short_circuit_nodes_are_acyclic,
    truthy_falsy_targets,
};

pub(super) fn analyze_value_merge_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
) -> Vec<ShortCircuitCandidate> {
    let dom_tree = &graph_facts.dominator_tree;
    let recursive_phis = recursive_phi_flags(dataflow);
    let build_ctx = ValueMergeBuildCtx {
        proto,
        cfg,
        dataflow,
        branch_by_header,
        dom_tree,
        postdom_tree: &graph_facts.post_dominator_tree,
        recursive_phis: &recursive_phis,
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
    recursive_phis: &'a [bool],
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
    decision_incoming_indices: Vec<usize>,
    value_leaf_values: BTreeMap<BlockRef, Option<SsaValue>>,
}

impl<'a, 'w> ValueMergeDagBuilder<'a, 'w> {
    fn new(
        ctx: &'a ValueMergeBuildCtx<'a>,
        root: BlockRef,
        phi: &'a PhiCandidate,
        node_refs: &'w mut DenseNodeRefs,
    ) -> Option<Self> {
        if phi.incoming.iter().any(|incoming| incoming.pred.is_none()) {
            return None;
        }
        if ctx.recursive_phis[phi.id.index()]
            && !phi
                .incoming
                .iter()
                .any(|incoming| incoming.value == SsaValue::Phi(phi.id))
        {
            return None;
        }
        let decision_incoming_indices = phi
            .incoming
            .iter()
            .enumerate()
            .filter_map(|(index, incoming)| {
                (incoming.value != SsaValue::Phi(phi.id)).then_some(index)
            })
            .collect::<Vec<_>>();
        if decision_incoming_indices.len() < 2 {
            return None;
        }
        let phi_predecessors = decision_incoming_indices
            .iter()
            .filter_map(|index| phi.incoming[*index].pred)
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
            decision_incoming_indices,
        })
    }

    fn build(mut self) -> Option<ShortCircuitCandidate> {
        if !self.branch_by_header.contains_key(&self.root)
            || self.phi.block == self.root
            || !self.dom_tree.dominates(self.root, self.phi.block)
        {
            return None;
        }

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
            let incoming = self
                .decision_incomings()
                .find(|incoming| incoming.pred == Some(from_header))?;
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
            |block, _| {
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
        if !block_writes_reg(self.proto, self.dataflow, self.cfg, leaf, self.phi.reg)
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
                let incoming = self
                    .decision_incomings()
                    .find(|incoming| incoming.pred == Some(current))?;
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
        self.decision_incoming_indices
            .iter()
            .map(|index| &self.phi.incoming[*index])
    }
}

enum ResolvedValueTarget {
    Final(ShortCircuitTarget),
    Header(BlockRef),
}

/// Phi incoming 依赖若能回到自身，该 phi 就不是可安全展开的 value-merge 叶。
/// 一次 SCC 标记替代为每个候选重复遍历整条历史 phi 链。
fn recursive_phi_flags(dataflow: &DataflowFacts) -> Vec<bool> {
    let phi_count = dataflow.phi_candidates.len();
    let mut visited = vec![false; phi_count];
    let mut postorder = Vec::with_capacity(phi_count);

    for root in dataflow.phi_candidates.iter().map(|phi| phi.id) {
        let mut pending = vec![(root, false)];
        while let Some((phi_id, expanded)) = pending.pop() {
            if expanded {
                postorder.push(phi_id);
                continue;
            }
            if std::mem::replace(&mut visited[phi_id.index()], true) {
                continue;
            }
            pending.push((phi_id, true));
            let phi = &dataflow.phi_candidates[phi_id.index()];
            pending.extend(
                phi.incoming
                    .iter()
                    .filter_map(|incoming| match incoming.value {
                        SsaValue::Phi(dependency) => Some((dependency, false)),
                        SsaValue::Entry(_) | SsaValue::Def(_) => None,
                    }),
            );
        }
    }

    visited.fill(false);
    let mut recursive = vec![false; phi_count];
    for root in postorder.into_iter().rev() {
        if visited[root.index()] {
            continue;
        }
        let mut component = Vec::new();
        let mut pending = vec![root];
        while let Some(phi_id) = pending.pop() {
            if std::mem::replace(&mut visited[phi_id.index()], true) {
                continue;
            }
            component.push(phi_id);
            pending.extend(dataflow.phi_consumer_ids(phi_id).iter().copied());
        }
        let is_recursive = component.len() > 1
            || dataflow.phi_candidates[root.index()]
                .incoming
                .iter()
                .any(|incoming| incoming.value == SsaValue::Phi(root));
        if is_recursive {
            for phi_id in component {
                recursive[phi_id.index()] = true;
            }
        }
    }
    recursive
}
