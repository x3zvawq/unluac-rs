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

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::cfg::{BlockRef, Cfg, DataflowFacts, DominatorTree, GraphFacts, PhiCandidate};
use crate::transformer::{LoweredProto, Reg};

use super::super::common::{
    BranchCandidate, ShortCircuitCandidate, ShortCircuitExit, ShortCircuitNode,
    ShortCircuitNodeRef, ShortCircuitTarget,
};
use super::super::phi_facts::short_circuit_phi_facts;
use super::shared::{
    LinearFollowCtx, LinearFollowTarget, block_writes_reg, is_reducible_candidate,
    prefer_short_circuit_candidate, short_circuit_nodes_are_acyclic, truthy_falsy_targets,
};

pub(super) fn analyze_value_merge_candidates(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
    branch_candidates: &[BranchCandidate],
) -> Vec<ShortCircuitCandidate> {
    let mut best_by_merge = BTreeMap::<(BlockRef, Reg), ShortCircuitCandidate>::new();
    let dom_tree = &graph_facts.dominator_tree;
    let build_ctx = ValueMergeBuildCtx {
        proto,
        cfg,
        dataflow,
        branch_by_header,
        dom_tree,
    };

    for phi in &dataflow.phi_candidates {
        if phi.incoming.len() < 2 {
            continue;
        }

        let merge_reachability = MergeReachability::for_merge(cfg, phi.block);

        for root in branch_candidates {
            if root.header == phi.block
                || !dom_tree.dominates(root.header, phi.block)
                || !merge_reachability.contains(root.header)
            {
                continue;
            }

            let Some(candidate) = ValueMergeDagBuilder::new(
                &build_ctx,
                root.header,
                phi,
                &merge_reachability,
            )
            .build() else {
                continue;
            };

            let key = (phi.block, phi.reg);
            match best_by_merge.get(&key) {
                Some(existing) if !prefer_short_circuit_candidate(&candidate, existing) => {}
                _ => {
                    best_by_merge.insert(key, candidate);
                }
            }
        }
    }

    best_by_merge.into_values().collect()
}

struct MergeReachability {
    reaches_merge: Vec<bool>,
}

struct ValueMergeBuildCtx<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    dataflow: &'a DataflowFacts,
    branch_by_header: &'a BTreeMap<BlockRef, &'a BranchCandidate>,
    dom_tree: &'a DominatorTree,
}

impl MergeReachability {
    fn for_merge(cfg: &Cfg, merge: BlockRef) -> Self {
        let mut reaches_merge = vec![false; cfg.blocks.len()];
        let mut worklist = VecDeque::from([merge]);

        while let Some(block) = worklist.pop_front() {
            if !cfg.reachable_blocks.contains(&block) || std::mem::replace(&mut reaches_merge[block.index()], true) {
                continue;
            }

            for edge_ref in &cfg.preds[block.index()] {
                let pred = cfg.edges[edge_ref.index()].from;
                if cfg.reachable_blocks.contains(&pred) && !reaches_merge[pred.index()] {
                    worklist.push_back(pred);
                }
            }
        }

        Self { reaches_merge }
    }

    fn contains(&self, block: BlockRef) -> bool {
        self.reaches_merge.get(block.index()).copied().unwrap_or(false)
    }
}

struct ValueMergeDagBuilder<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    dataflow: &'a DataflowFacts,
    branch_by_header: &'a BTreeMap<BlockRef, &'a BranchCandidate>,
    dom_tree: &'a DominatorTree,
    merge_reachability: &'a MergeReachability,
    root: BlockRef,
    phi: &'a PhiCandidate,
    nodes: Vec<ShortCircuitNode>,
    node_by_header: BTreeMap<BlockRef, ShortCircuitNodeRef>,
    visiting: BTreeSet<BlockRef>,
    blocks: BTreeSet<BlockRef>,
    value_leaves: BTreeSet<BlockRef>,
}

impl<'a> ValueMergeDagBuilder<'a> {
    fn new(
        ctx: &'a ValueMergeBuildCtx<'a>,
        root: BlockRef,
        phi: &'a PhiCandidate,
        merge_reachability: &'a MergeReachability,
    ) -> Self {
        Self {
            proto: ctx.proto,
            cfg: ctx.cfg,
            dataflow: ctx.dataflow,
            branch_by_header: ctx.branch_by_header,
            dom_tree: ctx.dom_tree,
            merge_reachability,
            root,
            phi,
            nodes: Vec::new(),
            node_by_header: BTreeMap::new(),
            visiting: BTreeSet::new(),
            blocks: BTreeSet::new(),
            value_leaves: BTreeSet::new(),
        }
    }

    fn build(mut self) -> Option<ShortCircuitCandidate> {
        if !self.branch_by_header.contains_key(&self.root)
            || self.phi.block == self.root
            || !self.dom_tree.dominates(self.root, self.phi.block)
            || !self.merge_reachability.contains(self.root)
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
        if !self.value_leaves_feed_phi() || !short_circuit_nodes_are_acyclic(&self.nodes, entry) {
            return None;
        }

        let phi_facts =
            short_circuit_phi_facts(self.cfg, self.dataflow, self.root, self.phi.reg, self.phi);
        let reducible = is_reducible_candidate(self.cfg, self.root, &self.blocks);
        Some(ShortCircuitCandidate {
            header: self.root,
            blocks: self.blocks,
            entry,
            nodes: self.nodes,
            exit: ShortCircuitExit::ValueMerge(self.phi.block),
            result_reg: Some(self.phi.reg),
            result_phi_id: Some(self.phi.id),
            entry_defs: phi_facts.entry_defs,
            value_incomings: phi_facts.value_incomings,
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
        if !self.dom_tree.dominates(self.root, header)
            || !self.merge_reachability.contains(header)
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
        if target == self.phi.block {
            self.value_leaves.insert(from_header);
            return Some(ShortCircuitTarget::Value(from_header));
        }

        match (LinearFollowCtx {
            proto: self.proto,
            cfg: self.cfg,
            branch_by_header: self.branch_by_header,
            dom_tree: self.dom_tree,
            root: self.root,
        })
        .follow(
            target,
            |block| block != self.phi.block && self.merge_reachability.contains(block),
            |block, succs| {
                matches!(succs, [succ] if *succ == self.phi.block)
                    && block_writes_reg(self.proto, self.dataflow, self.cfg, block, self.phi.reg)
            },
        )? {
            LinearFollowTarget::Header(header) => {
                Some(ShortCircuitTarget::Node(self.build_node(header)?))
            }
            LinearFollowTarget::Terminal(block) => {
                self.blocks.insert(block);
                self.value_leaves.insert(block);
                Some(ShortCircuitTarget::Value(block))
            }
        }
    }

    fn value_leaves_feed_phi(&self) -> bool {
        let mut incoming_preds = self
            .phi
            .incoming
            .iter()
            .map(|incoming| incoming.pred)
            .collect::<Vec<_>>();
        incoming_preds.sort();
        incoming_preds.dedup();

        let mut leaves = self.value_leaves.iter().copied().collect::<Vec<_>>();
        leaves.sort();
        leaves == incoming_preds
    }
}
