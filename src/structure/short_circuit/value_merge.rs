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

use crate::structure::{BlockRef, Cfg, DataflowFacts, DominatorTree, GraphFacts, PhiCandidate};
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
    let mut candidates = Vec::new();
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

        let Some(root) = value_merge_root(dom_tree, branch_by_header, phi) else {
            continue;
        };
        let Some(builder) = ValueMergeDagBuilder::new(&build_ctx, root.header, phi) else {
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
}

struct ValueMergeDagBuilder<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    dataflow: &'a DataflowFacts,
    branch_by_header: &'a BTreeMap<BlockRef, &'a BranchCandidate>,
    dom_tree: &'a DominatorTree,
    root: BlockRef,
    phi: &'a PhiCandidate,
    nodes: Vec<ShortCircuitNode>,
    node_by_header: BTreeMap<BlockRef, ShortCircuitNodeRef>,
    visiting: BTreeSet<BlockRef>,
    blocks: BTreeSet<BlockRef>,
    value_leaves: BTreeSet<BlockRef>,
    value_leaf_predecessors: BTreeSet<BlockRef>,
    phi_predecessors: BTreeSet<BlockRef>,
    phi_leaf_values: BTreeSet<crate::structure::SsaValue>,
}

impl<'a> ValueMergeDagBuilder<'a> {
    fn new(ctx: &'a ValueMergeBuildCtx<'a>, root: BlockRef, phi: &'a PhiCandidate) -> Option<Self> {
        let phi_value = crate::structure::SsaValue::Phi(phi.id);
        if phi.incoming.iter().any(|incoming| {
            incoming.pred.is_none() || ctx.dataflow.value_contains(incoming.value, phi_value)
        }) {
            return None;
        }

        let phi_predecessors = phi
            .incoming
            .iter()
            .filter_map(|incoming| incoming.pred)
            .collect();
        let phi_leaf_values = phi
            .incoming
            .iter()
            .flat_map(|incoming| ctx.dataflow.leaf_values(incoming.value))
            .collect();

        Some(Self {
            proto: ctx.proto,
            cfg: ctx.cfg,
            dataflow: ctx.dataflow,
            branch_by_header: ctx.branch_by_header,
            dom_tree: ctx.dom_tree,
            root,
            phi,
            nodes: Vec::new(),
            node_by_header: BTreeMap::new(),
            visiting: BTreeSet::new(),
            blocks: BTreeSet::new(),
            value_leaves: BTreeSet::new(),
            value_leaf_predecessors: BTreeSet::new(),
            phi_predecessors,
            phi_leaf_values,
        })
    }

    fn build(mut self) -> Option<ShortCircuitCandidate> {
        if !self.branch_by_header.contains_key(&self.root)
            || self.phi.block == self.root
            || !self.dom_tree.dominates(self.root, self.phi.block)
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

    fn build_node(&mut self, header: BlockRef) -> Option<ShortCircuitNodeRef> {
        if let Some(node_ref) = self.node_by_header.get(&header).copied() {
            return Some(node_ref);
        }
        if !self.visiting.insert(header) {
            return None;
        }

        let _candidate = self.branch_by_header.get(&header)?;
        if !self.dom_tree.dominates(self.root, header)
            || !self.cfg.can_reach(header, self.phi.block)
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
            let incoming = self
                .phi
                .incoming
                .iter()
                .find(|incoming| incoming.pred == Some(from_header))?;
            if matches!(incoming.value, crate::structure::SsaValue::Entry(_)) {
                return None;
            }
            self.value_leaves.insert(from_header);
            self.value_leaf_predecessors.insert(from_header);
            return Some(ShortCircuitTarget::Value(from_header));
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
            |block| block != self.phi.block && self.cfg.can_reach(block, self.phi.block),
            |block, _| {
                terminal = self.value_leaf_carrier(block);
                terminal.is_some()
            },
        )?;
        match followed {
            LinearFollowTarget::Header(header) => {
                Some(ShortCircuitTarget::Node(self.build_node(header)?))
            }
            LinearFollowTarget::Terminal(block) => {
                let (carriers, predecessor) = terminal?;
                self.blocks.extend(carriers);
                self.blocks.insert(block);
                self.value_leaves.insert(block);
                self.value_leaf_predecessors.insert(predecessor);
                Some(ShortCircuitTarget::Value(block))
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
                    .phi
                    .incoming
                    .iter()
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

        let leaf_values = self
            .value_leaves
            .iter()
            .flat_map(|leaf| {
                self.dataflow
                    .leaf_values(self.dataflow.block_exit_value(*leaf, self.phi.reg))
            })
            .collect::<BTreeSet<_>>();
        leaf_values == self.phi_leaf_values
    }
}
