//! 提取结果值合流的短路 DAG 与叶值来源。
//!
//! 消费 branch、Dataflow phi 和共享图事实，向 StructurePlan 发布候选。

use std::collections::{BTreeMap, BTreeSet};

use crate::structure::{
    BlockRef, Cfg, DataflowFacts, DominatorTree, GraphFacts, PhiCandidate, PostDominatorTree,
    SsaValue,
};
use crate::transformer::{CaptureSource, InstrRef, LowInstr, LoweredProto};

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
    // 一次枚举捕获源，避免每个候选沿 phi uses 再扫描同一 CLOSURE 的全部捕获。
    let mut reference_captured_phis = vec![false; dataflow.phi_candidates.len()];
    for (index, instr) in proto.instrs.iter().enumerate() {
        let LowInstr::Closure(closure) = instr else {
            continue;
        };
        for capture in &closure.captures {
            if let CaptureSource::ByReference(reg) = capture.source
                && let SsaValue::Phi(phi) = dataflow.use_value(InstrRef(index), reg)
            {
                reference_captured_phis[phi.index()] = true;
            }
        }
    }
    let build_ctx = ValueMergeBuildCtx {
        reference_captured_phis: &reference_captured_phis,
        proto,
        cfg,
        dataflow,
        branch_by_header,
        dom_tree,
        postdom_tree: &graph_facts.post_dominator_tree,
    };
    let mut candidates = Vec::new();
    let mut node_refs = DenseNodeRefs::new(cfg.blocks.len());
    let operand_entries = operand_entries(cfg, graph_facts, dataflow, branch_by_header);
    for phi in &dataflow.phi_candidates {
        if phi.incoming.len() < 2 {
            continue;
        }
        let Some(root) = value_merge_root(dom_tree, branch_by_header, phi) else {
            continue;
        };
        let operand_entry = operand_entries[root.header.index()];
        for header in std::iter::once(root.header)
            .chain((operand_entry != root.header).then_some(operand_entry))
        {
            if let Some(candidate) =
                ValueMergeDagBuilder::new(&build_ctx, header, phi, &mut node_refs)
                    .and_then(ValueMergeDagBuilder::build)
            {
                candidates.push(candidate);
            }
        }
    }
    candidates
}

/// 比较的单次 phi 输入可以先于外层决策入口完成。沿支配树缓存最早的准备入口，
/// 避免逐候选回溯；实际控制闭合与操作数归属仍由完整候选和 selected owner 证明。
fn operand_entries(
    cfg: &Cfg,
    graph: &GraphFacts,
    dataflow: &DataflowFacts,
    branches: &BTreeMap<BlockRef, &BranchCandidate>,
) -> Vec<BlockRef> {
    let mut entries = (0..cfg.blocks.len()).map(BlockRef).collect::<Vec<_>>();
    let mut order = branches.keys().copied().collect::<Vec<_>>();
    order.sort_unstable_by_key(|block| graph.dominator_tree.preorder_index[block.index()]);
    for block in order {
        let Some(parent) = graph.dominator_tree.parent[block.index()] else {
            continue;
        };
        if !branches.contains_key(&parent) || !graph.post_dominates(block, parent) {
            continue;
        }
        let consumes_operand = dataflow.phi_candidates_in_block(block).iter().any(|phi| {
            // 只排除当前开放的 cell；寄存器之后另作捕获槽，不改变此处临时取值的身份。
            matches!(dataflow.phi_uses[phi.id.index()].as_slice(), [site]
                if cfg.blocks[block.index()].instrs.last() == Some(site.instr)
                    && !dataflow.reference_capture_may_be_open(phi.reg, site.instr)
                    && !dataflow.instr_effects[site.instr.index()].repeats_fixed_use(site.reg))
                && phi.incoming.iter().all(|incoming| match incoming.value {
                    SsaValue::Def(def) => {
                        !dataflow.reference_capture_may_be_open(phi.reg, dataflow.def_instr(def))
                    }
                    _ => !dataflow.reg_is_reference_captured(phi.reg),
                })
                && dataflow.phi_consumer_ids(phi.id).is_empty()
                && phi.incoming.iter().all(|incoming| incoming.pred.is_some())
        });
        if consumes_operand {
            entries[block.index()] = entries[parent.index()];
        }
    }
    entries
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
    reference_captured_phis: &'a [bool],
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
    reference_captured_phis: &'a [bool],
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
            reference_captured_phis: ctx.reference_captured_phis,
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
        let predicate_operand = self.dataflow.phi_uses[self.phi.id.index()].as_slice();
        let predicate_operand = matches!(predicate_operand, [site]
            if self.cfg.blocks[self.cfg.instr_to_block[site.instr.index()].index()].instrs.last() == Some(site.instr)
                && self.cfg.branch_edges(self.cfg.instr_to_block[site.instr.index()]).is_some()
                && self.postdom_tree.dominates(self.cfg.instr_to_block[site.instr.index()], self.phi.block));
        // 编译器可省掉真值已知的中间 TEST，使嵌套 `a and 2 or 0` 只剩一个
        // 判断。若 phi 紧接着被谓词消费，它仍是取值操作数，不是独立语句分支。
        if self.nodes.len() == 1 && !has_header_leaf && !predicate_operand {
            return None;
        }
        if !self.value_leaves_feed_phi() || !short_circuit_nodes_are_acyclic(&self.nodes, entry) {
            return None;
        }

        let phi_facts =
            short_circuit_phi_facts(self.dataflow, self.root, self.phi.reg, &self.value_leaves);
        if self.nodes.len() == 1 && self.value_leaves.contains(&self.root) {
            let predicate = self.cfg.blocks[self.root.index()].instrs.last()?;
            let captured_result = self
                .dataflow
                .reference_capture_may_be_open(self.phi.reg, predicate)
                || self.reference_captured_phis[self.phi.id.index()];
            if captured_result
                && self
                    .dataflow
                    .use_values_at(predicate)
                    .get(self.phi.reg)
                    .is_none()
            {
                // 候选拒绝[PolicyBoundary]：已打开或在合流处捕获的 cell 在直达边保持
                // 旧值，条件又不读取它；保留条件写回，让普通 branch 和 phi carry
                // 恢复同一身份。匿名 Boolean 预写仍可参与取值 DAG，不按槽号曾被捕获
                // 就把无关的后继临时量认作 cell。
                return None;
            }
        }
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
            if matches!(incoming.value, crate::structure::SsaValue::Entry(reg)
                if reg.index() >= usize::from(self.proto.signature.num_params))
            {
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
            |block| {
                // 内嵌取值表达式的字面量臂不是外层 result leaf；继续收集到其
                // 消费谓词，由最终选择证明内部 phi、原写入与单次消费的归属。
                let range = self.cfg.blocks[block.index()].instrs;
                self.proto.instrs[range.start.index()..range.end()]
                    .iter()
                    .all(|instr| {
                        matches!(
                            instr,
                            crate::transformer::LowInstr::LoadNil(_)
                                | crate::transformer::LowInstr::LoadBool(_)
                                | crate::transformer::LowInstr::LoadConst(_)
                                | crate::transformer::LowInstr::LoadInteger(_)
                                | crate::transformer::LowInstr::LoadNumber(_)
                                | crate::transformer::LowInstr::Move(_)
                                | crate::transformer::LowInstr::Jump(_)
                        )
                    })
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
