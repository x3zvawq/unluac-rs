//! 选择并证明值短路判定 DAG；依赖 SSA、phi 与闭合性证据，不负责普通布尔条件；例如筛除结果定义逃逸的 and/or value merge。

use super::*;

pub(super) fn selected_value_decisions(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    loops: &[LoopCandidate],
    residual_transfers: &[ResidualTransferEvidence],
    candidates: &[ShortCircuitCandidate],
) -> Vec<ValueDecisionPlanInput> {
    let safety = ValueDecisionSafetyIndex::new(cfg, dataflow, loops, residual_transfers);
    let mut scratch = ValueDecisionCandidateScratch::new(proto, cfg, dataflow);
    let mut group_by_dag = HashMap::<ValueDecisionDagKey<'_>, usize>::new();
    let mut groups = Vec::<Vec<(usize, &ShortCircuitCandidate)>>::new();
    for (index, candidate) in candidates.iter().enumerate() {
        let (ShortCircuitExit::ValueMerge(merge), Some(_), Some(_), Some(_)) = (
            &candidate.exit,
            candidate.result_phi_id,
            candidate.result_reg,
            candidate.entry_value,
        ) else {
            continue;
        };
        if !candidate.reducible || candidate.nodes.is_empty() || candidate.value_incomings.len() < 2
        {
            continue;
        }
        let key = ValueDecisionDagKey::new(candidate, *merge);
        let next_group = groups.len();
        let group = *group_by_dag.entry(key).or_insert(next_group);
        if group == next_group {
            groups.push(Vec::new());
        }
        groups[group].push((index, candidate));
    }

    let mut selected = vec![None::<(usize, &ShortCircuitCandidate)>; dataflow.phi_candidates.len()];
    for mut group in groups {
        // 同一控制 DAG 最终只能有一个 containment owner。按最终 payload 的 PhiId
        // 顺序寻找首个合法 result，和 arena 原本的稳定胜出顺序一致；控制闭包只证明一次。
        group.sort_by_key(|(index, candidate)| (candidate.result_phi_id, *index));
        let Some((_, representative)) = group.first().copied() else {
            continue;
        };
        let control_closed = value_decision_control_dag_is_closed(
            proto,
            cfg,
            dataflow,
            &safety,
            &mut scratch,
            representative,
        );
        if !control_closed {
            continue;
        }

        for (index, candidate) in group {
            let Some(phi) = candidate.result_phi_id else {
                continue;
            };
            let result_closed = value_decision_result_is_closed(
                cfg,
                dataflow,
                &safety,
                &mut scratch,
                candidate,
                phi,
            );
            if !result_closed {
                continue;
            }
            let score = (
                candidate.nodes.len(),
                candidate.blocks.len(),
                Reverse(index),
            );
            let Some(slot) = selected.get_mut(phi.index()) else {
                continue;
            };
            let replace = slot.as_ref().is_none_or(|(old_index, old)| {
                score > (old.nodes.len(), old.blocks.len(), Reverse(*old_index))
            });
            if replace {
                *slot = Some((index, candidate));
            }
            break;
        }
    }
    selected
        .into_iter()
        .flatten()
        .map(|(_, candidate)| ValueDecisionPlanInput {
            candidate: candidate.clone(),
        })
        .collect()
}

/// 只描述 ValueDecision 的控制身份；result register、phi 与 leaf SSA 映射不参与分组。
///
/// key 借用原 evidence，因此建立 identity 时不会复制 nodes/blocks。`HashMap` 仍会用
/// 完整相等性消解哈希碰撞，用户输入不能靠构造碰撞把不同 DAG 合并。
#[derive(Clone, Copy)]
pub(super) struct ValueDecisionDagKey<'a> {
    header: super::super::BlockRef,
    merge: super::super::BlockRef,
    entry: ShortCircuitNodeRef,
    blocks: &'a BTreeSet<super::super::BlockRef>,
    nodes: &'a [super::super::ShortCircuitNode],
}

impl<'a> ValueDecisionDagKey<'a> {
    fn new(candidate: &'a ShortCircuitCandidate, merge: super::super::BlockRef) -> Self {
        Self {
            header: candidate.header,
            merge,
            entry: candidate.entry,
            blocks: &candidate.blocks,
            nodes: &candidate.nodes,
        }
    }
}

impl PartialEq for ValueDecisionDagKey<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.header == other.header
            && self.merge == other.merge
            && self.entry == other.entry
            && self.blocks == other.blocks
            && self.nodes == other.nodes
    }
}

impl Eq for ValueDecisionDagKey<'_> {}

impl Hash for ValueDecisionDagKey<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.header.hash(state);
        self.merge.hash(state);
        self.entry.hash(state);
        self.blocks.len().hash(state);
        for block in self.blocks {
            block.hash(state);
        }
        self.nodes.len().hash(state);
        for node in self.nodes {
            node.id.hash(state);
            node.header.hash(state);
            node.truthy.hash(state);
            node.falsy.hash(state);
        }
    }
}

/// ValueDecision 候选共享的全图索引。
///
/// 候选筛选只应遍历候选自身覆盖的 block/edge；loop、residual transfer 与 live phi
/// 都在这里按稠密 ID 一次投影，避免候选数量放大全图扫描成本。
pub(super) struct ValueDecisionSafetyIndex {
    forbidden_blocks: Vec<bool>,
    forbidden_edges: Vec<bool>,
    live_phi_edges: Vec<Vec<super::super::PhiId>>,
    phi_sources: Vec<Vec<super::super::PhiId>>,
    loop_input_blocks: Vec<bool>,
}

impl ValueDecisionSafetyIndex {
    fn new(
        cfg: &Cfg,
        dataflow: &DataflowFacts,
        loops: &[LoopCandidate],
        residual_transfers: &[ResidualTransferEvidence],
    ) -> Self {
        let mut forbidden_blocks = vec![true; cfg.blocks.len()];
        let mut loop_input_blocks = vec![false; cfg.blocks.len()];
        for block in &cfg.reachable_blocks {
            if let Some(forbidden) = forbidden_blocks.get_mut(block.index()) {
                *forbidden = false;
            }
        }
        for loop_ in loops {
            if let Some(input) = loop_input_blocks.get_mut(loop_.header.index()) {
                *input = true;
            }
            for block in loop_
                .preheader
                .into_iter()
                .chain(loop_.control_blocks.iter().copied())
            {
                if let Some(forbidden) = forbidden_blocks.get_mut(block.index()) {
                    *forbidden = true;
                }
            }
        }

        let mut forbidden_edges = vec![false; cfg.edges.len()];
        for residual in residual_transfers {
            if !matches!(residual.reason, super::super::GotoReason::IrreducibleFlow)
                && let Some(forbidden) = forbidden_edges.get_mut(residual.edge.index())
            {
                *forbidden = true;
            }
        }
        for loop_ in loops {
            for edge in loop_.backedges.iter().chain(&loop_.continue_edges) {
                if let Some(forbidden) = forbidden_edges.get_mut(edge.index()) {
                    *forbidden = true;
                }
            }
        }

        let mut live_phi_edges = vec![Vec::new(); cfg.edges.len()];
        for phi in &dataflow.phi_candidates {
            if dataflow.phi_is_truly_dead(phi.id) {
                continue;
            }
            for edge in phi.incoming.iter().filter_map(|incoming| incoming.edge) {
                if let Some(phis) = live_phi_edges.get_mut(edge.index()) {
                    phis.push(phi.id);
                }
            }
        }

        let mut phi_sources = vec![Vec::new(); dataflow.phi_candidates.len()];
        for (source_index, consumers) in dataflow.phi_phi_uses.iter().enumerate() {
            if source_index >= dataflow.phi_candidates.len() {
                break;
            }
            let source = super::super::PhiId(source_index);
            for consumer in consumers {
                if let Some(sources) = phi_sources.get_mut(consumer.index()) {
                    sources.push(source);
                }
            }
        }

        Self {
            forbidden_blocks,
            forbidden_edges,
            live_phi_edges,
            phi_sources,
            loop_input_blocks,
        }
    }
}

/// 候选内复用的 epoch scratch；每轮只清空实际使用的队列，不按候选重新分配全图集合。
pub(super) struct ValueDecisionCandidateScratch {
    group_epoch: usize,
    result_epoch: usize,
    block_epochs: Vec<usize>,
    edge_epochs: Vec<usize>,
    common_needed_instr_epochs: Vec<usize>,
    common_dependency_def_epochs: Vec<usize>,
    common_dependency_phi_epochs: Vec<usize>,
    result_needed_instr_epochs: Vec<usize>,
    result_dependency_def_epochs: Vec<usize>,
    result_dependency_phi_epochs: Vec<usize>,
    relevant_def_epochs: Vec<usize>,
    boundary_phi_epochs: Vec<usize>,
    internal_phi_epochs: Vec<usize>,
    reachable_phi_epochs: Vec<usize>,
    escaping_phi_epochs: Vec<usize>,
    relevant_defs: Vec<super::super::DefId>,
    boundary_live_phis: Vec<super::super::PhiId>,
    result_required_instrs: Vec<InstrRef>,
    pending_values: Vec<super::super::SsaValue>,
    pending_phis: Vec<super::super::PhiId>,
    escaping_phis: Vec<super::super::PhiId>,
}

impl ValueDecisionCandidateScratch {
    fn new(proto: &LoweredProto, cfg: &Cfg, dataflow: &DataflowFacts) -> Self {
        Self {
            group_epoch: 0,
            result_epoch: 0,
            block_epochs: vec![0; cfg.blocks.len()],
            edge_epochs: vec![0; cfg.edges.len()],
            common_needed_instr_epochs: vec![0; proto.instrs.len()],
            common_dependency_def_epochs: vec![0; dataflow.defs.len()],
            common_dependency_phi_epochs: vec![0; dataflow.phi_candidates.len()],
            result_needed_instr_epochs: vec![0; proto.instrs.len()],
            result_dependency_def_epochs: vec![0; dataflow.defs.len()],
            result_dependency_phi_epochs: vec![0; dataflow.phi_candidates.len()],
            relevant_def_epochs: vec![0; dataflow.defs.len()],
            boundary_phi_epochs: vec![0; dataflow.phi_candidates.len()],
            internal_phi_epochs: vec![0; dataflow.phi_candidates.len()],
            reachable_phi_epochs: vec![0; dataflow.phi_candidates.len()],
            escaping_phi_epochs: vec![0; dataflow.phi_candidates.len()],
            relevant_defs: Vec::new(),
            boundary_live_phis: Vec::new(),
            result_required_instrs: Vec::new(),
            pending_values: Vec::new(),
            pending_phis: Vec::new(),
            escaping_phis: Vec::new(),
        }
    }

    fn begin_group(&mut self) {
        if self.group_epoch == usize::MAX {
            self.block_epochs.fill(0);
            self.edge_epochs.fill(0);
            self.common_needed_instr_epochs.fill(0);
            self.common_dependency_def_epochs.fill(0);
            self.common_dependency_phi_epochs.fill(0);
            self.relevant_def_epochs.fill(0);
            self.boundary_phi_epochs.fill(0);
            self.group_epoch = 1;
        } else {
            self.group_epoch += 1;
        }
        self.relevant_defs.clear();
        self.boundary_live_phis.clear();
        self.result_required_instrs.clear();
        self.pending_values.clear();
    }

    fn begin_result(&mut self) {
        if self.result_epoch == usize::MAX {
            self.result_needed_instr_epochs.fill(0);
            self.result_dependency_def_epochs.fill(0);
            self.result_dependency_phi_epochs.fill(0);
            self.internal_phi_epochs.fill(0);
            self.reachable_phi_epochs.fill(0);
            self.escaping_phi_epochs.fill(0);
            self.result_epoch = 1;
        } else {
            self.result_epoch += 1;
        }
        self.pending_values.clear();
        self.pending_phis.clear();
        self.escaping_phis.clear();
    }

    fn contains_block(&self, block: super::super::BlockRef) -> bool {
        self.block_epochs.get(block.index()).copied() == Some(self.group_epoch)
    }

    fn common_needs_instr(&self, instr: InstrRef) -> bool {
        self.common_needed_instr_epochs.get(instr.index()).copied() == Some(self.group_epoch)
    }

    fn result_needs_instr(&self, instr: InstrRef) -> bool {
        self.result_needed_instr_epochs.get(instr.index()).copied() == Some(self.result_epoch)
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn value_decision_control_dag_is_closed(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    safety: &ValueDecisionSafetyIndex,
    scratch: &mut ValueDecisionCandidateScratch,
    candidate: &ShortCircuitCandidate,
) -> bool {
    scratch.begin_group();
    let ShortCircuitExit::ValueMerge(continuation) = &candidate.exit else {
        return false;
    };
    let continuation = *continuation;
    for block in &candidate.blocks {
        let Some(forbidden) = safety.forbidden_blocks.get(block.index()) else {
            return false;
        };
        let Some(stamp) = scratch.block_epochs.get_mut(block.index()) else {
            return false;
        };
        if *forbidden {
            return false;
        }
        *stamp = scratch.group_epoch;
    }

    // 同一 DAG 的 loop/control transfer 与 live phi 边界只登记一次；result 校验随后只
    // 投影自己的 phi/leaf 身份，不再重扫 block、edge 和 instruction。
    for block in &candidate.blocks {
        let Some(succs) = cfg.succs.get(block.index()) else {
            return false;
        };
        for edge in succs {
            let Some(stamp) = scratch.edge_epochs.get_mut(edge.index()) else {
                return false;
            };
            if *stamp == scratch.group_epoch {
                continue;
            }
            *stamp = scratch.group_epoch;
            let Some(forbidden) = safety.forbidden_edges.get(edge.index()) else {
                return false;
            };
            let Some(live_phis) = safety.live_phi_edges.get(edge.index()) else {
                return false;
            };
            // residual transfer 是在 value decision 选择前基于裸 CFG 推导的 evidence。
            // 候选的声明 result edge 可能因此看起来像 continue/goto；一旦该 edge
            // 直接落入唯一 continuation 且只携带 result phi，它就应由 decision 端口
            // 消费，不能让较早的 residual 分类反过来否决完整候选。
            let declared_result_edge = cfg
                .edges
                .get(edge.index())
                .is_some_and(|edge| edge.to == continuation);
            if *forbidden && !declared_result_edge {
                return false;
            }
            for phi in live_phis {
                let Some(stamp) = scratch.boundary_phi_epochs.get_mut(phi.index()) else {
                    return false;
                };
                if *stamp != scratch.group_epoch {
                    *stamp = scratch.group_epoch;
                    scratch.boundary_live_phis.push(*phi);
                }
            }
        }
    }

    let entry = candidate.header;
    for node in &candidate.nodes {
        let Some(predicate) = cfg
            .blocks
            .get(node.header.index())
            .and_then(|block| block.instrs.last())
        else {
            return false;
        };
        if node.header != entry {
            let Some(uses) = dataflow.use_values.get(predicate.index()) else {
                return false;
            };
            for value in uses.fixed.values() {
                if !mark_value_decision_common_dependencies(cfg, dataflow, scratch, value) {
                    return false;
                }
            }
        }
    }

    for block in &candidate.blocks {
        let Some(basic_block) = cfg.blocks.get(block.index()) else {
            return false;
        };
        let range = basic_block.instrs;
        for index in range.start.index()..range.end() {
            let instr_ref = InstrRef(index);
            let Some(instr) = proto.instrs.get(index) else {
                return false;
            };
            if *block != entry && matches!(instr, LowInstr::Close(_) | LowInstr::Tbc(_)) {
                return false;
            }
            if *block != entry {
                let Some(defs) = dataflow.instr_defs.get(index) else {
                    return false;
                };
                for def in defs {
                    let Some(stamp) = scratch.relevant_def_epochs.get_mut(def.index()) else {
                        return false;
                    };
                    if *stamp != scratch.group_epoch {
                        *stamp = scratch.group_epoch;
                        scratch.relevant_defs.push(*def);
                    }
                }
            }
            let terminator = range.last() == Some(instr_ref) && instr.is_control_terminator();
            if *block == entry || terminator || scratch.common_needs_instr(instr_ref) {
                continue;
            }
            let pure_dead = dataflow
                .effect_summaries
                .get(index)
                .is_some_and(|summary| summary.tags.is_empty())
                && dataflow.instr_defs.get(index).is_some();
            if !pure_dead {
                scratch.result_required_instrs.push(instr_ref);
            }
        }
    }
    true
}

pub(super) fn value_decision_result_is_closed(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    safety: &ValueDecisionSafetyIndex,
    scratch: &mut ValueDecisionCandidateScratch,
    candidate: &ShortCircuitCandidate,
    result_phi: super::super::PhiId,
) -> bool {
    scratch.begin_result();
    for leaf in &candidate.value_incomings {
        if !mark_value_decision_result_dependencies(cfg, dataflow, scratch, leaf.value) {
            return false;
        }
    }
    if scratch
        .result_required_instrs
        .iter()
        .any(|instr| !scratch.result_needs_instr(*instr))
    {
        return false;
    }
    for index in 0..scratch.boundary_live_phis.len() {
        let phi = scratch.boundary_live_phis[index];
        if phi != result_phi
            && !value_decision_boundary_phi_is_unchanged(cfg, dataflow, safety, scratch, phi)
            && !value_decision_phi_is_internal(cfg, dataflow, scratch, phi, result_phi)
        {
            return false;
        }
    }
    !value_decision_defs_escape(cfg, dataflow, safety, scratch, result_phi)
}

pub(super) fn value_decision_boundary_phi_is_unchanged(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    safety: &ValueDecisionSafetyIndex,
    scratch: &ValueDecisionCandidateScratch,
    phi: super::super::PhiId,
) -> bool {
    let Some(candidate) = dataflow.phi_candidate(phi) else {
        return false;
    };
    if !safety
        .loop_input_blocks
        .get(candidate.block.index())
        .copied()
        .unwrap_or(false)
    {
        return false;
    }
    let mut candidate_value = None;
    let mut saw_candidate_edge = false;
    for incoming in &candidate.incoming {
        let Some(edge) = incoming.edge else {
            continue;
        };
        if scratch.edge_epochs.get(edge.index()).copied() != Some(scratch.group_epoch)
            || cfg
                .edges
                .get(edge.index())
                .is_none_or(|edge| edge.to != candidate.block)
        {
            continue;
        }
        saw_candidate_edge = true;
        match candidate_value {
            None => candidate_value = Some(incoming.value),
            Some(value) if value == incoming.value => {}
            Some(_) => return false,
        }
    }
    saw_candidate_edge
}

pub(super) fn value_decision_phi_is_internal(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    scratch: &mut ValueDecisionCandidateScratch,
    root: super::super::PhiId,
    result_phi: super::super::PhiId,
) -> bool {
    scratch.pending_phis.clear();
    scratch.pending_phis.push(root);
    while let Some(phi) = scratch.pending_phis.pop() {
        if phi == result_phi {
            continue;
        }
        let Some(stamp) = scratch.internal_phi_epochs.get_mut(phi.index()) else {
            return false;
        };
        if *stamp == scratch.result_epoch {
            continue;
        }
        *stamp = scratch.result_epoch;

        let Some(candidate) = dataflow.phi_candidate(phi) else {
            return false;
        };
        if !scratch.contains_block(candidate.block) {
            return false;
        }
        if candidate.incoming.iter().any(|incoming| {
            incoming
                .edge
                .and_then(|edge| cfg.edges.get(edge.index()))
                .is_none_or(|edge| !scratch.contains_block(edge.from))
        }) {
            return false;
        }
        let Some(uses) = dataflow.phi_uses.get(phi.index()) else {
            return false;
        };
        if uses.iter().any(|site| {
            cfg.instr_to_block
                .get(site.instr.index())
                .is_none_or(|block| !scratch.contains_block(*block))
        }) {
            return false;
        }
        let Some(consumers) = dataflow.phi_phi_uses.get(phi.index()) else {
            return false;
        };
        for consumer in consumers {
            if *consumer == result_phi {
                continue;
            }
            let Some(consumer) = dataflow.phi_candidate(*consumer) else {
                return false;
            };
            if !scratch.contains_block(consumer.block) {
                return false;
            }
            scratch.pending_phis.push(consumer.id);
        }
    }
    true
}

pub(super) fn value_decision_defs_escape(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    safety: &ValueDecisionSafetyIndex,
    scratch: &mut ValueDecisionCandidateScratch,
    result_phi: super::super::PhiId,
) -> bool {
    for def in &scratch.relevant_defs {
        let Some(uses) = dataflow.def_uses.get(def.index()) else {
            return true;
        };
        if uses.iter().any(|site| {
            cfg.instr_to_block
                .get(site.instr.index())
                .is_none_or(|block| !scratch.contains_block(*block))
        }) {
            return true;
        }
        if let Some(phis) = dataflow.def_phi_uses.get(def.index()) {
            scratch.pending_phis.extend(phis.iter().copied());
        }
    }

    while let Some(phi) = scratch.pending_phis.pop() {
        if phi == result_phi {
            continue;
        }
        let Some(stamp) = scratch.reachable_phi_epochs.get_mut(phi.index()) else {
            return true;
        };
        if *stamp == scratch.result_epoch {
            continue;
        }
        *stamp = scratch.result_epoch;

        let Some(uses) = dataflow.phi_uses.get(phi.index()) else {
            return true;
        };
        if uses.iter().any(|site| {
            cfg.instr_to_block
                .get(site.instr.index())
                .is_none_or(|block| !scratch.contains_block(*block))
        }) {
            let Some(escaping) = scratch.escaping_phi_epochs.get_mut(phi.index()) else {
                return true;
            };
            *escaping = scratch.result_epoch;
            scratch.escaping_phis.push(phi);
        }

        let Some(consumers) = dataflow.phi_phi_uses.get(phi.index()) else {
            return true;
        };
        scratch.pending_phis.extend(consumers.iter().copied());
    }

    // 从真实越界 use 反向标记所有可到达它的 phi。result phi 是 ValueDecision 的
    // 显式结果端口，传播到它即终止，不能把端口外的正常使用误判为内部 def 泄漏。
    while let Some(phi) = scratch.escaping_phis.pop() {
        let Some(sources) = safety.phi_sources.get(phi.index()) else {
            return true;
        };
        for source in sources {
            if *source == result_phi
                || scratch.reachable_phi_epochs.get(source.index()).copied()
                    != Some(scratch.result_epoch)
            {
                continue;
            }
            let Some(escaping) = scratch.escaping_phi_epochs.get_mut(source.index()) else {
                return true;
            };
            if *escaping != scratch.result_epoch {
                *escaping = scratch.result_epoch;
                scratch.escaping_phis.push(*source);
            }
        }
    }

    scratch.relevant_defs.iter().any(|def| {
        dataflow
            .def_phi_uses
            .get(def.index())
            .into_iter()
            .flatten()
            .any(|phi| {
                *phi != result_phi
                    && scratch.escaping_phi_epochs.get(phi.index()).copied()
                        == Some(scratch.result_epoch)
            })
    })
}

pub(super) fn mark_value_decision_common_dependencies(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    scratch: &mut ValueDecisionCandidateScratch,
    root: super::super::SsaValue,
) -> bool {
    mark_value_decision_dependencies(
        cfg,
        dataflow,
        &scratch.block_epochs,
        scratch.group_epoch,
        &mut scratch.common_needed_instr_epochs,
        &mut scratch.common_dependency_def_epochs,
        &mut scratch.common_dependency_phi_epochs,
        scratch.group_epoch,
        &mut scratch.pending_values,
        root,
    )
}

pub(super) fn mark_value_decision_result_dependencies(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    scratch: &mut ValueDecisionCandidateScratch,
    root: super::super::SsaValue,
) -> bool {
    mark_value_decision_dependencies(
        cfg,
        dataflow,
        &scratch.block_epochs,
        scratch.group_epoch,
        &mut scratch.result_needed_instr_epochs,
        &mut scratch.result_dependency_def_epochs,
        &mut scratch.result_dependency_phi_epochs,
        scratch.result_epoch,
        &mut scratch.pending_values,
        root,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn mark_value_decision_dependencies(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    block_epochs: &[usize],
    block_epoch: usize,
    needed_instr_epochs: &mut [usize],
    dependency_def_epochs: &mut [usize],
    dependency_phi_epochs: &mut [usize],
    dependency_epoch: usize,
    pending_values: &mut Vec<super::super::SsaValue>,
    root: super::super::SsaValue,
) -> bool {
    pending_values.clear();
    pending_values.push(root);
    while let Some(value) = pending_values.pop() {
        match value {
            super::super::SsaValue::Entry(_) => {}
            super::super::SsaValue::Def(def) => {
                let Some(stamp) = dependency_def_epochs.get_mut(def.index()) else {
                    return false;
                };
                if *stamp == dependency_epoch {
                    continue;
                }
                *stamp = dependency_epoch;
                let Some(definition) = dataflow.defs.get(def.index()) else {
                    return false;
                };
                if block_epochs.get(definition.block.index()).copied() != Some(block_epoch) {
                    continue;
                }
                let Some(needed) = needed_instr_epochs.get_mut(definition.instr.index()) else {
                    return false;
                };
                *needed = dependency_epoch;
                if let Some(uses) = dataflow.use_values.get(definition.instr.index()) {
                    pending_values.extend(uses.fixed.values());
                }
            }
            super::super::SsaValue::Phi(phi) => {
                let Some(stamp) = dependency_phi_epochs.get_mut(phi.index()) else {
                    return false;
                };
                if *stamp == dependency_epoch {
                    continue;
                }
                *stamp = dependency_epoch;
                let Some(phi) = dataflow.phi_candidate(phi) else {
                    return false;
                };
                // 候选入口上的 phi 是显式 RegionInput。继续展开它的历史
                // incoming 不仅越过当前控制域，也会让连续 value-decision
                // 沿整条 SSA 链重复回溯。
                if block_epochs.get(phi.block.index()).copied() != Some(block_epoch)
                    || phi.incoming.iter().any(|incoming| {
                        incoming
                            .edge
                            .and_then(|edge| cfg.edges.get(edge.index()))
                            .is_none_or(|edge| {
                                block_epochs.get(edge.from.index()).copied() != Some(block_epoch)
                            })
                    })
                {
                    continue;
                }
                pending_values.extend(phi.incoming.iter().map(|incoming| incoming.value));
            }
        }
    }
    true
}
