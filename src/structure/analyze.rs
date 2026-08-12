//! 这个文件负责 Structure 层的总调度。
//!
//! 各类候选的提取规则已经拆到独立模块里，避免结构层继续膨胀成单个巨型文件；
//! 这里仅保留“先准备底层事实，再按顺序汇总结构候选”的壳。
//!
//! 它从主 pipeline 的 `DecompileState` 读取 low-IR，依次写回 CFG、GraphFacts、
//! Dataflow 和 StructureFacts；它不会越权恢复 HIR/AST 语法，只负责调度结构层内部
//! 分析并汇总结果。
//!
//! 例子：
//! - 一个 proto 如果同时包含 loop、branch 和 short-circuit 候选，这里会先提 loop/
//!   branch 骨架，再在同一套共享事实上继续推 short-circuit、region、scope 和 goto 约束
//! - 子 proto 会递归走完全相同的结构分析顺序，保证父子层结构事实口径一致

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::hash::{Hash, Hasher};

use crate::decompile::{ControlFlowCaps, DecompileContext, DecompileError, DecompileState};
use crate::structure::{Cfg, CfgGraph, DataflowFacts, EdgeKind, GraphFacts};
use crate::transformer::{InstrRef, LowInstr, LoweredProto};

use super::common::{
    BranchCandidate, BranchKind, BranchRegionFact, BranchValueMergeCandidate, LoopCandidate,
    RegionFact, ResidualTransferEvidence, ScopePlan, ShortCircuitCandidate, ShortCircuitExit,
    ShortCircuitNodeRef, ShortCircuitTarget, StructureFacts,
};
use super::plan::{
    BranchPlanInput, ConditionPlanId, ConditionPlanInput, FinalPlanInput, LoopPlanInput,
    StructureError, UnstructuredPlanData, ValueDecisionPlanInput,
};
use super::short_circuit::{ClosedControlDagEvidence, ConditionArcEvidence};
use super::{
    branch_values, branches, cfg, goto, helpers, loops, phi_facts, plan, regions, scope,
    short_circuit,
};

/// Structure 阶段入口：内部固定推进 CFG、图事实、数据流和结构候选。
pub(crate) fn analyze_structure_stage(
    state: &mut DecompileState,
    context: &DecompileContext<'_>,
) -> Result<(), DecompileError> {
    {
        let _timing = context.timings.scope("cfg");
        cfg::build_cfg_proto(state, context)?;
    }
    {
        let _timing = context.timings.scope("graph-facts");
        cfg::analyze_graph_facts(state, context)?;
    }
    {
        let _timing = context.timings.scope("dataflow");
        cfg::analyze_dataflow(state, context)?;
    }
    {
        let _timing = context.timings.scope("structure-facts");
        analyze_structure(state, context)?;
    }

    Ok(())
}

/// 从已经完成的底层事实读取图与数据流结果，写回结构候选。
pub(crate) fn analyze_structure(
    state: &mut DecompileState,
    context: &DecompileContext<'_>,
) -> Result<(), DecompileError> {
    let lowered = state.require_lowered()?;
    let cfg = state.require_cfg()?;
    let graph_facts = state.require_graph_facts()?;
    let dataflow = state.require_dataflow()?;
    state.structure_facts = Some(analyze_structure_proto(
        &lowered.main,
        &cfg.cfg,
        graph_facts,
        dataflow,
        &cfg.children,
        context.options.dialect.control_flow_caps(),
    )?);
    Ok(())
}

/// 对单个 proto 递归提取结构候选，子 proto 走完全相同的分析顺序。
pub(crate) fn analyze_structure_proto(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    child_cfgs: &[CfgGraph],
    caps: ControlFlowCaps,
) -> Result<StructureFacts, StructureError> {
    let mut loop_candidates = loops::analyze_loops(proto, cfg, graph_facts, dataflow);
    let irreducible_regions = helpers::compute_irreducible_regions(cfg, graph_facts);
    let (branch_candidates, single_pass_fences) = branches::analyze_branches(
        proto,
        cfg,
        graph_facts,
        dataflow,
        &loop_candidates,
        &irreducible_regions,
    );
    let branch_region_facts =
        branches::analyze_branch_regions(cfg, graph_facts, &branch_candidates, &single_pass_fences);
    let short_circuit_candidates = short_circuit::analyze_short_circuits(
        proto,
        cfg,
        graph_facts,
        dataflow,
        &branch_candidates,
    );
    let value_decision_blocks = short_circuit_candidates
        .iter()
        .filter(|candidate| matches!(candidate.exit, ShortCircuitExit::ValueMerge(_)))
        .flat_map(|candidate| candidate.blocks.iter().copied())
        .collect::<BTreeSet<_>>();
    let closed_control_dags = short_circuit::analyze_closed_control_dags(
        short_circuit::ClosedControlDagContext {
            proto,
            cfg,
            graph_facts,
            dataflow,
        },
        &irreducible_regions,
        &loop_candidates,
        &branch_candidates,
        &value_decision_blocks,
    );
    // repeat refinement 只查询 BranchExit；ValueMerge 往往携带最大的 blocks/nodes/leaf
    // payload，把整张 short-circuit 表复制一遍既无语义作用，也会按 phi 放大内存。
    let mut short_circuit_candidates_for_loops = short_circuit_candidates
        .iter()
        .filter(|candidate| matches!(candidate.exit, ShortCircuitExit::BranchExit { .. }))
        .cloned()
        .collect::<Vec<_>>();
    short_circuit_candidates_for_loops.extend(
        closed_control_dags
            .iter()
            .map(|evidence| evidence.candidate.clone()),
    );
    let loop_condition_supplements =
        short_circuit::analyze_cfg_linear_branch_exits(proto, cfg, &branch_candidates);
    loops::refine_short_circuit_repeat_candidates(
        loops::RepeatRefinementInput {
            proto,
            cfg,
            graph_facts,
            dataflow,
            branches: &branch_candidates,
            supplements: &loop_condition_supplements,
        },
        &mut short_circuit_candidates_for_loops,
        &mut loop_candidates,
    );
    loops::assign_continue_edge_ownership(proto, cfg, &branch_candidates, &mut loop_candidates);
    let residual_transfers = goto::analyze_residual_transfers(
        proto,
        cfg,
        &loop_candidates,
        &branch_candidates,
        &irreducible_regions,
    );
    let region_facts = regions::analyze_regions(cfg, &irreducible_regions);
    let branch_value_merge_candidates = branch_values::analyze_branch_value_merges(
        cfg,
        graph_facts,
        dataflow,
        &branch_candidates,
        &short_circuit_candidates,
        &loop_candidates,
    );
    let scope_candidates = scope::analyze_scopes(proto, cfg, graph_facts);
    let input = final_plan_input(
        &branch_candidates,
        &branch_region_facts,
        &branch_value_merge_candidates,
        &loop_candidates,
        &short_circuit_candidates_for_loops,
        &short_circuit_candidates,
        &closed_control_dags,
        &residual_transfers,
        &region_facts,
        &scope_candidates,
        proto,
        cfg,
        dataflow,
        graph_facts,
        cfg.exit_block,
        caps,
    )?;
    let mut plan =
        plan::build_final_structure_plan(proto, cfg, graph_facts, dataflow, caps, input)?;
    let (cleanup_dispositions, tbc_scopes) =
        scope::analyze_cleanup_dispositions(proto, cfg, &plan)?;
    plan.cleanup_dispositions = cleanup_dispositions;
    plan.tbc_scopes = tbc_scopes;
    scope::finalize_label_placements(proto, cfg, &mut plan)?;
    phi_facts::finalize_phi_ownership(cfg, graph_facts, dataflow, &mut plan)?;
    plan::finalize_loop_contracts(proto, cfg, graph_facts, dataflow, &mut plan)?;
    plan::finalize_block_emissions(cfg, &mut plan)?;
    plan::validate_final_structure_plan(proto, cfg, graph_facts, dataflow, &plan)?;
    let children = proto
        .children
        .iter()
        .zip(child_cfgs.iter())
        .zip(graph_facts.children.iter())
        .zip(dataflow.children.iter())
        .enumerate()
        .map(
            |(child_index, (((child_proto, child_cfg), child_graph_facts), child_dataflow))| {
                analyze_structure_proto(
                    child_proto,
                    &child_cfg.cfg,
                    child_graph_facts,
                    child_dataflow,
                    &child_cfg.children,
                    caps,
                )
                .map_err(|error| error.context(format!("child proto #{child_index}")))
            },
        )
        .collect::<Result<Vec<_>, _>>()?;

    Ok(StructureFacts { plan, children })
}

#[allow(clippy::too_many_arguments)]
fn final_plan_input(
    branches: &[BranchCandidate],
    branch_regions: &[BranchRegionFact],
    branch_value_merges: &[BranchValueMergeCandidate],
    loops: &[LoopCandidate],
    condition_candidates: &[ShortCircuitCandidate],
    value_candidates: &[ShortCircuitCandidate],
    closed_control_dags: &[ClosedControlDagEvidence],
    residual_transfers: &[ResidualTransferEvidence],
    regions: &[RegionFact],
    scopes: &[ScopePlan],
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    graph_facts: &GraphFacts,
    exit_block: super::BlockRef,
    caps: ControlFlowCaps,
) -> Result<FinalPlanInput, StructureError> {
    let branch_regions = unique_branch_regions(branch_regions)?;
    let branch_value_merges = unique_branch_value_merges(branch_value_merges)?;
    let (conditions, condition_by_header) = selected_conditions(ConditionSelectionInput {
        proto,
        cfg,
        dataflow,
        loops,
        caps,
        branches,
        candidates: condition_candidates,
        closed_control_dags,
        residual_transfers,
    })?;
    let value_decisions = selected_value_decisions(
        proto,
        cfg,
        dataflow,
        loops,
        residual_transfers,
        value_candidates,
    );

    let branches = branches
        .iter()
        .cloned()
        .map(|mut branch| {
            let condition = condition_by_header.get(&branch.header).copied();
            let condition_ref = condition.and_then(|id| conditions.get(id.index()));
            let frozen_region = branch_regions
                .get(&branch.header)
                .map(|region| (*region).clone());
            let boundary_changed = frozen_region
                .as_ref()
                .is_none_or(|region| region.single_pass_fence.is_none())
                && normalize_branch_condition_boundary(
                    cfg,
                    graph_facts,
                    loops,
                    &mut branch,
                    condition_ref,
                );
            let value_merge = branch
                .merge
                .and_then(|merge| branch_value_merges.get(&(branch.header, merge)))
                .map(|candidate| (*candidate).clone());
            let region = frozen_region
                .filter(|region| !boundary_changed || Some(region.merge) == branch.merge)
                .or_else(|| {
                    branch.merge.map(|merge| {
                        BranchRegionFact::new(graph_facts, branch.header, merge, branch.kind, None)
                    })
                });
            BranchPlanInput {
                region,
                condition,
                value_merge,
                branch,
            }
        })
        .collect();
    let loops = loops
        .iter()
        .cloned()
        .map(|loop_| {
            let condition = required_loop_condition_header(cfg, &loop_)
                .and_then(|header| condition_by_header.get(&header).copied());
            let continuation = loop_continuation(
                proto,
                &loop_,
                condition.and_then(|id| conditions.get(id.index())),
                cfg,
                graph_facts,
                exit_block,
            );
            LoopPlanInput {
                carried_values: loop_.header_value_merges.clone(),
                condition,
                continuation,
                candidate: loop_,
                semantic_continue_edges: BTreeSet::new(),
            }
        })
        .collect();
    let unstructured = regions
        .iter()
        .cloned()
        .map(|fact| UnstructuredPlanData { fact, layout: None })
        .collect();

    Ok(FinalPlanInput {
        branches,
        loops,
        conditions,
        value_decisions,
        scopes: scopes.to_vec(),
        unstructured,
        residual_transfers: residual_transfers.to_vec(),
    })
}

fn normalize_branch_condition_boundary(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    loops: &[LoopCandidate],
    branch: &mut BranchCandidate,
    condition: Option<&ConditionPlanInput>,
) -> bool {
    let Some(condition) = condition.filter(|condition| condition.candidate.nodes.len() > 1) else {
        return false;
    };
    let ShortCircuitExit::BranchExit { truthy, falsy } = condition.candidate.exit else {
        return false;
    };
    if let Some((then_entry, continuation)) =
        loop_guard_boundary(branch.header, truthy, falsy, loops)
    {
        branch.then_entry = then_entry;
        branch.else_entry = None;
        branch.merge = Some(continuation);
        branch.kind = BranchKind::Guard;
        branch.invert_hint = false;
        return true;
    }
    if let Some((then_entry, continuation)) = branch_endpoint_boundary(graph_facts, truthy, falsy) {
        branch.then_entry = then_entry;
        branch.else_entry = None;
        branch.merge = Some(continuation);
        branch.kind = BranchKind::Guard;
        branch.invert_hint = false;
        return true;
    }
    let Some(merge) = branches::find_soft_merge(cfg, graph_facts, branch.header, truthy, falsy)
    else {
        return false;
    };
    if merge == truthy
        || merge == falsy
        || condition.candidate.blocks.contains(&merge)
        || branch.merge.is_some_and(|current| {
            current != truthy && current != falsy && !graph_facts.dominates(merge, current)
        })
    {
        return false;
    }
    branch.then_entry = truthy;
    branch.else_entry = Some(falsy);
    branch.merge = Some(merge);
    branch.kind = BranchKind::IfElse;
    branch.invert_hint = false;
    true
}

fn branch_endpoint_boundary(
    graph_facts: &GraphFacts,
    truthy: super::BlockRef,
    falsy: super::BlockRef,
) -> Option<(super::BlockRef, super::BlockRef)> {
    let truthy_joins_falsy = graph_facts
        .dominance_frontier
        .get(truthy.index())
        .is_some_and(|frontier| frontier.contains(&falsy));
    let falsy_joins_truthy = graph_facts
        .dominance_frontier
        .get(falsy.index())
        .is_some_and(|frontier| frontier.contains(&truthy));
    match (truthy_joins_falsy, falsy_joins_truthy) {
        (true, false) => Some((truthy, falsy)),
        (false, true) => Some((falsy, truthy)),
        (true, true) | (false, false) => None,
    }
}

fn loop_guard_boundary(
    header: super::BlockRef,
    truthy: super::BlockRef,
    falsy: super::BlockRef,
    loops: &[LoopCandidate],
) -> Option<(super::BlockRef, super::BlockRef)> {
    loops
        .iter()
        .filter(|loop_| {
            loop_.condition_header != Some(header)
                && (loop_.kind_hint == super::LoopKindHint::RepeatLike || loop_.header != header)
                && (loop_.blocks.contains(&header) || loop_.body_scope_blocks.contains(&header))
        })
        .filter_map(|loop_| {
            let is_iteration_boundary = |block| {
                block == loop_.header
                    || loop_.continue_target == Some(block)
                    || loop_.control_blocks.contains(&block)
            };
            match (is_iteration_boundary(truthy), is_iteration_boundary(falsy)) {
                (true, false) => Some((
                    (loop_.body_scope_blocks.len(), loop_.blocks.len()),
                    (falsy, truthy),
                )),
                (false, true) => Some((
                    (loop_.body_scope_blocks.len(), loop_.blocks.len()),
                    (truthy, falsy),
                )),
                (true, true) | (false, false) => None,
            }
        })
        .min_by_key(|(score, _)| *score)
        .map(|(_, boundary)| boundary)
}

fn selected_value_decisions(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    loops: &[LoopCandidate],
    residual_transfers: &[ResidualTransferEvidence],
    candidates: &[ShortCircuitCandidate],
) -> Vec<ValueDecisionPlanInput> {
    let dead_phis = dataflow.compute_truly_dead_phis();
    let safety =
        ValueDecisionSafetyIndex::new(cfg, dataflow, loops, residual_transfers, &dead_phis);
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
struct ValueDecisionDagKey<'a> {
    header: super::BlockRef,
    merge: super::BlockRef,
    entry: ShortCircuitNodeRef,
    blocks: &'a BTreeSet<super::BlockRef>,
    nodes: &'a [super::ShortCircuitNode],
}

impl<'a> ValueDecisionDagKey<'a> {
    fn new(candidate: &'a ShortCircuitCandidate, merge: super::BlockRef) -> Self {
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
struct ValueDecisionSafetyIndex {
    forbidden_blocks: Vec<bool>,
    forbidden_edges: Vec<bool>,
    live_phi_edges: Vec<Vec<super::PhiId>>,
    phi_sources: Vec<Vec<super::PhiId>>,
    loop_input_blocks: Vec<bool>,
}

impl ValueDecisionSafetyIndex {
    fn new(
        cfg: &Cfg,
        dataflow: &DataflowFacts,
        loops: &[LoopCandidate],
        residual_transfers: &[ResidualTransferEvidence],
        dead_phis: &BTreeSet<super::PhiId>,
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
            if !matches!(residual.reason, super::GotoReason::IrreducibleFlow)
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
            if dead_phis.contains(&phi.id) {
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
            let source = super::PhiId(source_index);
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
struct ValueDecisionCandidateScratch {
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
    relevant_defs: Vec<super::DefId>,
    boundary_live_phis: Vec<super::PhiId>,
    result_required_instrs: Vec<InstrRef>,
    pending_values: Vec<super::SsaValue>,
    pending_phis: Vec<super::PhiId>,
    escaping_phis: Vec<super::PhiId>,
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

    fn contains_block(&self, block: super::BlockRef) -> bool {
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
fn value_decision_control_dag_is_closed(
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

fn value_decision_result_is_closed(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    safety: &ValueDecisionSafetyIndex,
    scratch: &mut ValueDecisionCandidateScratch,
    candidate: &ShortCircuitCandidate,
    result_phi: super::PhiId,
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

fn value_decision_boundary_phi_is_unchanged(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    safety: &ValueDecisionSafetyIndex,
    scratch: &ValueDecisionCandidateScratch,
    phi: super::PhiId,
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

fn value_decision_phi_is_internal(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    scratch: &mut ValueDecisionCandidateScratch,
    root: super::PhiId,
    result_phi: super::PhiId,
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

fn value_decision_defs_escape(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    safety: &ValueDecisionSafetyIndex,
    scratch: &mut ValueDecisionCandidateScratch,
    result_phi: super::PhiId,
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

fn mark_value_decision_common_dependencies(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    scratch: &mut ValueDecisionCandidateScratch,
    root: super::SsaValue,
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

fn mark_value_decision_result_dependencies(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    scratch: &mut ValueDecisionCandidateScratch,
    root: super::SsaValue,
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
fn mark_value_decision_dependencies(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    block_epochs: &[usize],
    block_epoch: usize,
    needed_instr_epochs: &mut [usize],
    dependency_def_epochs: &mut [usize],
    dependency_phi_epochs: &mut [usize],
    dependency_epoch: usize,
    pending_values: &mut Vec<super::SsaValue>,
    root: super::SsaValue,
) -> bool {
    pending_values.clear();
    pending_values.push(root);
    while let Some(value) = pending_values.pop() {
        match value {
            super::SsaValue::Entry(_) => {}
            super::SsaValue::Def(def) => {
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
            super::SsaValue::Phi(phi) => {
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

fn unique_branch_regions(
    regions: &[BranchRegionFact],
) -> Result<BTreeMap<super::BlockRef, &BranchRegionFact>, StructureError> {
    let mut by_header = BTreeMap::new();
    for region in regions {
        if by_header.insert(region.header, region).is_some() {
            return Err(StructureError::invalid(format!(
                "branch {} has multiple region facts",
                region.header
            )));
        }
    }
    Ok(by_header)
}

fn unique_branch_value_merges(
    candidates: &[BranchValueMergeCandidate],
) -> Result<BTreeMap<(super::BlockRef, super::BlockRef), &BranchValueMergeCandidate>, StructureError>
{
    let mut by_region = BTreeMap::new();
    for candidate in candidates {
        let key = (candidate.header, candidate.merge);
        if by_region.insert(key, candidate).is_some() {
            return Err(StructureError::invalid(format!(
                "branch {} -> {} has multiple value plans",
                candidate.header, candidate.merge
            )));
        }
    }
    Ok(by_region)
}

struct ConditionSelectionInput<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    dataflow: &'a DataflowFacts,
    loops: &'a [LoopCandidate],
    caps: ControlFlowCaps,
    branches: &'a [BranchCandidate],
    candidates: &'a [ShortCircuitCandidate],
    closed_control_dags: &'a [ClosedControlDagEvidence],
    residual_transfers: &'a [ResidualTransferEvidence],
}

fn selected_conditions(
    input: ConditionSelectionInput<'_>,
) -> Result<
    (
        Vec<ConditionPlanInput>,
        BTreeMap<super::BlockRef, ConditionPlanId>,
    ),
    StructureError,
> {
    let ConditionSelectionInput {
        proto,
        cfg,
        dataflow,
        loops,
        caps,
        branches,
        candidates,
        closed_control_dags,
        residual_transfers,
    } = input;
    let edge_actions = preliminary_edge_actions(cfg, dataflow, loops, residual_transfers, caps);
    let mut loops_by_condition_header = vec![Vec::new(); cfg.blocks.len()];
    for (index, loop_) in loops.iter().enumerate() {
        if let Some(header) = required_loop_condition_header(cfg, loop_) {
            loops_by_condition_header[header.index()].push(index);
        }
    }
    let mut condition_arc_workspace = ConditionArcWorkspace::new(cfg.blocks.len());
    let mut condition_safety_workspace = ConditionSafetyWorkspace::new(dataflow);
    let mut selected = BTreeMap::<super::BlockRef, (usize, ConditionPlanInput)>::new();
    for (index, candidate) in candidates.iter().enumerate() {
        if !candidate.reducible || !matches!(candidate.exit, ShortCircuitExit::BranchExit { .. }) {
            continue;
        }
        if condition_crosses_foreign_loop_header(candidate, loops, &loops_by_condition_header) {
            continue;
        }
        let Some(candidate) =
            safe_condition_candidate(cfg, dataflow, candidate, &mut condition_safety_workspace)
        else {
            continue;
        };
        let input = ConditionPlanInput {
            arcs: synthesize_direct_condition_arcs(
                proto,
                cfg,
                &candidate,
                &mut condition_arc_workspace,
            )?
            .unwrap_or_default(),
            candidate: candidate.clone(),
        };
        if input.arcs.is_empty() || !condition_terminal_actions_are_uniform(&input, &edge_actions) {
            continue;
        }
        let score = score_condition(&input, index);
        let replace = selected
            .get(&candidate.header)
            .is_none_or(|(current, old)| score > score_condition(old, *current));
        if replace {
            selected.insert(input.candidate.header, (index, input));
        }
    }
    for (index, evidence) in closed_control_dags.iter().enumerate() {
        if !evidence.candidate.reducible
            || !matches!(evidence.candidate.exit, ShortCircuitExit::BranchExit { .. })
        {
            continue;
        }
        if condition_crosses_foreign_loop_header(
            &evidence.candidate,
            loops,
            &loops_by_condition_header,
        ) {
            continue;
        }
        let Some(candidate) = safe_condition_candidate(
            cfg,
            dataflow,
            &evidence.candidate,
            &mut condition_safety_workspace,
        ) else {
            continue;
        };
        let arcs = if candidate == evidence.candidate {
            evidence.arcs.clone()
        } else {
            synthesize_direct_condition_arcs(proto, cfg, &candidate, &mut condition_arc_workspace)?
                .unwrap_or_default()
        };
        let input = ConditionPlanInput { candidate, arcs };
        if input.arcs.is_empty() || !condition_terminal_actions_are_uniform(&input, &edge_actions) {
            continue;
        }
        let score = score_condition(&input, candidates.len() + index);
        let replace = selected
            .get(&input.candidate.header)
            .is_none_or(|(current, old)| score > score_condition(old, *current));
        if replace {
            selected.insert(input.candidate.header, (candidates.len() + index, input));
        }
    }
    for branch in branches {
        if selected.contains_key(&branch.header) {
            continue;
        }
        if let Some(input) = simple_condition_input(proto, cfg, branch.header) {
            selected.insert(
                branch.header,
                (usize::MAX / 2 + branch.header.index(), input),
            );
        }
    }
    for loop_ in loops {
        let Some(header) = required_loop_condition_header(cfg, loop_) else {
            continue;
        };
        if selected.contains_key(&header) {
            continue;
        }
        if let Some(input) = simple_condition_input(proto, cfg, header) {
            selected.insert(
                header,
                (usize::MAX / 2 + cfg.blocks.len() + header.index(), input),
            );
        }
    }
    selected = compose_adjacent_condition_guards(cfg, dataflow, loops, selected, &edge_actions);
    let mut conditions = Vec::with_capacity(selected.len());
    let mut by_header = BTreeMap::new();
    for (header, (_, condition)) in selected {
        let id = ConditionPlanId(conditions.len());
        conditions.push(condition);
        by_header.insert(header, id);
    }
    Ok((conditions, by_header))
}

fn compose_adjacent_condition_guards(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    loops: &[LoopCandidate],
    selected: BTreeMap<super::BlockRef, (usize, ConditionPlanInput)>,
    edge_actions: &[PreliminaryEdgeAction],
) -> BTreeMap<super::BlockRef, (usize, ConditionPlanInput)> {
    let mut entries = selected
        .into_iter()
        .map(|(header, (score, input))| (header, score, Some(input)))
        .collect::<Vec<_>>();
    let mut by_header = vec![None; cfg.blocks.len()];
    for (index, (header, _, _)) in entries.iter().enumerate() {
        by_header[header.index()] = Some(index);
    }
    let mut absorbed_header = vec![false; cfg.blocks.len()];
    for (header, _, input) in &entries {
        let Some(input) = input else { continue };
        for block in &input.candidate.blocks {
            if block != header {
                absorbed_header[block.index()] = true;
            }
        }
    }
    let mut child_by_parent = vec![None; entries.len()];
    for (index, (header, _, input)) in entries.iter().enumerate() {
        if absorbed_header[header.index()] {
            continue;
        }
        let Some(input) = input else { continue };
        let Some(child) = adjacent_condition_guard(
            cfg,
            dataflow,
            loops,
            input,
            &entries,
            &by_header,
            edge_actions,
        ) else {
            continue;
        };
        child_by_parent[index] = Some(child);
    }
    for parent in 0..entries.len() {
        let Some(child) = child_by_parent[parent] else {
            continue;
        };
        let Some(mut downstream) = entries[child].2.clone() else {
            continue;
        };
        let Some(mut root) = entries[parent].2.take() else {
            continue;
        };
        let _ = compose_condition_guard(&mut root, &mut downstream);
        entries[parent].2 = Some(root);
    }
    entries
        .into_iter()
        .filter_map(|(header, score, input)| input.map(|input| (header, (score, input))))
        .collect()
}

fn adjacent_condition_guard(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    loops: &[LoopCandidate],
    root: &ConditionPlanInput,
    entries: &[(super::BlockRef, usize, Option<ConditionPlanInput>)],
    by_header: &[Option<usize>],
    edge_actions: &[PreliminaryEdgeAction],
) -> Option<usize> {
    let ShortCircuitExit::BranchExit { truthy, falsy } = &root.candidate.exit else {
        return None;
    };
    let mut selected = None;
    for (continuation, other, other_truthy) in [(*truthy, *falsy, false), (*falsy, *truthy, true)] {
        let Some(child) = by_header.get(continuation.index()).copied().flatten() else {
            continue;
        };
        let Some(downstream) = entries.get(child).and_then(|entry| entry.2.as_ref()) else {
            continue;
        };
        let ShortCircuitExit::BranchExit {
            truthy: downstream_truthy,
            falsy: downstream_falsy,
        } = &downstream.candidate.exit
        else {
            continue;
        };
        let downstream_other_truthy = other == *downstream_truthy;
        let actions_match = condition_exit_action(root, other_truthy, edge_actions)
            .zip(condition_exit_action(
                downstream,
                downstream_other_truthy,
                edge_actions,
            ))
            .is_some_and(|(root, downstream)| {
                root.has_continue_evidence == downstream.has_continue_evidence
                    && root.iteration == downstream.iteration
                    && root.phi_inputs == downstream.phi_inputs
            });
        if downstream.candidate.nodes.len() != 1
            || !downstream
                .candidate
                .blocks
                .is_disjoint(&root.candidate.blocks)
            || (!downstream_other_truthy && other != *downstream_falsy)
            || !repeated_loop_break_guard(cfg, dataflow, loops, downstream.candidate.header, other)
            || !actions_match
        {
            continue;
        }
        if selected.replace(child).is_some() {
            return None;
        }
    }
    selected
}

fn repeated_loop_break_guard(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    loops: &[LoopCandidate],
    condition: super::BlockRef,
    repeated: super::BlockRef,
) -> bool {
    let condition_uses = block_condition_uses(cfg, dataflow, condition);
    if condition_uses.is_none() || condition_uses != block_condition_uses(cfg, dataflow, repeated) {
        return false;
    }
    loops.iter().any(|loop_| {
        loop_.body_scope_blocks.contains(&condition)
            && loop_.body_scope_blocks.contains(&repeated)
            && cfg.succs[repeated.index()].iter().any(|edge| {
                let target = cfg.edges[edge.index()].to;
                loop_.exits.contains(&target)
                    || cfg
                        .unique_reachable_successor(target)
                        .is_some_and(|target| loop_.exits.contains(&target))
            })
    })
}

fn block_condition_uses<'a>(
    cfg: &Cfg,
    dataflow: &'a DataflowFacts,
    block: super::BlockRef,
) -> Option<&'a super::SsaRegMap> {
    cfg.branch_edges(block)?;
    let range = cfg.blocks.get(block.index())?.instrs;
    let offset = range.len.checked_sub(1)?;
    dataflow
        .use_values
        .get(range.start.index() + offset)
        .map(|uses| &uses.fixed)
}

fn compose_condition_guard(
    root: &mut ConditionPlanInput,
    downstream: &mut ConditionPlanInput,
) -> bool {
    let (
        ShortCircuitExit::BranchExit {
            truthy: root_truthy,
            falsy: root_falsy,
        },
        ShortCircuitExit::BranchExit {
            truthy: downstream_truthy,
            falsy: downstream_falsy,
        },
    ) = (&root.candidate.exit, &downstream.candidate.exit)
    else {
        return false;
    };
    let (continued_target, other_target, other_block) =
        if *root_truthy == downstream.candidate.header {
            (
                ShortCircuitTarget::TruthyExit,
                ShortCircuitTarget::FalsyExit,
                *root_falsy,
            )
        } else if *root_falsy == downstream.candidate.header {
            (
                ShortCircuitTarget::FalsyExit,
                ShortCircuitTarget::TruthyExit,
                *root_truthy,
            )
        } else {
            return false;
        };
    let final_other = if other_block == *downstream_truthy {
        ShortCircuitTarget::TruthyExit
    } else if other_block == *downstream_falsy {
        ShortCircuitTarget::FalsyExit
    } else {
        return false;
    };
    let offset = root.candidate.nodes.len();
    let downstream_entry = ShortCircuitTarget::Node(ShortCircuitNodeRef(
        offset + downstream.candidate.entry.index(),
    ));
    let rewrite_root_target = |target: &mut ShortCircuitTarget| {
        if *target == continued_target {
            *target = downstream_entry.clone();
        } else if *target == other_target {
            *target = final_other.clone();
        }
    };
    for node in &mut root.candidate.nodes {
        rewrite_root_target(&mut node.truthy);
        rewrite_root_target(&mut node.falsy);
    }
    for arc in &mut root.arcs {
        rewrite_root_target(&mut arc.target);
    }
    for node in &mut downstream.candidate.nodes {
        node.id = ShortCircuitNodeRef(offset + node.id.index());
        offset_condition_target(&mut node.truthy, offset);
        offset_condition_target(&mut node.falsy, offset);
    }
    for arc in &mut downstream.arcs {
        arc.source = ShortCircuitNodeRef(offset + arc.source.index());
        offset_condition_target(&mut arc.target, offset);
    }
    root.candidate
        .blocks
        .append(&mut downstream.candidate.blocks);
    root.candidate.nodes.append(&mut downstream.candidate.nodes);
    root.arcs.append(&mut downstream.arcs);
    root.candidate.exit = downstream.candidate.exit.clone();
    true
}

fn condition_exit_action<'a>(
    condition: &ConditionPlanInput,
    truthy: bool,
    edge_actions: &'a [PreliminaryEdgeAction],
) -> Option<&'a PreliminaryEdgeAction> {
    condition
        .arcs
        .iter()
        .find(|arc| {
            matches!(
                (&arc.target, truthy),
                (ShortCircuitTarget::TruthyExit, true) | (ShortCircuitTarget::FalsyExit, false)
            )
        })
        .and_then(|arc| arc.edges.last())
        .and_then(|edge| edge_actions.get(edge.index()))
}

fn offset_condition_target(target: &mut ShortCircuitTarget, offset: usize) {
    if let ShortCircuitTarget::Node(node) = target {
        *node = ShortCircuitNodeRef(offset + node.index());
    }
}

fn condition_crosses_foreign_loop_header(
    candidate: &ShortCircuitCandidate,
    loops: &[LoopCandidate],
    loops_by_condition_header: &[Vec<usize>],
) -> bool {
    let owner_headers = loops_by_condition_header
        .get(candidate.header.index())
        .into_iter()
        .flatten()
        .filter_map(|index| loops.get(*index))
        .filter(|loop_| {
            candidate.blocks.iter().all(|block| {
                loop_.blocks.contains(block)
                    || loop_.body_scope_blocks.contains(block)
                    || loop_.control_blocks.contains(block)
            })
        })
        .map(|loop_| loop_.header)
        .collect::<BTreeSet<_>>();
    candidate
        .blocks
        .iter()
        .filter(|block| **block != candidate.header)
        .any(|block| {
            loops_by_condition_header
                .get(block.index())
                .into_iter()
                .flatten()
                .filter_map(|index| loops.get(*index))
                .any(|loop_| !owner_headers.contains(&loop_.header))
        })
}

fn score_condition(condition: &ConditionPlanInput, index: usize) -> (usize, usize, Reverse<usize>) {
    (
        condition.candidate.nodes.len(),
        condition.candidate.blocks.len(),
        Reverse(index),
    )
}

fn condition_terminal_actions_are_uniform(
    condition: &ConditionPlanInput,
    edge_actions: &[PreliminaryEdgeAction],
) -> bool {
    let mut truthy = None::<super::EdgeRef>;
    let mut falsy = None::<super::EdgeRef>;
    for arc in &condition.arcs {
        let Some(edge) = arc.edges.last().copied() else {
            return false;
        };
        let slot = match arc.target {
            ShortCircuitTarget::TruthyExit => &mut truthy,
            ShortCircuitTarget::FalsyExit => &mut falsy,
            ShortCircuitTarget::Node(_) => continue,
            ShortCircuitTarget::Value(_) => return false,
        };
        let Some(action) = edge_actions.get(edge.index()) else {
            return false;
        };
        match slot {
            Some(expected) => {
                let Some(expected) = edge_actions.get(expected.index()) else {
                    return false;
                };
                if expected != action || action.goto.is_some() || action.has_continue_evidence {
                    return false;
                }
            }
            None => *slot = Some(edge),
        }
    }
    truthy.is_some() && falsy.is_some()
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PreliminaryEdgeAction {
    goto: Option<super::GotoReason>,
    has_continue_evidence: bool,
    iteration: Option<PreliminaryIteration>,
    phi_inputs: Vec<(super::PhiId, super::SsaValue)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PreliminaryIteration {
    LoopBack(super::BlockRef),
    Continue(super::BlockRef),
    Conflicting,
}

fn preliminary_edge_actions(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    loops: &[LoopCandidate],
    residual_transfers: &[ResidualTransferEvidence],
    caps: ControlFlowCaps,
) -> Vec<PreliminaryEdgeAction> {
    // terminal 一致性会被多个 condition evidence 查询；先按 EdgeRef 稠密登记，避免
    // 每个叶子都重新扫描全部 loop 与 phi incoming。
    let mut actions = cfg
        .edges
        .iter()
        .map(|_| PreliminaryEdgeAction {
            goto: None,
            has_continue_evidence: false,
            iteration: None,
            phi_inputs: Vec::new(),
        })
        .collect::<Vec<_>>();
    for residual in residual_transfers {
        if let Some(action) = actions.get_mut(residual.edge.index()) {
            action.goto = Some(residual.reason);
        }
    }
    for loop_ in loops {
        for edge in &loop_.backedges {
            if let Some(action) = actions.get_mut(edge.index()) {
                record_preliminary_iteration(action, PreliminaryIteration::LoopBack(loop_.header));
            }
        }
    }
    if caps.continue_stmt {
        for loop_ in loops {
            for edge in &loop_.continue_edges {
                if let Some(action) = actions.get_mut(edge.index()) {
                    action.has_continue_evidence = true;
                    record_preliminary_iteration(
                        action,
                        PreliminaryIteration::Continue(loop_.header),
                    );
                }
            }
            let Some(target) = loop_.continue_target else {
                continue;
            };
            for edge in &cfg.preds[target.index()] {
                let cfg_edge = cfg.edges[edge.index()];
                let source_in_body = loop_.blocks.contains(&cfg_edge.from)
                    || loop_.body_scope_blocks.contains(&cfg_edge.from);
                let conditional_escape = cfg.succs[cfg_edge.from.index()].len() > 1
                    && cfg.succs[cfg_edge.from.index()].iter().any(|sibling| {
                        *sibling != *edge && {
                            let target = cfg.edges[sibling.index()].to;
                            loop_.blocks.contains(&target)
                                || loop_.body_scope_blocks.contains(&target)
                        }
                    });
                if source_in_body
                    && conditional_escape
                    && loop_.backedges.binary_search(edge).is_err()
                    && let Some(action) = actions.get_mut(edge.index())
                {
                    action.has_continue_evidence = true;
                    record_preliminary_iteration(
                        action,
                        PreliminaryIteration::Continue(loop_.header),
                    );
                }
            }
        }
    }
    for phi in &dataflow.phi_candidates {
        for incoming in &phi.incoming {
            if let Some(edge) = incoming.edge
                && let Some(action) = actions.get_mut(edge.index())
            {
                action.phi_inputs.push((phi.id, incoming.value));
            }
        }
    }
    actions
}

fn record_preliminary_iteration(
    action: &mut PreliminaryEdgeAction,
    iteration: PreliminaryIteration,
) {
    action.iteration = match action.iteration {
        None => Some(iteration),
        Some(current) if current == iteration => Some(current),
        Some(_) => Some(PreliminaryIteration::Conflicting),
    };
}

fn simple_condition_input(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: super::BlockRef,
) -> Option<ConditionPlanInput> {
    let (truthy_edge, falsy_edge) = semantic_branch_edges(proto, cfg, header)?;
    let truthy = cfg.edges.get(truthy_edge.index())?.to;
    let falsy = cfg.edges.get(falsy_edge.index())?.to;
    let candidate = ShortCircuitCandidate {
        header,
        blocks: BTreeSet::from([header]),
        entry: ShortCircuitNodeRef(0),
        nodes: vec![super::ShortCircuitNode {
            id: ShortCircuitNodeRef(0),
            header,
            truthy: ShortCircuitTarget::TruthyExit,
            falsy: ShortCircuitTarget::FalsyExit,
        }],
        exit: ShortCircuitExit::BranchExit { truthy, falsy },
        result_reg: None,
        result_phi_id: None,
        entry_value: None,
        value_incomings: Vec::new(),
        reducible: true,
    };
    Some(ConditionPlanInput {
        arcs: vec![
            ConditionArcEvidence {
                source: ShortCircuitNodeRef(0),
                truthy: true,
                edges: vec![truthy_edge],
                connector_blocks: Vec::new(),
                target: ShortCircuitTarget::TruthyExit,
            },
            ConditionArcEvidence {
                source: ShortCircuitNodeRef(0),
                truthy: false,
                edges: vec![falsy_edge],
                connector_blocks: Vec::new(),
                target: ShortCircuitTarget::FalsyExit,
            },
        ],
        candidate,
    })
}

fn required_loop_condition_header(cfg: &Cfg, loop_: &LoopCandidate) -> Option<super::BlockRef> {
    use super::LoopKindHint;

    match loop_.kind_hint {
        LoopKindHint::NumericForLike
        | LoopKindHint::GenericForLike
        | LoopKindHint::WhileTrueLike => None,
        LoopKindHint::RepeatLike => loop_
            .condition_header
            .or(loop_.continue_target)
            .filter(|block| cfg.branch_edges(*block).is_some()),
        LoopKindHint::WhileLike => loop_
            .condition_header
            .or(Some(loop_.header))
            .filter(|block| cfg.branch_edges(*block).is_some()),
        LoopKindHint::Unknown => loop_
            .condition_header
            .or(Some(loop_.header))
            .filter(|block| cfg.branch_edges(*block).is_some()),
    }
}

fn synthesize_direct_condition_arcs(
    proto: &LoweredProto,
    cfg: &Cfg,
    condition: &ShortCircuitCandidate,
    workspace: &mut ConditionArcWorkspace,
) -> Result<Option<Vec<ConditionArcEvidence>>, StructureError> {
    let context = DirectConditionArcContext {
        proto,
        cfg,
        condition,
    };
    let arcs = condition
        .nodes
        .iter()
        .map(|node| -> Result<Option<_>, StructureError> {
            let Some((truthy_edge, falsy_edge)) = semantic_branch_edges(proto, cfg, node.header)
            else {
                return Ok(None);
            };
            let Some(truthy) = synthesize_direct_condition_arc(
                &context,
                node.id,
                true,
                truthy_edge,
                node.truthy.clone(),
                workspace,
            )?
            else {
                return Ok(None);
            };
            let Some(falsy) = synthesize_direct_condition_arc(
                &context,
                node.id,
                false,
                falsy_edge,
                node.falsy.clone(),
                workspace,
            )?
            else {
                return Ok(None);
            };
            Ok(Some([truthy, falsy]))
        })
        .collect::<Result<Option<Vec<_>>, _>>()?
        .map(|pairs| pairs.into_iter().flatten().collect());
    Ok(arcs)
}

struct DirectConditionArcContext<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    condition: &'a ShortCircuitCandidate,
}

/// 所有候选共享访问代次，避免每条 condition arc 都按全图分配并清零 visited。
struct ConditionArcWorkspace {
    marks: Vec<usize>,
    epoch: usize,
}

impl ConditionArcWorkspace {
    fn new(block_count: usize) -> Self {
        Self {
            marks: vec![0; block_count],
            epoch: 0,
        }
    }

    fn next_epoch(&mut self) -> Result<usize, StructureError> {
        self.epoch = self
            .epoch
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("direct condition arc visit epoch overflow"))?;
        Ok(self.epoch)
    }

    fn mark_once(&mut self, block: super::BlockRef, epoch: usize) -> Option<bool> {
        let mark = self.marks.get_mut(block.index())?;
        if *mark == epoch {
            Some(false)
        } else {
            *mark = epoch;
            Some(true)
        }
    }
}

fn synthesize_direct_condition_arc(
    context: &DirectConditionArcContext<'_>,
    source: ShortCircuitNodeRef,
    truthy: bool,
    first_edge: super::EdgeRef,
    target: ShortCircuitTarget,
    workspace: &mut ConditionArcWorkspace,
) -> Result<Option<ConditionArcEvidence>, StructureError> {
    let DirectConditionArcContext {
        proto,
        cfg,
        condition,
    } = *context;
    let expected = match target {
        ShortCircuitTarget::Node(node) => {
            let Some(node) = condition.nodes.get(node.index()) else {
                return Ok(None);
            };
            node.header
        }
        ShortCircuitTarget::TruthyExit => match condition.exit {
            ShortCircuitExit::BranchExit { truthy, .. } => truthy,
            ShortCircuitExit::ValueMerge(_) => return Ok(None),
        },
        ShortCircuitTarget::FalsyExit => match condition.exit {
            ShortCircuitExit::BranchExit { falsy, .. } => falsy,
            ShortCircuitExit::ValueMerge(_) => return Ok(None),
        },
        ShortCircuitTarget::Value(_) => return Ok(None),
    };
    let mut edges = vec![first_edge];
    let mut connector_blocks = Vec::new();
    let epoch = workspace.next_epoch()?;
    let Some(first_edge) = cfg.edges.get(first_edge.index()) else {
        return Ok(None);
    };
    let mut block = first_edge.to;
    while block != expected {
        if !workspace.mark_once(block, epoch).unwrap_or(false) {
            return Ok(None);
        }
        let Some(block_data) = cfg.blocks.get(block.index()) else {
            return Ok(None);
        };
        let range = block_data.instrs;
        let Some(successors) = cfg.succs.get(block.index()) else {
            return Ok(None);
        };
        let [edge] = successors.as_slice() else {
            return Ok(None);
        };
        if range.len != 1
            || !matches!(
                proto.instrs.get(range.start.index()),
                Some(LowInstr::Jump(_))
            )
            || !matches!(
                cfg.edges.get(edge.index()),
                Some(edge) if edge.kind == EdgeKind::Jump
            )
        {
            return Ok(None);
        }
        connector_blocks.push(block);
        edges.push(*edge);
        let Some(edge) = cfg.edges.get(edge.index()) else {
            return Ok(None);
        };
        block = edge.to;
    }
    Ok(Some(ConditionArcEvidence {
        source,
        truthy,
        edges,
        connector_blocks,
        target,
    }))
}

fn semantic_branch_edges(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: super::BlockRef,
) -> Option<(super::EdgeRef, super::EdgeRef)> {
    let (then_edge, else_edge) = cfg.branch_edges(header)?;
    match cfg.terminator(&proto.instrs, header) {
        Some(crate::transformer::LowInstr::Branch(branch)) if branch.cond.negated => {
            Some((else_edge, then_edge))
        }
        Some(crate::transformer::LowInstr::Branch(_)) => Some((then_edge, else_edge)),
        _ => None,
    }
}

fn safe_condition_candidate(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    candidate: &ShortCircuitCandidate,
    workspace: &mut ConditionSafetyWorkspace,
) -> Option<ShortCircuitCandidate> {
    let cut_index = candidate
        .nodes
        .iter()
        .enumerate()
        .skip(1)
        .find_map(|(index, node)| {
            (block_has_escaping_defs(cfg, dataflow, candidate, node.header)
                || block_has_unabsorbed_effects(cfg, dataflow, node.header, workspace))
            .then_some(index)
        });
    match cut_index {
        Some(cut_index) => truncate_condition_at(candidate, cut_index),
        None => Some(candidate.clone()),
    }
}

struct ConditionSafetyWorkspace {
    epoch: usize,
    needed_instr_epochs: Vec<usize>,
    def_epochs: Vec<usize>,
    phi_epochs: Vec<usize>,
    pending: Vec<super::SsaValue>,
}

impl ConditionSafetyWorkspace {
    fn new(dataflow: &DataflowFacts) -> Self {
        Self {
            epoch: 0,
            needed_instr_epochs: vec![0; dataflow.instr_effects.len()],
            def_epochs: vec![0; dataflow.defs.len()],
            phi_epochs: vec![0; dataflow.phi_candidates.len()],
            pending: Vec::new(),
        }
    }

    fn begin(&mut self) {
        if self.epoch == usize::MAX {
            self.needed_instr_epochs.fill(0);
            self.def_epochs.fill(0);
            self.phi_epochs.fill(0);
            self.epoch = 1;
        } else {
            self.epoch += 1;
        }
        self.pending.clear();
    }

    fn needs_instr(&self, instr: InstrRef) -> bool {
        self.needed_instr_epochs.get(instr.index()).copied() == Some(self.epoch)
    }
}

fn block_has_unabsorbed_effects(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    block: super::BlockRef,
    workspace: &mut ConditionSafetyWorkspace,
) -> bool {
    workspace.begin();
    let Some(range) = cfg.blocks.get(block.index()).map(|block| block.instrs) else {
        return true;
    };
    let Some(predicate) = range.last() else {
        return true;
    };
    let Some(uses) = dataflow.use_values.get(predicate.index()) else {
        return true;
    };
    workspace.pending.extend(uses.fixed.values());
    while let Some(value) = workspace.pending.pop() {
        match value {
            super::SsaValue::Entry(_) => {}
            super::SsaValue::Def(def) => {
                let Some(stamp) = workspace.def_epochs.get_mut(def.index()) else {
                    return true;
                };
                if *stamp == workspace.epoch {
                    continue;
                }
                *stamp = workspace.epoch;
                let Some(definition) = dataflow.defs.get(def.index()) else {
                    return true;
                };
                let Some(needed) = workspace
                    .needed_instr_epochs
                    .get_mut(definition.instr.index())
                else {
                    return true;
                };
                *needed = workspace.epoch;
                let Some(uses) = dataflow.use_values.get(definition.instr.index()) else {
                    return true;
                };
                workspace.pending.extend(uses.fixed.values());
            }
            super::SsaValue::Phi(phi) => {
                let Some(stamp) = workspace.phi_epochs.get_mut(phi.index()) else {
                    return true;
                };
                if *stamp == workspace.epoch {
                    continue;
                }
                *stamp = workspace.epoch;
                let Some(phi) = dataflow.phi_candidate(phi) else {
                    return true;
                };
                workspace
                    .pending
                    .extend(phi.incoming.iter().map(|incoming| incoming.value));
            }
        }
    }

    (range.start.index()..predicate.index()).any(|index| {
        dataflow.effect_summaries.get(index).is_none_or(|summary| {
            !summary.tags.is_empty() && !workspace.needs_instr(InstrRef(index))
        })
    })
}

fn block_has_escaping_defs(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    condition: &ShortCircuitCandidate,
    block: super::BlockRef,
) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    (range.start.index()..range.end()).any(|instr| {
        dataflow.instr_defs[instr]
            .iter()
            .copied()
            .any(|def| dataflow.def_has_use_outside(cfg, def, &condition.blocks))
    })
}

fn truncate_condition_at(
    condition: &ShortCircuitCandidate,
    cut_index: usize,
) -> Option<ShortCircuitCandidate> {
    let ShortCircuitExit::BranchExit { falsy, .. } = condition.exit else {
        return None;
    };
    let cut_ref = ShortCircuitNodeRef(cut_index);
    let cut_header = condition.nodes[cut_index].header;
    let mut nodes = condition.nodes[..cut_index].to_vec();
    let mut replaced = false;
    for node in &mut nodes {
        for target in [&mut node.truthy, &mut node.falsy] {
            if matches!(target, ShortCircuitTarget::TruthyExit) {
                return None;
            }
            if *target == ShortCircuitTarget::Node(cut_ref) {
                *target = ShortCircuitTarget::TruthyExit;
                replaced = true;
            } else if matches!(target, ShortCircuitTarget::Node(node) if node.index() >= cut_index)
            {
                return None;
            }
        }
    }
    if !replaced {
        return None;
    }
    let blocks = nodes
        .iter()
        .map(|node| node.header)
        .collect::<BTreeSet<_>>();
    Some(ShortCircuitCandidate {
        header: condition.header,
        blocks,
        entry: condition.entry,
        nodes,
        exit: ShortCircuitExit::BranchExit {
            truthy: cut_header,
            falsy,
        },
        result_reg: None,
        result_phi_id: None,
        entry_value: None,
        value_incomings: Vec::new(),
        reducible: true,
    })
}

fn loop_continuation(
    proto: &LoweredProto,
    candidate: &LoopCandidate,
    condition: Option<&ConditionPlanInput>,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    exit_block: super::BlockRef,
) -> Option<super::BlockRef> {
    let condition_exit = condition.and_then(|condition| {
        let ShortCircuitExit::BranchExit { truthy, falsy } = condition.candidate.exit else {
            return None;
        };
        let is_iteration_target = |block| {
            candidate.blocks.contains(&block)
                || candidate.control_blocks.contains(&block)
                || candidate.continue_target == Some(block)
        };
        let direct = match (is_iteration_target(truthy), is_iteration_target(falsy)) {
            (true, false) if falsy != exit_block => Some(falsy),
            (false, true) if truthy != exit_block => Some(truthy),
            (true, true) | (false, false) | (true, false) | (false, true) => None,
        }?;
        Some(loops::transparent_loop_exit_target(proto, cfg, direct).unwrap_or(direct))
    });
    let mut exits = candidate.exits.iter().copied();
    let first = exits.next()?;
    let common = exits
        .try_fold(first, |common, exit| {
            graph_facts.nearest_common_postdom(common, exit)
        })
        .filter(|continuation| *continuation != exit_block);
    if common.is_none()
        && matches!(
            candidate.kind_hint,
            super::LoopKindHint::Unknown | super::LoopKindHint::WhileTrueLike
        )
        && let Some(continuation) =
            unique_cleanup_to_empty_return_exit(proto, cfg, &candidate.exits)
        && (condition_exit.is_some_and(|exit| loop_exit_is_terminal(proto, cfg, exit))
            || candidate
                .exits
                .iter()
                .copied()
                .any(|exit| exit != continuation && loop_exit_is_terminal(proto, cfg, exit)))
    {
        // Unknown/while-true 的 header guard 可以直接 return；它不是 loop 的 break
        // continuation。若另有唯一 Close-only 路径落到空 return，则该路径才是词法
        // break 后的函数尾，选它可保留 loop scope 而无需伪 goto。
        return Some(continuation);
    }
    match (condition_exit, common) {
        (Some(direct), Some(common))
            if direct != common && !linear_loop_exit_tail(cfg, candidate, direct, common) =>
        {
            Some(direct)
        }
        (Some(direct), None) => Some(direct),
        (_, common) => common,
    }
}

fn unique_cleanup_to_empty_return_exit(
    proto: &LoweredProto,
    cfg: &Cfg,
    exits: &BTreeSet<super::BlockRef>,
) -> Option<super::BlockRef> {
    let mut continuation = None;
    for exit in exits {
        let range = cfg.blocks.get(exit.index())?.instrs;
        let [edge_ref] = cfg.succs.get(exit.index())?.as_slice() else {
            continue;
        };
        let edge = cfg.edges.get(edge_ref.index())?;
        if !matches!(edge.kind, EdgeKind::Fallthrough | EdgeKind::Jump) {
            continue;
        }
        let body_end = range.last().map_or(range.end(), |last| {
            if matches!(proto.instrs.get(last.index()), Some(LowInstr::Jump(_))) {
                range.end() - 1
            } else {
                range.end()
            }
        });
        if range.start.index() == body_end
            || !(range.start.index()..body_end)
                .all(|index| matches!(proto.instrs.get(index), Some(LowInstr::Close(_))))
        {
            continue;
        }
        let Some(target) = cfg.blocks.get(edge.to.index()) else {
            continue;
        };
        let Some(return_instr) = target.instrs.last() else {
            continue;
        };
        if !(target.instrs.start.index()..return_instr.index())
            .all(|index| matches!(proto.instrs.get(index), Some(LowInstr::Close(_))))
            || !matches!(
                proto.instrs.get(return_instr.index()),
                Some(LowInstr::Return(return_))
                    if matches!(
                        return_.values,
                        crate::transformer::ValuePack::Fixed(range) if range.len == 0
                    )
            )
        {
            continue;
        }
        if continuation.replace(*exit).is_some() {
            return None;
        }
    }
    continuation
}

fn loop_exit_is_terminal(proto: &LoweredProto, cfg: &Cfg, exit: super::BlockRef) -> bool {
    let is_terminal = |block| {
        matches!(
            cfg.terminator(&proto.instrs, block),
            Some(LowInstr::Return(_) | LowInstr::TailCall(_))
        )
    };
    is_terminal(exit)
        || cfg
            .unique_reachable_successor(exit)
            .is_some_and(is_terminal)
}

fn linear_loop_exit_tail(
    cfg: &Cfg,
    candidate: &LoopCandidate,
    mut block: super::BlockRef,
    continuation: super::BlockRef,
) -> bool {
    let mut remaining = cfg.blocks.len();
    while block != continuation && remaining > 0 {
        if candidate.blocks.contains(&block) || candidate.control_blocks.contains(&block) {
            return false;
        }
        let Some([edge]) = cfg.succs.get(block.index()).map(Vec::as_slice) else {
            return false;
        };
        block = cfg.edges[edge.index()].to;
        remaining -= 1;
    }
    block == continuation
}
