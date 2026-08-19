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
    BranchCandidate, BranchKind, BranchRegionFact, BranchValueMergeCandidate, DebugBindingConflict,
    DebugBindingFact, DebugBindingFacts, LoopCandidate, RegionFact, ResidualTransferEvidence,
    ScopePlan, ShortCircuitCandidate, ShortCircuitExit, ShortCircuitNodeRef, ShortCircuitTarget,
    StructureFacts,
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

mod condition_arcs;
mod conditions;
mod debug_bindings;
mod final_input;
mod loop_continuation;
mod value_decisions;

use condition_arcs::*;
use conditions::*;
use debug_bindings::*;
use final_input::*;
use loop_continuation::*;
use value_decisions::*;

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
    // repeat refinement 与最终 condition 冻结必须消费同一份安全边界。否则带可观察
    // 副作用的后继节点会先参与 loop 形态判断、再在 condition selection 中被截断，
    // 同一个 header 最终就可能拿到一份更窄、且仍指向 loop body 的伪尾条件。
    // 这里只查询 BranchExit；ValueMerge 往往携带最大的 blocks/nodes/leaf payload，
    // 把整张 short-circuit 表复制一遍既无语义作用，也会按 phi 放大内存。
    let mut loop_condition_safety_workspace = ConditionSafetyWorkspace::new(dataflow);
    let mut short_circuit_candidates_for_loops = short_circuit_candidates
        .iter()
        .filter(|candidate| matches!(candidate.exit, ShortCircuitExit::BranchExit { .. }))
        .filter_map(|candidate| {
            safe_condition_candidate(
                cfg,
                dataflow,
                candidate,
                &mut loop_condition_safety_workspace,
            )
        })
        .collect::<Vec<_>>();
    short_circuit_candidates_for_loops.extend(closed_control_dags.iter().filter_map(|evidence| {
        safe_condition_candidate(
            cfg,
            dataflow,
            &evidence.candidate,
            &mut loop_condition_safety_workspace,
        )
    }));
    let loop_condition_supplements =
        short_circuit::analyze_cfg_linear_branch_exits(proto, cfg, &branch_candidates)
            .iter()
            .filter_map(|candidate| {
                safe_condition_candidate(
                    cfg,
                    dataflow,
                    candidate,
                    &mut loop_condition_safety_workspace,
                )
            })
            .collect::<Vec<_>>();
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
    loops::assign_continue_edge_ownership(
        proto,
        cfg,
        graph_facts,
        &branch_candidates,
        &mut loop_candidates,
    );
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

    let debug_bindings = analyze_debug_bindings(proto, cfg, dataflow);

    Ok(StructureFacts {
        plan,
        debug_bindings,
        children,
    })
}
