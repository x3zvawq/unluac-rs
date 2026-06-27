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

use crate::decompile::{DecompileContext, DecompileError, DecompileState};
use crate::structure::{Cfg, CfgGraph, DataflowFacts, GraphFacts};
use crate::transformer::LoweredProto;

use super::common::StructureFacts;
use super::{
    branch_values, branches, cfg, goto, helpers, loops, phi_facts, regions, scope, short_circuit,
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
    _context: &DecompileContext<'_>,
) -> Result<(), DecompileError> {
    let lowered = state.lowered.as_ref().unwrap();
    let cfg = state.cfg.as_ref().unwrap();
    let graph_facts = state.graph_facts.as_ref().unwrap();
    let dataflow = state.dataflow.as_ref().unwrap();
    state.structure_facts = Some(analyze_structure_proto(
        &lowered.main,
        &cfg.cfg,
        graph_facts,
        dataflow,
        &cfg.children,
    ));
    Ok(())
}

/// 对单个 proto 递归提取结构候选，子 proto 走完全相同的分析顺序。
pub(crate) fn analyze_structure_proto(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    child_cfgs: &[CfgGraph],
) -> StructureFacts {
    let loop_candidates = loops::analyze_loops(proto, cfg, graph_facts, dataflow);
    let branch_candidates = branches::analyze_branches(cfg, graph_facts);
    let branch_region_facts =
        branches::analyze_branch_regions(cfg, graph_facts, &branch_candidates);
    let irreducible_regions = helpers::compute_irreducible_regions(cfg);
    let goto_requirements = goto::analyze_goto_requirements(
        proto,
        cfg,
        &loop_candidates,
        &branch_candidates,
        &branch_region_facts,
        &irreducible_regions,
    );
    let region_facts = regions::analyze_regions(
        cfg,
        &loop_candidates,
        &branch_region_facts,
        &irreducible_regions,
    );
    let short_circuit_candidates = short_circuit::analyze_short_circuits(
        proto,
        cfg,
        graph_facts,
        dataflow,
        &branch_candidates,
    );
    let branch_value_merge_candidates = branch_values::analyze_branch_value_merges(
        cfg,
        graph_facts,
        dataflow,
        &branch_region_facts,
        &short_circuit_candidates,
    );
    let generic_phi_materializations = phi_facts::analyze_generic_phi_materializations(
        dataflow,
        &branch_value_merge_candidates,
        &loop_candidates,
        &short_circuit_candidates,
    );
    let scope_candidates = scope::analyze_scopes(
        proto,
        cfg,
        graph_facts,
        &loop_candidates,
        &branch_region_facts,
    );

    let children = proto
        .children
        .iter()
        .zip(child_cfgs.iter())
        .zip(graph_facts.children.iter())
        .zip(dataflow.children.iter())
        .map(
            |(((child_proto, child_cfg), child_graph_facts), child_dataflow)| {
                analyze_structure_proto(
                    child_proto,
                    &child_cfg.cfg,
                    child_graph_facts,
                    child_dataflow,
                    &child_cfg.children,
                )
            },
        )
        .collect();

    StructureFacts {
        branch_candidates,
        branch_region_facts,
        branch_value_merge_candidates,
        generic_phi_materializations,
        loop_candidates,
        short_circuit_candidates,
        goto_requirements,
        region_facts,
        scope_candidates,
        children,
    }
}
