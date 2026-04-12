//! 这个文件负责 StructureFacts 的总调度。
//!
//! 各类候选的提取规则已经拆到独立模块里，避免结构层继续膨胀成单个巨型文件；
//! 这里仅保留“按顺序汇总事实并递归处理子 proto”的壳。
//!
//! 它依赖 CFG / GraphFacts / Dataflow 已经先算好，并把这些底层事实按固定顺序翻译成
//! StructureFacts；它不会越权恢复 HIR/AST 语法，只负责调度各个结构 pass 并汇总结果。
//!
//! 例子：
//! - 一个 proto 如果同时包含 loop、branch 和 short-circuit 候选，这里会先提 loop/
//!   branch 骨架，再在同一套共享事实上继续推 short-circuit、region、scope 和 goto 约束
//! - 子 proto 会递归走完全相同的结构分析顺序，保证父子层结构事实口径一致

use crate::cfg::{Cfg, CfgGraph, DataflowFacts, GraphFacts};
use crate::transformer::LoweredProto;

use super::common::StructureFacts;
use super::{
    branch_values, branches, goto, helpers, loops, phi_facts, regions, scope, short_circuit,
};

/// 对单个 proto 递归提取结构候选，子 proto 走完全相同的分析顺序。
pub fn analyze_structure(
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
                analyze_structure(
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
