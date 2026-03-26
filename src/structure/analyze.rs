//! 这个文件负责 StructureFacts 的总调度。
//!
//! 各类候选的提取规则已经拆到独立模块里，避免结构层继续膨胀成单个巨型文件；
//! 这里仅保留“按顺序汇总事实并递归处理子 proto”的壳。

use crate::cfg::{Cfg, CfgGraph, DataflowFacts, GraphFacts};
use crate::transformer::{LoweredChunk, LoweredProto};

use super::common::StructureFacts;
use super::{branch_values, branches, goto, helpers, loops, regions, scope, short_circuit};

/// 对整个 lowered chunk 递归提取结构候选。
pub fn analyze_structure(
    chunk: &LoweredChunk,
    cfg_graph: &CfgGraph,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
) -> StructureFacts {
    analyze_proto_structure(
        &chunk.main,
        &cfg_graph.cfg,
        graph_facts,
        dataflow,
        &cfg_graph.children,
    )
}

fn analyze_proto_structure(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    child_cfgs: &[CfgGraph],
) -> StructureFacts {
    let loop_candidates = loops::analyze_loops(proto, cfg, graph_facts);
    let branch_candidates = branches::analyze_branches(cfg, graph_facts);
    let irreducible_regions = helpers::compute_irreducible_regions(cfg);
    let goto_requirements = goto::analyze_goto_requirements(
        proto,
        cfg,
        &loop_candidates,
        &branch_candidates,
        &irreducible_regions,
    );
    let region_facts = regions::analyze_regions(
        cfg,
        graph_facts,
        &loop_candidates,
        &branch_candidates,
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
        &branch_candidates,
        &short_circuit_candidates,
    );
    let scope_candidates = scope::analyze_scopes(
        proto,
        cfg,
        graph_facts,
        &loop_candidates,
        &branch_candidates,
    );

    let children = proto
        .children
        .iter()
        .zip(child_cfgs.iter())
        .zip(graph_facts.children.iter())
        .zip(dataflow.children.iter())
        .map(
            |(((child_proto, child_cfg), child_graph_facts), child_dataflow)| {
                analyze_proto_structure(
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
        branch_value_merge_candidates,
        loop_candidates,
        short_circuit_candidates,
        goto_requirements,
        region_facts,
        scope_candidates,
        children,
    }
}
