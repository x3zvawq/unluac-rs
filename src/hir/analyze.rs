//! 这个文件承载 HIR 初始恢复的主入口。
//!
//! 外层文件只负责声明 analyze 子模块、组织跨 proto 的递归入口，并把目录内真正的
//! lowering 能力串起来。这样 `src/hir/analyze` 和 `src/hir/simplify` 的外层形状就会
//! 保持一致，后续继续拆分实现时也更容易定位“入口”与“细节”。

mod bindings;
mod exprs;
mod helpers;
mod lower;
mod short_circuit;
mod structure;

use self::lower::{ChildAnalyses, lower_proto};
use super::simplify::simplify_hir_with_timing;
use crate::cfg::{CfgGraph, DataflowFacts, GraphFacts};
use crate::hir::common::HirModule;
use crate::readability::ReadabilityOptions;
use crate::structure::StructureFacts;
use crate::timing::TimingCollector;
use crate::transformer::LoweredChunk;

use self::exprs::lower_branch_cond;
use self::helpers::{assign_stmt, branch_stmt};
use self::lower::{
    ProtoBindings, ProtoLowering, is_control_terminator, lower_control_instr,
    lower_phi_materialization_with_allowed_blocks_except, lower_regular_instr,
};

/// 对整个 lowered chunk 递归构造 HIR。
pub fn analyze_hir(
    chunk: &LoweredChunk,
    cfg_graph: &CfgGraph,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    structure: &StructureFacts,
    readability: ReadabilityOptions,
) -> HirModule {
    let timings = TimingCollector::disabled();
    analyze_hir_with_timing(
        chunk,
        cfg_graph,
        graph_facts,
        dataflow,
        structure,
        &timings,
        readability,
    )
}

pub(crate) fn analyze_hir_with_timing(
    chunk: &LoweredChunk,
    cfg_graph: &CfgGraph,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    structure: &StructureFacts,
    timings: &TimingCollector,
    readability: ReadabilityOptions,
) -> HirModule {
    let mut protos = Vec::new();
    let child_analyses = ChildAnalyses {
        cfg_graphs: &cfg_graph.children,
        graph_facts: &graph_facts.children,
        dataflow: &dataflow.children,
        structure: &structure.children,
    };
    let entry = timings.record("lower", || {
        lower_proto(
            &chunk.main,
            &cfg_graph.cfg,
            graph_facts,
            dataflow,
            structure,
            child_analyses,
            &mut protos,
        )
    });

    let mut module = HirModule { entry, protos };
    timings.record("simplify", || {
        simplify_hir_with_timing(&mut module, readability, timings);
    });
    module
}
