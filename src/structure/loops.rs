//! 从 CFG、GraphFacts、Dataflow 与 Low-IR 提取循环候选。
//!
//! 发布循环形态、绑定和控制转移证据，最终计划由 StructurePlan 冻结。

use std::collections::{BTreeMap, BTreeSet};

use crate::structure::{BlockRef, Cfg, DataflowFacts, EdgeKind, EdgeRef, GraphFacts};
use crate::transformer::{GenericForLoopInstr, LowInstr, LoweredProto, Reg};

use super::common::{
    BranchCandidate, BranchKind, LoopCandidate, LoopExitAlias, LoopExitValueMergeCandidate,
    LoopKindHint, LoopSourceBindings, LoopValueMerge, ShortCircuitCandidate, ShortCircuitExit,
    ShortCircuitTarget,
};
use super::helpers::{
    block_has_non_control_prefix, collect_forward_region_blocks, collect_region_exits,
    equivalent_single_return_targets, is_reducible_region, same_or_transparent_jump_target,
};
use super::phi_facts::loop_value_merges_in_block;

mod candidates;
mod continue_edges;
mod exits;
mod natural_loops;
mod repeat_refine;
mod shape;

pub(super) use candidates::generic_for_immediate_break;
use candidates::*;
pub(super) use continue_edges::assign_continue_edge_ownership;
use exits::*;
pub(super) use exits::{private_forward_exit_continuation, transparent_loop_exit_target};
pub(super) use natural_loops::branch_conditions_share_subject;
use natural_loops::*;
use repeat_refine::*;
pub(super) use repeat_refine::{RepeatRefinementInput, refine_short_circuit_repeat_candidates};
use shape::*;

#[derive(Clone, Copy)]
struct LoopAnalysisContext<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    graph_facts: &'a GraphFacts,
    dataflow: &'a DataflowFacts,
}

pub(super) fn analyze_loops(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
) -> Vec<LoopCandidate> {
    let context = LoopAnalysisContext {
        proto,
        cfg,
        graph_facts,
        dataflow,
    };
    let mut shared_exit_workspace = SharedExitWorkspace::new(cfg.blocks.len());
    let mut domain_workspace = NaturalLoopDomainWorkspace::new(cfg.blocks.len());
    let mut loop_candidates = Vec::with_capacity(graph_facts.natural_loops.len());
    for natural_loop in &graph_facts.natural_loops {
        if let Some(partition) = reachable_numeric_for_loop(
            &context,
            &mut shared_exit_workspace,
            &mut domain_workspace,
            natural_loop,
        ) {
            loop_candidates.extend(partition);
        } else if let Some(partition) = partition_repeat_like_natural_loop(
            &context,
            &mut shared_exit_workspace,
            &mut domain_workspace,
            natural_loop,
        ) {
            loop_candidates.extend(partition);
        } else {
            loop_candidates.push(build_loop_candidate(
                &context,
                &mut shared_exit_workspace,
                natural_loop.header,
                natural_loop.blocks.clone(),
                natural_loop.backedges.clone(),
            ));
        }
    }
    let mut grouped_headers = vec![false; cfg.blocks.len()];
    let mut numeric_headers = vec![false; cfg.blocks.len()];
    for candidate in &loop_candidates {
        grouped_headers[candidate.header.index()] = true;
        if candidate.kind_hint == LoopKindHint::NumericForLike {
            numeric_headers[candidate.header.index()] = true;
        }
    }

    let degenerate_generic_for_loops = analyze_degenerate_generic_for_loops(
        proto,
        cfg,
        dataflow,
        graph_facts,
        &grouped_headers,
        &mut shared_exit_workspace,
    );
    loop_candidates.extend(degenerate_generic_for_loops);
    let numeric_for_latches = index_numeric_for_latches(proto, cfg);
    loop_candidates.extend(
        cfg.reachable_blocks
            .iter()
            .copied()
            .filter_map(|preheader| {
                degenerate_numeric_for_loop(
                    &context,
                    &numeric_headers,
                    &numeric_for_latches,
                    &mut shared_exit_workspace,
                    preheader,
                )
            }),
    );
    loop_candidates.sort_by_key(|candidate| (candidate.header, candidate.blocks.len()));
    refine_nested_for_exit_loops(proto, cfg, graph_facts, &mut loop_candidates);
    refine_ambiguous_repeat_candidates(
        proto,
        cfg,
        graph_facts,
        &mut shared_exit_workspace,
        &mut loop_candidates,
    );
    loop_candidates
}
