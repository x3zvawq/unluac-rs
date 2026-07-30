//! 这个模块承载 Structure 层内部的 CFG / 图事实 / 数据流分析。
//!
//! 从 CFG 开始，这些逻辑已经不再依赖某个 Lua dialect 的原始 opcode 细节，
//! 因此统一收敛到一个共享模块里，后续 StructureFacts/HIR 也直接复用这里的事实。

mod build;
mod common;
mod dataflow;
#[cfg(feature = "decompile-debug")]
mod debug;
mod graph;

use crate::structure::StructureError;

pub use build::build_cfg_graph;
pub(crate) use build::build_cfg_proto;
pub use common::{
    BasicBlock, BlockKind, BlockRef, Cfg, CfgEdge, CfgGraph, DataflowFacts, Def, DefId,
    DominatorTree, EdgeKind, EdgeRef, EffectTag, GraphFacts, InstrEffect, InstrRange,
    InstrUseValues, NaturalLoop, OpenDef, OpenDefId, OpenUseSources, PhiCandidate, PhiId,
    PhiIncoming, PostDominatorTree, ReachableSuccessorShape, SideEffectSummary, SsaRegMap,
    SsaValue, UseSite,
};
pub(crate) use dataflow::analyze_dataflow;
pub use dataflow::compute_dataflow_facts;
#[cfg(feature = "decompile-debug")]
pub(super) use debug::{dump_cfg_graph, dump_dataflow_facts, dump_graph_facts_tree};
pub(crate) use graph::analyze_graph_facts;

fn validate_cfg(cfg: &Cfg) -> Result<(), StructureError> {
    let block_count = cfg.blocks.len();
    if block_count == 0 {
        return Err(StructureError::invalid("CFG has no blocks"));
    }
    if cfg.entry_block.index() >= block_count || cfg.exit_block.index() >= block_count {
        return Err(StructureError::invalid(
            "CFG entry or exit block is missing",
        ));
    }
    if cfg.entry_block == cfg.exit_block {
        return Err(StructureError::invalid(
            "CFG entry and exit blocks are identical",
        ));
    }
    if cfg.preds.len() != block_count || cfg.succs.len() != block_count {
        return Err(StructureError::invalid(
            "CFG predecessor/successor index length does not match blocks",
        ));
    }

    let instr_count = cfg.instr_to_block.len();
    let mut seen_blocks = vec![false; block_count];
    let mut seen_instrs = vec![false; instr_count];
    for block in cfg.block_order.iter().copied() {
        let Some(seen) = seen_blocks.get_mut(block.index()) else {
            return Err(StructureError::invalid(format!(
                "CFG block order references missing {block}"
            )));
        };
        if block == cfg.exit_block || std::mem::replace(seen, true) {
            return Err(StructureError::invalid(format!(
                "CFG block order contains invalid or duplicate {block}"
            )));
        }
        let basic_block = cfg.blocks[block.index()];
        let Some(end) = basic_block
            .instrs
            .start
            .index()
            .checked_add(basic_block.instrs.len)
        else {
            return Err(StructureError::invalid(format!(
                "CFG block {block} instruction range overflows"
            )));
        };
        if end > instr_count {
            return Err(StructureError::invalid(format!(
                "CFG block {block} instruction range exceeds the proto"
            )));
        }
        for (instr_index, seen) in seen_instrs
            .iter_mut()
            .enumerate()
            .take(end)
            .skip(basic_block.instrs.start.index())
        {
            if *seen || cfg.instr_to_block.get(instr_index).copied() != Some(block) {
                return Err(StructureError::invalid(format!(
                    "CFG instruction @{instr_index} has conflicting block ownership"
                )));
            }
            *seen = true;
        }
    }
    for (index, seen) in seen_blocks.iter().copied().enumerate() {
        if index != cfg.exit_block.index() && !seen {
            return Err(StructureError::invalid(format!(
                "CFG block #{index} is missing from block order"
            )));
        }
    }
    if seen_instrs.iter().any(|seen| !seen) {
        return Err(StructureError::invalid(
            "CFG instruction ownership does not cover the proto",
        ));
    }
    if cfg.blocks[cfg.exit_block.index()].kind != BlockKind::SyntheticExit {
        return Err(StructureError::invalid(
            "CFG exit block is not marked synthetic",
        ));
    }

    let edge_count = cfg.edges.len();
    let mut successor_refs = vec![0u8; edge_count];
    let mut predecessor_refs = vec![0u8; edge_count];
    for (index, edge) in cfg.edges.iter().copied().enumerate() {
        if edge.from.index() >= block_count || edge.to.index() >= block_count {
            return Err(StructureError::invalid(format!(
                "CFG edge #{index} references a missing block"
            )));
        }
    }
    for (block_index, edges) in cfg.succs.iter().enumerate() {
        for edge_ref in edges {
            let Some(edge) = cfg.edges.get(edge_ref.index()) else {
                return Err(StructureError::invalid(format!(
                    "CFG successor index for block #{block_index} references missing {edge_ref}"
                )));
            };
            if edge.from.index() != block_index {
                return Err(StructureError::invalid(format!(
                    "CFG successor index assigns {edge_ref} to the wrong source block"
                )));
            }
            successor_refs[edge_ref.index()] = successor_refs[edge_ref.index()].saturating_add(1);
        }
    }
    for (block_index, edges) in cfg.preds.iter().enumerate() {
        for edge_ref in edges {
            let Some(edge) = cfg.edges.get(edge_ref.index()) else {
                return Err(StructureError::invalid(format!(
                    "CFG predecessor index for block #{block_index} references missing {edge_ref}"
                )));
            };
            if edge.to.index() != block_index {
                return Err(StructureError::invalid(format!(
                    "CFG predecessor index assigns {edge_ref} to the wrong target block"
                )));
            }
            predecessor_refs[edge_ref.index()] =
                predecessor_refs[edge_ref.index()].saturating_add(1);
        }
    }
    if successor_refs.iter().any(|count| *count != 1)
        || predecessor_refs.iter().any(|count| *count != 1)
    {
        return Err(StructureError::invalid(
            "CFG edge is missing from or duplicated in an adjacency index",
        ));
    }

    let mut reachable = vec![false; block_count];
    let mut pending = vec![cfg.entry_block];
    while let Some(block) = pending.pop() {
        if std::mem::replace(&mut reachable[block.index()], true) {
            continue;
        }
        for edge_ref in &cfg.succs[block.index()] {
            pending.push(cfg.edges[edge_ref.index()].to);
        }
    }
    let mut declared_reachable = vec![false; block_count];
    for block in cfg.reachable_blocks.iter().copied() {
        let Some(slot) = declared_reachable.get_mut(block.index()) else {
            return Err(StructureError::invalid(format!(
                "CFG reachability references missing {block}"
            )));
        };
        *slot = true;
    }
    if reachable != declared_reachable {
        return Err(StructureError::invalid("CFG reachability index is stale"));
    }
    Ok(())
}
