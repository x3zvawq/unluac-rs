//! 这个文件承载共享分析层的调试输出。
//!
//! CFG/GraphFacts/Dataflow 都是跨 dialect 共享的，所以观察视图也放在这一层，
//! 让 CLI、主 pipeline 和单测都复用同一套稳定文本格式。

use std::collections::BTreeSet;
use std::fmt::Write as _;

use crate::debug::{DebugDetail, DebugFilters};
use crate::transformer::{LowInstr, LoweredChunk, LoweredProto, Reg};

use super::common::{
    BlockRef, CfgGraph, CompactSet, DataflowFacts, DefId, EffectTag, GraphFacts, OpenDefId,
    RegValueMap, SsaValue,
};

#[derive(Debug, Clone, Copy)]
struct ProtoEntry<'a, T> {
    id: usize,
    depth: usize,
    facts: &'a T,
}

#[derive(Debug, Clone, Copy)]
struct DataflowProtoEntry<'a> {
    id: usize,
    depth: usize,
    proto: &'a LoweredProto,
    cfg: &'a CfgGraph,
    facts: &'a DataflowFacts,
}

/// 输出 CFG 的人类可读摘要。
pub fn dump_cfg(graph: &CfgGraph, detail: DebugDetail, filters: &DebugFilters) -> String {
    let mut output = String::new();
    let entries = collect_proto_entries(graph);
    let visible = visible_proto_ids(&entries, filters);

    let _ = writeln!(output, "===== Dump CFG =====");
    let _ = writeln!(output, "cfg detail={} protos={}", detail, entries.len());
    if let Some(proto_id) = filters.proto {
        let _ = writeln!(output, "filters proto=proto#{proto_id}");
    }
    let _ = writeln!(output);

    for entry in &entries {
        if !visible.contains(&entry.id) {
            continue;
        }

        let cfg = &entry.facts.cfg;
        let indent = "  ".repeat(entry.depth);
        let _ = writeln!(
            output,
            "{indent}proto#{} blocks={} edges={} entry=#{} exit=#{} reachable={}",
            entry.id,
            cfg.block_order.len(),
            cfg.edges.len(),
            cfg.entry_block.index(),
            cfg.exit_block.index(),
            format_block_set(&cfg.reachable_blocks),
        );

        if matches!(detail, DebugDetail::Summary) {
            continue;
        }

        let _ = writeln!(output, "{indent}  block listing");
        for block_ref in &cfg.block_order {
            let block = cfg.blocks[block_ref.index()];
            let _ = writeln!(
                output,
                "{indent}    block #{} instrs=[@{}..@{}) preds={} succs={}",
                block_ref.index(),
                block.instrs.start.index(),
                block.instrs.end(),
                format_edge_refs(&cfg.preds[block_ref.index()]),
                format_edge_refs(&cfg.succs[block_ref.index()]),
            );
        }
        let _ = writeln!(
            output,
            "{indent}    block #{} <synthetic-exit> preds={} succs={}",
            cfg.exit_block.index(),
            format_edge_refs(&cfg.preds[cfg.exit_block.index()]),
            format_edge_refs(&cfg.succs[cfg.exit_block.index()]),
        );

        let _ = writeln!(output, "{indent}  edge listing");
        for (edge_index, edge) in cfg.edges.iter().enumerate() {
            let _ = writeln!(
                output,
                "{indent}    edge #{} #{} -> #{} kind={}",
                edge_index,
                edge.from.index(),
                edge.to.index(),
                format_edge_kind(edge.kind),
            );
        }
    }

    output
}

/// 输出 GraphFacts 的人类可读摘要。
pub fn dump_graph_facts(
    graph_facts: &GraphFacts,
    detail: DebugDetail,
    filters: &DebugFilters,
) -> String {
    let mut output = String::new();
    let entries = collect_proto_entries(graph_facts);
    let visible = visible_proto_ids(&entries, filters);

    let _ = writeln!(output, "===== Dump GraphFacts =====");
    let _ = writeln!(
        output,
        "graph-facts detail={} protos={}",
        detail,
        entries.len()
    );
    if let Some(proto_id) = filters.proto {
        let _ = writeln!(output, "filters proto=proto#{proto_id}");
    }
    let _ = writeln!(output);

    for entry in &entries {
        if !visible.contains(&entry.id) {
            continue;
        }

        let facts = entry.facts;
        let indent = "  ".repeat(entry.depth);
        let _ = writeln!(
            output,
            "{indent}proto#{} rpo={} backedges={} loop_headers={}",
            entry.id,
            format_block_list(&facts.rpo),
            format_edge_refs(&facts.backedges),
            format_block_set(&facts.loop_headers),
        );

        if matches!(detail, DebugDetail::Summary) {
            continue;
        }

        let _ = writeln!(output, "{indent}  dominator tree");
        for (block_index, parent) in facts.dominator_tree.parent.iter().enumerate() {
            let _ = writeln!(
                output,
                "{indent}    block #{} parent={}",
                block_index,
                parent
                    .map(|block| format!("#{}", block.index()))
                    .unwrap_or_else(|| "-".to_owned()),
            );
        }

        let _ = writeln!(output, "{indent}  post-dominator tree");
        for (block_index, parent) in facts.post_dominator_tree.parent.iter().enumerate() {
            let _ = writeln!(
                output,
                "{indent}    block #{} parent={}",
                block_index,
                parent
                    .map(|block| format!("#{}", block.index()))
                    .unwrap_or_else(|| "-".to_owned()),
            );
        }

        let _ = writeln!(output, "{indent}  dominance frontier");
        for (block_index, frontier) in facts.dominance_frontier.iter().enumerate() {
            if frontier.is_empty() && matches!(detail, DebugDetail::Normal) {
                continue;
            }
            let _ = writeln!(
                output,
                "{indent}    block #{} frontier={}",
                block_index,
                format_block_set(frontier),
            );
        }

        let _ = writeln!(output, "{indent}  natural loops");
        if facts.natural_loops.is_empty() {
            let _ = writeln!(output, "{indent}    <none>");
        } else {
            for natural_loop in &facts.natural_loops {
                let _ = writeln!(
                    output,
                    "{indent}    header=#{} backedge=#{} blocks={}",
                    natural_loop.header.index(),
                    natural_loop.backedge.index(),
                    format_block_set(&natural_loop.blocks),
                );
            }
        }
    }

    output
}

/// 输出数据流层的人类可读摘要。
pub fn dump_dataflow(
    chunk: &LoweredChunk,
    cfg: &CfgGraph,
    dataflow: &DataflowFacts,
    detail: DebugDetail,
    filters: &DebugFilters,
) -> String {
    let mut output = String::new();
    let entries = collect_dataflow_entries(&chunk.main, cfg, dataflow);
    let visible = visible_dataflow_ids(&entries, filters);

    let _ = writeln!(output, "===== Dump Dataflow =====");
    let _ = writeln!(
        output,
        "dataflow detail={} protos={}",
        detail,
        entries.len()
    );
    if let Some(proto_id) = filters.proto {
        let _ = writeln!(output, "filters proto=proto#{proto_id}");
    }
    let _ = writeln!(output);

    for entry in &entries {
        if !visible.contains(&entry.id) {
            continue;
        }

        let indent = "  ".repeat(entry.depth);
        let _ = writeln!(
            output,
            "{indent}proto#{} defs={} open_defs={} phis={}",
            entry.id,
            entry.facts.defs.len(),
            entry.facts.open_defs.len(),
            entry.facts.phi_candidates.len(),
        );

        if matches!(detail, DebugDetail::Summary) {
            continue;
        }

        let _ = writeln!(output, "{indent}  instr effects");
        for (instr_index, instr) in entry.proto.instrs.iter().enumerate() {
            let effect = &entry.facts.instr_effects[instr_index];
            let summary = &entry.facts.effect_summaries[instr_index];
            let block = entry.cfg.cfg.instr_to_block[instr_index];
            let _ = writeln!(
                output,
                "{indent}    @{instr_index:03} block=#{} {:<18} reads={} writes={} open-use={} open-def={} effects={}",
                block.index(),
                format_low_instr_head(instr),
                format_reg_set(&effect.fixed_uses),
                format_reg_set(&effect.fixed_must_defs),
                effect
                    .open_use
                    .map(format_reg)
                    .unwrap_or_else(|| "-".to_owned()),
                effect
                    .open_must_def
                    .map(format_reg)
                    .unwrap_or_else(|| "-".to_owned()),
                format_effect_tags(&summary.tags),
            );
        }

        let _ = writeln!(output, "{indent}  liveness");
        for block in &entry.cfg.cfg.block_order {
            let _ = writeln!(
                output,
                "{indent}    block #{} live_in={} live_out={} open_in={} open_out={}",
                block.index(),
                format_reg_set(&entry.facts.live_in[block.index()]),
                format_reg_set(&entry.facts.live_out[block.index()]),
                entry.facts.open_live_in[block.index()],
                entry.facts.open_live_out[block.index()],
            );
        }

        let _ = writeln!(output, "{indent}  phi candidates");
        if entry.facts.phi_candidates.is_empty() {
            let _ = writeln!(output, "{indent}    <none>");
        } else {
            for candidate in &entry.facts.phi_candidates {
                let _ = writeln!(
                    output,
                    "{indent}    block #{} reg={} incoming={}",
                    candidate.block.index(),
                    format_reg(candidate.reg),
                    format_phi_incoming(&candidate.incoming),
                );
            }
        }

        if matches!(detail, DebugDetail::Verbose) {
            let _ = writeln!(output, "{indent}  reaching defs");
            for (instr_index, defs) in entry.facts.reaching_defs.iter().enumerate() {
                let _ = writeln!(
                    output,
                    "{indent}    @{instr_index:03} fixed={} open={}",
                    format_reaching_defs(&defs.fixed),
                    format_open_def_set(&entry.facts.open_reaching_defs[instr_index]),
                );
            }

            let _ = writeln!(output, "{indent}  reaching values");
            for (instr_index, values) in entry.facts.reaching_values.iter().enumerate() {
                let _ = writeln!(
                    output,
                    "{indent}    @{instr_index:03} fixed={}",
                    format_reaching_values(&values.fixed),
                );
            }
        }
    }

    output
}

fn collect_proto_entries<'a, T>(root: &'a T) -> Vec<ProtoEntry<'a, T>>
where
    T: ProtoChildren<T>,
{
    let mut entries = Vec::new();
    collect_proto_entries_inner(root, 0, &mut entries);
    entries
}

fn collect_proto_entries_inner<'a, T>(
    node: &'a T,
    depth: usize,
    entries: &mut Vec<ProtoEntry<'a, T>>,
) where
    T: ProtoChildren<T>,
{
    let id = entries.len();
    entries.push(ProtoEntry {
        id,
        depth,
        facts: node,
    });

    for child in node.children() {
        collect_proto_entries_inner(child, depth + 1, entries);
    }
}

fn collect_dataflow_entries<'a>(
    proto: &'a LoweredProto,
    cfg: &'a CfgGraph,
    dataflow: &'a DataflowFacts,
) -> Vec<DataflowProtoEntry<'a>> {
    let mut entries = Vec::new();
    collect_dataflow_entries_inner(proto, cfg, dataflow, 0, &mut entries);
    entries
}

fn collect_dataflow_entries_inner<'a>(
    proto: &'a LoweredProto,
    cfg: &'a CfgGraph,
    dataflow: &'a DataflowFacts,
    depth: usize,
    entries: &mut Vec<DataflowProtoEntry<'a>>,
) {
    let id = entries.len();
    entries.push(DataflowProtoEntry {
        id,
        depth,
        proto,
        cfg,
        facts: dataflow,
    });

    for ((child_proto, child_cfg), child_dataflow) in proto
        .children
        .iter()
        .zip(cfg.children.iter())
        .zip(dataflow.children.iter())
    {
        collect_dataflow_entries_inner(child_proto, child_cfg, child_dataflow, depth + 1, entries);
    }
}

fn visible_proto_ids<T>(entries: &[ProtoEntry<'_, T>], filters: &DebugFilters) -> Vec<usize> {
    match filters.proto {
        Some(id) if entries.iter().any(|entry| entry.id == id) => vec![id],
        Some(_) => Vec::new(),
        None => entries.iter().map(|entry| entry.id).collect(),
    }
}

fn visible_dataflow_ids(entries: &[DataflowProtoEntry<'_>], filters: &DebugFilters) -> Vec<usize> {
    match filters.proto {
        Some(id) if entries.iter().any(|entry| entry.id == id) => vec![id],
        Some(_) => Vec::new(),
        None => entries.iter().map(|entry| entry.id).collect(),
    }
}

trait ProtoChildren<T> {
    fn children(&self) -> &[T];
}

impl ProtoChildren<CfgGraph> for CfgGraph {
    fn children(&self) -> &[CfgGraph] {
        &self.children
    }
}

impl ProtoChildren<GraphFacts> for GraphFacts {
    fn children(&self) -> &[GraphFacts] {
        &self.children
    }
}

fn format_edge_refs(edge_refs: &[super::common::EdgeRef]) -> String {
    if edge_refs.is_empty() {
        "-".to_owned()
    } else {
        edge_refs
            .iter()
            .map(|edge| format!("#{}", edge.index()))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

fn format_block_set(blocks: &BTreeSet<BlockRef>) -> String {
    if blocks.is_empty() {
        "[-]".to_owned()
    } else {
        format!(
            "[{}]",
            blocks
                .iter()
                .map(|block| format!("#{}", block.index()))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

fn format_block_list(blocks: &[BlockRef]) -> String {
    if blocks.is_empty() {
        "[-]".to_owned()
    } else {
        format!(
            "[{}]",
            blocks
                .iter()
                .map(|block| format!("#{}", block.index()))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

fn format_reg_set(regs: &BTreeSet<Reg>) -> String {
    if regs.is_empty() {
        "[-]".to_owned()
    } else {
        format!(
            "[{}]",
            regs.iter()
                .map(|reg| format_reg(*reg))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

fn format_reaching_defs(defs: &RegValueMap<DefId>) -> String {
    if defs.iter().next().is_none() {
        "[-]".to_owned()
    } else {
        defs.iter()
            .map(|(reg, defs)| format!("{}<-{}", format_reg(reg), format_def_set(defs)))
            .collect::<Vec<_>>()
            .join(" ")
    }
}

fn format_def_set(defs: &CompactSet<DefId>) -> String {
    format_def_iter(defs.iter())
}

fn format_btree_def_set(defs: &BTreeSet<DefId>) -> String {
    format_def_iter(defs.iter())
}

fn format_def_iter<'a>(defs: impl Iterator<Item = &'a DefId>) -> String {
    let defs = defs.collect::<Vec<_>>();
    if defs.is_empty() {
        "[-]".to_owned()
    } else {
        format!(
            "[{}]",
            defs.into_iter()
                .map(|def| format!("def{}", def.index()))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

fn format_reaching_values(values: &RegValueMap<SsaValue>) -> String {
    if values.iter().next().is_none() {
        "[-]".to_owned()
    } else {
        values
            .iter()
            .map(|(reg, values)| format!("{}<-{}", format_reg(reg), format_value_set(values)))
            .collect::<Vec<_>>()
            .join(" ")
    }
}

fn format_value_set(values: &CompactSet<SsaValue>) -> String {
    if values.is_empty() {
        "[-]".to_owned()
    } else {
        format!(
            "[{}]",
            values
                .iter()
                .map(|value| match value {
                    SsaValue::Def(def) => format!("def{}", def.index()),
                    SsaValue::Phi(phi) => format!("phi{}", phi.index()),
                })
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

fn format_open_def_set(defs: &BTreeSet<OpenDefId>) -> String {
    if defs.is_empty() {
        "[-]".to_owned()
    } else {
        format!(
            "[{}]",
            defs.iter()
                .map(|def| format!("open{}", def.index()))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

fn format_effect_tags(tags: &BTreeSet<EffectTag>) -> String {
    if tags.is_empty() {
        "[-]".to_owned()
    } else {
        format!(
            "[{}]",
            tags.iter()
                .map(|tag| format_effect_tag(*tag))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

fn format_phi_incoming(incoming: &[super::common::PhiIncoming]) -> String {
    incoming
        .iter()
        .map(|incoming| {
            format!(
                "#{}:{}",
                incoming.pred.index(),
                format_btree_def_set(&incoming.defs)
            )
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_reg(reg: Reg) -> String {
    format!("r{}", reg.index())
}

fn format_low_instr_head(instr: &LowInstr) -> &'static str {
    match instr {
        LowInstr::Move(_instr) => "move",
        LowInstr::LoadNil(_instr) => "load-nil",
        LowInstr::LoadBool(_instr) => "load-bool",
        LowInstr::LoadConst(_instr) => "load-const",
        LowInstr::LoadInteger(_instr) => "load-int",
        LowInstr::LoadNumber(_instr) => "load-num",
        LowInstr::UnaryOp(_instr) => "unary-op",
        LowInstr::BinaryOp(_instr) => "binary-op",
        LowInstr::Concat(_instr) => "concat",
        LowInstr::GetUpvalue(_instr) => "get-upvalue",
        LowInstr::SetUpvalue(_instr) => "set-upvalue",
        LowInstr::GetTable(_instr) => "get-table",
        LowInstr::SetTable(_instr) => "set-table",
        LowInstr::ErrNil(_instr) => "err-nnil",
        LowInstr::NewTable(_instr) => "new-table",
        LowInstr::SetList(_instr) => "set-list",
        LowInstr::Call(_instr) => "call",
        LowInstr::TailCall(_instr) => "tail-call",
        LowInstr::VarArg(_instr) => "vararg",
        LowInstr::Return(_instr) => "return",
        LowInstr::Closure(_instr) => "closure",
        LowInstr::Close(_instr) => "close",
        LowInstr::Tbc(_instr) => "tbc",
        LowInstr::NumericForInit(_instr) => "numeric-for-init",
        LowInstr::NumericForLoop(_instr) => "numeric-for-loop",
        LowInstr::GenericForCall(_instr) => "generic-for-call",
        LowInstr::GenericForLoop(_instr) => "generic-for-loop",
        LowInstr::Jump(_instr) => "jump",
        LowInstr::Branch(_instr) => "branch",
    }
}

fn format_effect_tag(tag: EffectTag) -> &'static str {
    match tag {
        EffectTag::Alloc => "alloc",
        EffectTag::ReadTable => "read-table",
        EffectTag::WriteTable => "write-table",
        EffectTag::ReadEnv => "read-env",
        EffectTag::WriteEnv => "write-env",
        EffectTag::ReadUpvalue => "read-upvalue",
        EffectTag::WriteUpvalue => "write-upvalue",
        EffectTag::Call => "call",
        EffectTag::Close => "close",
    }
}

fn format_edge_kind(kind: super::common::EdgeKind) -> &'static str {
    match kind {
        super::common::EdgeKind::Fallthrough => "fallthrough",
        super::common::EdgeKind::Jump => "jump",
        super::common::EdgeKind::BranchTrue => "branch-true",
        super::common::EdgeKind::BranchFalse => "branch-false",
        super::common::EdgeKind::LoopBody => "loop-body",
        super::common::EdgeKind::LoopExit => "loop-exit",
        super::common::EdgeKind::Return => "return",
        super::common::EdgeKind::TailCall => "tail-call",
    }
}
