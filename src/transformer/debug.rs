//! 这个文件承载 transformer 层对外暴露的调试入口。
//!
//! low-IR 是跨 dialect 共享的稳定契约，因此 dump 视图也应尽量共享实现；
//! stage dump 入口在这里直接从主 pipeline state 读取 LoweredChunk，dialect-specific
//! 的复杂性应该留在 lowering 阶段，而不是再次渗回观察层。

use std::fmt::Write as _;

use crate::debug::{
    DebugColorMode, DebugDetail, DebugFilters, FocusPlan, ProtoSummaryRow, build_proto_nodes,
    colorize_debug_text, compute_focus_plan, define_stage_dump, format_breadcrumb,
    format_proto_summary_row,
};
use crate::decompile::DecompileDialect;

use super::{LoweredChunk, LoweredProto, RawInstrRef, format_low_instr};

#[derive(Debug, Clone, Copy)]
struct ProtoEntry<'a> {
    id: usize,
    parent: Option<usize>,
    depth: usize,
    proto: &'a LoweredProto,
}

define_stage_dump! {
    /// Transformer 阶段的调试导出。
    pub fn dump_lir(state, options) => Transformer,
        dump_lir_chunk(
            state.require_lowered()?,
            options.detail,
            &options.filters,
            options.color
        );
}

/// 输出统一 low-IR 的人类可读调试视图。
fn dump_lir_chunk(
    chunk: &LoweredChunk,
    detail: DebugDetail,
    filters: &DebugFilters,
    color: DebugColorMode,
) -> String {
    let mut output = String::new();
    let protos = collect_proto_entries(&chunk.main);
    let plan = plan_focus(&protos, filters);

    let _ = writeln!(output, "===== Dump LIR =====");
    let _ = writeln!(
        output,
        "lir dialect={} detail={} protos={}",
        dialect_label(chunk.header.version),
        detail,
        protos.len()
    );
    if let Some(proto_id) = filters.proto {
        let _ = writeln!(output, "filters proto=proto#{proto_id}");
    }
    let _ = writeln!(output, "filters proto_depth={}", filters.proto_depth);
    if let Some(breadcrumb) = format_breadcrumb(&plan) {
        let _ = writeln!(output, "focus {breadcrumb}");
    }
    let _ = writeln!(output);

    write_proto_tree_view(&mut output, &protos, &plan, detail);
    let _ = writeln!(output);
    write_lir_listing(&mut output, &protos, &plan);

    colorize_debug_text(&output, color)
}

fn collect_proto_entries(root: &LoweredProto) -> Vec<ProtoEntry<'_>> {
    let mut entries = Vec::new();
    collect_proto_entries_inner(root, None, 0, &mut entries);
    entries
}

fn collect_proto_entries_inner<'a>(
    proto: &'a LoweredProto,
    parent: Option<usize>,
    depth: usize,
    entries: &mut Vec<ProtoEntry<'a>>,
) {
    let id = entries.len();
    entries.push(ProtoEntry {
        id,
        parent,
        depth,
        proto,
    });

    for child in &proto.children {
        collect_proto_entries_inner(child, Some(id), depth + 1, entries);
    }
}

fn plan_focus(protos: &[ProtoEntry<'_>], filters: &DebugFilters) -> FocusPlan {
    let parents: Vec<Option<usize>> = protos.iter().map(|e| e.parent).collect();
    let nodes = build_proto_nodes(&parents);
    compute_focus_plan(&nodes, &filters.as_focus_request())
}

fn build_summary_row(entry: &ProtoEntry<'_>) -> ProtoSummaryRow {
    ProtoSummaryRow {
        id: entry.id,
        depth_below_focus: entry.depth,
        name: None,
        first: None,
        lines: Some((
            entry.proto.line_range.defined_start,
            entry.proto.line_range.defined_end,
        )),
        instrs: Some(entry.proto.instrs.len()),
        children: Some(entry.proto.children.len()),
    }
}

fn write_proto_tree_view(
    output: &mut String,
    protos: &[ProtoEntry<'_>],
    plan: &FocusPlan,
    detail: DebugDetail,
) {
    let _ = writeln!(output, "proto tree");
    if plan.focus.is_none() {
        let _ = writeln!(output, "  <no proto matched filters>");
        return;
    }

    for entry in protos {
        if plan.is_elided(entry.id) {
            let indent = "  ".repeat(entry.depth + 1);
            let _ = writeln!(
                output,
                "{indent}{}",
                format_proto_summary_row(&build_summary_row(entry)),
            );
            continue;
        }
        if !plan.is_visible(entry.id) {
            continue;
        }

        let indent = "  ".repeat(entry.depth + 1);
        let _ = writeln!(
            output,
            "{indent}proto#{} parent={} params={} upvalues={} stack={} instrs={} children={} lines={}..{} source={}",
            entry.id,
            entry
                .parent
                .map_or_else(|| "-".to_owned(), |parent| format!("proto#{parent}")),
            entry.proto.signature.num_params,
            entry.proto.upvalues.common.count,
            entry.proto.frame.max_stack_size,
            entry.proto.instrs.len(),
            entry.proto.children.len(),
            entry.proto.line_range.defined_start,
            entry.proto.line_range.defined_end,
            format_optional_source(entry.proto),
        );

        if matches!(detail, DebugDetail::Verbose) {
            let _ = writeln!(
                output,
                "{indent}  raw_instrs={} consts={} low_instrs={}",
                entry.proto.lowering_map.raw_to_low.len(),
                entry.proto.constants.common.literals.len(),
                entry.proto.instrs.len(),
            );
        }
    }
}

fn write_lir_listing(output: &mut String, protos: &[ProtoEntry<'_>], plan: &FocusPlan) {
    let _ = writeln!(output, "low-ir listing");
    if plan.focus.is_none() {
        let _ = writeln!(output, "  <no proto matched filters>");
        return;
    }

    for entry in protos {
        if plan.is_elided(entry.id) {
            let _ = writeln!(
                output,
                "  {}",
                format_proto_summary_row(&build_summary_row(entry)),
            );
            continue;
        }
        if !plan.is_visible(entry.id) {
            continue;
        }

        let _ = writeln!(output, "  proto#{}", entry.id);
        if entry.proto.instrs.is_empty() {
            let _ = writeln!(output, "    <empty>");
            continue;
        }

        for (index, instr) in entry.proto.instrs.iter().enumerate() {
            let pcs = &entry.proto.lowering_map.pc_map[index];
            let raws = &entry.proto.lowering_map.low_to_raw[index];
            let line = entry.proto.lowering_map.line_hints[index]
                .map_or_else(|| "-".to_owned(), |line| line.to_string());

            let _ = writeln!(
                output,
                "    @{index:03} {:<60} origin=pc={} raw={} line={}",
                format_low_instr(instr),
                format_pc_list(pcs),
                format_raw_refs(raws),
                line,
            );
        }
    }
}

fn format_optional_source(proto: &LoweredProto) -> String {
    proto
        .source
        .as_ref()
        .and_then(|source| source.text.as_ref())
        .map_or_else(|| "-".to_owned(), |text| format!("{:?}", text.value))
}

fn dialect_label(version: DecompileDialect) -> &'static str {
    match version {
        DecompileDialect::Auto => "auto",
        DecompileDialect::Lua51 => "lua5.1",
        DecompileDialect::Lua52 => "lua5.2",
        DecompileDialect::Lua53 => "lua5.3",
        DecompileDialect::Lua54 => "lua5.4",
        DecompileDialect::Lua55 => "lua5.5",
        DecompileDialect::Luajit => "luajit",
        DecompileDialect::Luau => "luau",
    }
}

fn format_raw_refs(raws: &[RawInstrRef]) -> String {
    if raws.is_empty() {
        "-".to_owned()
    } else {
        raws.iter()
            .map(|raw| format!("raw#{}", raw.index()))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

fn format_pc_list(pcs: &[u32]) -> String {
    if pcs.is_empty() {
        "-".to_owned()
    } else {
        let joined = pcs
            .iter()
            .map(u32::to_string)
            .collect::<Vec<_>>()
            .join(", ");
        format!("[{joined}]")
    }
}
