//! 这个文件承载 transformer 层对外暴露的调试入口。
//!
//! low-IR 是跨 dialect 共享的稳定契约，因此 dump 视图也应尽量共享实现；
//! stage dump 入口在这里直接从主 pipeline state 读取 LoweredChunk，dialect-specific
//! 的复杂性应该留在 lowering 阶段，而不是再次渗回观察层。

use std::fmt::Write as _;

use crate::debug::{
    DebugColorMode, DebugDetail, DebugFilters, FocusPlan, ProtoSummaryRow, ProtoTreeEntry,
    collect_proto_tree, colorize_debug_text, define_stage_dump, format_breadcrumb,
    format_proto_summary_row, plan_proto_focus,
};
use crate::decompile::DecompileDialect;

use super::{
    DebugLocalKind, LoweredChunk, LoweredProto, RawInstrRef, UpvalueRef, format_low_instr,
};

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
    let protos = collect_proto_tree(&chunk.main, |proto| {
        proto.children.iter().map(|child| child.as_ref())
    });
    let plan = plan_proto_focus(&protos, filters);

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

fn build_summary_row(entry: &ProtoTreeEntry<&LoweredProto>) -> ProtoSummaryRow {
    ProtoSummaryRow {
        id: entry.id,
        name: None,
        first: None,
        lines: Some((
            entry.value.line_range.defined_start,
            entry.value.line_range.defined_end,
        )),
        instrs: Some(entry.value.instrs.len()),
        children: Some(entry.value.children.len()),
    }
}

fn write_proto_tree_view(
    output: &mut String,
    protos: &[ProtoTreeEntry<&LoweredProto>],
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
            "{indent}proto#{} parent={} params={} upvalues={} env-upvalues={} stack={} instrs={} children={} lines={}..{} source={} debug-name={}",
            entry.id,
            entry
                .parent
                .map_or_else(|| "-".to_owned(), |parent| format!("proto#{parent}")),
            entry.value.signature.num_params,
            entry.value.upvalue_count,
            format_environment_upvalues(&entry.value.environment_upvalues),
            entry.value.frame.max_stack_size,
            entry.value.instrs.len(),
            entry.value.children.len(),
            entry.value.line_range.defined_start,
            entry.value.line_range.defined_end,
            format_optional_source(entry.value),
            format_optional_raw_string(entry.value.debug_name.as_ref()),
        );

        if matches!(detail, DebugDetail::Verbose) {
            let _ = writeln!(
                output,
                "{indent}  raw_instrs={} consts={} low_instrs={} debug_locals={}",
                entry.value.lowering_map.raw_to_low.len(),
                entry.value.constants.len(),
                entry.value.instrs.len(),
                entry.value.debug_locals.len(),
            );
        }
    }
}

fn format_environment_upvalues(upvalues: &[UpvalueRef]) -> String {
    if upvalues.is_empty() {
        "-".to_owned()
    } else {
        upvalues
            .iter()
            .map(|upvalue| format!("u{}", upvalue.index()))
            .collect::<Vec<_>>()
            .join(",")
    }
}

fn write_lir_listing(
    output: &mut String,
    protos: &[ProtoTreeEntry<&LoweredProto>],
    plan: &FocusPlan,
) {
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
        let _ = writeln!(output, "    debug locals");
        if entry.value.debug_locals.is_empty() {
            let _ = writeln!(output, "      <none>");
        } else {
            for (scope, local) in entry.value.debug_locals.iter().enumerate() {
                let kind = match local.kind {
                    DebugLocalKind::Source => "source",
                    DebugLocalKind::CompilerInternal => "compiler-internal",
                };
                let name = local.name.text.as_ref().map_or_else(
                    || String::from_utf8_lossy(&local.name.bytes).into_owned(),
                    |text| text.value.to_string(),
                );
                let _ = writeln!(
                    output,
                    "      scope#{scope} {kind} name={name:?} r{} pc={}..{}",
                    local.reg.index(),
                    local.start_pc,
                    local.end_pc,
                );
            }
        }
        let _ = writeln!(output, "    instructions");
        if entry.value.instrs.is_empty() {
            let _ = writeln!(output, "      <empty>");
            continue;
        }

        for (index, instr) in entry.value.instrs.iter().enumerate() {
            let pcs = &entry.value.lowering_map.pc_map()[index];
            let raws = &entry.value.lowering_map.low_to_raw[index];
            let line = entry.value.lowering_map.line_hints[index]
                .map_or_else(|| "-".to_owned(), |line| line.to_string());

            let _ = writeln!(
                output,
                "      @{index:03} {:<60} origin=pc={} raw={} line={}",
                format_low_instr(instr),
                format_pc_list(pcs),
                format_raw_refs(raws),
                line,
            );
        }
    }
}

fn format_optional_source(proto: &LoweredProto) -> String {
    format_optional_raw_string(proto.source.as_ref())
}

fn format_optional_raw_string(source: Option<&crate::parser::RawString>) -> String {
    source
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
