//! 这个文件实现 Lua 5.4 parser 的专用调试视图。
//!
//! 它不追求和 5.3 dump 完全逐字对齐，但会把 5.4 新增的 header 差异、upvalue
//! `kind`、`line_deltas/abs_line_info`、以及 7-bit opcode 解析结果稳定地打出来。

use std::fmt::Write as _;

use crate::debug::{
    DebugColorMode, DebugDetail, DebugFilters, FocusPlan, colorize_debug_text,
    format_proto_summary_row,
};
use crate::parser::debug::{build_parser_summary_row, ParserProtoEntry};
use crate::parser::{
    ChunkHeader, DecodedText, Endianness, Origin, RawChunk, RawInstr, RawLiteralConst, RawProto,
    RawString,
};

use super::raw::{Lua54DebugExtra, Lua54InstrExtra, Lua54Opcode, Lua54Operands, Lua54UpvalueExtra};

#[derive(Debug, Clone, Copy)]
struct ProtoEntry<'a> {
    id: usize,
    parent: Option<usize>,
    depth: usize,
    proto: &'a RawProto,
}

pub(crate) fn dump_chunk(
    chunk: &RawChunk,
    detail: DebugDetail,
    filters: &DebugFilters,
    color: DebugColorMode,
) -> String {
    let mut output = String::new();
    let protos = collect_proto_entries(&chunk.main);
    let plan = plan_focus(&protos, filters);

    let _ = writeln!(output, "===== Dump Parser =====");
    let _ = writeln!(
        output,
        "parser dialect=lua5.4 detail={} protos={}",
        detail,
        protos.len()
    );
    if let Some(proto_id) = filters.proto {
        let _ = writeln!(output, "filters proto=proto#{proto_id}");
    }
    let _ = writeln!(output, "filters proto_depth={}", filters.proto_depth);
    if let Some(breadcrumb) = crate::debug::format_breadcrumb(&plan) {
        let _ = writeln!(output, "focus {breadcrumb}");
    }
    let _ = writeln!(output);

    write_header_view(&mut output, &chunk.header);
    let _ = writeln!(output);
    write_proto_tree_view(&mut output, &protos, &plan, detail);

    if !matches!(detail, DebugDetail::Summary) {
        let _ = writeln!(output);
        write_constants_view(&mut output, &protos, &plan);
        let _ = writeln!(output);
        write_raw_instructions_view(&mut output, &protos, &plan, detail);
    }

    colorize_debug_text(&output, color)
}

fn collect_proto_entries(root: &RawProto) -> Vec<ProtoEntry<'_>> {
    let mut entries = Vec::new();
    collect_proto_entries_inner(root, None, 0, &mut entries);
    entries
}

fn collect_proto_entries_inner<'a>(
    proto: &'a RawProto,
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

    for child in &proto.common.children {
        collect_proto_entries_inner(child, Some(id), depth + 1, entries);
    }
}

fn plan_focus(protos: &[ProtoEntry<'_>], filters: &DebugFilters) -> FocusPlan {
    let parents: Vec<Option<usize>> = protos.iter().map(|e| e.parent).collect();
    let nodes = crate::debug::build_proto_nodes(&parents);
    crate::debug::compute_focus_plan(&nodes, &filters.as_focus_request())
}

fn to_shared_entry<'a>(entry: &ProtoEntry<'a>) -> ParserProtoEntry<'a> {
    ParserProtoEntry {
        id: entry.id,
        parent: entry.parent,
        depth: entry.depth,
        proto: entry.proto,
    }
}

fn write_elided_row(output: &mut String, indent: &str, entry: &ProtoEntry<'_>) {
    let _ = writeln!(
        output,
        "{indent}{}",
        format_proto_summary_row(&build_parser_summary_row(&to_shared_entry(entry))),
    );
}

fn write_header_view(output: &mut String, header: &ChunkHeader) {
    let layout = header
        .puc_lua_layout()
        .expect("lua54 debug should only receive puc-lua chunk layouts");
    let _ = writeln!(output, "header");
    let _ = writeln!(output, "  dialect: puc-lua");
    let _ = writeln!(output, "  version: lua5.4");
    let _ = writeln!(output, "  format: {}", layout.format);
    let _ = writeln!(
        output,
        "  endianness: {}",
        format_endianness(layout.endianness)
    );
    let _ = writeln!(output, "  integer_size: {}", layout.integer_size);
    if let Some(lua_integer_size) = layout.lua_integer_size {
        let _ = writeln!(output, "  lua_integer_size: {lua_integer_size}");
    }
    let _ = writeln!(output, "  size_t_size: {}", layout.size_t_size);
    let _ = writeln!(output, "  instruction_size: {}", layout.instruction_size);
    let _ = writeln!(output, "  number_size: {}", layout.number_size);
    let _ = writeln!(output, "  integral_number: {}", layout.integral_number);
    let _ = writeln!(output, "  origin: {}", format_origin(header.origin));
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
            write_elided_row(output, &indent, entry);
            continue;
        }
        if !plan.is_visible(entry.id) {
            continue;
        }

        let indent = "  ".repeat(entry.depth + 1);
        let common = &entry.proto.common;
        let _ = writeln!(
            output,
            "{indent}proto#{} parent={} params={} upvalues={} stack={} instrs={} consts={} children={} lines={}..{} source={}",
            entry.id,
            entry
                .parent
                .map_or_else(|| "-".to_owned(), |parent| format!("proto#{parent}")),
            common.signature.num_params,
            common.upvalues.common.count,
            common.frame.max_stack_size,
            common.instructions.len(),
            common.constants.common.literals.len(),
            common.children.len(),
            common.line_range.defined_start,
            common.line_range.defined_end,
            format_optional_source(common.source.as_ref()),
        );

        if matches!(detail, DebugDetail::Verbose) {
            let debug_extra = lua54_debug_extra(entry.proto);
            let _ = writeln!(
                output,
                "{indent}  origin={} vararg={} raw_vararg={} debug_lines={} line_deltas={} abs_lines={} locals={} upvalue_names={} upvalue_descs={}",
                format_origin(entry.proto.origin),
                common.signature.is_vararg,
                raw_vararg_bits(entry.proto),
                common.debug_info.common.line_info.len(),
                debug_extra.line_deltas.len(),
                debug_extra.abs_line_info.len(),
                common.debug_info.common.local_vars.len(),
                common.debug_info.common.upvalue_names.len(),
                common.upvalues.common.descriptors.len(),
            );
        }
    }
}

fn write_constants_view(output: &mut String, protos: &[ProtoEntry<'_>], plan: &FocusPlan) {
    let _ = writeln!(output, "constants");
    if plan.focus.is_none() {
        let _ = writeln!(output, "  <no proto matched filters>");
        return;
    }

    for entry in protos {
        if plan.is_elided(entry.id) {
            write_elided_row(output, "  ", entry);
            continue;
        }
        if !plan.is_visible(entry.id) {
            continue;
        }

        let _ = writeln!(output, "  proto#{}", entry.id);
        let literals = &entry.proto.common.constants.common.literals;
        if literals.is_empty() {
            let _ = writeln!(output, "    <empty>");
        } else {
            for (index, literal) in literals.iter().enumerate() {
                let _ = writeln!(output, "    k{index:<3} {}", format_literal(literal));
            }
        }
    }
}

fn write_raw_instructions_view(
    output: &mut String,
    protos: &[ProtoEntry<'_>],
    plan: &FocusPlan,
    detail: DebugDetail,
) {
    let _ = writeln!(output, "raw instructions");
    if plan.focus.is_none() {
        let _ = writeln!(output, "  <no proto matched filters>");
        return;
    }

    for entry in protos {
        if plan.is_elided(entry.id) {
            write_elided_row(output, "  ", entry);
            continue;
        }
        if !plan.is_visible(entry.id) {
            continue;
        }

        let _ = writeln!(output, "  proto#{}", entry.id);
        let instructions = &entry.proto.common.instructions;
        if instructions.is_empty() {
            let _ = writeln!(output, "    <empty>");
        } else {
            for instruction in instructions {
                let (opcode, operands, extra) = decode_lua54(instruction);
                let _ = writeln!(
                    output,
                    "    pc={:03} opcode={:<10} operands={} origin={}",
                    extra.pc,
                    opcode.label(),
                    operands.label(),
                    format_origin(instruction.origin),
                );

                if matches!(detail, DebugDetail::Verbose) {
                    let _ = writeln!(
                        output,
                        "      raw_word={} word_len={} extra_arg={} line={}",
                        format_optional_raw_word(instruction.origin.raw_word),
                        extra.word_len,
                        format_optional_u32(extra.extra_arg),
                        format_optional_line(
                            entry
                                .proto
                                .common
                                .debug_info
                                .common
                                .line_info
                                .get(extra.pc as usize,)
                        ),
                    );
                }
            }
        }

        if matches!(detail, DebugDetail::Verbose) {
            write_verbose_debug_info(output, entry.proto);
        }
    }
}

fn write_verbose_debug_info(output: &mut String, proto: &RawProto) {
    let debug_info = &proto.common.debug_info;
    let debug_extra = lua54_debug_extra(proto);
    let upvalue_extra = lua54_upvalue_extra(proto);

    let _ = writeln!(output, "    upvalue_descs");
    if proto.common.upvalues.common.descriptors.is_empty() {
        let _ = writeln!(output, "      <empty>");
    } else {
        for (index, descriptor) in proto.common.upvalues.common.descriptors.iter().enumerate() {
            let kind = upvalue_extra.kinds.get(index).copied().unwrap_or_default();
            let _ = writeln!(
                output,
                "      u{index:<3} instack={} idx={} kind={}",
                descriptor.in_stack, descriptor.index, kind
            );
        }
    }

    let _ = writeln!(output, "    abs_line_info");
    if debug_extra.abs_line_info.is_empty() {
        let _ = writeln!(output, "      <empty>");
    } else {
        for entry in &debug_extra.abs_line_info {
            let _ = writeln!(output, "      pc={} line={}", entry.pc, entry.line);
        }
    }

    let _ = writeln!(output, "    debug locals");
    if debug_info.common.local_vars.is_empty() {
        let _ = writeln!(output, "      <empty>");
    } else {
        for local in &debug_info.common.local_vars {
            let _ = writeln!(
                output,
                "      {} [{}..{}]",
                format_raw_string(&local.name),
                local.start_pc,
                local.end_pc,
            );
        }
    }

    let _ = writeln!(output, "    debug upvalue names");
    if debug_info.common.upvalue_names.is_empty() {
        let _ = writeln!(output, "      <empty>");
    } else {
        for (index, name) in debug_info.common.upvalue_names.iter().enumerate() {
            let _ = writeln!(output, "      u{index:<3} {}", format_raw_string(name));
        }
    }
}

fn format_optional_source(source: Option<&RawString>) -> String {
    source.map_or_else(|| "-".to_owned(), format_raw_string)
}

fn format_raw_string(raw: &RawString) -> String {
    match raw.text.as_ref() {
        Some(DecodedText { value, .. }) => format!("{value:?}"),
        None => format!("<{} bytes>", raw.bytes.len()),
    }
}

fn format_literal(literal: &RawLiteralConst) -> String {
    match literal {
        RawLiteralConst::Nil => "nil".to_owned(),
        RawLiteralConst::Boolean(value) => format!("bool({value})"),
        RawLiteralConst::Integer(value) => format!("int({value})"),
        RawLiteralConst::Number(value) => format!("num({value})"),
        RawLiteralConst::String(value) => format!("str({})", format_raw_string(value)),
        RawLiteralConst::Int64(value) => format!("i64({value})"),
        RawLiteralConst::UInt64(value) => format!("u64({value})"),
        RawLiteralConst::Complex { real, imag } => format!("complex({real},{imag})"),
    }
}

fn format_origin(origin: Origin) -> String {
    let end = origin.span.offset + origin.span.size;
    let raw = format_optional_raw_word(origin.raw_word);
    format!("[{}..{} raw={}]", origin.span.offset, end, raw)
}

fn format_optional_raw_word(raw_word: Option<u64>) -> String {
    raw_word.map_or_else(|| "-".to_owned(), |word| format!("0x{word:08x}"))
}

fn format_optional_u32(value: Option<u32>) -> String {
    value.map_or_else(|| "-".to_owned(), |value| value.to_string())
}

fn format_optional_line(line: Option<&u32>) -> String {
    line.map_or_else(|| "-".to_owned(), |line| line.to_string())
}

fn format_endianness(endianness: Endianness) -> &'static str {
    match endianness {
        Endianness::Little => "little",
        Endianness::Big => "big",
    }
}

fn raw_vararg_bits(proto: &RawProto) -> u8 {
    proto
        .extra
        .lua54()
        .expect("lua54 debug should only receive lua54 proto extras")
        .raw_is_vararg
}

fn lua54_debug_extra(proto: &RawProto) -> &Lua54DebugExtra {
    proto
        .common
        .debug_info
        .extra
        .lua54()
        .expect("lua54 debug should only receive lua54 debug extras")
}

fn lua54_upvalue_extra(proto: &RawProto) -> &Lua54UpvalueExtra {
    proto
        .common
        .upvalues
        .extra
        .lua54()
        .expect("lua54 debug should only receive lua54 upvalue extras")
}

fn decode_lua54(raw: &RawInstr) -> (Lua54Opcode, &Lua54Operands, Lua54InstrExtra) {
    let opcode = raw
        .opcode
        .lua54()
        .expect("lua54 debug should only receive lua54 opcodes");
    let operands = raw
        .operands
        .lua54()
        .expect("lua54 debug should only receive lua54 operands");
    let extra = raw
        .extra
        .lua54()
        .expect("lua54 debug should only receive lua54 instruction extras");
    (*opcode, operands, *extra)
}

trait Lua54OperandsDebugExt {
    fn label(&self) -> String;
}

impl Lua54OperandsDebugExt for Lua54Operands {
    fn label(&self) -> String {
        match self {
            Lua54Operands::None => "-".to_owned(),
            Lua54Operands::A { a } => format!("A={a}"),
            Lua54Operands::Ak { a, k } => format!("A={a} k={}", u8::from(*k)),
            Lua54Operands::AB { a, b } => format!("A={a} B={b}"),
            Lua54Operands::AC { a, c } => format!("A={a} C={c}"),
            Lua54Operands::ABk { a, b, k } => format!("A={a} B={b} k={}", u8::from(*k)),
            Lua54Operands::ABCk { a, b, c, k } => {
                format!("A={a} B={b} C={c} k={}", u8::from(*k))
            }
            Lua54Operands::ABx { a, bx } => format!("A={a} Bx={bx}"),
            Lua54Operands::AsBx { a, sbx } => format!("A={a} sBx={sbx}"),
            Lua54Operands::AsJ { sj } => format!("sJ={sj}"),
            Lua54Operands::Ax { ax } => format!("Ax={ax}"),
            Lua54Operands::ABsCk { a, b, sc, k } => {
                format!("A={a} B={b} sC={sc} k={}", u8::from(*k))
            }
            Lua54Operands::AsBCk { a, sb, c, k } => {
                format!("A={a} sB={sb} C={c} k={}", u8::from(*k))
            }
        }
    }
}
