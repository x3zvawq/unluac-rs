//! 这个文件实现 Lua 5.2 parser 的专用调试视图。
//!
//! 它和 Lua 5.1 的 dump 形状保持一致，这样不同版本的 parser 输出可以横向对比；
//! 同时把 5.2 的 upvalue 描述符、`LOADKX/SETLIST` 绑定的 `EXTRAARG` 等事实显式打出来。

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

use super::raw::{Lua52InstrExtra, Lua52Opcode, Lua52Operands};

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
    colorize_debug_text(&render_human(chunk, detail, filters), color)
}

fn render_human(chunk: &RawChunk, detail: DebugDetail, filters: &DebugFilters) -> String {
    let mut output = String::new();
    let protos = collect_proto_entries(&chunk.main);
    let plan = plan_focus(&protos, filters);

    let _ = writeln!(output, "===== Dump Parser =====");
    let _ = writeln!(
        output,
        "parser dialect=lua5.2 detail={} protos={}",
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

    output
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
        .expect("lua52 debug should only receive puc-lua chunk layouts");
    let _ = writeln!(output, "header");
    let _ = writeln!(output, "  dialect: puc-lua");
    let _ = writeln!(output, "  version: lua5.2");
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
            let _ = writeln!(
                output,
                "{indent}  origin={} vararg={} raw_vararg={} debug_lines={} locals={} upvalue_names={} upvalue_descs={}",
                format_origin(entry.proto.origin),
                common.signature.is_vararg,
                raw_vararg_bits(entry.proto),
                common.debug_info.common.line_info.len(),
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
                let (opcode, operands, extra) = decode_lua52(instruction);
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

    let descriptors = &proto.common.upvalues.common.descriptors;
    if descriptors.is_empty() {
        let _ = writeln!(output, "      upvalue_descs=<empty>");
    } else {
        let _ = writeln!(output, "      upvalue_descs");
        for (index, descriptor) in descriptors.iter().enumerate() {
            let _ = writeln!(
                output,
                "        u{index}: instack={} idx={}",
                descriptor.in_stack, descriptor.index,
            );
        }
    }

    let locals = &debug_info.common.local_vars;
    if locals.is_empty() {
        let _ = writeln!(output, "      locals=<empty>");
    } else {
        let _ = writeln!(output, "      locals");
        for local in locals {
            let _ = writeln!(
                output,
                "        {} [{}..{}]",
                format_raw_string(&local.name),
                local.start_pc,
                local.end_pc,
            );
        }
    }

    let upvalue_names = &debug_info.common.upvalue_names;
    if upvalue_names.is_empty() {
        let _ = writeln!(output, "      upvalue_names=<empty>");
    } else {
        let _ = writeln!(output, "      upvalue_names");
        for (index, name) in upvalue_names.iter().enumerate() {
            let _ = writeln!(output, "        u{index}: {}", format_raw_string(name));
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
        .lua52()
        .expect("lua52 debug should only receive lua52 proto extras")
        .raw_is_vararg
}

fn decode_lua52(raw: &RawInstr) -> (Lua52Opcode, &Lua52Operands, Lua52InstrExtra) {
    let opcode = raw
        .opcode
        .lua52()
        .expect("lua52 debug should only receive lua52 opcodes");
    let operands = raw
        .operands
        .lua52()
        .expect("lua52 debug should only receive lua52 operands");
    let extra = raw
        .extra
        .lua52()
        .expect("lua52 debug should only receive lua52 instruction extras");
    (*opcode, operands, *extra)
}

trait Lua52OperandsDebugExt {
    fn label(&self) -> String;
}

impl Lua52OperandsDebugExt for Lua52Operands {
    fn label(&self) -> String {
        match self {
            Self::A { a } => format!("A(a={a})"),
            Self::AB { a, b } => format!("AB(a={a}, b={b})"),
            Self::AC { a, c } => format!("AC(a={a}, c={c})"),
            Self::ABC { a, b, c } => format!("ABC(a={a}, b={b}, c={c})"),
            Self::ABx { a, bx } => format!("ABx(a={a}, bx={bx})"),
            Self::AsBx { a, sbx } => format!("AsBx(a={a}, sbx={sbx})"),
            Self::Ax { ax } => format!("Ax(ax={ax})"),
        }
    }
}
