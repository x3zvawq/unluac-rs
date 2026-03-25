//! 这个文件实现 Lua 5.2 parser 的专用调试视图。
//!
//! 它和 Lua 5.1 的 dump 形状保持一致，这样不同版本的 parser 输出可以横向对比；
//! 同时把 5.2 的 upvalue 描述符、`LOADKX/SETLIST` 绑定的 `EXTRAARG` 等事实显式打出来。

use std::fmt::Write as _;

use crate::debug::{DebugDetail, DebugFilters};
use crate::parser::{
    ChunkHeader, DecodedText, Dialect, DialectConstPoolExtra, DialectDebugExtra,
    DialectHeaderExtra, DialectInstrExtra, DialectProtoExtra, DialectUpvalueExtra, DialectVersion,
    Endianness, Origin, RawChunk, RawInstr, RawInstrOpcode, RawInstrOperands, RawLiteralConst,
    RawProto, RawString,
};

use super::raw::{
    Lua52ConstPoolExtra, Lua52DebugExtra, Lua52HeaderExtra, Lua52InstrExtra, Lua52Opcode,
    Lua52Operands, Lua52ProtoExtra, Lua52UpvalueExtra,
};

#[derive(Debug, Clone, Copy)]
struct ProtoEntry<'a> {
    id: usize,
    parent: Option<usize>,
    depth: usize,
    proto: &'a RawProto,
}

pub(crate) fn dump_chunk(chunk: &RawChunk, detail: DebugDetail, filters: &DebugFilters) -> String {
    render_human(chunk, detail, filters)
}

fn render_human(chunk: &RawChunk, detail: DebugDetail, filters: &DebugFilters) -> String {
    let mut output = String::new();
    let protos = collect_proto_entries(&chunk.main);
    let visible_protos = visible_proto_ids(&protos, filters);

    let _ = writeln!(output, "===== Dump Parser =====");
    let _ = writeln!(
        output,
        "parser dialect={} detail={} protos={}",
        chunk.header.version_label(),
        detail,
        protos.len()
    );
    if let Some(proto_id) = filters.proto {
        let _ = writeln!(output, "filters proto=proto#{proto_id}");
    }
    let _ = writeln!(output);

    write_header_view(&mut output, &chunk.header);
    let _ = writeln!(output);
    write_proto_tree_view(&mut output, &protos, &visible_protos, detail);

    if !matches!(detail, DebugDetail::Summary) {
        let _ = writeln!(output);
        write_constants_view(&mut output, &protos, &visible_protos);
        let _ = writeln!(output);
        write_raw_instructions_view(&mut output, &protos, &visible_protos, detail);
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

fn visible_proto_ids(protos: &[ProtoEntry<'_>], filters: &DebugFilters) -> Vec<usize> {
    match filters.proto {
        Some(id) if protos.iter().any(|entry| entry.id == id) => vec![id],
        Some(_) => Vec::new(),
        None => protos.iter().map(|entry| entry.id).collect(),
    }
}

fn write_header_view(output: &mut String, header: &ChunkHeader) {
    let _ = writeln!(output, "header");
    let _ = writeln!(output, "  dialect: {}", header.dialect_label());
    let _ = writeln!(output, "  version: {}", header.version_label());
    let _ = writeln!(output, "  format: {}", header.format);
    let _ = writeln!(output, "  endianness: {}", header.endianness_label());
    let _ = writeln!(output, "  integer_size: {}", header.integer_size);
    let _ = writeln!(output, "  size_t_size: {}", header.size_t_size);
    let _ = writeln!(output, "  instruction_size: {}", header.instruction_size);
    let _ = writeln!(output, "  number_size: {}", header.number_size);
    let _ = writeln!(output, "  integral_number: {}", header.integral_number);
    let _ = writeln!(output, "  origin: {}", format_origin(header.origin));

    match &header.extra {
        DialectHeaderExtra::Lua52(extra) => {
            let Lua52HeaderExtra = extra;
        }
        DialectHeaderExtra::Lua51(_) => {}
    }
}

fn write_proto_tree_view(
    output: &mut String,
    protos: &[ProtoEntry<'_>],
    visible_protos: &[usize],
    detail: DebugDetail,
) {
    let _ = writeln!(output, "proto tree");
    if visible_protos.is_empty() {
        let _ = writeln!(output, "  <no proto matched filters>");
        return;
    }

    for entry in protos {
        if !visible_protos.contains(&entry.id) {
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
                entry.proto.raw_vararg_bits(),
                common.debug_info.common.line_info.len(),
                common.debug_info.common.local_vars.len(),
                common.debug_info.common.upvalue_names.len(),
                common.upvalues.common.descriptors.len(),
            );
        }
    }
}

fn write_constants_view(output: &mut String, protos: &[ProtoEntry<'_>], visible_protos: &[usize]) {
    let _ = writeln!(output, "constants");
    if visible_protos.is_empty() {
        let _ = writeln!(output, "  <no proto matched filters>");
        return;
    }

    for entry in protos {
        if !visible_protos.contains(&entry.id) {
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

        match &entry.proto.common.constants.extra {
            DialectConstPoolExtra::Lua52(extra) => {
                let Lua52ConstPoolExtra = extra;
            }
            DialectConstPoolExtra::Lua51(_) => {}
        }
    }
}

fn write_raw_instructions_view(
    output: &mut String,
    protos: &[ProtoEntry<'_>],
    visible_protos: &[usize],
    detail: DebugDetail,
) {
    let _ = writeln!(output, "raw instructions");
    if visible_protos.is_empty() {
        let _ = writeln!(output, "  <no proto matched filters>");
        return;
    }

    for entry in protos {
        if !visible_protos.contains(&entry.id) {
            continue;
        }

        let _ = writeln!(output, "  proto#{}", entry.id);
        let instructions = &entry.proto.common.instructions;
        if instructions.is_empty() {
            let _ = writeln!(output, "    <empty>");
        } else {
            for instruction in instructions {
                let _ = writeln!(
                    output,
                    "    pc={:03} opcode={:<10} operands={} origin={}",
                    instruction.pc(),
                    instruction.opcode_label(),
                    instruction.operands_label(),
                    format_origin(instruction.origin),
                );

                if matches!(detail, DebugDetail::Verbose) {
                    let _ = writeln!(
                        output,
                        "      raw_word={} word_len={} extra_arg={} line={}",
                        format_optional_raw_word(instruction.origin.raw_word),
                        instruction.word_len(),
                        format_optional_u32(instruction.extra_arg()),
                        format_optional_line(
                            entry
                                .proto
                                .common
                                .debug_info
                                .common
                                .line_info
                                .get(instruction.pc())
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

    match &debug_info.extra {
        DialectDebugExtra::Lua52(extra) => {
            let Lua52DebugExtra = extra;
        }
        DialectDebugExtra::Lua51(_) => {}
    }
    match &proto.common.upvalues.extra {
        DialectUpvalueExtra::Lua52(extra) => {
            let Lua52UpvalueExtra = extra;
        }
        DialectUpvalueExtra::Lua51(_) => {}
    }

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

trait HeaderDebugExt {
    fn dialect_label(&self) -> &'static str;
    fn version_label(&self) -> &'static str;
    fn endianness_label(&self) -> &'static str;
}

impl HeaderDebugExt for ChunkHeader {
    fn dialect_label(&self) -> &'static str {
        match self.dialect {
            Dialect::PucLua => "puc-lua",
        }
    }

    fn version_label(&self) -> &'static str {
        match self.version {
            DialectVersion::Lua51 => "lua5.1",
            DialectVersion::Lua52 => "lua5.2",
        }
    }

    fn endianness_label(&self) -> &'static str {
        match self.endianness {
            Endianness::Little => "little",
            Endianness::Big => "big",
        }
    }
}

trait RawProtoDebugExt {
    fn raw_vararg_bits(&self) -> u8;
}

impl RawProtoDebugExt for RawProto {
    fn raw_vararg_bits(&self) -> u8 {
        match &self.extra {
            DialectProtoExtra::Lua52(Lua52ProtoExtra { raw_is_vararg }) => *raw_is_vararg,
            DialectProtoExtra::Lua51(_) => 0,
        }
    }
}

trait RawInstrDebugExt {
    fn pc(&self) -> usize;
    fn word_len(&self) -> u8;
    fn extra_arg(&self) -> Option<u32>;
    fn opcode_label(&self) -> &'static str;
    fn operands_label(&self) -> String;
}

impl RawInstrDebugExt for RawInstr {
    fn pc(&self) -> usize {
        match &self.extra {
            DialectInstrExtra::Lua52(Lua52InstrExtra { pc, .. }) => *pc as usize,
            DialectInstrExtra::Lua51(_) => 0,
        }
    }

    fn word_len(&self) -> u8 {
        match &self.extra {
            DialectInstrExtra::Lua52(Lua52InstrExtra { word_len, .. }) => *word_len,
            DialectInstrExtra::Lua51(_) => 1,
        }
    }

    fn extra_arg(&self) -> Option<u32> {
        match &self.extra {
            DialectInstrExtra::Lua52(Lua52InstrExtra { extra_arg, .. }) => *extra_arg,
            DialectInstrExtra::Lua51(_) => None,
        }
    }

    fn opcode_label(&self) -> &'static str {
        match self.opcode {
            RawInstrOpcode::Lua52(opcode) => opcode.label(),
            RawInstrOpcode::Lua51(_) => "-",
        }
    }

    fn operands_label(&self) -> String {
        match &self.operands {
            RawInstrOperands::Lua52(operands) => operands.label(),
            RawInstrOperands::Lua51(_) => "-".to_owned(),
        }
    }
}

trait Lua52OpcodeDebugExt {
    fn label(self) -> &'static str;
}

impl Lua52OpcodeDebugExt for Lua52Opcode {
    fn label(self) -> &'static str {
        match self {
            Self::Move => "MOVE",
            Self::LoadK => "LOADK",
            Self::LoadKx => "LOADKX",
            Self::LoadBool => "LOADBOOL",
            Self::LoadNil => "LOADNIL",
            Self::GetUpVal => "GETUPVAL",
            Self::GetTabUp => "GETTABUP",
            Self::GetTable => "GETTABLE",
            Self::SetTabUp => "SETTABUP",
            Self::SetUpVal => "SETUPVAL",
            Self::SetTable => "SETTABLE",
            Self::NewTable => "NEWTABLE",
            Self::Self_ => "SELF",
            Self::Add => "ADD",
            Self::Sub => "SUB",
            Self::Mul => "MUL",
            Self::Div => "DIV",
            Self::Mod => "MOD",
            Self::Pow => "POW",
            Self::Unm => "UNM",
            Self::Not => "NOT",
            Self::Len => "LEN",
            Self::Concat => "CONCAT",
            Self::Jmp => "JMP",
            Self::Eq => "EQ",
            Self::Lt => "LT",
            Self::Le => "LE",
            Self::Test => "TEST",
            Self::TestSet => "TESTSET",
            Self::Call => "CALL",
            Self::TailCall => "TAILCALL",
            Self::Return => "RETURN",
            Self::ForLoop => "FORLOOP",
            Self::ForPrep => "FORPREP",
            Self::TForCall => "TFORCALL",
            Self::TForLoop => "TFORLOOP",
            Self::SetList => "SETLIST",
            Self::Closure => "CLOSURE",
            Self::VarArg => "VARARG",
            Self::ExtraArg => "EXTRAARG",
        }
    }
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
