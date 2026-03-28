//! 这个文件实现 Lua 5.1 parser 的专用调试视图。
//!
//! 它放在 dialect 实现旁边，而不是继续堆在主 pipeline 里，是为了让“解析规则”
//! 和“如何观察这些解析结果”保持邻近，后续扩 dialect 时也不会互相挤在一起。

use std::fmt::Write as _;

use crate::debug::{DebugColorMode, DebugDetail, DebugFilters, colorize_debug_text};
use crate::parser::{
    ChunkHeader, DecodedText, Dialect, DialectConstPoolExtra, DialectDebugExtra,
    DialectHeaderExtra, DialectInstrExtra, DialectProtoExtra, DialectUpvalueExtra, DialectVersion,
    Endianness, Origin, RawChunk, RawInstr, RawInstrOpcode, RawInstrOperands, RawLiteralConst,
    RawProto, RawString,
};

use super::raw::{
    Lua51ConstPoolExtra, Lua51DebugExtra, Lua51HeaderExtra, Lua51InstrExtra, Lua51Opcode,
    Lua51Operands, Lua51ProtoExtra, Lua51UpvalueExtra,
};

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
    let layout = header
        .puc_lua_layout()
        .expect("lua51 debug should only receive puc-lua chunk layouts");
    let _ = writeln!(output, "header");
    let _ = writeln!(output, "  dialect: {}", header.dialect_label());
    let _ = writeln!(output, "  version: {}", header.version_label());
    let _ = writeln!(output, "  format: {}", layout.format);
    let _ = writeln!(output, "  endianness: {}", header.endianness_label());
    let _ = writeln!(output, "  integer_size: {}", layout.integer_size);
    if let Some(lua_integer_size) = layout.lua_integer_size {
        let _ = writeln!(output, "  lua_integer_size: {lua_integer_size}");
    }
    let _ = writeln!(output, "  size_t_size: {}", layout.size_t_size);
    let _ = writeln!(output, "  instruction_size: {}", layout.instruction_size);
    let _ = writeln!(output, "  number_size: {}", layout.number_size);
    let _ = writeln!(output, "  integral_number: {}", layout.integral_number);
    let _ = writeln!(output, "  origin: {}", format_origin(header.origin));

    match &header.extra {
        DialectHeaderExtra::Lua51(extra) => {
            let Lua51HeaderExtra = extra;
        }
        DialectHeaderExtra::Lua52(_) => {
            unreachable!("lua51 debug should not receive lua52 header extras")
        }
        DialectHeaderExtra::Lua53(_) => {
            unreachable!("lua51 debug should not receive lua53 header extras")
        }
        DialectHeaderExtra::Lua54(_) => {
            unreachable!("lua51 debug should not receive lua54 header extras")
        }
        _ => unreachable!("lua51 debug should not receive non-lua51 header extras"),
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
                "{indent}  origin={} vararg={} raw_vararg={} debug_lines={} locals={} upvalue_names={}",
                format_origin(entry.proto.origin),
                common.signature.is_vararg,
                entry.proto.raw_vararg_bits(),
                common.debug_info.common.line_info.len(),
                common.debug_info.common.local_vars.len(),
                common.debug_info.common.upvalue_names.len(),
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
            continue;
        }

        for (index, literal) in literals.iter().enumerate() {
            let _ = writeln!(output, "    k{index:<3} {}", format_literal(literal));
        }

        match &entry.proto.common.constants.extra {
            DialectConstPoolExtra::Lua51(extra) => {
                let Lua51ConstPoolExtra = extra;
            }
            DialectConstPoolExtra::Lua52(_) => {
                unreachable!("lua51 debug should not receive lua52 const-pool extras")
            }
            DialectConstPoolExtra::Lua53(_) => {
                unreachable!("lua51 debug should not receive lua53 const-pool extras")
            }
            DialectConstPoolExtra::Lua54(_) => {
                unreachable!("lua51 debug should not receive lua54 const-pool extras")
            }
            _ => unreachable!("lua51 debug should not receive non-lua51 const-pool extras"),
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
                        "      raw_word={} word_len={} setlist_extra={} line={}",
                        format_optional_raw_word(instruction.origin.raw_word),
                        instruction.word_len(),
                        format_optional_u32(instruction.setlist_extra_arg()),
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
        DialectDebugExtra::Lua51(extra) => {
            let Lua51DebugExtra = extra;
        }
        DialectDebugExtra::Lua52(_) => {
            unreachable!("lua51 debug should not receive lua52 debug extras")
        }
        DialectDebugExtra::Lua53(_) => {
            unreachable!("lua51 debug should not receive lua53 debug extras")
        }
        DialectDebugExtra::Lua54(_) => {
            unreachable!("lua51 debug should not receive lua54 debug extras")
        }
        _ => unreachable!("lua51 debug should not receive non-lua51 debug extras"),
    }
    match &proto.common.upvalues.extra {
        DialectUpvalueExtra::Lua51(extra) => {
            let Lua51UpvalueExtra = extra;
        }
        DialectUpvalueExtra::Lua52(_) => {
            unreachable!("lua51 debug should not receive lua52 upvalue extras")
        }
        DialectUpvalueExtra::Lua53(_) => {
            unreachable!("lua51 debug should not receive lua53 upvalue extras")
        }
        DialectUpvalueExtra::Lua54(_) => {
            unreachable!("lua51 debug should not receive lua54 upvalue extras")
        }
        _ => unreachable!("lua51 debug should not receive non-lua51 upvalue extras"),
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

trait HeaderDebugExt {
    fn dialect_label(&self) -> &'static str;
    fn version_label(&self) -> &'static str;
    fn endianness_label(&self) -> &'static str;
}

impl HeaderDebugExt for ChunkHeader {
    fn dialect_label(&self) -> &'static str {
        match self.dialect {
            Dialect::PucLua => "puc-lua",
            Dialect::LuaJit => "luajit",
            Dialect::Luau => "luau",
        }
    }

    fn version_label(&self) -> &'static str {
        match self.version {
            DialectVersion::Lua51 => "lua5.1",
            DialectVersion::Lua52 => "lua5.2",
            DialectVersion::Lua53 => "lua5.3",
            DialectVersion::Lua54 => "lua5.4",
            DialectVersion::Lua55 => "lua5.5",
            DialectVersion::LuaJit => "luajit",
            DialectVersion::Luau => "luau",
        }
    }

    fn endianness_label(&self) -> &'static str {
        match self
            .puc_lua_layout()
            .expect("lua51 debug should only receive puc-lua chunk layouts")
            .endianness
        {
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
            DialectProtoExtra::Lua51(Lua51ProtoExtra { raw_is_vararg }) => *raw_is_vararg,
            DialectProtoExtra::Lua52(_) => {
                unreachable!("lua51 debug should not receive lua52 proto extras")
            }
            DialectProtoExtra::Lua53(_) => {
                unreachable!("lua51 debug should not receive lua53 proto extras")
            }
            DialectProtoExtra::Lua54(_) => {
                unreachable!("lua51 debug should not receive lua54 proto extras")
            }
            _ => unreachable!("lua51 debug should not receive non-lua51 proto extras"),
        }
    }
}

trait RawInstrDebugExt {
    fn pc(&self) -> usize;
    fn word_len(&self) -> u8;
    fn setlist_extra_arg(&self) -> Option<u32>;
    fn opcode_label(&self) -> &'static str;
    fn operands_label(&self) -> String;
}

impl RawInstrDebugExt for RawInstr {
    fn pc(&self) -> usize {
        match &self.extra {
            DialectInstrExtra::Lua51(Lua51InstrExtra { pc, .. }) => *pc as usize,
            DialectInstrExtra::Lua52(_) => {
                unreachable!("lua51 debug should not receive lua52 instruction extras")
            }
            DialectInstrExtra::Lua53(_) => {
                unreachable!("lua51 debug should not receive lua53 instruction extras")
            }
            DialectInstrExtra::Lua54(_) => {
                unreachable!("lua51 debug should not receive lua54 instruction extras")
            }
            _ => unreachable!("lua51 debug should not receive non-lua51 instruction extras"),
        }
    }

    fn word_len(&self) -> u8 {
        match &self.extra {
            DialectInstrExtra::Lua51(Lua51InstrExtra { word_len, .. }) => *word_len,
            DialectInstrExtra::Lua52(_) => {
                unreachable!("lua51 debug should not receive lua52 instruction extras")
            }
            DialectInstrExtra::Lua53(_) => {
                unreachable!("lua51 debug should not receive lua53 instruction extras")
            }
            DialectInstrExtra::Lua54(_) => {
                unreachable!("lua51 debug should not receive lua54 instruction extras")
            }
            _ => unreachable!("lua51 debug should not receive non-lua51 instruction extras"),
        }
    }

    fn setlist_extra_arg(&self) -> Option<u32> {
        match &self.extra {
            DialectInstrExtra::Lua51(Lua51InstrExtra {
                setlist_extra_arg, ..
            }) => *setlist_extra_arg,
            DialectInstrExtra::Lua52(_) => {
                unreachable!("lua51 debug should not receive lua52 instruction extras")
            }
            DialectInstrExtra::Lua53(_) => {
                unreachable!("lua51 debug should not receive lua53 instruction extras")
            }
            DialectInstrExtra::Lua54(_) => {
                unreachable!("lua51 debug should not receive lua54 instruction extras")
            }
            _ => unreachable!("lua51 debug should not receive non-lua51 instruction extras"),
        }
    }

    fn opcode_label(&self) -> &'static str {
        match self.opcode {
            RawInstrOpcode::Lua51(opcode) => opcode.label(),
            RawInstrOpcode::Lua52(_) => {
                unreachable!("lua51 debug should not receive lua52 opcodes")
            }
            RawInstrOpcode::Lua53(_) => {
                unreachable!("lua51 debug should not receive lua53 opcodes")
            }
            RawInstrOpcode::Lua54(_) => {
                unreachable!("lua51 debug should not receive lua54 opcodes")
            }
            _ => unreachable!("lua51 debug should not receive non-lua51 opcodes"),
        }
    }

    fn operands_label(&self) -> String {
        match &self.operands {
            RawInstrOperands::Lua51(operands) => operands.label(),
            RawInstrOperands::Lua52(_) => {
                unreachable!("lua51 debug should not receive lua52 operands")
            }
            RawInstrOperands::Lua53(_) => {
                unreachable!("lua51 debug should not receive lua53 operands")
            }
            RawInstrOperands::Lua54(_) => {
                unreachable!("lua51 debug should not receive lua54 operands")
            }
            _ => unreachable!("lua51 debug should not receive non-lua51 operands"),
        }
    }
}

trait Lua51OpcodeDebugExt {
    fn label(self) -> &'static str;
}

impl Lua51OpcodeDebugExt for Lua51Opcode {
    fn label(self) -> &'static str {
        match self {
            Self::Move => "MOVE",
            Self::LoadK => "LOADK",
            Self::LoadBool => "LOADBOOL",
            Self::LoadNil => "LOADNIL",
            Self::GetUpVal => "GETUPVAL",
            Self::GetGlobal => "GETGLOBAL",
            Self::GetTable => "GETTABLE",
            Self::SetGlobal => "SETGLOBAL",
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
            Self::TForLoop => "TFORLOOP",
            Self::SetList => "SETLIST",
            Self::Close => "CLOSE",
            Self::Closure => "CLOSURE",
            Self::VarArg => "VARARG",
        }
    }
}

trait Lua51OperandsDebugExt {
    fn label(&self) -> String;
}

impl Lua51OperandsDebugExt for Lua51Operands {
    fn label(&self) -> String {
        match self {
            Self::A { a } => format!("A(a={a})"),
            Self::AB { a, b } => format!("AB(a={a}, b={b})"),
            Self::AC { a, c } => format!("AC(a={a}, c={c})"),
            Self::ABC { a, b, c } => format!("ABC(a={a}, b={b}, c={c})"),
            Self::ABx { a, bx } => format!("ABx(a={a}, bx={bx})"),
            Self::AsBx { a, sbx } => format!("AsBx(a={a}, sbx={sbx})"),
        }
    }
}
