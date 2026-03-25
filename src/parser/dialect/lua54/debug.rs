//! 这个文件实现 Lua 5.4 parser 的专用调试视图。
//!
//! 它不追求和 5.3 dump 完全逐字对齐，但会把 5.4 新增的 header 差异、upvalue
//! `kind`、`line_deltas/abs_line_info`、以及 7-bit opcode 解析结果稳定地打出来。

use std::fmt::Write as _;

use crate::debug::{DebugDetail, DebugFilters};
use crate::parser::{
    ChunkHeader, DecodedText, Dialect, DialectConstPoolExtra, DialectDebugExtra,
    DialectHeaderExtra, DialectInstrExtra, DialectProtoExtra, DialectUpvalueExtra, DialectVersion,
    Endianness, Origin, RawChunk, RawInstr, RawInstrOpcode, RawInstrOperands, RawLiteralConst,
    RawProto, RawString,
};

use super::raw::{
    Lua54ConstPoolExtra, Lua54HeaderExtra, Lua54InstrExtra, Lua54Opcode, Lua54Operands,
    Lua54ProtoExtra,
};

#[derive(Debug, Clone, Copy)]
struct ProtoEntry<'a> {
    id: usize,
    parent: Option<usize>,
    depth: usize,
    proto: &'a RawProto,
}

pub(crate) fn dump_chunk(chunk: &RawChunk, detail: DebugDetail, filters: &DebugFilters) -> String {
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
    if let Some(lua_integer_size) = header.lua_integer_size {
        let _ = writeln!(output, "  lua_integer_size: {lua_integer_size}");
    }
    let _ = writeln!(output, "  size_t_size: {}", header.size_t_size);
    let _ = writeln!(output, "  instruction_size: {}", header.instruction_size);
    let _ = writeln!(output, "  number_size: {}", header.number_size);
    let _ = writeln!(output, "  integral_number: {}", header.integral_number);
    let _ = writeln!(output, "  origin: {}", format_origin(header.origin));

    match &header.extra {
        DialectHeaderExtra::Lua54(extra) => {
            let Lua54HeaderExtra = extra;
        }
        DialectHeaderExtra::Lua51(_) | DialectHeaderExtra::Lua52(_) | DialectHeaderExtra::Lua53(_) => {
            unreachable!("lua54 debug should not receive non-lua54 header extras")
        }
        _ => unreachable!("lua54 debug should not receive non-lua54 header extras"),
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
            let DialectDebugExtra::Lua54(debug_extra) = &common.debug_info.extra else {
                unreachable!("lua54 debug should not receive non-lua54 debug extras");
            };
            let _ = writeln!(
                output,
                "{indent}  origin={} vararg={} raw_vararg={} debug_lines={} line_deltas={} abs_lines={} locals={} upvalue_names={} upvalue_descs={}",
                format_origin(entry.proto.origin),
                common.signature.is_vararg,
                entry.proto.raw_vararg_bits(),
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
            DialectConstPoolExtra::Lua54(extra) => {
                let Lua54ConstPoolExtra = extra;
            }
            DialectConstPoolExtra::Lua51(_)
            | DialectConstPoolExtra::Lua52(_)
            | DialectConstPoolExtra::Lua53(_) => {
                unreachable!("lua54 debug should not receive non-lua54 const-pool extras")
            }
            _ => unreachable!("lua54 debug should not receive non-lua54 const-pool extras"),
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
    let DialectDebugExtra::Lua54(debug_extra) = &debug_info.extra else {
        unreachable!("lua54 debug should not receive non-lua54 debug extras");
    };
    let DialectUpvalueExtra::Lua54(upvalue_extra) = &proto.common.upvalues.extra else {
        unreachable!("lua54 debug should not receive non-lua54 upvalue extras");
    };

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
            DialectVersion::Lua53 => "lua5.3",
            DialectVersion::Lua54 => "lua5.4",
            DialectVersion::Lua55 => "lua5.5",
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
            DialectProtoExtra::Lua54(Lua54ProtoExtra { raw_is_vararg }) => *raw_is_vararg,
            DialectProtoExtra::Lua51(_)
            | DialectProtoExtra::Lua52(_)
            | DialectProtoExtra::Lua53(_) => {
                unreachable!("lua54 debug should not receive non-lua54 proto extras")
            }
            _ => unreachable!("lua54 debug should not receive non-lua54 proto extras"),
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
            DialectInstrExtra::Lua54(Lua54InstrExtra { pc, .. }) => *pc as usize,
            DialectInstrExtra::Lua51(_)
            | DialectInstrExtra::Lua52(_)
            | DialectInstrExtra::Lua53(_) => {
                unreachable!("lua54 debug should not receive non-lua54 instruction extras")
            }
            _ => unreachable!("lua54 debug should not receive non-lua54 instruction extras"),
        }
    }

    fn word_len(&self) -> u8 {
        match &self.extra {
            DialectInstrExtra::Lua54(Lua54InstrExtra { word_len, .. }) => *word_len,
            DialectInstrExtra::Lua51(_)
            | DialectInstrExtra::Lua52(_)
            | DialectInstrExtra::Lua53(_) => {
                unreachable!("lua54 debug should not receive non-lua54 instruction extras")
            }
            _ => unreachable!("lua54 debug should not receive non-lua54 instruction extras"),
        }
    }

    fn extra_arg(&self) -> Option<u32> {
        match &self.extra {
            DialectInstrExtra::Lua54(Lua54InstrExtra { extra_arg, .. }) => *extra_arg,
            DialectInstrExtra::Lua51(_)
            | DialectInstrExtra::Lua52(_)
            | DialectInstrExtra::Lua53(_) => {
                unreachable!("lua54 debug should not receive non-lua54 instruction extras")
            }
            _ => unreachable!("lua54 debug should not receive non-lua54 instruction extras"),
        }
    }

    fn opcode_label(&self) -> &'static str {
        match self.opcode {
            RawInstrOpcode::Lua54(opcode) => opcode.label(),
            RawInstrOpcode::Lua51(_) | RawInstrOpcode::Lua52(_) | RawInstrOpcode::Lua53(_) => {
                unreachable!("lua54 debug should not receive non-lua54 opcodes")
            }
            _ => unreachable!("lua54 debug should not receive non-lua54 opcodes"),
        }
    }

    fn operands_label(&self) -> String {
        match &self.operands {
            RawInstrOperands::Lua54(operands) => operands.label(),
            RawInstrOperands::Lua51(_)
            | RawInstrOperands::Lua52(_)
            | RawInstrOperands::Lua53(_) => {
                unreachable!("lua54 debug should not receive non-lua54 operands")
            }
            _ => unreachable!("lua54 debug should not receive non-lua54 operands"),
        }
    }
}

trait Lua54OpcodeDebugExt {
    fn label(self) -> &'static str;
}

impl Lua54OpcodeDebugExt for Lua54Opcode {
    fn label(self) -> &'static str {
        match self {
            Self::Move => "MOVE",
            Self::LoadI => "LOADI",
            Self::LoadF => "LOADF",
            Self::LoadK => "LOADK",
            Self::LoadKx => "LOADKX",
            Self::LoadFalse => "LOADFALSE",
            Self::LFalseSkip => "LFALSESKIP",
            Self::LoadTrue => "LOADTRUE",
            Self::LoadNil => "LOADNIL",
            Self::GetUpVal => "GETUPVAL",
            Self::SetUpVal => "SETUPVAL",
            Self::GetTabUp => "GETTABUP",
            Self::GetTable => "GETTABLE",
            Self::GetI => "GETI",
            Self::GetField => "GETFIELD",
            Self::SetTabUp => "SETTABUP",
            Self::SetTable => "SETTABLE",
            Self::SetI => "SETI",
            Self::SetField => "SETFIELD",
            Self::NewTable => "NEWTABLE",
            Self::Self_ => "SELF",
            Self::AddI => "ADDI",
            Self::AddK => "ADDK",
            Self::SubK => "SUBK",
            Self::MulK => "MULK",
            Self::ModK => "MODK",
            Self::PowK => "POWK",
            Self::DivK => "DIVK",
            Self::IdivK => "IDIVK",
            Self::BandK => "BANDK",
            Self::BorK => "BORK",
            Self::BxorK => "BXORK",
            Self::ShrI => "SHRI",
            Self::ShlI => "SHLI",
            Self::Add => "ADD",
            Self::Sub => "SUB",
            Self::Mul => "MUL",
            Self::Mod => "MOD",
            Self::Pow => "POW",
            Self::Div => "DIV",
            Self::Idiv => "IDIV",
            Self::Band => "BAND",
            Self::Bor => "BOR",
            Self::Bxor => "BXOR",
            Self::Shl => "SHL",
            Self::Shr => "SHR",
            Self::MMBin => "MMBIN",
            Self::MMBinI => "MMBINI",
            Self::MMBinK => "MMBINK",
            Self::Unm => "UNM",
            Self::BNot => "BNOT",
            Self::Not => "NOT",
            Self::Len => "LEN",
            Self::Concat => "CONCAT",
            Self::Close => "CLOSE",
            Self::Tbc => "TBC",
            Self::Jmp => "JMP",
            Self::Eq => "EQ",
            Self::Lt => "LT",
            Self::Le => "LE",
            Self::EqK => "EQK",
            Self::EqI => "EQI",
            Self::LtI => "LTI",
            Self::LeI => "LEI",
            Self::GtI => "GTI",
            Self::GeI => "GEI",
            Self::Test => "TEST",
            Self::TestSet => "TESTSET",
            Self::Call => "CALL",
            Self::TailCall => "TAILCALL",
            Self::Return => "RETURN",
            Self::Return0 => "RETURN0",
            Self::Return1 => "RETURN1",
            Self::ForLoop => "FORLOOP",
            Self::ForPrep => "FORPREP",
            Self::TForPrep => "TFORPREP",
            Self::TForCall => "TFORCALL",
            Self::TForLoop => "TFORLOOP",
            Self::SetList => "SETLIST",
            Self::Closure => "CLOSURE",
            Self::VarArg => "VARARG",
            Self::VarArgPrep => "VARARGPREP",
            Self::ExtraArg => "EXTRAARG",
        }
    }
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
