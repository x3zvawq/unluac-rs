//! 这个文件实现主 pipeline 共享的调试导出能力。
//!
//! 这里不直接复用 Rust 的 `Debug`，而是提供面向人类排错的稳定文本视图；
//! 这样 library、CLI 和后续 wasm 封装都能共享同一套 dump 语义。

use std::fmt;
use std::fmt::Write as _;

use crate::parser::{
    ChunkHeader, DecodedText, DialectConstPoolExtra, DialectDebugExtra, DialectHeaderExtra,
    DialectInstrExtra, DialectProtoExtra, DialectUpvalueExtra, Endianness, Lua51ConstPoolExtra,
    Lua51DebugExtra, Lua51HeaderExtra, Lua51InstrExtra, Lua51Opcode, Lua51Operands,
    Lua51ProtoExtra, Lua51UpvalueExtra, Origin, RawChunk, RawInstr, RawInstrOpcode,
    RawInstrOperands, RawLiteralConst, RawProto, RawString,
};

use super::error::DecompileError;
use super::state::{DecompileStage, DecompileState};

/// 调试输出格式。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub enum DebugFormat {
    #[default]
    Human,
    Json,
}

impl DebugFormat {
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "human" => Some(Self::Human),
            "json" => Some(Self::Json),
            _ => None,
        }
    }

    pub const fn label(self) -> &'static str {
        match self {
            Self::Human => "human",
            Self::Json => "json",
        }
    }
}

impl fmt::Display for DebugFormat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

/// 调试输出详细程度。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub enum DebugDetail {
    Summary,
    #[default]
    Normal,
    Verbose,
}

impl DebugDetail {
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "summary" => Some(Self::Summary),
            "normal" => Some(Self::Normal),
            "verbose" => Some(Self::Verbose),
            _ => None,
        }
    }

    pub const fn label(self) -> &'static str {
        match self {
            Self::Summary => "summary",
            Self::Normal => "normal",
            Self::Verbose => "verbose",
        }
    }
}

impl fmt::Display for DebugDetail {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

/// 统一过滤器先从 proto 维度开始，后续再按同样模式扩展到 block、instr、reg。
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct DebugFilters {
    pub proto: Option<usize>,
}

/// 供主 pipeline 和 CLI 共享的调试选项。
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct DebugOptions {
    pub enable: bool,
    pub output_stage: Option<DecompileStage>,
    pub format: DebugFormat,
    pub detail: DebugDetail,
    pub filters: DebugFilters,
}

/// 某个阶段导出的调试文本。
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct StageDebugOutput {
    pub stage: DecompileStage,
    pub format: DebugFormat,
    pub detail: DebugDetail,
    pub content: String,
}

#[derive(Debug, Clone, Copy)]
struct ProtoEntry<'a> {
    id: usize,
    parent: Option<usize>,
    depth: usize,
    proto: &'a RawProto,
}

/// 直接导出 parser 层视图，方便单测和未来 wasm 绑定复用。
pub fn dump_parser(
    chunk: &RawChunk,
    options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    match options.format {
        DebugFormat::Human => Ok(StageDebugOutput {
            stage: DecompileStage::Parse,
            format: options.format,
            detail: options.detail,
            content: render_parser_human(chunk, options),
        }),
        format => Err(DecompileError::UnsupportedDebugFormat {
            stage: DecompileStage::Parse,
            format,
        }),
    }
}

pub(crate) fn collect_stage_dump(
    state: &DecompileState,
    options: &DebugOptions,
) -> Result<Option<StageDebugOutput>, DecompileError> {
    if !options.enable {
        return Ok(None);
    }

    let Some(stage) = options.output_stage else {
        return Ok(None);
    };

    match stage {
        DecompileStage::Parse => {
            let Some(chunk) = state.raw_chunk.as_ref() else {
                return Err(DecompileError::MissingStageOutput { stage });
            };
            dump_parser(chunk, options).map(Some)
        }
        _ => Err(DecompileError::MissingStageOutput { stage }),
    }
}

fn render_parser_human(chunk: &RawChunk, options: &DebugOptions) -> String {
    let mut output = String::new();
    let protos = collect_proto_entries(&chunk.main);
    let visible_protos = visible_proto_ids(&protos, &options.filters);

    let _ = writeln!(output, "===== Dump Parser =====");
    let _ = writeln!(
        output,
        "parser dialect={} detail={} protos={}",
        chunk.header.version_label(),
        options.detail,
        protos.len()
    );
    if let Some(proto_id) = options.filters.proto {
        let _ = writeln!(output, "filters proto=proto#{proto_id}");
    }
    let _ = writeln!(output);

    write_header_view(&mut output, &chunk.header);
    let _ = writeln!(output);
    write_proto_tree_view(&mut output, &protos, &visible_protos, options.detail);

    if !matches!(options.detail, DebugDetail::Summary) {
        let _ = writeln!(output);
        write_constants_view(&mut output, &protos, &visible_protos);
        let _ = writeln!(output);
        write_raw_instructions_view(&mut output, &protos, &visible_protos, options.detail);
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
        DialectHeaderExtra::Lua51(extra) => {
            let Lua51HeaderExtra = extra;
        }
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
    }
    match &proto.common.upvalues.extra {
        DialectUpvalueExtra::Lua51(extra) => {
            let Lua51UpvalueExtra = extra;
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
            crate::parser::Dialect::PucLua => "puc-lua",
        }
    }

    fn version_label(&self) -> &'static str {
        match self.version {
            crate::parser::DialectVersion::Lua51 => "lua5.1",
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
            DialectProtoExtra::Lua51(Lua51ProtoExtra { raw_is_vararg }) => *raw_is_vararg,
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
        }
    }

    fn word_len(&self) -> u8 {
        match &self.extra {
            DialectInstrExtra::Lua51(Lua51InstrExtra { word_len, .. }) => *word_len,
        }
    }

    fn setlist_extra_arg(&self) -> Option<u32> {
        match &self.extra {
            DialectInstrExtra::Lua51(Lua51InstrExtra {
                setlist_extra_arg, ..
            }) => *setlist_extra_arg,
        }
    }

    fn opcode_label(&self) -> &'static str {
        match self.opcode {
            RawInstrOpcode::Lua51(opcode) => opcode.label(),
        }
    }

    fn operands_label(&self) -> String {
        match &self.operands {
            RawInstrOperands::Lua51(operands) => operands.label(),
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
