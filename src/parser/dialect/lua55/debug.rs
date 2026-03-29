//! 这个文件承载 Lua 5.5 parser 产物的轻量调试输出。

use std::fmt::Write as _;

use crate::debug::{DebugColorMode, DebugDetail, DebugFilters, colorize_debug_text};
use crate::parser::raw::{DecodedText, RawChunk, RawInstr, RawProto, RawString};

use super::raw::{Lua55DebugExtra, Lua55InstrExtra, Lua55Opcode, Lua55Operands};

pub(crate) fn dump_chunk(
    chunk: &RawChunk,
    detail: DebugDetail,
    filters: &DebugFilters,
    color: DebugColorMode,
) -> String {
    let mut output = String::new();
    let mut protos = Vec::new();
    collect_protos(&chunk.main, 0, &mut protos);

    let _ = writeln!(output, "===== Dump Parser =====");
    let _ = writeln!(
        output,
        "parser dialect=lua5.5 detail={} protos={}",
        detail,
        protos.len()
    );
    if let Some(proto_id) = filters.proto {
        let _ = writeln!(output, "filters proto=proto#{proto_id}");
    }
    let _ = writeln!(output);

    for (id, depth, proto) in protos {
        if filters.proto.is_some_and(|proto_id| proto_id != id) {
            continue;
        }

        let indent = "  ".repeat(depth);
        let raw_flag = proto
            .extra
            .lua55()
            .expect("lua55 debug should only receive lua55 protos")
            .raw_flag;
        let _ = writeln!(
            output,
            "{indent}proto#{id} source={} lines={}..{} params={} vararg={} raw_flag=0x{raw_flag:02x} stack={} instrs={} consts={} upvalues={} children={}",
            format_optional_source(proto.common.source.as_ref()),
            proto.common.line_range.defined_start,
            proto.common.line_range.defined_end,
            proto.common.signature.num_params,
            proto.common.signature.is_vararg,
            proto.common.frame.max_stack_size,
            proto.common.instructions.len(),
            proto.common.constants.common.literals.len(),
            proto.common.upvalues.common.count,
            proto.common.children.len(),
        );

        if matches!(detail, DebugDetail::Summary) {
            continue;
        }

        if let Some(Lua55DebugExtra {
            line_deltas,
            abs_line_info,
        }) = proto.common.debug_info.extra.lua55()
            && matches!(detail, DebugDetail::Verbose)
        {
            let _ = writeln!(
                output,
                "{indent}  debug line-deltas={} abs-line-info={} locals={} upvalue-names={}",
                line_deltas.len(),
                abs_line_info.len(),
                proto.common.debug_info.common.local_vars.len(),
                proto.common.debug_info.common.upvalue_names.len(),
            );
        }

        let _ = writeln!(output, "{indent}  instructions");
        if proto.common.instructions.is_empty() {
            let _ = writeln!(output, "{indent}    <empty>");
            continue;
        }

        for (index, instr) in proto.common.instructions.iter().enumerate() {
            let (opcode, operands, extra) = decode_lua55(instr);
            let _ = writeln!(
                output,
                "{indent}    @{index:03} pc={} words={} opcode={} operands={} extraarg={}",
                extra.pc,
                extra.word_len,
                opcode.label(),
                operands.label(),
                extra
                    .extra_arg
                    .map_or_else(|| "-".to_owned(), |value| value.to_string()),
            );
        }
    }

    colorize_debug_text(&output, color)
}

fn collect_protos<'a>(
    proto: &'a RawProto,
    depth: usize,
    out: &mut Vec<(usize, usize, &'a RawProto)>,
) {
    let id = out.len();
    out.push((id, depth, proto));
    for child in &proto.common.children {
        collect_protos(child, depth + 1, out);
    }
}

fn format_optional_source(source: Option<&RawString>) -> String {
    source.map_or_else(|| "-".to_owned(), format_raw_string)
}

fn format_raw_string(source: &RawString) -> String {
    source
        .text
        .as_ref()
        .map(|DecodedText { value, .. }| format!("{value:?}"))
        .unwrap_or_else(|| format!("<{} bytes>", source.bytes.len()))
}

fn decode_lua55(raw: &RawInstr) -> (Lua55Opcode, &Lua55Operands, Lua55InstrExtra) {
    let opcode = raw
        .opcode
        .lua55()
        .expect("lua55 debug should only receive lua55 opcodes");
    let operands = raw
        .operands
        .lua55()
        .expect("lua55 debug should only receive lua55 operands");
    let extra = raw
        .extra
        .lua55()
        .expect("lua55 debug should only receive lua55 extras");
    (*opcode, operands, *extra)
}

trait Lua55OperandsDebugExt {
    fn label(&self) -> String;
}

impl Lua55OperandsDebugExt for Lua55Operands {
    fn label(&self) -> String {
        match self {
            Lua55Operands::None => "-".to_owned(),
            Lua55Operands::A { a } => format!("A={a}"),
            Lua55Operands::Ak { a, k } => format!("A={a} k={}", u8::from(*k)),
            Lua55Operands::AB { a, b } => format!("A={a} B={b}"),
            Lua55Operands::AC { a, c } => format!("A={a} C={c}"),
            Lua55Operands::ABC { a, b, c } => format!("A={a} B={b} C={c}"),
            Lua55Operands::ABk { a, b, k } => format!("A={a} B={b} k={}", u8::from(*k)),
            Lua55Operands::ABCk { a, b, c, k } => {
                format!("A={a} B={b} C={c} k={}", u8::from(*k))
            }
            Lua55Operands::ABx { a, bx } => format!("A={a} Bx={bx}"),
            Lua55Operands::AsBx { a, sbx } => format!("A={a} sBx={sbx}"),
            Lua55Operands::AsJ { sj } => format!("sJ={sj}"),
            Lua55Operands::Ax { ax } => format!("Ax={ax}"),
            Lua55Operands::ABsCk { a, b, sc, k } => {
                format!("A={a} B={b} sC={sc} k={}", u8::from(*k))
            }
            Lua55Operands::AsBCk { a, sb, c, k } => {
                format!("A={a} sB={sb} C={c} k={}", u8::from(*k))
            }
            Lua55Operands::AvBCk { a, vb, vc, k } => {
                format!("A={a} vB={vb} vC={vc} k={}", u8::from(*k))
            }
        }
    }
}
