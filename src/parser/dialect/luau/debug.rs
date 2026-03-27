//! 这个文件承载 Luau parser 产物的轻量调试输出。
//!
//! 第一阶段先保证我们能稳定观察 Luau header/proto/instruction/constant 的解码结果，
//! 不把格式细节重新塞回公共调试入口里。

use std::fmt::Write as _;

use crate::debug::{DebugColorMode, DebugDetail, DebugFilters, colorize_debug_text};
use crate::parser::raw::{
    DecodedText, DialectConstPoolExtra, DialectDebugExtra, DialectInstrExtra, DialectProtoExtra,
    RawChunk, RawInstr, RawInstrOpcode, RawInstrOperands, RawProto, RawString,
};

use super::raw::{
    LuauConstEntry, LuauDebugExtra, LuauInstrExtra, LuauOpcode, LuauOperands, LuauProtoExtra,
};

pub(crate) fn dump_chunk(
    chunk: &RawChunk,
    detail: DebugDetail,
    filters: &DebugFilters,
    color: DebugColorMode,
) -> String {
    let mut output = String::new();
    let mut protos = Vec::new();
    collect_protos(&chunk.main, 0, &mut protos);

    let layout = chunk
        .header
        .luau_layout()
        .expect("luau debug should only receive luau chunk layouts");

    let _ = writeln!(output, "===== Dump Parser =====");
    let _ = writeln!(
        output,
        "parser dialect=luau detail={} protos={}",
        detail,
        protos.len()
    );
    let _ = writeln!(
        output,
        "header bytecode_version={} type_version={}",
        layout.bytecode_version,
        layout
            .type_version
            .map_or_else(|| "-".to_owned(), |value| value.to_string()),
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
        let DialectProtoExtra::Luau(LuauProtoExtra {
            flags,
            type_info,
            debug_name,
            ..
        }) = &proto.extra
        else {
            unreachable!("luau debug should only receive luau protos");
        };
        let DialectConstPoolExtra::Luau(const_pool_extra) = &proto.common.constants.extra else {
            unreachable!("luau debug should only receive luau constants");
        };

        let _ = writeln!(
            output,
            "{indent}proto#{id} source={} debug_name={} lines={}..{} params={} vararg={} flags=0x{flags:02x} stack={} instrs={} consts={} upvalues={} children={}",
            format_optional_source(proto.common.source.as_ref()),
            format_optional_source(debug_name.as_ref()),
            proto.common.line_range.defined_start,
            proto.common.line_range.defined_end,
            proto.common.signature.num_params,
            proto.common.signature.is_vararg,
            proto.common.frame.max_stack_size,
            proto.common.instructions.len(),
            const_pool_extra.entries.len(),
            proto.common.upvalues.common.count,
            proto.common.children.len(),
        );

        if matches!(detail, DebugDetail::Summary) {
            continue;
        }

        if let DialectDebugExtra::Luau(LuauDebugExtra {
            line_gap_log2,
            local_regs,
        }) = &proto.common.debug_info.extra
        {
            let _ = writeln!(
                output,
                "{indent}  debug lines={} locals={} local-regs={} upvalue-names={} line-gap-log2={} type-bytes={}",
                proto.common.debug_info.common.line_info.len(),
                proto.common.debug_info.common.local_vars.len(),
                local_regs.len(),
                proto.common.debug_info.common.upvalue_names.len(),
                line_gap_log2.map_or_else(|| "-".to_owned(), |value| value.to_string()),
                type_info.len(),
            );
        }

        if matches!(detail, DebugDetail::Verbose) {
            let _ = writeln!(output, "{indent}  constants");
            if const_pool_extra.entries.is_empty() {
                let _ = writeln!(output, "{indent}    <empty>");
            } else {
                for (index, entry) in const_pool_extra.entries.iter().enumerate() {
                    let _ = writeln!(
                        output,
                        "{indent}    k{index:03} {}",
                        format_const_entry(entry)
                    );
                }
            }
        }

        let _ = writeln!(output, "{indent}  instructions");
        if proto.common.instructions.is_empty() {
            let _ = writeln!(output, "{indent}    <empty>");
            continue;
        }

        for (index, instr) in proto.common.instructions.iter().enumerate() {
            let (opcode, operands, extra) = decode_luau(instr);
            let _ = writeln!(
                output,
                "{indent}    @{index:03} pc={} words={} opcode={opcode:?} operands={} aux={}",
                extra.pc,
                extra.word_len,
                format_operands(operands),
                extra
                    .aux
                    .map_or_else(|| "-".to_owned(), |value| format!("0x{value:08x}")),
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

fn format_const_entry(entry: &LuauConstEntry) -> String {
    match entry {
        LuauConstEntry::Literal { literal_index } => format!("literal l{literal_index}"),
        LuauConstEntry::Import { import_id } => format!("import 0x{import_id:08x}"),
        LuauConstEntry::Table { key_consts } => format!("table keys={key_consts:?}"),
        LuauConstEntry::TableWithConstants { entries } => {
            format!("table+consts entries={entries:?}")
        }
        LuauConstEntry::Closure { proto_index } => format!("closure proto={proto_index}"),
        LuauConstEntry::Vector { x, y, z, w } => format!("vector ({x}, {y}, {z}, {w})"),
    }
}

fn decode_luau(raw: &RawInstr) -> (LuauOpcode, &LuauOperands, LuauInstrExtra) {
    let RawInstrOpcode::Luau(opcode) = raw.opcode else {
        unreachable!("luau debug should only receive luau opcodes");
    };
    let RawInstrOperands::Luau(ref operands) = raw.operands else {
        unreachable!("luau debug should only receive luau operands");
    };
    let DialectInstrExtra::Luau(extra) = raw.extra else {
        unreachable!("luau debug should only receive luau extras");
    };
    (opcode, operands, extra)
}

fn format_operands(operands: &LuauOperands) -> String {
    match operands {
        LuauOperands::None => "-".to_owned(),
        LuauOperands::A { a } => format!("A={a}"),
        LuauOperands::AB { a, b } => format!("A={a} B={b}"),
        LuauOperands::AC { a, c } => format!("A={a} C={c}"),
        LuauOperands::ABC { a, b, c } => format!("A={a} B={b} C={c}"),
        LuauOperands::AD { a, d } => format!("A={a} D={d}"),
        LuauOperands::E { e } => format!("E={e}"),
    }
}
