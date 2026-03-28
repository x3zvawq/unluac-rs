//! 这个文件承载 LuaJIT parser 产物的轻量调试输出。

use std::fmt::Write as _;

use crate::debug::{DebugColorMode, DebugDetail, DebugFilters, colorize_debug_text};
use crate::parser::raw::{
    DecodedText, DialectConstPoolExtra, DialectDebugExtra, DialectHeaderExtra, DialectInstrExtra,
    DialectProtoExtra, RawChunk, RawInstr, RawInstrOpcode, RawInstrOperands, RawLiteralConst,
    RawProto, RawString,
};

use super::raw::{
    LuaJitConstPoolExtra, LuaJitDebugExtra, LuaJitHeaderExtra, LuaJitInstrExtra, LuaJitKgcEntry,
    LuaJitNumberConstEntry, LuaJitOperands, LuaJitProtoExtra, LuaJitTableConst, LuaJitTableLiteral,
    LuaJitTableRecord,
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
        .luajit_layout()
        .expect("luajit debug should only receive luajit layouts");
    let DialectHeaderExtra::LuaJit(LuaJitHeaderExtra {
        chunk_name,
        stripped,
        uses_ffi,
        fr2,
        big_endian,
    }) = &chunk.header.extra
    else {
        unreachable!("luajit debug should only receive luajit header extras");
    };

    let _ = writeln!(output, "===== Dump Parser =====");
    let _ = writeln!(
        output,
        "parser dialect=luajit detail={} protos={}",
        detail,
        protos.len()
    );
    let _ = writeln!(
        output,
        "header dump_version={} flags=0x{:02x} chunk_name={} stripped={} ffi={} fr2={} big_endian={}",
        layout.dump_version,
        layout.flags,
        format_optional_source(chunk_name.as_ref()),
        stripped,
        uses_ffi,
        fr2,
        big_endian,
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
        let DialectProtoExtra::LuaJit(LuaJitProtoExtra {
            flags,
            first_line,
            line_count,
            debug_size,
        }) = &proto.extra
        else {
            unreachable!("luajit debug should only receive luajit protos");
        };
        let DialectConstPoolExtra::LuaJit(LuaJitConstPoolExtra {
            kgc_entries,
            knum_entries,
        }) = &proto.common.constants.extra
        else {
            unreachable!("luajit debug should only receive luajit constants");
        };

        let _ = writeln!(
            output,
            "{indent}proto#{id} source={} lines={}..{} params={} vararg={} flags=0x{flags:02x} stack={} instrs={} literals={} kgc={} knum={} upvalues={} children={} first_line={} line_count={} debug_size={}",
            format_optional_source(proto.common.source.as_ref()),
            proto.common.line_range.defined_start,
            proto.common.line_range.defined_end,
            proto.common.signature.num_params,
            proto.common.signature.is_vararg,
            proto.common.frame.max_stack_size,
            proto.common.instructions.len(),
            proto.common.constants.common.literals.len(),
            kgc_entries.len(),
            knum_entries.len(),
            proto.common.upvalues.common.count,
            proto.common.children.len(),
            first_line.map_or_else(|| "-".to_owned(), |value| value.to_string()),
            line_count.map_or_else(|| "-".to_owned(), |value| value.to_string()),
            debug_size,
        );

        if matches!(detail, DebugDetail::Summary) {
            continue;
        }

        if let DialectDebugExtra::LuaJit(LuaJitDebugExtra {
            stripped,
            debug_size,
        }) = &proto.common.debug_info.extra
        {
            let _ = writeln!(
                output,
                "{indent}  debug lines={} locals={} upvalue-names={} stripped={} size={}",
                proto.common.debug_info.common.line_info.len(),
                proto.common.debug_info.common.local_vars.len(),
                proto.common.debug_info.common.upvalue_names.len(),
                stripped,
                debug_size,
            );
        }

        if matches!(detail, DebugDetail::Verbose) {
            let _ = writeln!(output, "{indent}  constants");
            for (index, literal) in proto.common.constants.common.literals.iter().enumerate() {
                let _ = writeln!(
                    output,
                    "{indent}    l{index:03} {}",
                    format_literal(literal)
                );
            }
            for (index, entry) in kgc_entries.iter().enumerate() {
                let _ = writeln!(
                    output,
                    "{indent}    kgc{index:03} {}",
                    format_kgc_entry(entry)
                );
            }
            for (index, entry) in knum_entries.iter().enumerate() {
                let _ = writeln!(
                    output,
                    "{indent}    kn{index:03} {}",
                    format_knum_entry(entry)
                );
            }
        }

        let _ = writeln!(output, "{indent}  instructions");
        if proto.common.instructions.is_empty() {
            let _ = writeln!(output, "{indent}    <empty>");
        } else {
            for (index, instr) in proto.common.instructions.iter().enumerate() {
                let _ = writeln!(output, "{indent}    @{index:03} {}", format_instr(instr));
            }
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

fn format_instr(raw: &RawInstr) -> String {
    let RawInstrOpcode::LuaJit(opcode) = raw.opcode else {
        unreachable!("luajit debug should only receive luajit opcodes");
    };
    let RawInstrOperands::LuaJit(ref operands) = raw.operands else {
        unreachable!("luajit debug should only receive luajit operands");
    };
    let DialectInstrExtra::LuaJit(LuaJitInstrExtra { pc, raw_word }) = raw.extra else {
        unreachable!("luajit debug should only receive luajit extras");
    };
    format!(
        "pc={} opcode={opcode:?} operands={} raw=0x{raw_word:08x}",
        pc,
        format_operands(operands),
    )
}

fn format_operands(operands: &LuaJitOperands) -> String {
    match operands {
        LuaJitOperands::A { a } => format!("A={a}"),
        LuaJitOperands::AD { a, d } => format!("A={a} D={d}"),
        LuaJitOperands::ABC { a, b, c } => format!("A={a} B={b} C={c}"),
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

fn format_kgc_entry(entry: &LuaJitKgcEntry) -> String {
    match entry {
        LuaJitKgcEntry::Child { child_proto_index } => format!("child proto={child_proto_index}"),
        LuaJitKgcEntry::Table(table) => format!("table {}", format_table(table)),
        LuaJitKgcEntry::Literal {
            value,
            literal_index,
        } => format!("literal l{literal_index:03} {}", format_literal(value)),
    }
}

fn format_knum_entry(entry: &LuaJitNumberConstEntry) -> String {
    match entry {
        LuaJitNumberConstEntry::Integer {
            value,
            literal_index,
        } => format!("int l{literal_index:03} {value}"),
        LuaJitNumberConstEntry::Number {
            value,
            literal_index,
        } => format!("num l{literal_index:03} {value}"),
    }
}

fn format_table(table: &LuaJitTableConst) -> String {
    let array = table
        .array
        .iter()
        .map(format_table_literal)
        .collect::<Vec<_>>()
        .join(", ");
    let hash = table
        .hash
        .iter()
        .map(format_record)
        .collect::<Vec<_>>()
        .join(", ");
    format!("array=[{array}] hash=[{hash}]")
}

fn format_record(record: &LuaJitTableRecord) -> String {
    format!(
        "{} => {}",
        format_table_literal(&record.key),
        format_table_literal(&record.value)
    )
}

fn format_table_literal(literal: &LuaJitTableLiteral) -> String {
    format!(
        "l{:03} {}",
        literal.literal_index,
        format_literal(&literal.value)
    )
}
