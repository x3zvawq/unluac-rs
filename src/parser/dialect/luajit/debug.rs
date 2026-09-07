//! 这个文件承载 LuaJIT parser 产物的轻量调试输出。

use std::fmt::Write as _;

use crate::debug::{
    DebugColorMode, DebugDetail, DebugFilters, collect_proto_tree, colorize_debug_text,
    format_breadcrumb, plan_proto_focus,
};
use crate::parser::debug::{format_literal, format_optional_source, write_elided_summary};
use crate::parser::raw::{RawChunk, RawInstr};

use super::raw::{
    LuaJitConstPoolExtra, LuaJitDebugExtra, LuaJitHeaderExtra, LuaJitKgcEntry,
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
    let protos = collect_proto_tree(&chunk.main, |proto| {
        proto.common.children.iter().map(|child| child.as_ref())
    });
    let plan = plan_proto_focus(&protos, filters);

    let layout = chunk
        .header
        .luajit_layout()
        .expect("luajit debug should only receive luajit layouts");
    let LuaJitHeaderExtra {
        chunk_name,
        stripped,
        uses_ffi,
        fr2,
        big_endian,
    } = chunk
        .header
        .extra
        .luajit()
        .expect("luajit debug should only receive luajit header extras");

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
    let _ = writeln!(output, "filters proto_depth={}", filters.proto_depth);
    if let Some(breadcrumb) = format_breadcrumb(&plan) {
        let _ = writeln!(output, "focus {breadcrumb}");
    }
    let _ = writeln!(output);

    if plan.focus.is_none() {
        let _ = writeln!(output, "  <no proto matched filters>");
        return colorize_debug_text(&output, color);
    }

    for entry in protos {
        if plan.is_elided(entry.id) {
            let indent = "  ".repeat(entry.depth);
            write_elided_summary(&mut output, &indent, &entry);
            continue;
        }
        if !plan.is_visible(entry.id) {
            continue;
        }

        let indent = "  ".repeat(entry.depth);
        let id = entry.id;
        let proto = entry.value;
        let LuaJitProtoExtra {
            flags,
            first_line,
            line_count,
            debug_size,
        } = proto
            .extra
            .luajit()
            .expect("luajit debug should only receive luajit protos");
        let LuaJitConstPoolExtra {
            kgc_entries,
            knum_entries,
        } = proto
            .common
            .constants
            .extra
            .luajit()
            .expect("luajit debug should only receive luajit constants");

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

        if let Some(LuaJitDebugExtra {
            stripped,
            debug_size,
        }) = proto.common.debug_info.extra.luajit()
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

fn format_instr(raw: &RawInstr) -> String {
    let opcode = raw
        .opcode
        .luajit()
        .expect("luajit debug should only receive luajit opcodes");
    let operands = raw
        .operands
        .luajit()
        .expect("luajit debug should only receive luajit operands");
    let extra = raw
        .extra
        .luajit()
        .expect("luajit debug should only receive luajit extras");
    format!(
        "pc={} opcode={opcode:?} operands={} raw=0x{raw_word:08x}",
        extra.pc,
        format_operands(operands),
        raw_word = extra.raw_word,
    )
}

fn format_operands(operands: &LuaJitOperands) -> String {
    match operands {
        LuaJitOperands::A { a } => format!("A={a}"),
        LuaJitOperands::AD { a, d } => format!("A={a} D={d}"),
        LuaJitOperands::ABC { a, b, c } => format!("A={a} B={b} C={c}"),
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
