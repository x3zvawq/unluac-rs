//! 这个文件承载 parser debug 输出里的跨 dialect 公共工具。
//!
//! dialect debug 需要展示的方言字段各不相同，但 RawString/literal/origin 的基础格式化
//! 是一致的；这里消费共享 debug 层的前序身份与 focus，不重新遍历 proto 树。
//! 例如同一子 proto 在树视图和常量视图中共享前序 id 与折叠状态；方言只选择视图布局，
//! 不重新声明身份记录或遍历规则。独立常量视图读取公共 literal 池，不解释方言私有常量。

use std::fmt::Write as _;

use crate::debug::{FocusPlan, ProtoSummaryRow, ProtoTreeEntry, format_proto_summary_row};
use crate::parser::{DecodedText, Endianness, Origin, RawLiteralConst, RawProto, RawString, Span};

/// 把 `RawProto` 压成 elided 行。parser 阶段拿不到函数名，只能呈现
/// `lines / instrs / children` 三项，这些都从 `RawProto::common` 里直接取得。
fn build_parser_summary_row(entry: &ProtoTreeEntry<&RawProto>) -> ProtoSummaryRow {
    ProtoSummaryRow {
        id: entry.id,
        name: None,
        first: None,
        lines: Some((
            entry.value.common.line_range.defined_start,
            entry.value.common.line_range.defined_end,
        )),
        instrs: Some(entry.value.common.instructions.len()),
        children: Some(entry.value.common.children.len()),
    }
}

/// 写出被 focus plan 折叠的 proto 摘要行。
pub(crate) fn write_elided_summary(
    output: &mut String,
    indent: &str,
    entry: &ProtoTreeEntry<&RawProto>,
) {
    let _ = writeln!(
        output,
        "{indent}{}",
        format_proto_summary_row(&build_parser_summary_row(entry)),
    );
}

pub(crate) fn write_constants_view(
    output: &mut String,
    protos: &[ProtoTreeEntry<&RawProto>],
    plan: &FocusPlan,
) {
    let _ = writeln!(output, "constants");
    if plan.focus.is_none() {
        let _ = writeln!(output, "  <no proto matched filters>");
        return;
    }

    for entry in protos {
        if plan.is_elided(entry.id) {
            write_elided_summary(output, "  ", entry);
            continue;
        }
        if !plan.is_visible(entry.id) {
            continue;
        }

        let _ = writeln!(output, "  proto#{}", entry.id);
        let literals = &entry.value.common.constants.common.literals;
        if literals.is_empty() {
            let _ = writeln!(output, "    <empty>");
        } else {
            for (index, literal) in literals.iter().enumerate() {
                let _ = writeln!(output, "    k{index:<3} {}", format_literal(literal));
            }
        }
    }
}

pub(crate) fn format_optional_source(source: Option<&RawString>) -> String {
    source.map_or_else(|| "-".to_owned(), format_raw_string)
}

pub(crate) fn format_raw_string(raw: &RawString) -> String {
    match raw.text.as_ref() {
        Some(DecodedText { value, .. }) => format!("{value:?}"),
        None => format!("<{} bytes>", raw.bytes.len()),
    }
}

pub(crate) fn format_literal(literal: &RawLiteralConst) -> String {
    match literal {
        RawLiteralConst::Nil => "nil".to_owned(),
        RawLiteralConst::Boolean(value) => format!("bool({value})"),
        RawLiteralConst::Integer(value) => format!("int({value})"),
        RawLiteralConst::Number(value) => format!("num({value})"),
        RawLiteralConst::String(value) => format!("str({})", format_raw_string(value)),
        RawLiteralConst::Int64(value) => format!("i64({value})"),
        RawLiteralConst::UInt64(value) => format!("u64({value})"),
        RawLiteralConst::Vector(vector) => {
            format!("vector({:?})", vector.components.map(f32::from_bits))
        }
        RawLiteralConst::Complex { real, imag } => format!("complex({real},{imag})"),
    }
}

pub(crate) fn format_origin(origin: Origin) -> String {
    let Span { offset, size } = origin.span;
    let end = offset + size;
    let raw = format_optional_raw_word(origin.raw_word);
    format!("[{offset}..{end} raw={raw}]")
}

pub(crate) fn format_optional_raw_word(raw_word: Option<u64>) -> String {
    raw_word.map_or_else(|| "-".to_owned(), |word| format!("0x{word:08x}"))
}

pub(crate) fn format_optional_u32(value: Option<u32>) -> String {
    value.map_or_else(|| "-".to_owned(), |value| value.to_string())
}

pub(crate) fn format_optional_line(line: Option<&u32>) -> String {
    line.map_or_else(|| "-".to_owned(), |line| line.to_string())
}

pub(crate) fn format_endianness(endianness: Endianness) -> &'static str {
    match endianness {
        Endianness::Little => "little",
        Endianness::Big => "big",
    }
}
