//! 这个文件承载 parser debug 输出里的跨 dialect 公共工具。
//!
//! dialect debug 需要展示的方言字段各不相同，但 proto traversal、focus/elide 规则、
//! RawString/literal/origin 这类基础格式化是一致的；集中在这里可以避免每个 dialect
//! debug 文件复制同一套展示细节。

use std::fmt::Write as _;

use crate::debug::{
    DebugFilters, FocusPlan, ProtoSummaryRow, build_proto_nodes, compute_focus_plan,
    format_proto_summary_row,
};
use crate::parser::{DecodedText, Endianness, Origin, RawLiteralConst, RawProto, RawString, Span};

/// 各 dialect parser dump 复用的 `(id, parent, depth, proto)` 快照。
#[derive(Debug, Clone, Copy)]
pub(crate) struct ParserProtoEntry<'a> {
    pub id: usize,
    pub parent: Option<usize>,
    pub depth: usize,
    pub proto: &'a RawProto,
}

/// 收集 proto tree 的前序遍历视图，供 focus plan 和 elided 行共用。
pub(crate) fn collect_parser_proto_entries(root: &RawProto) -> Vec<ParserProtoEntry<'_>> {
    let mut entries = Vec::new();
    collect_parser_proto_entries_inner(root, None, 0, &mut entries);
    entries
}

fn collect_parser_proto_entries_inner<'a>(
    proto: &'a RawProto,
    parent: Option<usize>,
    depth: usize,
    entries: &mut Vec<ParserProtoEntry<'a>>,
) {
    let id = entries.len();
    entries.push(ParserProtoEntry {
        id,
        parent,
        depth,
        proto,
    });

    for child in &proto.common.children {
        collect_parser_proto_entries_inner(child, Some(id), depth + 1, entries);
    }
}

/// 根据 parser proto traversal 生成统一 focus plan。
pub(crate) fn plan_parser_focus(
    entries: &[ParserProtoEntry<'_>],
    filters: &DebugFilters,
) -> FocusPlan {
    let parents: Vec<Option<usize>> = entries.iter().map(|entry| entry.parent).collect();
    let nodes = build_proto_nodes(&parents);
    compute_focus_plan(&nodes, &filters.as_focus_request())
}

/// 把 `RawProto` 压成 elided 行。parser 阶段拿不到函数名，只能呈现
/// `lines / instrs / children` 三项，这些都从 `RawProto::common` 里直接取得。
pub(crate) fn build_parser_summary_row(entry: &ParserProtoEntry<'_>) -> ProtoSummaryRow {
    ProtoSummaryRow {
        id: entry.id,
        depth_below_focus: entry.depth,
        name: None,
        first: None,
        lines: Some((
            entry.proto.common.line_range.defined_start,
            entry.proto.common.line_range.defined_end,
        )),
        instrs: Some(entry.proto.common.instructions.len()),
        children: Some(entry.proto.common.children.len()),
    }
}

/// 写出被 focus plan 折叠的 proto 摘要行。
pub(crate) fn write_elided_summary(
    output: &mut String,
    indent: &str,
    entry: &ParserProtoEntry<'_>,
) {
    let _ = writeln!(
        output,
        "{indent}{}",
        format_proto_summary_row(&build_parser_summary_row(entry)),
    );
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
