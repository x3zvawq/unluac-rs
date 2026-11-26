//! 零额外依赖的 CLI 结构化 JSON 输出（供脚本与 AI Agent 检索 proto、常量与批量结果）。

use std::collections::BTreeSet;
use std::fmt::Write as _;

use unluac::decompile::{DecompileDialect, GeneratedChunkKind};
use unluac::parser::{RawChunk, RawLiteralConst, RawProto, RawString};

use super::batch::BatchSummary;

pub(super) fn render_proto_listing_json(chunk: &RawChunk, dialect: DecompileDialect) -> String {
    let mut rows = Vec::new();
    collect_proto_json_rows(&chunk.main, None, 0, &mut rows);

    let mut out = String::from("{\n");
    let _ = writeln!(
        out,
        "  \"dialect\": {},",
        json_str(<&'static str>::from(dialect))
    );
    match chunk.main.common.source.as_ref() {
        Some(src) => {
            let _ = writeln!(out, "  \"source\": {},", json_str(&raw_string_text(src)));
        }
        None => out.push_str("  \"source\": null,\n"),
    }
    out.push_str("  \"protos\": [\n");
    for (idx, row) in rows.iter().enumerate() {
        out.push_str("    {");
        let _ = write!(out, "\"id\": {}, \"parent\": ", row.id);
        match row.parent {
            Some(p) => {
                let _ = write!(out, "{p}");
            }
            None => out.push_str("null"),
        }
        let _ = write!(
            out,
            ", \"depth\": {}, \"lineStart\": {}, \"lineEnd\": {}, \"params\": {}, \"isVararg\": {}, \"upvalues\": {}, \"instrs\": {}, \"children\": [",
            row.depth,
            row.line_start,
            row.line_end,
            row.params,
            row.is_vararg,
            row.upvalues,
            row.instrs,
        );
        for (ci, child_id) in row.children.iter().enumerate() {
            if ci > 0 {
                out.push_str(", ");
            }
            let _ = write!(out, "{child_id}");
        }
        out.push_str("], \"strings\": [");
        for (si, s) in row.strings.iter().enumerate() {
            if si > 0 {
                out.push_str(", ");
            }
            out.push_str(&json_str(s));
        }
        out.push_str("]}");
        if idx + 1 < rows.len() {
            out.push(',');
        }
        out.push('\n');
    }
    out.push_str("  ]\n}\n");
    out
}

pub(super) fn render_single_result_json(
    dialect: DecompileDialect,
    kind: GeneratedChunkKind,
    source: &str,
    proto_id: Option<usize>,
    proto_count: usize,
    failed_protos: &[usize],
) -> String {
    let mut out = String::from("{\n");
    let _ = writeln!(
        out,
        "  \"dialect\": {},",
        json_str(<&'static str>::from(dialect))
    );
    let _ = writeln!(out, "  \"kind\": {},", json_str(<&'static str>::from(kind)));
    match proto_id {
        Some(id) => {
            let _ = writeln!(out, "  \"protoId\": {id},");
        }
        None => out.push_str("  \"protoId\": null,\n"),
    }
    let _ = writeln!(out, "  \"protoCount\": {proto_count},");
    out.push_str("  \"failedProtos\": [");
    for (i, pid) in failed_protos.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        let _ = write!(out, "{pid}");
    }
    out.push_str("],\n");
    let _ = writeln!(out, "  \"source\": {}", json_str(source));
    out.push_str("}\n");
    out
}

pub(super) fn render_batch_summary_json(summary: &BatchSummary) -> String {
    let mut out = String::from("{\n");
    let _ = writeln!(out, "  \"inputDir\": {},", json_str(&summary.input_dir));
    let _ = writeln!(out, "  \"outputDir\": {},", json_str(&summary.output_dir));
    let _ = writeln!(out, "  \"scanned\": {},", summary.scanned);
    let _ = writeln!(out, "  \"decompiled\": {},", summary.decompiled);
    let _ = writeln!(out, "  \"diagnostic\": {},", summary.diagnostic);
    let _ = writeln!(out, "  \"skipped\": {},", summary.skipped);
    let _ = writeln!(out, "  \"failed\": {},", summary.failed);
    out.push_str("  \"failures\": [");
    if !summary.failures.is_empty() {
        out.push('\n');
        for (idx, item) in summary.failures.iter().enumerate() {
            let _ = write!(
                out,
                "    {{\"path\": {}, \"error\": {}}}",
                json_str(&item.path),
                json_str(&item.error)
            );
            if idx + 1 < summary.failures.len() {
                out.push(',');
            }
            out.push('\n');
        }
        out.push_str("  ");
    }
    out.push_str("]\n}\n");
    out
}

struct ProtoJsonRow {
    id: usize,
    parent: Option<usize>,
    depth: usize,
    line_start: u32,
    line_end: u32,
    params: u8,
    is_vararg: bool,
    upvalues: usize,
    instrs: usize,
    children: Vec<usize>,
    strings: Vec<String>,
}

fn collect_proto_json_rows(
    proto: &RawProto,
    parent: Option<usize>,
    depth: usize,
    rows: &mut Vec<ProtoJsonRow>,
) -> usize {
    let id = rows.len();
    let mut unique_strings = BTreeSet::new();
    let mut strings = Vec::new();
    for constant in proto.common.constants.common.literals.iter() {
        if let RawLiteralConst::String(raw) = constant {
            let text = raw_string_text(raw);
            if !text.is_empty() && unique_strings.insert(text.clone()) {
                strings.push(text);
                if strings.len() >= 32 {
                    break;
                }
            }
        }
    }
    rows.push(ProtoJsonRow {
        id,
        parent,
        depth,
        line_start: proto.common.line_range.defined_start,
        line_end: proto.common.line_range.defined_end,
        params: proto.common.signature.num_params,
        is_vararg: proto.common.signature.is_vararg,
        upvalues: proto.common.upvalues.common.count as usize,
        instrs: proto.common.instructions.len(),
        children: Vec::new(),
        strings,
    });
    let mut child_ids = Vec::with_capacity(proto.common.children.len());
    for child in &proto.common.children {
        child_ids.push(collect_proto_json_rows(child, Some(id), depth + 1, rows));
    }
    rows[id].children = child_ids;
    id
}

fn raw_string_text(raw: &RawString) -> String {
    if let Some(decoded) = &raw.text {
        decoded.value.to_string()
    } else {
        String::from_utf8_lossy(&raw.bytes).into_owned()
    }
}

fn json_str(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
