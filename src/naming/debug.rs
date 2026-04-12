//! Naming 层调试输出。

use std::fmt::Write as _;

use crate::debug::{DebugColorMode, DebugDetail, DebugFilters, colorize_debug_text};

use super::{FunctionNameMap, NameMap};

/// 输出 Naming 的调试文本。
pub fn dump_naming(
    names: &NameMap,
    detail: DebugDetail,
    filters: &DebugFilters,
    color: DebugColorMode,
) -> String {
    let mut output = String::new();
    let _ = writeln!(output, "===== Dump Naming =====");
    let _ = writeln!(
        output,
        "naming mode={} functions={}",
        names.mode.as_str(),
        names.functions.len()
    );
    if let Some(proto_id) = filters.proto {
        let _ = writeln!(output, "filters proto=proto#{proto_id}");
    }
    let _ = writeln!(output);

    for (index, function) in names.functions.iter().enumerate() {
        if filters.proto.is_some_and(|proto_id| proto_id != index) {
            continue;
        }
        let _ = writeln!(output, "proto#{index}");
        write_function(&mut output, function, detail);
    }

    colorize_debug_text(&output, color)
}

fn write_function(output: &mut String, function: &FunctionNameMap, detail: DebugDetail) {
    write_section(output, "params", "p", &function.params, detail);
    write_section(output, "locals", "l", &function.locals, detail);
    write_sparse_section(
        output,
        "synthetic-locals",
        "sl",
        function.synthetic_locals.iter(),
        detail,
    );
    write_section(output, "upvalues", "u", &function.upvalues, detail);
}

fn write_section(
    output: &mut String,
    title: &str,
    prefix: &str,
    names: &[super::NameInfo],
    detail: DebugDetail,
) {
    if names.is_empty() && matches!(detail, DebugDetail::Summary) {
        return;
    }
    let _ = writeln!(output, "  {title}");
    if names.is_empty() {
        let _ = writeln!(output, "    <empty>");
        return;
    }
    for (index, info) in names.iter().enumerate() {
        let rename_note = if info.renamed {
            ", renamed-for-conflict"
        } else {
            ""
        };
        let source = info.source.as_str();
        let _ = writeln!(
            output,
            "    {prefix}{index} -> {} (source={source}{rename_note})",
            info.text,
        );
    }
}

fn write_sparse_section<'a>(
    output: &mut String,
    title: &str,
    prefix: &str,
    names: impl Iterator<Item = (&'a crate::ast::AstSyntheticLocalId, &'a super::NameInfo)>,
    detail: DebugDetail,
) {
    let names = names.collect::<Vec<_>>();
    if names.is_empty() && matches!(detail, DebugDetail::Summary) {
        return;
    }
    let _ = writeln!(output, "  {title}");
    if names.is_empty() {
        let _ = writeln!(output, "    <empty>");
        return;
    }
    for (index, info) in names {
        let rename_note = if info.renamed {
            ", renamed-for-conflict"
        } else {
            ""
        };
        let source = info.source.as_str();
        let _ = writeln!(
            output,
            "    {prefix}{} -> {} (source={source}{rename_note})",
            index.index(),
            info.text,
        );
    }
}
