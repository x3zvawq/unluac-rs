//! Naming 层调试输出。

use std::fmt::Write as _;

use crate::debug::{DebugColorMode, DebugDetail, DebugFilters, ProtoDepth, colorize_debug_text};

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
    let _ = writeln!(output, "filters proto_depth={}", filters.proto_depth);
    let _ = writeln!(output);

    // Naming 不持有 proto 父子拓扑；按「focus=proto」+「depth 控制是否展开其他 proto」
    // 的最小化语义来消费 filters：
    // - depth = Fixed(0) 时：只展示焦点 proto（未指定则默认 proto 0）；其余以单行
    //   `<elided>` 占位，提醒调用者存在其他 proto。
    // - depth = Fixed(N>=1) 或 All：展示全部 proto（naming 没有层级可言，简化处理）。
    let focus = filters.proto.unwrap_or(0);
    let expand_all = !matches!(filters.proto_depth, ProtoDepth::Fixed(0));

    for (index, function) in names.functions.iter().enumerate() {
        if expand_all || index == focus {
            let _ = writeln!(output, "proto#{index}");
            write_function(&mut output, function, detail);
        } else {
            let _ = writeln!(
                output,
                "proto#{index} <elided> params={} locals={} upvalues={}",
                function.params.len(),
                function.locals.len(),
                function.upvalues.len(),
            );
        }
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
