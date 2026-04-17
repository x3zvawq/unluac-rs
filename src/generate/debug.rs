//! Generate 层调试输出。
//!
//! 聚焦策略：Generate 的产物是最终 Lua 源码，语法完整性依赖文件级结构（顶层
//! `return`、重复 `end` 匹配等），任何局部裁剪都会产出非法 Lua。所以这一层
//! 不支持 `--proto` / `--proto-depth`：若用户传了 `--proto` 这里只会打一条
//! 提示行指向 `--stop-after readability --proto N`，然后照样 dump 完整文件。

use std::fmt::Write as _;

use crate::debug::{DebugColorMode, DebugDetail, DebugFilters, colorize_debug_text};

use super::common::GeneratedChunk;

/// 输出 Generate 的调试文本。
pub fn dump_generate(
    chunk: &GeneratedChunk,
    detail: DebugDetail,
    filters: &DebugFilters,
    color: DebugColorMode,
) -> String {
    let mut output = String::new();
    let _ = writeln!(output, "===== Dump Generate =====");
    let _ = writeln!(output, "generate detail={}", detail.as_str());
    let _ = writeln!(output, "target={}", chunk.dialect);
    if filters.proto.is_some() {
        let _ = writeln!(
            output,
            "note: --proto has no effect on generate stage (final source would not be syntactically valid if sliced); use --stop-after readability --proto N to preview a single function",
        );
    }
    if !chunk.warnings.is_empty() {
        let _ = writeln!(output, "warnings={}", chunk.warnings.len());
        for warning in &chunk.warnings {
            let _ = writeln!(output, "  - {warning}");
        }
    }
    let _ = writeln!(output);
    let _ = write!(output, "{}", chunk.source);
    colorize_debug_text(&output, color)
}
