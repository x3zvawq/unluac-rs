//! Generate 层调试输出。

use std::fmt::Write as _;

use crate::debug::{DebugColorMode, DebugDetail, DebugFilters, colorize_debug_text};

use super::common::GeneratedChunk;

/// 输出 Generate 的调试文本。
pub fn dump_generate(
    chunk: &GeneratedChunk,
    detail: DebugDetail,
    _filters: &DebugFilters,
    color: DebugColorMode,
) -> String {
    let mut output = String::new();
    let _ = writeln!(output, "===== Dump Generate =====");
    let _ = writeln!(output, "generate detail={}", detail.label());
    let _ = writeln!(output);
    let _ = write!(output, "{}", chunk.source);
    colorize_debug_text(&output, color)
}
