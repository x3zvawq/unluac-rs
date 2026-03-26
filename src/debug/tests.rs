//! 这个文件承载 debug 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use super::{DebugColorMode, DebugPalette, colorize_inline};

#[test]
fn colorizes_elseif_as_keyword() {
    let palette = DebugPalette::new(DebugColorMode::Always);

    assert_eq!(
        colorize_inline("elseif", palette),
        palette.keyword("elseif")
    );
}
