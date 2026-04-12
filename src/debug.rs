//! 这个模块定义各层调试能力共享的公共契约。
//!
//! 之所以把 `detail / filters` 这类类型单独提出来，是为了让 parser、
//! 后续 transformer/cfg 和主 pipeline 共享同一套调试开关，同时避免低层反向
//! 依赖 `decompile` 模块。
//!
//! 着色引擎在 `colorize` 子模块中，独立于这些契约类型。

mod colorize;

pub(crate) use colorize::colorize_debug_text;

use std::{fmt, str::FromStr};
use std::io::IsTerminal;

/// 调试输出详细程度。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub enum DebugDetail {
    Summary,
    #[default]
    Normal,
    Verbose,
}

impl DebugDetail {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Summary => "summary",
            Self::Normal => "normal",
            Self::Verbose => "verbose",
        }
    }
}

impl fmt::Display for DebugDetail {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for DebugDetail {
    type Err = ();

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "summary" => Ok(Self::Summary),
            "normal" => Ok(Self::Normal),
            "verbose" => Ok(Self::Verbose),
            _ => Err(()),
        }
    }
}

/// 调试输出颜色策略。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub enum DebugColorMode {
    #[default]
    Auto,
    Always,
    Never,
}

impl DebugColorMode {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Auto => "auto",
            Self::Always => "always",
            Self::Never => "never",
        }
    }

    pub(crate) fn enabled(self) -> bool {
        match self {
            Self::Auto => std::io::stdout().is_terminal(),
            Self::Always => true,
            Self::Never => false,
        }
    }
}

impl fmt::Display for DebugColorMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for DebugColorMode {
    type Err = ();

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "auto" => Ok(Self::Auto),
            "always" => Ok(Self::Always),
            "never" => Ok(Self::Never),
            _ => Err(()),
        }
    }
}

/// 统一过滤器先从 proto 维度开始，后续再按同样模式扩展到 block、instr、reg。
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct DebugFilters {
    pub proto: Option<usize>,
}

/// 把一组 `Display` 元素格式化为 `[a, b, c]`，空集输出 `[-]`。
///
/// 各层 debug.rs 共享此通用格式化逻辑，避免每个模块各写一份。
pub fn format_display_set(items: impl IntoIterator<Item = impl fmt::Display>) -> String {
    let formatted: Vec<String> = items.into_iter().map(|item| item.to_string()).collect();
    if formatted.is_empty() {
        "[-]".to_string()
    } else {
        format!("[{}]", formatted.join(", "))
    }
}

#[cfg(test)]
mod tests;
