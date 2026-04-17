//! 这个模块定义各层调试能力共享的公共契约。
//!
//! 之所以把 `detail / filters` 这类类型单独提出来，是为了让 parser、
//! 后续 transformer/cfg 和主 pipeline 共享同一套调试开关，同时避免低层反向
//! 依赖 `decompile` 模块。
//!
//! 着色引擎在 `colorize` 子模块中；跨层共享的「聚焦 proto + 限深展开」模型
//! 在 `focus` 子模块中，每一层 dump 通过同一套 helper 决定哪些 proto 完整输出、
//! 哪些以 summary 行占位。

mod colorize;
mod focus;

pub(crate) use colorize::colorize_debug_text;
pub use focus::{
    FocusPlan, FocusRequest, ProtoDepth, ProtoNode, ProtoSummaryRow, build_proto_nodes,
    compute_focus_plan, format_breadcrumb, format_proto_summary_row,
};

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

/// 统一过滤器。proto 决定「聚焦哪一个 proto」，proto_depth 决定「从聚焦点向下展开多少层」。
///
/// 历史上这个结构只有 proto 一项，且 `proto=None` 表示全量。现在我们引入 proto_depth
/// 之后仍然保留「库层默认=全量」的语义（`Default` = `ProtoDepth::All`），让库内
/// 单测/诊断打印不会因默认值改变而突然变少；CLI 层自行把默认改成 `Fixed(0)`。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub struct DebugFilters {
    pub proto: Option<usize>,
    pub proto_depth: ProtoDepth,
}

impl DebugFilters {
    /// 把 `DebugFilters` 投射成 `FocusRequest`，方便传给 `compute_focus_plan`。
    pub fn as_focus_request(&self) -> FocusRequest {
        FocusRequest {
            proto: self.proto,
            depth: self.proto_depth,
        }
    }

    /// 旧的「全量、不过滤」语义。库内诊断用途（如单测失败时 dump 全部 HIR）使用这个。
    ///
    /// `Default` 实现走的是「默认只看入口 proto」的新语义，所以当你真的想要
    /// 旧的全量行为时请显式走这个构造器。
    pub fn unfiltered() -> Self {
        Self {
            proto: None,
            proto_depth: ProtoDepth::All,
        }
    }
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
