//! 各层调试能力共用的选项、聚焦与着色入口。
//!
//! 低层与主流水线共享这些契约，无需反向依赖 decompile。

#[cfg(any(feature = "decompile-debug", feature = "timing-report"))]
mod colorize;
#[cfg(feature = "decompile-debug")]
mod focus;

#[cfg(any(feature = "decompile-debug", feature = "timing-report"))]
pub(crate) use colorize::colorize_debug_text;
#[cfg(feature = "decompile-debug")]
pub(crate) use focus::{
    FocusPlan, FocusRequest, ProtoNode, ProtoSummaryRow, ProtoTreeEntry, build_proto_nodes,
    collect_proto_tree, compute_focus_plan, format_breadcrumb, format_proto_summary_row,
    plan_proto_focus,
};

/// 生成一对 `#[cfg(feature)]` / `#[cfg(not)]` 的阶段 dump 入口。
///
/// 各业务层在自己的 `debug.rs` 里声明 stage dump：启用 `decompile-debug` 时从
/// `DecompileState` 读取本层产物并渲染文本；禁用时只保留同签名空实现，避免 wasm
/// 入口把调试渲染逻辑作为可用能力暴露出去。
#[cfg(feature = "decompile-debug")]
macro_rules! define_stage_dump {
    (
        $(
            $(#[doc = $doc:literal])*
            pub fn $name:ident ( $state:ident, $options:ident ) => $stage:ident, $content:expr;
        )+
    ) => {
        $(
            $(#[doc = $doc])*
            #[cfg(feature = "decompile-debug")]
            pub fn $name(
                $state: &$crate::decompile::DecompileState,
                $options: &$crate::decompile::DebugOptions,
            ) -> Result<$crate::decompile::StageDebugOutput, $crate::decompile::DecompileError> {
                Ok($crate::decompile::StageDebugOutput {
                    stage: $crate::decompile::DecompileStage::$stage,
                    detail: $options.detail,
                    content: $content,
                })
            }

            $(#[doc = $doc])*
            #[cfg(not(feature = "decompile-debug"))]
            pub fn $name(
                _state: &$crate::decompile::DecompileState,
                _options: &$crate::decompile::DebugOptions,
            ) -> Result<$crate::decompile::StageDebugOutput, $crate::decompile::DecompileError> {
                Err($crate::decompile::DecompileError::DebugUnavailable)
            }
        )+
    };
}

#[cfg(feature = "decompile-debug")]
pub(crate) use define_stage_dump;

/// 生成关闭 `decompile-debug` feature 时的阶段 dump stub。
///
/// wasm/JS 这类发布入口不暴露调试渲染能力；只保留同签名函数，让主 pipeline
/// 不需要为 feature 组合复制阶段表。
#[cfg(not(feature = "decompile-debug"))]
macro_rules! define_unavailable_stage_dump {
    ($name:ident) => {
        pub fn $name(
            _state: &$crate::decompile::DecompileState,
            _options: &$crate::decompile::DebugOptions,
        ) -> Result<$crate::decompile::StageDebugOutput, $crate::decompile::DecompileError> {
            Err($crate::decompile::DecompileError::DebugUnavailable)
        }
    };
}

#[cfg(not(feature = "decompile-debug"))]
pub(crate) use define_unavailable_stage_dump;

use std::fmt;
#[cfg(any(feature = "decompile-debug", feature = "timing-report"))]
use std::io::IsTerminal;
use strum_macros::{Display, EnumString, IntoStaticStr};

/// 调试输出详细程度。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, Display, EnumString, IntoStaticStr)]
#[strum(serialize_all = "kebab-case")]
pub enum DebugDetail {
    Summary,
    #[default]
    Normal,
    Verbose,
}

/// 调试输出颜色策略。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, Display, EnumString, IntoStaticStr)]
#[strum(serialize_all = "kebab-case")]
pub enum DebugColorMode {
    #[default]
    Auto,
    Always,
    Never,
}

#[cfg(any(feature = "decompile-debug", feature = "timing-report"))]
impl DebugColorMode {
    pub(crate) fn enabled(self) -> bool {
        match self {
            Self::Auto => std::io::stdout().is_terminal(),
            Self::Always => true,
            Self::Never => false,
        }
    }
}

/// proto 向下展开的层数语义。
///
/// `Fixed(N)` 表示相对焦点 proto 向下展开 N 层；`All` 表示不设上限（等价于旧的全量行为）。
/// 默认值 `Fixed(0)` 意味着只展开焦点本身，子 proto 以占位行出现。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum ProtoDepth {
    Fixed(usize),
    All,
}

impl Default for ProtoDepth {
    fn default() -> Self {
        Self::Fixed(0)
    }
}

impl fmt::Display for ProtoDepth {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Fixed(n) => write!(f, "{n}"),
            Self::All => f.write_str("all"),
        }
    }
}

/// 统一过滤器。proto 决定「聚焦哪一个 proto」，proto_depth 决定「从聚焦点向下展开多少层」。
///
/// 默认只展开焦点 proto；`unfiltered()` 显式选择整棵树。选项类型在关闭 debug 特性时
/// 仍然可用，聚焦计算及渲染只在启用 `decompile-debug` 时编译。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub struct DebugFilters {
    pub proto: Option<usize>,
    pub proto_depth: ProtoDepth,
}

impl DebugFilters {
    /// 把 `DebugFilters` 投射成 `FocusRequest`，方便传给 `compute_focus_plan`。
    #[cfg(feature = "decompile-debug")]
    pub(crate) fn as_focus_request(&self) -> FocusRequest {
        FocusRequest {
            proto: self.proto,
            depth: self.proto_depth,
        }
    }

    /// 展开整棵 proto 树，例如测试失败时查看完整 HIR。
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
