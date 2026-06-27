//! 这个模块定义各层调试能力共享的公共契约。
//!
//! 之所以把 `detail / filters` 这类类型单独提出来，是为了让 parser、
//! transformer/structure 和主 pipeline 共享同一套调试开关，同时避免低层反向
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

/// 生成一对 `#[cfg(feature)]` / `#[cfg(not)]` 的阶段 dump 入口。
///
/// 各业务层在自己的 `debug.rs` 里声明 stage dump：启用 `decompile-debug` 时从
/// `DecompileState` 读取本层产物并渲染文本；禁用时只保留同签名空实现，避免 wasm
/// 入口把调试渲染逻辑作为可用能力暴露出去。
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

pub(crate) use define_stage_dump;

use std::{fmt, io::IsTerminal};
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

impl DebugColorMode {
    pub(crate) fn enabled(self) -> bool {
        match self {
            Self::Auto => std::io::stdout().is_terminal(),
            Self::Always => true,
            Self::Never => false,
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
