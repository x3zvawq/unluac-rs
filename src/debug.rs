//! 这个模块定义各层调试能力共享的公共契约。
//!
//! 之所以把 `detail / filters` 这类类型单独提出来，是为了让 parser、
//! 后续 transformer/cfg 和主 pipeline 共享同一套调试开关，同时避免低层反向
//! 依赖 `decompile` 模块。

use std::fmt;

/// 调试输出详细程度。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub enum DebugDetail {
    Summary,
    #[default]
    Normal,
    Verbose,
}

impl DebugDetail {
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "summary" => Some(Self::Summary),
            "normal" => Some(Self::Normal),
            "verbose" => Some(Self::Verbose),
            _ => None,
        }
    }

    pub const fn label(self) -> &'static str {
        match self {
            Self::Summary => "summary",
            Self::Normal => "normal",
            Self::Verbose => "verbose",
        }
    }
}

impl fmt::Display for DebugDetail {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

/// 统一过滤器先从 proto 维度开始，后续再按同样模式扩展到 block、instr、reg。
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct DebugFilters {
    pub proto: Option<usize>,
}
