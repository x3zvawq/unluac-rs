//! Generate 层共享类型。
//!
//! 这些类型需要同时被 decompile 入口、renderer 和调试输出复用，所以单独抽到这里，
//! 避免把“生成选项”和“最终产物”散落在 emit/render 两边。

/// 最终生成的源码结果。
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GeneratedChunk {
    pub source: String,
}

/// 代码生成选项。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GenerateOptions {
    pub indent_width: usize,
    pub max_line_length: usize,
    pub quote_style: QuoteStyle,
    pub table_style: TableStyle,
    pub conservative_output: bool,
}

impl Default for GenerateOptions {
    fn default() -> Self {
        Self {
            indent_width: 4,
            max_line_length: 100,
            quote_style: QuoteStyle::MinEscape,
            table_style: TableStyle::Balanced,
            conservative_output: true,
        }
    }
}

/// 字符串引号策略。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum QuoteStyle {
    PreferDouble,
    PreferSingle,
    #[default]
    MinEscape,
}

impl QuoteStyle {
    pub const fn label(self) -> &'static str {
        match self {
            Self::PreferDouble => "prefer-double",
            Self::PreferSingle => "prefer-single",
            Self::MinEscape => "min-escape",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "prefer-double" => Some(Self::PreferDouble),
            "prefer-single" => Some(Self::PreferSingle),
            "min-escape" => Some(Self::MinEscape),
            _ => None,
        }
    }
}

/// 表构造器布局策略。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TableStyle {
    Compact,
    #[default]
    Balanced,
    Expanded,
}

impl TableStyle {
    pub const fn label(self) -> &'static str {
        match self {
            Self::Compact => "compact",
            Self::Balanced => "balanced",
            Self::Expanded => "expanded",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "compact" => Some(Self::Compact),
            "balanced" => Some(Self::Balanced),
            "expanded" => Some(Self::Expanded),
            _ => None,
        }
    }
}
