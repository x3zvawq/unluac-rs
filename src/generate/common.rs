//! Generate 层共享类型。
//!
//! 这些类型需要同时被 decompile 入口、renderer 和调试输出复用，所以单独抽到这里，
//! 避免把“生成选项”和“最终产物”散落在 emit/render 两边。

use crate::ast::AstDialectVersion;

/// 最终生成的源码结果。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneratedChunk {
    pub dialect: AstDialectVersion,
    pub source: String,
    pub warnings: Vec<String>,
}

impl Default for GeneratedChunk {
    fn default() -> Self {
        Self {
            dialect: AstDialectVersion::Lua51,
            source: String::new(),
            warnings: Vec::new(),
        }
    }
}

/// 代码生成选项。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GenerateOptions {
    pub mode: GenerateMode,
    pub indent_width: usize,
    pub max_line_length: usize,
    pub quote_style: QuoteStyle,
    pub table_style: TableStyle,
    pub conservative_output: bool,
}

impl Default for GenerateOptions {
    fn default() -> Self {
        Self {
            mode: GenerateMode::Strict,
            indent_width: 4,
            max_line_length: 100,
            quote_style: QuoteStyle::MinEscape,
            table_style: TableStyle::Balanced,
            conservative_output: true,
        }
    }
}

/// 输出层在遇到目标方言不支持的语法时该如何处理。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum GenerateMode {
    #[default]
    Strict,
    BestEffort,
    Permissive,
}

impl GenerateMode {
    pub const fn label(self) -> &'static str {
        match self {
            Self::Strict => "strict",
            Self::BestEffort => "best-effort",
            Self::Permissive => "permissive",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "strict" => Some(Self::Strict),
            "best-effort" | "best_effort" | "besteffort" => Some(Self::BestEffort),
            "permissive" => Some(Self::Permissive),
            _ => None,
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
