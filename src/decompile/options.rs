//! 这个文件定义主 pipeline 的公共选项。
//!
//! 入口层集中补默认值，比把默认逻辑散在各阶段里更稳；后续阶段变多后，
//! 仍然只需要维护这一处归一化逻辑。

use std::fmt;

use crate::parser::ParseOptions;

use super::debug::DebugOptions;
use super::state::DecompileStage;

/// 调用方请求解析的目标 dialect。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub enum DecompileDialect {
    #[default]
    Lua51,
    Lua52,
    Lua53,
}

impl DecompileDialect {
    pub const fn label(self) -> &'static str {
        match self {
            Self::Lua51 => "lua5.1",
            Self::Lua52 => "lua5.2",
            Self::Lua53 => "lua5.3",
        }
    }

    /// 入口层统一做字符串解析，可以避免 CLI、wasm 绑定和测试各写一套映射。
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "lua5.1" | "lua51" => Some(Self::Lua51),
            "lua5.2" | "lua52" => Some(Self::Lua52),
            "lua5.3" | "lua53" => Some(Self::Lua53),
            _ => None,
        }
    }
}

impl fmt::Display for DecompileDialect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

/// 一次主反编译调用的顶层选项。
#[derive(Debug, Clone, PartialEq)]
pub struct DecompileOptions {
    pub dialect: DecompileDialect,
    pub parse: ParseOptions,
    pub target_stage: DecompileStage,
    pub debug: DebugOptions,
}

impl Default for DecompileOptions {
    fn default() -> Self {
        Self {
            dialect: DecompileDialect::Lua51,
            parse: ParseOptions::default(),
            // 默认仍停在 parse，是为了保留当前最常用的 parser 调试工作流。
            target_stage: DecompileStage::Parse,
            debug: DebugOptions::default(),
        }
    }
}

impl DecompileOptions {
    pub(crate) fn normalized(mut self) -> Self {
        if self.debug.enable && self.debug.output_stages.is_empty() {
            self.debug.output_stages.push(self.target_stage);
        }
        self
    }
}
