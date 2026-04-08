//! 这个文件定义主 pipeline 的公共选项。
//!
//! 入口层集中补默认值，比把默认逻辑散在各阶段里更稳；后续阶段变多后，
//! 仍然只需要维护这一处归一化逻辑。

use std::fmt;

use crate::generate::GenerateOptions;
use crate::naming::{NamingMode, NamingOptions};
use crate::parser::{
    ParseMode, ParseOptions, RawChunk, StringDecodeMode, StringEncoding, parse_lua51_chunk,
    parse_lua52_chunk, parse_lua53_chunk, parse_lua54_chunk, parse_lua55_chunk,
    parse_luajit_chunk, parse_luau_chunk,
};
use crate::readability::ReadabilityOptions;

use super::debug::DebugOptions;
use super::state::DecompileStage;

/// 调用方请求解析的目标 dialect。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub enum DecompileDialect {
    #[default]
    Lua51,
    Lua52,
    Lua53,
    Lua54,
    Lua55,
    Luajit,
    Luau,
}

impl DecompileDialect {
    pub const fn label(self) -> &'static str {
        match self {
            Self::Lua51 => "lua5.1",
            Self::Lua52 => "lua5.2",
            Self::Lua53 => "lua5.3",
            Self::Lua54 => "lua5.4",
            Self::Lua55 => "lua5.5",
            Self::Luajit => "luajit",
            Self::Luau => "luau",
        }
    }

    /// 入口层统一做字符串解析，可以避免 CLI、wasm 绑定和测试各写一套映射。
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "lua5.1" | "lua51" => Some(Self::Lua51),
            "lua5.2" | "lua52" => Some(Self::Lua52),
            "lua5.3" | "lua53" => Some(Self::Lua53),
            "lua5.4" | "lua54" => Some(Self::Lua54),
            "lua5.5" | "lua55" => Some(Self::Lua55),
            "luajit" => Some(Self::Luajit),
            "luau" => Some(Self::Luau),
            _ => None,
        }
    }

    /// 按 dialect 分派到对应的字节码 parser。
    pub fn parse_chunk(
        self,
        bytes: &[u8],
        options: ParseOptions,
    ) -> Result<RawChunk, crate::parser::ParseError> {
        match self {
            Self::Lua51 => parse_lua51_chunk(bytes, options),
            Self::Lua52 => parse_lua52_chunk(bytes, options),
            Self::Lua53 => parse_lua53_chunk(bytes, options),
            Self::Lua54 => parse_lua54_chunk(bytes, options),
            Self::Lua55 => parse_lua55_chunk(bytes, options),
            Self::Luajit => parse_luajit_chunk(bytes, options),
            Self::Luau => parse_luau_chunk(bytes, options),
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
    pub readability: ReadabilityOptions,
    pub naming: NamingOptions,
    pub generate: GenerateOptions,
}

impl Default for DecompileOptions {
    fn default() -> Self {
        Self {
            dialect: DecompileDialect::Lua51,
            parse: ParseOptions {
                mode: ParseMode::Permissive,
                string_encoding: StringEncoding::Utf8,
                string_decode_mode: StringDecodeMode::Strict,
            },
            // 默认更偏向直接拿到最终源码，仓库内 CLI / wasm / 集成调用方都共享这套预期。
            target_stage: DecompileStage::Generate,
            debug: DebugOptions::default(),
            readability: ReadabilityOptions {
                return_inline_max_complexity: 10,
                index_inline_max_complexity: 10,
                args_inline_max_complexity: 6,
                access_base_inline_max_complexity: 5,
            },
            naming: NamingOptions {
                mode: NamingMode::DebugLike,
                debug_like_include_function: true,
            },
            generate: GenerateOptions::default(),
        }
    }
}

impl DecompileOptions {
    pub(crate) fn normalized(mut self) -> Self {
        if self.debug.enable && self.debug.output_stages.is_empty() && !self.debug.timing {
            self.debug.output_stages.push(self.target_stage);
        }
        self
    }
}
