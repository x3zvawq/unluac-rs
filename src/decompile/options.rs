//! 这个文件定义主 pipeline 的公共选项。
//!
//! 入口层集中补默认值，比把默认逻辑散在各阶段里更稳；后续阶段变多后，
//! 仍然只需要维护这一处归一化逻辑。

use crate::ast::ReadabilityOptions;
use crate::ast::{NamingMode, NamingOptions};
use crate::debug::{DebugColorMode, DebugDetail, DebugFilters};
use crate::generate::GenerateOptions;
use crate::parser::{ParseMode, ParseOptions, StringDecodeMode, StringEncoding};
use strum_macros::{Display, EnumString, IntoStaticStr};

use super::state::DecompileStage;

/// 供主 pipeline 和 CLI 共享的调试选项。
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct DebugOptions {
    pub enable: bool,
    pub output_stages: Vec<DecompileStage>,
    pub timing: bool,
    pub color: DebugColorMode,
    pub detail: DebugDetail,
    pub filters: DebugFilters,
    pub dump_passes: Vec<String>,
}

/// 调用方请求解析的目标 dialect。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, Display, EnumString, IntoStaticStr)]
pub enum DecompileDialect {
    #[default]
    #[strum(serialize = "lua5.1", serialize = "lua51")]
    Lua51,
    #[strum(serialize = "lua5.2", serialize = "lua52")]
    Lua52,
    #[strum(serialize = "lua5.3", serialize = "lua53")]
    Lua53,
    #[strum(serialize = "lua5.4", serialize = "lua54")]
    Lua54,
    #[strum(serialize = "lua5.5", serialize = "lua55")]
    Lua55,
    #[strum(serialize = "luajit")]
    Luajit,
    #[strum(serialize = "luau")]
    Luau,
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
            readability: ReadabilityOptions::default(),
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
