//! 这个文件先提供 Luau parser 的显式入口。
//!
//! 在 raw model 完成去 PUC-Lua 中心化之前，这里只负责占住 Luau 的 dialect
//! 分派位，避免调用方继续落回错误的 PUC-Lua 自动探测路径。

use crate::parser::{ParseError, ParseOptions, RawChunk};

/// Luau bytecode parser。
#[derive(Debug, Clone, Copy)]
pub struct LuauParser {
    options: ParseOptions,
}

impl LuauParser {
    pub const fn new(options: ParseOptions) -> Self {
        Self { options }
    }

    pub fn parse(self, _bytes: &[u8]) -> Result<RawChunk, ParseError> {
        let _options = self.options;
        Err(ParseError::UnsupportedDialect { dialect: "luau" })
    }
}
