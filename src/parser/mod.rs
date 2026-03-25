//! 这个模块承载整个字节码 parser 层。
//!
//! 它的职责是提供统一入口、共享基础设施和跨 dialect 共享的数据模型；
//! 具体某个 dialect 的 parser 本体与专属枚举都放到子目录里，避免公共层
//! 被单个版本的细节持续污染。

mod debug;
mod dialect;
mod error;
mod options;
mod raw;
mod reader;

pub use debug::dump_parser;
pub use dialect::lua51::*;
pub use dialect::lua52::*;
pub use error::ParseError;
pub use options::{ParseMode, ParseOptions, StringDecodeMode, StringEncoding};
pub use raw::*;

use dialect::lua51::Lua51Parser;
use dialect::lua52::Lua52Parser;

const LUA_SIGNATURE: &[u8; 4] = b"\x1bLua";
const LUA51_VERSION: u8 = 0x51;
const LUA52_VERSION: u8 = 0x52;

/// 根据 chunk header 自动选择对应 dialect parser。
pub fn parse_chunk(bytes: &[u8], options: ParseOptions) -> Result<RawChunk, ParseError> {
    if bytes.len() < 5 {
        return Err(ParseError::UnexpectedEof {
            offset: 0,
            requested: 5,
            remaining: bytes.len(),
        });
    }

    if &bytes[..4] != LUA_SIGNATURE {
        return Err(ParseError::InvalidSignature { offset: 0 });
    }

    match bytes[4] {
        LUA51_VERSION => Lua51Parser::new(options).parse(bytes),
        LUA52_VERSION => Lua52Parser::new(options).parse(bytes),
        found => Err(ParseError::UnsupportedVersion { found }),
    }
}

/// 直接按 Lua 5.1 规则解析 chunk，不做版本自动探测。
pub fn parse_lua51_chunk(bytes: &[u8], options: ParseOptions) -> Result<RawChunk, ParseError> {
    Lua51Parser::new(options).parse(bytes)
}

/// 直接按 Lua 5.2 规则解析 chunk，不做版本自动探测。
pub fn parse_lua52_chunk(bytes: &[u8], options: ParseOptions) -> Result<RawChunk, ParseError> {
    Lua52Parser::new(options).parse(bytes)
}
