//! 这个模块承载整个字节码 parser 层。
//!
//! 它的职责是提供统一入口、共享基础设施和跨 dialect 共享的数据模型；
//! 主 pipeline 的 Parse stage 入口也在这里落点，由 parser 自己按已解析的 `DecompileDialect` 分派。
//! 具体某个 dialect 的 parser 本体与专属枚举都放到子目录里，避免公共层被单个版本的细节持续污染。

mod debug;
mod dialect;
mod error;
mod family;
mod options;
mod raw;
mod reader;
pub(crate) mod strings;

pub use debug::dump_parser;
pub use dialect::lua51::*;
pub use dialect::lua52::*;
pub use dialect::lua53::*;
pub use dialect::lua54::*;
pub use dialect::lua55::*;
pub use dialect::luajit::*;
pub use dialect::luau::*;
pub use error::ParseError;
pub use options::{ParseMode, ParseOptions, StringDecodeMode, StringEncoding};
pub use raw::*;

use dialect::lua51::Lua51Parser;
use dialect::lua52::Lua52Parser;
use dialect::lua53::Lua53Parser;
use dialect::lua54::Lua54Parser;
use dialect::lua55::Lua55Parser;
use dialect::luajit::LuaJitParser;
use dialect::luau::LuauParser;

use crate::decompile::{DecompileContext, DecompileDialect, DecompileError, DecompileState};

/// Parse 阶段入口：按请求 dialect 解析输入字节并写回 raw chunk 槽位。
pub(crate) fn parse_input(
    state: &mut DecompileState,
    context: &DecompileContext<'_>,
) -> Result<(), DecompileError> {
    state.raw_chunk = Some(parse_chunk_with_dialect(
        context.options.dialect,
        context.bytes,
        context.options.parse,
    )?);
    Ok(())
}

/// 根据 chunk 头部识别真实 dialect。
///
/// PUC-Lua 和 LuaJIT 有稳定 magic；Luau 没有独立签名，只能用版本前缀做轻量判断，
/// 真正的结构合法性仍交给 Luau parser 负责。
pub fn detect_dialect(bytes: &[u8]) -> Result<DecompileDialect, ParseError> {
    if bytes.starts_with(b"\x1bLua") {
        return match bytes.get(4).copied() {
            Some(0x51) => Ok(DecompileDialect::Lua51),
            Some(0x52) => Ok(DecompileDialect::Lua52),
            Some(0x53) => Ok(DecompileDialect::Lua53),
            Some(0x54) => Ok(DecompileDialect::Lua54),
            Some(0x55) => Ok(DecompileDialect::Lua55),
            Some(found) => Err(ParseError::UnsupportedVersion { found }),
            None => Err(ParseError::UnexpectedEof {
                offset: bytes.len(),
                requested: 1,
                remaining: 0,
            }),
        };
    }
    if bytes.starts_with(b"\x1bLJ") {
        return Ok(DecompileDialect::Luajit);
    }
    if looks_like_luau(bytes) {
        return Ok(DecompileDialect::Luau);
    }
    Err(ParseError::InvalidSignature { offset: 0 })
}

fn looks_like_luau(bytes: &[u8]) -> bool {
    let Some((&version, rest)) = bytes.split_first() else {
        return false;
    };
    if version == 0 || version > 32 {
        return false;
    }
    version < 4 || rest.first().is_some_and(|type_version| *type_version <= 3)
}

/// 按调用方指定或自动识别出的 dialect 解析 chunk。
pub fn parse_chunk_with_dialect(
    dialect: DecompileDialect,
    bytes: &[u8],
    options: ParseOptions,
) -> Result<RawChunk, ParseError> {
    let dialect = match dialect {
        DecompileDialect::Auto => detect_dialect(bytes)?,
        resolved => resolved,
    };
    match dialect {
        DecompileDialect::Auto => unreachable!("auto dialect must be resolved before parsing"),
        DecompileDialect::Lua51 => Lua51Parser::new(options).parse(bytes),
        DecompileDialect::Lua52 => Lua52Parser::new(options).parse(bytes),
        DecompileDialect::Lua53 => Lua53Parser::new(options).parse(bytes),
        DecompileDialect::Lua54 => Lua54Parser::new(options).parse(bytes),
        DecompileDialect::Lua55 => Lua55Parser::new(options).parse(bytes),
        DecompileDialect::Luajit => LuaJitParser::new(options).parse(bytes),
        DecompileDialect::Luau => LuauParser::new(options).parse(bytes),
    }
}
