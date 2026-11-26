//! 这个模块承载整个字节码 parser 层。
//!
//! 它的职责是提供统一入口、共享基础设施和跨 dialect 共享的数据模型；
//! 主 pipeline 的 Parse stage 入口也在这里落点，由 parser 自己按已解析的 `DecompileDialect` 分派。
//! 具体某个 dialect 的 parser 本体与专属枚举都放到子目录里，避免公共层被单个版本的细节持续污染。

#[cfg(feature = "decompile-debug")]
mod debug;
#[cfg(not(feature = "decompile-debug"))]
mod debug {
    crate::debug::define_unavailable_stage_dump!(dump_parser);
}
mod dialect;
mod error;
mod family;
mod limits;
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
    let mut reader = reader::BinaryReader::new(bytes);
    let Ok(version) = reader.read_u8() else {
        return false;
    };
    if !(3..=7).contains(&version) {
        return false;
    }
    let type_version = if version >= 4 {
        let Ok(tv) = reader.read_u8() else {
            return false;
        };
        if !(1..=3).contains(&tv) || (version < 5 && tv >= 3) {
            return false;
        }
        tv
    } else {
        0
    };
    let Ok(string_count) = reader.read_varint_u32_luau("luau string count") else {
        return false;
    };
    let string_count = string_count as usize;
    if string_count > reader.remaining() {
        return false;
    }
    for _ in 0..string_count {
        let Ok(len) = reader.read_varint_u32_luau("luau string length") else {
            return false;
        };
        if reader.read_exact(len as usize).is_err() {
            return false;
        }
    }
    if type_version == 3 {
        loop {
            let Ok(idx) = reader.read_u8() else {
                return false;
            };
            if idx == 0 {
                break;
            }
            let Ok(sref) = reader.read_varint_u32_luau("luau userdata type name") else {
                return false;
            };
            if sref == 0 || (sref as usize) > string_count {
                return false;
            }
        }
    }
    let Ok(proto_count) = reader.read_varint_u32_luau("luau proto count") else {
        return false;
    };
    proto_count >= 1 && (proto_count as usize) <= reader.remaining()
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
    let mut chunk = match dialect {
        DecompileDialect::Auto => unreachable!("auto dialect must be resolved before parsing"),
        DecompileDialect::Lua51 => Lua51Parser::new(options).parse(bytes),
        DecompileDialect::Lua52 => Lua52Parser::new(options).parse(bytes),
        DecompileDialect::Lua53 => Lua53Parser::new(options).parse(bytes),
        DecompileDialect::Lua54 => Lua54Parser::new(options).parse(bytes),
        DecompileDialect::Lua55 => Lua55Parser::new(options).parse(bytes),
        DecompileDialect::Luajit => LuaJitParser::new(options).parse(bytes),
        DecompileDialect::Luau => LuauParser::new(options).parse(bytes),
    }?;
    if options.string_encoding == StringEncoding::Auto {
        chunk = chunk.resolve_auto_string_encoding();
    }
    if options.ignore_debug {
        // parser 仍需先完整消费并校验变长 debug section；只有成功解析后才统一清除，
        // 这样 ignore 模式不会成为绕过格式校验或错位读取后续 proto 的入口。
        chunk = chunk.discard_debug_metadata();
    }
    Ok(chunk)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::{DecompileOptions, decompile};

    const SAMPLE_LUA51: &[u8] = &[
        27, 76, 117, 97, 81, 0, 1, 4, 8, 4, 8, 0, 12, 0, 0, 0, 0, 0, 0, 0, 64, 115, 97, 109, 112,
        108, 101, 46, 108, 117, 97, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 5, 9, 0, 0, 0, 36, 0, 0, 0,
        65, 0, 0, 0, 133, 64, 0, 0, 192, 0, 0, 0, 1, 129, 0, 0, 220, 128, 0, 1, 20, 1, 128, 0, 156,
        64, 128, 1, 30, 0, 128, 0, 3, 0, 0, 0, 4, 5, 0, 0, 0, 0, 0, 0, 0, 128, 129, 1, 2, 0, 4, 6,
        0, 0, 0, 0, 0, 0, 0, 112, 114, 105, 110, 116, 0, 4, 7, 0, 0, 0, 0, 0, 0, 0, 228, 184, 150,
        231, 149, 140, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 3,
        5, 0, 0, 0, 65, 0, 0, 0, 128, 0, 0, 0, 85, 128, 128, 0, 94, 0, 0, 1, 30, 0, 128, 0, 1, 0,
        0, 0, 4, 9, 0, 0, 0, 0, 0, 0, 0, 228, 189, 160, 229, 165, 189, 44, 32, 0, 0, 0, 0, 0, 5, 0,
        0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0,
        0, 0, 0, 0, 110, 97, 109, 101, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 3, 0, 0,
        0, 4, 0, 0, 0, 5, 0, 0, 0, 5, 0, 0, 0, 5, 0, 0, 0, 5, 0, 0, 0, 5, 0, 0, 0, 5, 0, 0, 0, 5,
        0, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 103, 114, 101, 101, 116, 0, 1, 0, 0, 0, 8, 0,
        0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 114, 97, 119, 0, 2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0,
    ];
    const GBK_LUA51: &[u8] = &[
        27, 76, 117, 97, 81, 0, 1, 4, 8, 4, 8, 0, 9, 0, 0, 0, 0, 0, 0, 0, 64, 103, 98, 107, 46,
        108, 117, 97, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 0, 0, 1, 0, 0, 0, 30, 0, 0, 1,
        30, 0, 128, 0, 1, 0, 0, 0, 4, 17, 0, 0, 0, 0, 0, 0, 0, 196, 227, 186, 195, 202, 192, 189,
        231, 178, 226, 202, 212, 206, 196, 177, 190, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 1, 0,
        0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ];
    const SAMPLE_LUAU: &[u8] = &[
        7, 3, 1, 3, 97, 100, 100, 0, 2, 3, 2, 0, 0, 0, 0, 2, 33, 2, 0, 1, 22, 2, 2, 0, 0, 0, 1, 1,
        1, 24, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 1, 2, 0, 7, 65, 0, 0, 0, 64, 0, 0, 0, 6, 1, 0, 0, 4,
        2, 1, 0, 4, 3, 2, 0, 21, 1, 3, 0, 22, 1, 0, 0, 1, 6, 0, 1, 0, 1, 0, 1, 24, 0, 0, 3, 0, 0,
        0, 0, 1, 0, 0, 0, 0, 1,
    ];

    #[test]
    fn detect_dialect_rejects_non_bytecode_and_recognizes_valid_chunks() {
        assert_eq!(detect_dialect(SAMPLE_LUA51).unwrap(), DecompileDialect::Lua51);
        assert_eq!(detect_dialect(SAMPLE_LUAU).unwrap(), DecompileDialect::Luau);

        // Plain Lua source, random binary starting with Luau-like version bytes, empty, truncated.
        for bad in [
            &b""[..],
            &b"local x = 1\n"[..],
            &b"\x03\x00\x00\x00\x00"[..],
            &b"\x04\x01\x99\x01\x02\x03"[..],
            &b"\x06\x03\x01\x03abc\x00\x00"[..],
            &b"\x1bLua"[..],
            &b"\x1bLua\x59"[..],
        ] {
            assert!(
                detect_dialect(bad).is_err(),
                "expected detect_dialect to reject {bad:?}"
            );
        }
    }

    #[test]
    fn parser_rejects_malformed_and_overflow_inputs_without_panic() {
        let mut malformed_inputs: Vec<Vec<u8>> = vec![
            // Lua 5.1 truncated header & oversized string length
            b"\x1bLua\x51\x00\x01\x04\x08\x04\x08\x00\xff\xff\xff\xff\xff\xff\xff\xff".to_vec(),
            // LuaJIT header with invalid flags & huge LEB128 counts
            b"\x1bLJ\x02\x00\xff\xff\xff\xff\x0f\x00\x00\x00".to_vec(),
            // LuaJIT with huge D operand jump / register overflow
            b"\x1bLJ\x02\x02\x0c\x00\x01\x01\x00\x00\x00\x01\x12\x00\xff\xff\x00".to_vec(),
            // Lua 5.4 header with huge varint
            b"\x1bLua\x54\x00\x19\x93\r\n\x1a\n\x04\x08\x08\x78\x56\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x28\x77\x40\x01\x00".to_vec(),
        ];
        // Truncations of valid chunks at every byte boundary should never panic.
        for len in 0..SAMPLE_LUA51.len() {
            malformed_inputs.push(SAMPLE_LUA51[..len].to_vec());
        }
        for len in 0..SAMPLE_LUAU.len() {
            malformed_inputs.push(SAMPLE_LUAU[..len].to_vec());
        }

        for payload in malformed_inputs {
            let _ = decompile(&payload, DecompileOptions::default());
        }
    }

    #[test]
    fn auto_encoding_decodes_utf8_and_gbk_while_guarding_binary_bytes() {
        let utf8_res = decompile(SAMPLE_LUA51, DecompileOptions::default()).expect("decompile utf8");
        let generated = utf8_res.state.generated.as_ref().expect("generated");
        assert!(generated.source.contains("你好, "), "source:\n{}", generated.source);
        assert!(generated.source.contains("世界"), "source:\n{}", generated.source);
        // Binary bytes \x80\x81\x01\x02 must remain escaped rather than garbled into replacement chars.
        assert!(!generated.source.contains('\u{FFFD}'));
        assert!(
            generated.source.contains("\\128\\129\\001\\002")
                || generated.source.contains("\\x80\\x81\\x01\\x02"),
            "binary bytes should stay escaped:\n{}",
            generated.source
        );

        let gbk_res = decompile(GBK_LUA51, DecompileOptions::default()).expect("decompile gbk");
        let gbk_source = &gbk_res.state.generated.as_ref().expect("generated").source;
        assert!(
            gbk_source.contains("你好世界测试文本"),
            "auto encoding should detect GBK:\n{gbk_source}"
        );
    }

    #[test]
    fn generated_chunk_records_exact_proto_line_spans() {
        let res = decompile(SAMPLE_LUA51, DecompileOptions::default()).expect("decompile");
        let generated = res.state.generated.as_ref().expect("generated");
        let lines: Vec<&str> = generated.source.lines().collect();
        let (start, end) = generated
            .proto_line_spans
            .get(&1)
            .copied()
            .expect("child proto#1 line span must be recorded");
        assert!(start >= 1 && start <= end && end <= lines.len());
        assert!(
            lines[start - 1].contains("function greet(name)"),
            "expected greet header at line {start}, got {:?}",
            lines[start - 1]
        );
        assert_eq!(lines[end - 1].trim(), "end");
    }
}
