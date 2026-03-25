//! 这个文件定义 parser 层的错误类型。
//!
//! 错误里保留 offset 等定位信息，是为了让调试输出和回归测试可以直接定位
//! 原始 chunk 的问题位置，而不是把底层读取细节泄漏到更高层。

use thiserror::Error;

/// 将 Lua 字节码解析成 raw 结构时可能产生的错误。
#[derive(Debug, Error)]
pub enum ParseError {
    #[error(
        "unexpected end of input at offset {offset}: need {requested} bytes but only {remaining} remain"
    )]
    UnexpectedEof {
        offset: usize,
        requested: usize,
        remaining: usize,
    },
    #[error("invalid Lua chunk signature at offset {offset}")]
    InvalidSignature { offset: usize },
    #[error("unsupported Lua version byte 0x{found:02x}")]
    UnsupportedVersion { found: u8 },
    #[error("unsupported PUC-Lua header format {found}")]
    UnsupportedHeaderFormat { found: u8 },
    #[error("unsupported {field} size {value} in PUC-Lua chunk")]
    UnsupportedSize { field: &'static str, value: u8 },
    #[error("unsupported {field} value {value} in PUC-Lua chunk")]
    UnsupportedValue { field: &'static str, value: u64 },
    #[error("integer overflow while decoding {field}: {value}")]
    IntegerOverflow { field: &'static str, value: u64 },
    #[error("negative {field} value {value} is not valid in PUC-Lua chunks")]
    NegativeValue { field: &'static str, value: i64 },
    #[error("invalid constant tag {tag} at offset {offset}")]
    InvalidConstantTag { offset: usize, tag: u8 },
    #[error("invalid opcode {opcode} at raw pc {pc}")]
    InvalidOpcode { pc: usize, opcode: u8 },
    #[error("missing SETLIST extra argument after raw pc {pc}")]
    MissingSetListWord { pc: usize },
    #[error("opcode `{opcode}` at raw pc {pc} must be followed by EXTRAARG")]
    MissingExtraArgWord { pc: usize, opcode: &'static str },
    #[error("opcode `{opcode}` at raw pc {pc} must be followed by EXTRAARG, found opcode {found}")]
    InvalidExtraArgWord {
        pc: usize,
        opcode: &'static str,
        found: u8,
    },
    #[error("unterminated string payload at offset {offset}")]
    UnterminatedString { offset: usize },
    #[error("failed to decode string payload at offset {offset} as {encoding}")]
    StringDecode {
        offset: usize,
        encoding: &'static str,
    },
}
