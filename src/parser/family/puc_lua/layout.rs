//! 这个文件承载 PUC-Lua family 在解析 proto 时复用的布局读取 helper。
//!
//! chunk header 已经把机器布局固化为 `PucLuaChunkLayout`，共享层继续使用同一份
//! raw 事实读取指令字、固定宽度整数和 `lua_Integer`，避免 parser 内部再维护一套
//! 字段完全重叠的工作态布局。

use crate::parser::error::ParseError;
use crate::parser::raw::PucLuaChunkLayout;
use crate::parser::reader::BinaryReader;

/// 一条原始 32-bit 指令字及其来源 offset。
#[derive(Debug, Clone, Copy)]
pub(crate) struct RawInstructionWord {
    pub(crate) offset: usize,
    pub(crate) word: u32,
}

/// 按给定布局读取一段连续的指令字，供各个 PUC-Lua parser 共享。
pub(crate) fn read_instruction_words(
    reader: &mut BinaryReader<'_>,
    layout: &PucLuaChunkLayout,
    count: u32,
    instruction_size_field: &'static str,
) -> Result<Vec<RawInstructionWord>, ParseError> {
    let capacity = reader.checked_count_capacity(count as usize, layout.instruction_size.into())?;
    let mut words = Vec::with_capacity(capacity);

    for _ in 0..count {
        let offset = reader.offset();
        let word = reader.read_u64_sized(
            layout.instruction_size,
            layout.endianness,
            instruction_size_field,
        )?;
        let word = u32::try_from(word).map_err(|_| ParseError::UnsupportedValue {
            field: "instruction word",
            value: word,
        })?;
        words.push(RawInstructionWord { offset, word });
    }

    Ok(words)
}

/// 读取 5.2/5.3 这类固定宽度整数字段。
pub(crate) fn read_sized_i64(
    reader: &mut BinaryReader<'_>,
    layout: &PucLuaChunkLayout,
    field: &'static str,
) -> Result<i64, ParseError> {
    reader.read_i64_sized(layout.integer_size, layout.endianness, field)
}

/// 读取固定宽度、必须非负的计数/行号字段。
pub(crate) fn read_sized_u32(
    reader: &mut BinaryReader<'_>,
    layout: &PucLuaChunkLayout,
    field: &'static str,
) -> Result<u32, ParseError> {
    let value = read_sized_i64(reader, layout, field)?;
    if value < 0 {
        return Err(ParseError::NegativeValue { field, value });
    }

    u32::try_from(value).map_err(|_| ParseError::IntegerOverflow {
        field,
        value: value as u64,
    })
}

/// 读取 header 中单独声明宽度的 `lua_Integer` 字段。
pub(crate) fn read_layout_lua_integer(
    reader: &mut BinaryReader<'_>,
    layout: &PucLuaChunkLayout,
    field: &'static str,
    parser_label: &'static str,
) -> Result<i64, ParseError> {
    let Some(size) = layout.lua_integer_size else {
        unreachable!("{parser_label} parser should always carry lua_integer_size in layout");
    };
    reader.read_i64_sized(size, layout.endianness, field)
}
