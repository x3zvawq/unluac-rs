use crate::parser::Endianness;
use crate::parser::error::ParseError;
use crate::parser::reader::BinaryReader;

/// PUC-Lua chunk header 里显式声明的基础布局。
#[derive(Debug, Clone, Copy)]
pub(crate) struct PucLuaLayout {
    pub(crate) endianness: Endianness,
    pub(crate) integer_size: u8,
    pub(crate) lua_integer_size: Option<u8>,
    pub(crate) size_t_size: u8,
    pub(crate) instruction_size: u8,
    pub(crate) number_size: u8,
    pub(crate) integral_number: bool,
}

/// 一条原始 32-bit 指令字及其来源 offset。
#[derive(Debug, Clone, Copy)]
pub(crate) struct RawInstructionWord {
    pub(crate) offset: usize,
    pub(crate) word: u32,
}

/// 按给定布局读取一段连续的指令字，供各个 PUC-Lua parser 共享。
pub(crate) fn read_instruction_words(
    reader: &mut BinaryReader<'_>,
    layout: &PucLuaLayout,
    count: u32,
    instruction_size_field: &'static str,
) -> Result<Vec<RawInstructionWord>, ParseError> {
    let mut words = Vec::with_capacity(count as usize);

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
    layout: &PucLuaLayout,
    field: &'static str,
) -> Result<i64, ParseError> {
    reader.read_i64_sized(layout.integer_size, layout.endianness, field)
}

/// 读取固定宽度、必须非负的计数/行号字段。
pub(crate) fn read_sized_u32(
    reader: &mut BinaryReader<'_>,
    layout: &PucLuaLayout,
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
    layout: &PucLuaLayout,
    field: &'static str,
    parser_label: &'static str,
) -> Result<i64, ParseError> {
    let Some(size) = layout.lua_integer_size else {
        unreachable!("{parser_label} parser should always carry lua_integer_size in layout");
    };
    reader.read_i64_sized(size, layout.endianness, field)
}
