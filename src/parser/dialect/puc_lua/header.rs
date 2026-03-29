use crate::parser::Endianness;
use crate::parser::error::ParseError;
use crate::parser::reader::BinaryReader;

pub(crate) const LUA_SIGNATURE: &[u8; 4] = b"\x1bLua";
pub(crate) const LUA52_LUAC_TAIL: &[u8; 6] = b"\x19\x93\r\n\x1a\n";
pub(crate) const LUA53_LUAC_DATA: &[u8; 6] = b"\x19\x93\r\n\x1a\n";
pub(crate) const LUA53_LUAC_INT: i64 = 0x5678;
pub(crate) const LUA53_LUAC_NUM: f64 = 370.5;
pub(crate) const LUA54_LUAC_DATA: &[u8; 6] = LUA53_LUAC_DATA;
pub(crate) const LUA54_LUAC_INT: i64 = LUA53_LUAC_INT;
pub(crate) const LUA54_LUAC_NUM: f64 = LUA53_LUAC_NUM;
pub(crate) const LUA55_LUAC_DATA: &[u8; 6] = LUA53_LUAC_DATA;
pub(crate) const LUA55_LUAC_INT: i64 = -0x5678;
pub(crate) const LUA55_LUAC_INST: u32 = 0x1234_5678;
pub(crate) const LUA55_LUAC_NUM: f64 = -370.5;

/// 读取 PUC-Lua 5.3+ 共享的 header prelude：
/// `signature / version / format / luac_data`。
pub(crate) fn parse_luac_data_header_prelude(
    reader: &mut BinaryReader<'_>,
    version: u8,
    format: u8,
    luac_data: &[u8; 6],
    permissive: bool,
) -> Result<usize, ParseError> {
    let start = reader.offset();
    let signature = reader.read_array::<4>()?;
    if signature != *LUA_SIGNATURE {
        return Err(ParseError::InvalidSignature { offset: start });
    }

    let found_version = reader.read_u8()?;
    if found_version != version {
        return Err(ParseError::UnsupportedVersion {
            found: found_version,
        });
    }

    let found_format = reader.read_u8()?;
    if found_format != format && !permissive {
        return Err(ParseError::UnsupportedHeaderFormat {
            found: found_format,
        });
    }

    let found_luac_data = reader.read_array::<6>()?;
    if found_luac_data != *luac_data && !permissive {
        return Err(ParseError::UnsupportedValue {
            field: "luac_data",
            value: u64::from(u32::from_le_bytes([
                found_luac_data[0],
                found_luac_data[1],
                found_luac_data[2],
                found_luac_data[3],
            ])),
        });
    }

    Ok(start)
}

/// 校验 main proto 头里单独记录的 upvalue 数量是否和 proto 内部一致。
pub(crate) fn validate_main_proto_upvalue_count(
    permissive: bool,
    actual: u8,
    expected: u8,
) -> Result<(), ParseError> {
    if !permissive && actual != expected {
        return Err(ParseError::UnsupportedValue {
            field: "main proto upvalue count",
            value: u64::from(actual),
        });
    }
    Ok(())
}

/// PUC-Lua family 目前都只支持 32-bit 指令字；把这条协议约束集中到共享层。
pub(crate) fn validate_instruction_word_size(instruction_size: u8) -> Result<(), ParseError> {
    if instruction_size != 4 {
        return Err(ParseError::UnsupportedSize {
            field: "instruction_size",
            value: instruction_size,
        });
    }
    Ok(())
}

/// 读取一个 i64 sentinel，同时用它推断大小端并校验值。
pub(crate) fn read_i64_sentinel_endianness(
    reader: &mut BinaryReader<'_>,
    size: u8,
    expected: i64,
    decode_field: &'static str,
    sentinel_field: &'static str,
    permissive: bool,
) -> Result<Endianness, ParseError> {
    let bytes = reader.read_exact(usize::from(size))?;
    let endianness = detect_endianness_from_i64_sentinel(
        bytes,
        expected,
        decode_field,
        sentinel_field,
        permissive,
    )?;
    validate_i64_sentinel_bytes(
        bytes,
        endianness,
        expected,
        decode_field,
        sentinel_field,
        permissive,
    )?;
    Ok(endianness)
}

/// 用既定 endianness 校验一个 i64 sentinel。
pub(crate) fn read_i64_sentinel(
    reader: &mut BinaryReader<'_>,
    size: u8,
    endianness: Endianness,
    expected: i64,
    decode_field: &'static str,
    sentinel_field: &'static str,
    permissive: bool,
) -> Result<(), ParseError> {
    let bytes = reader.read_exact(usize::from(size))?;
    validate_i64_sentinel_bytes(
        bytes,
        endianness,
        expected,
        decode_field,
        sentinel_field,
        permissive,
    )
}

fn validate_i64_sentinel_bytes(
    bytes: &[u8],
    endianness: Endianness,
    expected: i64,
    decode_field: &'static str,
    sentinel_field: &'static str,
    permissive: bool,
) -> Result<(), ParseError> {
    let decoded = decode_i64_bytes(bytes, endianness, decode_field)?;
    if decoded != expected && !permissive {
        return Err(ParseError::UnsupportedValue {
            field: sentinel_field,
            value: decoded as u64,
        });
    }
    Ok(())
}

/// 用既定 endianness 校验一个 f64 sentinel。
pub(crate) fn read_f64_sentinel(
    reader: &mut BinaryReader<'_>,
    size: u8,
    endianness: Endianness,
    expected: f64,
    decode_field: &'static str,
    sentinel_field: &'static str,
    permissive: bool,
) -> Result<(), ParseError> {
    let bytes = reader.read_exact(usize::from(size))?;
    let decoded = decode_f64_bytes(bytes, endianness, decode_field)?;
    if decoded != expected && !permissive {
        return Err(ParseError::UnsupportedValue {
            field: sentinel_field,
            value: decoded.to_bits(),
        });
    }
    Ok(())
}

/// 按给定字节序把 1..=8 字节的有符号整数样本扩展成 `i64`。
pub(crate) fn decode_i64_bytes(
    bytes: &[u8],
    endianness: Endianness,
    field: &'static str,
) -> Result<i64, ParseError> {
    if !(1..=8).contains(&bytes.len()) {
        return Err(ParseError::UnsupportedSize {
            field,
            value: bytes.len() as u8,
        });
    }

    let mut buffer = [0_u8; 8];
    match endianness {
        Endianness::Little => buffer[..bytes.len()].copy_from_slice(bytes),
        Endianness::Big => buffer[8 - bytes.len()..].copy_from_slice(bytes),
    }

    if bytes.len() == 8 {
        return Ok(match endianness {
            Endianness::Little => i64::from_le_bytes(buffer),
            Endianness::Big => i64::from_be_bytes(buffer),
        });
    }

    let unsigned = match endianness {
        Endianness::Little => u64::from_le_bytes(buffer),
        Endianness::Big => u64::from_be_bytes(buffer),
    };
    let bits = (bytes.len() as u32) * 8;
    let shift = 64 - bits;
    Ok(((unsigned << shift) as i64) >> shift)
}

/// 按给定字节序把 4/8 字节浮点样本扩展成 `f64`。
pub(crate) fn decode_f64_bytes(
    bytes: &[u8],
    endianness: Endianness,
    field: &'static str,
) -> Result<f64, ParseError> {
    match bytes.len() {
        4 => {
            let mut buffer = [0_u8; 4];
            buffer.copy_from_slice(bytes);
            Ok(match endianness {
                Endianness::Little => f32::from_le_bytes(buffer),
                Endianness::Big => f32::from_be_bytes(buffer),
            } as f64)
        }
        8 => {
            let mut buffer = [0_u8; 8];
            buffer.copy_from_slice(bytes);
            Ok(match endianness {
                Endianness::Little => f64::from_le_bytes(buffer),
                Endianness::Big => f64::from_be_bytes(buffer),
            })
        }
        value => Err(ParseError::UnsupportedSize {
            field,
            value: value as u8,
        }),
    }
}

/// 用 `luac_int` 一类 header sentinel 识别 chunk 真实字节序。
pub(crate) fn detect_endianness_from_i64_sentinel(
    bytes: &[u8],
    expected: i64,
    decode_field: &'static str,
    mismatch_field: &'static str,
    permissive: bool,
) -> Result<Endianness, ParseError> {
    let little = decode_i64_bytes(bytes, Endianness::Little, decode_field)?;
    if little == expected {
        return Ok(Endianness::Little);
    }

    let big = decode_i64_bytes(bytes, Endianness::Big, decode_field)?;
    if big == expected {
        return Ok(Endianness::Big);
    }

    if permissive {
        Ok(Endianness::Little)
    } else {
        Err(ParseError::UnsupportedValue {
            field: mismatch_field,
            value: little as u64,
        })
    }
}
