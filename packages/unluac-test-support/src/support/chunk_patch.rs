//! 对测试专用 Lua 5.1 chunk 执行受控跳转补丁；依赖格式边界检查，不负责生产解析器；例如构造普通源码难以触发的 unsupported island。

pub(super) fn patch_lua51_main_jump(
    chunk: &mut [u8],
    jump_pc: usize,
    target_pc: usize,
) -> Result<(), String> {
    const LUA_SIGNATURE: &[u8; 4] = b"\x1bLua";
    const LUA51_VERSION: u8 = 0x51;
    const OP_JMP: u32 = 22;
    const MAXARG_SBX: i32 = 131_071;

    let header = chunk
        .get(..12)
        .ok_or_else(|| "Lua 5.1 fixture is shorter than its binary header".to_owned())?;
    if &header[..4] != LUA_SIGNATURE || header[4] != LUA51_VERSION || header[5] != 0 {
        return Err("unsupported-island fixture is not a standard Lua 5.1 chunk".to_owned());
    }
    let little_endian = match header[6] {
        0 => false,
        1 => true,
        value => return Err(format!("invalid Lua 5.1 endian flag {value}")),
    };
    let int_size = usize::from(header[7]);
    let size_t_size = usize::from(header[8]);
    let instruction_size = usize::from(header[9]);
    if int_size == 0 || size_t_size == 0 || instruction_size != 4 {
        return Err(format!(
            "unsupported Lua 5.1 fixture widths: int={int_size}, size_t={size_t_size}, instruction={instruction_size}"
        ));
    }

    let mut cursor = 12usize;
    let source_len = read_lua_uint(chunk, &mut cursor, size_t_size, little_endian)?;
    cursor = cursor
        .checked_add(source_len)
        .ok_or_else(|| "Lua 5.1 source name length overflow".to_owned())?;
    let proto_header_len = int_size
        .checked_mul(2)
        .and_then(|len| len.checked_add(4))
        .ok_or_else(|| "Lua 5.1 proto header width overflow".to_owned())?;
    cursor = cursor
        .checked_add(proto_header_len)
        .ok_or_else(|| "Lua 5.1 proto header offset overflow".to_owned())?;
    let code_len = read_lua_uint(chunk, &mut cursor, int_size, little_endian)?;
    if jump_pc == 0 || jump_pc > code_len || target_pc == 0 || target_pc > code_len {
        return Err(format!(
            "Lua 5.1 jump patch is outside the main code arena: pc={jump_pc}, target={target_pc}, code={code_len}"
        ));
    }
    let instruction_offset = (jump_pc - 1)
        .checked_mul(instruction_size)
        .ok_or_else(|| "Lua 5.1 instruction index overflow".to_owned())?;
    let offset = cursor
        .checked_add(instruction_offset)
        .ok_or_else(|| "Lua 5.1 instruction offset overflow".to_owned())?;
    let end = offset
        .checked_add(instruction_size)
        .ok_or_else(|| "Lua 5.1 instruction end overflow".to_owned())?;
    let bytes = chunk
        .get_mut(offset..end)
        .ok_or_else(|| "Lua 5.1 main code is truncated".to_owned())?;
    let encoded: [u8; 4] = bytes
        .as_ref()
        .try_into()
        .map_err(|_| "Lua 5.1 instruction is not four bytes".to_owned())?;
    let mut word = if little_endian {
        u32::from_le_bytes(encoded)
    } else {
        u32::from_be_bytes(encoded)
    };
    if word & 0x3f != OP_JMP {
        return Err(format!(
            "Lua 5.1 fixture pc {jump_pc} is opcode {}, expected JMP",
            word & 0x3f
        ));
    }
    let sbx = i32::try_from(target_pc)
        .and_then(|target| i32::try_from(jump_pc).map(|pc| target - pc - 1))
        .map_err(|_| "Lua 5.1 jump pc does not fit i32".to_owned())?;
    let bx = sbx + MAXARG_SBX;
    if !(0..=2 * MAXARG_SBX + 1).contains(&bx) {
        return Err(format!("Lua 5.1 jump offset {sbx} is not encodable"));
    }
    word = (word & 0x3fff) | ((bx as u32) << 14);
    let encoded = if little_endian {
        word.to_le_bytes()
    } else {
        word.to_be_bytes()
    };
    bytes.copy_from_slice(&encoded);
    Ok(())
}

pub(super) fn read_lua_uint(
    bytes: &[u8],
    cursor: &mut usize,
    width: usize,
    little_endian: bool,
) -> Result<usize, String> {
    if width > 8 {
        return Err(format!("Lua integer width {width} exceeds u64"));
    }
    let end = cursor
        .checked_add(width)
        .ok_or_else(|| "Lua integer offset overflow".to_owned())?;
    let raw = bytes
        .get(*cursor..end)
        .ok_or_else(|| "Lua chunk is truncated while reading an integer".to_owned())?;
    *cursor = end;
    let mut value = 0u64;
    if little_endian {
        for (shift, byte) in raw.iter().copied().enumerate() {
            value |= u64::from(byte) << (shift * 8);
        }
    } else {
        for byte in raw {
            value = (value << 8) | u64::from(*byte);
        }
    }
    usize::try_from(value).map_err(|_| format!("Lua integer {value} does not fit usize"))
}
