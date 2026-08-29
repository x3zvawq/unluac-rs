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

pub(super) fn patch_luau_self_value_capture_carrier(
    chunk: &mut [u8],
    closure_pc: usize,
    save_pc: usize,
    overwrite_pc: usize,
    target_reg: u8,
) -> Result<(), String> {
    use unluac::decompile::DecompileDialect;
    use unluac::parser::{
        LuauCaptureKind, LuauOpcode, LuauOperands, ParseOptions, RawInstrOpcode, RawInstrOperands,
        parse_chunk_with_dialect,
    };

    let parsed = parse_chunk_with_dialect(DecompileDialect::Luau, chunk, ParseOptions::default())
        .map_err(|error| format!("parse Luau carrier before patch: {error}"))?;
    let layout = parsed
        .header
        .luau_layout()
        .ok_or_else(|| "self-value carrier is not a Luau chunk".to_owned())?;
    if !(3..=7).contains(&layout.bytecode_version) {
        return Err(format!(
            "unsupported Luau self-value carrier bytecode version {}",
            layout.bytecode_version
        ));
    }
    if usize::from(target_reg) >= usize::from(parsed.main.common.frame.max_stack_size) {
        return Err(format!(
            "Luau self-value carrier target R{target_reg} exceeds max stack {}",
            parsed.main.common.frame.max_stack_size
        ));
    }
    if closure_pc.checked_add(2) != Some(save_pc) {
        return Err(format!(
            "Luau self-value carrier must keep closure/capture/save adjacent: closure={closure_pc}, save={save_pc}"
        ));
    }

    let instrs = &parsed.main.common.instructions;
    let closure = instrs.get(closure_pc).ok_or_else(|| {
        format!("Luau self-value carrier closure pc {closure_pc} is out of bounds")
    })?;
    let capture_pc = closure_pc + 1;
    let capture = instrs.get(capture_pc).ok_or_else(|| {
        format!("Luau self-value carrier capture pc {capture_pc} is out of bounds")
    })?;
    let save = instrs
        .get(save_pc)
        .ok_or_else(|| format!("Luau self-value carrier save pc {save_pc} is out of bounds"))?;
    let overwrite = instrs.get(overwrite_pc).ok_or_else(|| {
        format!("Luau self-value carrier overwrite pc {overwrite_pc} is out of bounds")
    })?;

    let closure_reg = match (&closure.opcode, &closure.operands) {
        (
            RawInstrOpcode::Luau(LuauOpcode::NewClosure | LuauOpcode::DupClosure),
            RawInstrOperands::Luau(LuauOperands::AD { a, .. }),
        ) => *a,
        _ => {
            return Err(format!(
                "Luau self-value carrier pc {closure_pc} is not NEWCLOSURE/DUPCLOSURE AD"
            ));
        }
    };
    match (&capture.opcode, &capture.operands) {
        (
            RawInstrOpcode::Luau(LuauOpcode::Capture),
            RawInstrOperands::Luau(LuauOperands::AB { a, b }),
        ) if *a == LuauCaptureKind::Val as u8 && *b == closure_reg => {}
        _ => {
            return Err(format!(
                "Luau self-value carrier pc {capture_pc} is not CAPTURE VAL R{closure_reg}"
            ));
        }
    }
    match (&save.opcode, &save.operands) {
        (
            RawInstrOpcode::Luau(LuauOpcode::Move),
            RawInstrOperands::Luau(LuauOperands::AB { b, .. }),
        ) if *b == closure_reg => {}
        _ => {
            return Err(format!(
                "Luau self-value carrier pc {save_pc} is not MOVE from R{closure_reg}"
            ));
        }
    }
    let overwritten_reg = match (&overwrite.opcode, &overwrite.operands) {
        (
            RawInstrOpcode::Luau(LuauOpcode::LoadN),
            RawInstrOperands::Luau(LuauOperands::AD { a, d }),
        ) if *d == 99 => *a,
        _ => {
            return Err(format!(
                "Luau self-value carrier pc {overwrite_pc} is not LOADN <reg> 99"
            ));
        }
    };
    if closure_reg == target_reg || overwritten_reg == target_reg {
        return Err(format!(
            "Luau self-value carrier already uses target R{target_reg}"
        ));
    }

    let closure_offset = closure.origin.span.offset;
    let capture_offset = capture.origin.span.offset;
    let save_offset = save.origin.span.offset;
    let overwrite_offset = overwrite.origin.span.offset;
    patch_luau_operand_byte(
        chunk,
        closure_offset + 1,
        closure_reg,
        target_reg,
        "closure A",
    )?;
    patch_luau_operand_byte(
        chunk,
        capture_offset + 2,
        closure_reg,
        target_reg,
        "capture B",
    )?;
    patch_luau_operand_byte(chunk, save_offset + 2, closure_reg, target_reg, "save B")?;
    patch_luau_operand_byte(
        chunk,
        overwrite_offset + 1,
        overwritten_reg,
        target_reg,
        "overwrite A",
    )?;

    let reparsed = parse_chunk_with_dialect(DecompileDialect::Luau, chunk, ParseOptions::default())
        .map_err(|error| format!("parse Luau carrier after patch: {error}"))?;
    let reparsed_instrs = &reparsed.main.common.instructions;
    match (
        reparsed_instrs.get(closure_pc).map(|instr| &instr.operands),
        reparsed_instrs.get(capture_pc).map(|instr| &instr.operands),
        reparsed_instrs.get(save_pc).map(|instr| &instr.operands),
        reparsed_instrs
            .get(overwrite_pc)
            .map(|instr| &instr.operands),
    ) {
        (
            Some(RawInstrOperands::Luau(LuauOperands::AD { a, .. })),
            Some(RawInstrOperands::Luau(LuauOperands::AB { b: capture, .. })),
            Some(RawInstrOperands::Luau(LuauOperands::AB { b: save, .. })),
            Some(RawInstrOperands::Luau(LuauOperands::AD { a: overwrite, .. })),
        ) if *a == target_reg
            && *capture == target_reg
            && *save == target_reg
            && *overwrite == target_reg =>
        {
            Ok(())
        }
        _ => Err("Luau self-value carrier operands disagree after patch".to_owned()),
    }
}

fn patch_luau_operand_byte(
    chunk: &mut [u8],
    offset: usize,
    expected: u8,
    replacement: u8,
    field: &str,
) -> Result<(), String> {
    let byte = chunk
        .get_mut(offset)
        .ok_or_else(|| format!("Luau self-value carrier {field} offset {offset} is truncated"))?;
    if *byte != expected {
        return Err(format!(
            "Luau self-value carrier {field} byte is {}, expected {expected}",
            *byte
        ));
    }
    *byte = replacement;
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
