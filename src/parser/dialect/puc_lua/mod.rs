//! 这个模块承载 PUC-Lua 5.x 各版本 parser 共用的轻量 helper。
//!
//! 这里刻意只放“编码布局、公共常量、位域拆解”这类稳定事实，不把 5.1/5.2/5.3
//! 的 proto 布局和 opcode 规则硬揉成一个大框架；这样既能减少重复，又不会把
//! 版本差异藏进过强抽象里。

use crate::parser::Endianness;

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
pub(crate) const MAXARG_SBX_18: i32 = ((1 << 18) - 1) >> 1;
pub(crate) const MAXARG_SBX_17: i32 = ((1 << 17) - 1) >> 1;
pub(crate) const MAXARG_SJ_25: i32 = ((1 << 25) - 1) >> 1;
pub(crate) const OFFSET_SC_8: i16 = (((1 << 8) - 1) >> 1) as i16;

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

/// PUC-Lua 指令字公共位域拆解结果。
#[derive(Debug, Clone, Copy)]
pub(crate) struct DecodedInstructionFields {
    pub(crate) opcode: u8,
    pub(crate) a: u8,
    pub(crate) b: u16,
    pub(crate) c: u16,
    pub(crate) bx: u32,
    pub(crate) sbx: i32,
    pub(crate) ax: u32,
}

/// Lua 5.4 指令字公共位域拆解结果。
#[derive(Debug, Clone, Copy)]
pub(crate) struct DecodedInstructionFields54 {
    pub(crate) opcode: u8,
    pub(crate) a: u8,
    pub(crate) k: bool,
    pub(crate) b: u8,
    pub(crate) c: u8,
    pub(crate) bx: u32,
    pub(crate) sbx: i32,
    pub(crate) ax: u32,
    pub(crate) sj: i32,
    pub(crate) sb: i16,
    pub(crate) sc: i16,
}

/// Lua 5.5 指令字公共位域拆解结果。
#[derive(Debug, Clone, Copy)]
pub(crate) struct DecodedInstructionFields55 {
    pub(crate) opcode: u8,
    pub(crate) a: u8,
    pub(crate) k: bool,
    pub(crate) b: u8,
    pub(crate) c: u8,
    pub(crate) bx: u32,
    pub(crate) sbx: i32,
    pub(crate) ax: u32,
    pub(crate) sj: i32,
    pub(crate) sb: i16,
    pub(crate) sc: i16,
    pub(crate) vb: u8,
    pub(crate) vc: u16,
}

/// 按 PUC-Lua 5.x 共享编码格式拆开一条 32-bit 指令字。
pub(crate) fn decode_instruction_word(word: u32) -> DecodedInstructionFields {
    let opcode = (word & 0x3f) as u8;
    let a = ((word >> 6) & 0xff) as u8;
    let c = ((word >> 14) & 0x1ff) as u16;
    let b = ((word >> 23) & 0x1ff) as u16;
    let bx = (word >> 14) & 0x3ffff;
    let sbx = bx as i32 - MAXARG_SBX_18;
    let ax = word >> 6;

    DecodedInstructionFields {
        opcode,
        a,
        b,
        c,
        bx,
        sbx,
        ax,
    }
}

/// 按 Lua 5.4 的 7-bit opcode 编码拆开一条 32-bit 指令字。
pub(crate) fn decode_instruction_word_54(word: u32) -> DecodedInstructionFields54 {
    let opcode = (word & 0x7f) as u8;
    let a = ((word >> 7) & 0xff) as u8;
    let k = ((word >> 15) & 0x1) != 0;
    let b = ((word >> 16) & 0xff) as u8;
    let c = ((word >> 24) & 0xff) as u8;
    let bx = (word >> 15) & 0x1ffff;
    let sbx = bx as i32 - MAXARG_SBX_17;
    let ax = word >> 7;
    let sj_raw = (word >> 7) & 0x1ffffff;
    let sj = sj_raw as i32 - MAXARG_SJ_25;
    let sb = i16::from(b) - OFFSET_SC_8;
    let sc = i16::from(c) - OFFSET_SC_8;

    DecodedInstructionFields54 {
        opcode,
        a,
        k,
        b,
        c,
        bx,
        sbx,
        ax,
        sj,
        sb,
        sc,
    }
}

/// 按 Lua 5.5 的 7-bit opcode 编码拆开一条 32-bit 指令字。
pub(crate) fn decode_instruction_word_55(word: u32) -> DecodedInstructionFields55 {
    let opcode = (word & 0x7f) as u8;
    let a = ((word >> 7) & 0xff) as u8;
    let k = ((word >> 15) & 0x1) != 0;
    let b = ((word >> 16) & 0xff) as u8;
    let c = ((word >> 24) & 0xff) as u8;
    let bx = (word >> 15) & 0x1ffff;
    let sbx = bx as i32 - MAXARG_SBX_17;
    let ax = word >> 7;
    let sj_raw = (word >> 7) & 0x1ffffff;
    let sj = sj_raw as i32 - MAXARG_SJ_25;
    let sb = i16::from(b) - OFFSET_SC_8;
    let sc = i16::from(c) - OFFSET_SC_8;
    let vb = ((word >> 16) & 0x3f) as u8;
    let vc = ((word >> 22) & 0x03ff) as u16;

    DecodedInstructionFields55 {
        opcode,
        a,
        k,
        b,
        c,
        bx,
        sbx,
        ax,
        sj,
        sb,
        sc,
        vb,
        vc,
    }
}
