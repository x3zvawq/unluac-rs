//! 这个模块承载 PUC-Lua 5.x 各版本 parser 共用的轻量 helper。
//!
//! 这里刻意只放“编码布局、公共常量、位域拆解”这类稳定事实，不把 5.1/5.2/5.3
//! 的 proto 布局和 opcode 规则硬揉成一个大框架；这样既能减少重复，又不会把
//! 版本差异藏进过强抽象里。

use crate::parser::Endianness;

pub(crate) const LUA_SIGNATURE: &[u8; 4] = b"\x1bLua";
pub(crate) const LUA52_LUAC_TAIL: &[u8; 6] = b"\x19\x93\r\n\x1a\n";
pub(crate) const MAXARG_SBX_18: i32 = ((1 << 18) - 1) >> 1;

/// PUC-Lua chunk header 里显式声明的基础布局。
#[derive(Debug, Clone, Copy)]
pub(crate) struct PucLuaLayout {
    pub(crate) endianness: Endianness,
    pub(crate) integer_size: u8,
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
