//! 这个模块承载 PUC-Lua 5.x lowering 之间共享的轻量 helper。
//!
//! 这些 helper 只负责 RK/寄存器区间/调用包这类稳定编码事实，避免 5.1 和 5.2
//! 各自复制一套样板；真正的 opcode 语义和模式识别仍留在版本目录里实现。

use crate::transformer::{Reg, RegRange, ResultPack, ValuePack};

pub(crate) const BITRK: u16 = 1 << 8;
pub(crate) const LFIELDS_PER_FLUSH: u32 = 50;

pub(crate) fn reg_from_u8(index: u8) -> Reg {
    Reg(index as usize)
}

pub(crate) fn reg_from_u16(index: u16) -> Reg {
    Reg(index as usize)
}

pub(crate) fn is_k(value: u16) -> bool {
    value & BITRK != 0
}

pub(crate) fn index_k(value: u16) -> usize {
    usize::from(value & !BITRK)
}

pub(crate) fn range_len_inclusive(start: usize, end: usize) -> usize {
    end.saturating_sub(start) + 1
}

pub(crate) fn call_args_pack(a: u8, b: u16) -> ValuePack {
    if b == 0 {
        ValuePack::Open(Reg(usize::from(a) + 1))
    } else {
        ValuePack::Fixed(RegRange::new(Reg(usize::from(a) + 1), usize::from(b - 1)))
    }
}

pub(crate) fn call_result_pack(a: u8, c: u16) -> ResultPack {
    match c {
        0 => ResultPack::Open(reg_from_u8(a)),
        1 => ResultPack::Ignore,
        _ => ResultPack::Fixed(RegRange::new(reg_from_u8(a), usize::from(c - 1))),
    }
}

pub(crate) fn return_pack(a: u8, b: u16) -> ValuePack {
    if b == 0 {
        ValuePack::Open(reg_from_u8(a))
    } else {
        ValuePack::Fixed(RegRange::new(reg_from_u8(a), usize::from(b - 1)))
    }
}
