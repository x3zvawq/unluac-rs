//! 这个文件保存 raw 模型里的 dialect 分派点和 accessor。
//!
//! 后续阶段需要保留 typed opcode、operand 和 extra，避免在 transformer 里重新猜测
//! 指令来自哪个协议版本；公共结构只在这里做一次 wrapper 分派。

use crate::parser::dialect::lua51::{Lua51InstrExtra, Lua51Opcode, Lua51Operands, Lua51ProtoExtra};
use crate::parser::dialect::lua52::{Lua52InstrExtra, Lua52Opcode, Lua52Operands, Lua52ProtoExtra};
use crate::parser::dialect::lua53::{Lua53InstrExtra, Lua53Opcode, Lua53Operands, Lua53ProtoExtra};
use crate::parser::dialect::lua54::{
    Lua54DebugExtra, Lua54InstrExtra, Lua54Opcode, Lua54Operands, Lua54ProtoExtra,
    Lua54UpvalueExtra,
};
use crate::parser::dialect::lua55::{
    Lua55DebugExtra, Lua55InstrExtra, Lua55Opcode, Lua55Operands, Lua55ProtoExtra,
    Lua55UpvalueExtra,
};
use crate::parser::dialect::luajit::{
    LuaJitConstPoolExtra, LuaJitDebugExtra, LuaJitHeaderExtra, LuaJitInstrExtra, LuaJitKgcEntry,
    LuaJitNumberConstEntry, LuaJitOpcode, LuaJitOperands, LuaJitProtoExtra, LuaJitUpvalueExtra,
};
use crate::parser::dialect::luau::{
    LuauConstEntry, LuauConstPoolExtra, LuauDebugExtra, LuauHeaderExtra, LuauInstrExtra,
    LuauOpcode, LuauOperands, LuauProtoExtra,
};

use super::{RawConstPool, RawInstr};

/// 各 dialect 自己的 opcode 命名空间。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum RawInstrOpcode {
    Lua51(Lua51Opcode),
    Lua52(Lua52Opcode),
    Lua53(Lua53Opcode),
    Lua54(Lua54Opcode),
    Lua55(Lua55Opcode),
    LuaJit(LuaJitOpcode),
    Luau(LuauOpcode),
}

/// 各 dialect 自己的 operand 形态。
#[derive(Debug, Clone, PartialEq)]
pub enum RawInstrOperands {
    Lua51(Lua51Operands),
    Lua52(Lua52Operands),
    Lua53(Lua53Operands),
    Lua54(Lua54Operands),
    Lua55(Lua55Operands),
    LuaJit(LuaJitOperands),
    Luau(LuauOperands),
}

/// 各 dialect 在 header 上附加的专属信息。
#[derive(Debug, Clone, PartialEq)]
pub enum DialectHeaderExtra {
    Lua51,
    Lua52,
    Lua53,
    Lua54,
    Lua55,
    LuaJit(LuaJitHeaderExtra),
    Luau(LuauHeaderExtra),
}

/// 各 dialect 在 proto 上附加的专属信息。
#[derive(Debug, Clone, PartialEq)]
pub enum DialectProtoExtra {
    Lua51(Lua51ProtoExtra),
    Lua52(Lua52ProtoExtra),
    Lua53(Lua53ProtoExtra),
    Lua54(Lua54ProtoExtra),
    Lua55(Lua55ProtoExtra),
    LuaJit(LuaJitProtoExtra),
    Luau(LuauProtoExtra),
}

/// 各 dialect 在常量池上附加的专属信息。
#[derive(Debug, Clone, PartialEq)]
pub enum DialectConstPoolExtra {
    Lua51,
    Lua52,
    Lua53,
    Lua54,
    Lua55,
    LuaJit(LuaJitConstPoolExtra),
    Luau(LuauConstPoolExtra),
}

/// 各 dialect 在 upvalue 信息上附加的专属内容。
#[derive(Debug, Clone, PartialEq)]
pub enum DialectUpvalueExtra {
    Lua51,
    Lua52,
    Lua53,
    Lua54(Lua54UpvalueExtra),
    Lua55(Lua55UpvalueExtra),
    LuaJit(LuaJitUpvalueExtra),
    Luau,
}

/// 各 dialect 在调试信息上附加的专属内容。
#[derive(Debug, Clone, PartialEq)]
pub enum DialectDebugExtra {
    Lua51,
    Lua52,
    Lua53,
    Lua54(Lua54DebugExtra),
    Lua55(Lua55DebugExtra),
    LuaJit(LuaJitDebugExtra),
    Luau(LuauDebugExtra),
}

/// 各 dialect 在指令上附加的专属内容。
#[derive(Debug, Clone, PartialEq)]
pub enum DialectInstrExtra {
    Lua51(Lua51InstrExtra),
    Lua52(Lua52InstrExtra),
    Lua53(Lua53InstrExtra),
    Lua54(Lua54InstrExtra),
    Lua55(Lua55InstrExtra),
    LuaJit(LuaJitInstrExtra),
    Luau(LuauInstrExtra),
}

macro_rules! define_dialect_ref_accessors {
    ($enum:ident {$($method:ident => $variant:ident($ty:ty)),+ $(,)?}) => {
        impl $enum {
            $(
                #[cfg_attr(not(feature = "decompile-debug"), allow(dead_code))]
                pub(crate) fn $method(&self) -> Option<&$ty> {
                    if let Self::$variant(extra) = self {
                        Some(extra)
                    } else {
                        None
                    }
                }
            )+
        }
    };
}

define_dialect_ref_accessors!(RawInstrOpcode {
    lua51 => Lua51(Lua51Opcode),
    lua52 => Lua52(Lua52Opcode),
    lua53 => Lua53(Lua53Opcode),
    lua54 => Lua54(Lua54Opcode),
    lua55 => Lua55(Lua55Opcode),
    luajit => LuaJit(LuaJitOpcode),
    luau => Luau(LuauOpcode),
});

define_dialect_ref_accessors!(RawInstrOperands {
    lua51 => Lua51(Lua51Operands),
    lua52 => Lua52(Lua52Operands),
    lua53 => Lua53(Lua53Operands),
    lua54 => Lua54(Lua54Operands),
    lua55 => Lua55(Lua55Operands),
    luajit => LuaJit(LuaJitOperands),
    luau => Luau(LuauOperands),
});

define_dialect_ref_accessors!(DialectHeaderExtra {
    luajit => LuaJit(LuaJitHeaderExtra),
});

define_dialect_ref_accessors!(DialectProtoExtra {
    lua51 => Lua51(Lua51ProtoExtra),
    lua52 => Lua52(Lua52ProtoExtra),
    lua53 => Lua53(Lua53ProtoExtra),
    lua54 => Lua54(Lua54ProtoExtra),
    lua55 => Lua55(Lua55ProtoExtra),
    luajit => LuaJit(LuaJitProtoExtra),
    luau => Luau(LuauProtoExtra),
});

define_dialect_ref_accessors!(DialectConstPoolExtra {
    luajit => LuaJit(LuaJitConstPoolExtra),
    luau => Luau(LuauConstPoolExtra),
});

define_dialect_ref_accessors!(DialectUpvalueExtra {
    lua54 => Lua54(Lua54UpvalueExtra),
});

define_dialect_ref_accessors!(DialectDebugExtra {
    lua54 => Lua54(Lua54DebugExtra),
    lua55 => Lua55(Lua55DebugExtra),
    luajit => LuaJit(LuaJitDebugExtra),
    luau => Luau(LuauDebugExtra),
});

define_dialect_ref_accessors!(DialectInstrExtra {
    lua51 => Lua51(Lua51InstrExtra),
    lua52 => Lua52(Lua52InstrExtra),
    lua53 => Lua53(Lua53InstrExtra),
    lua54 => Lua54(Lua54InstrExtra),
    lua55 => Lua55(Lua55InstrExtra),
    luajit => LuaJit(LuaJitInstrExtra),
    luau => Luau(LuauInstrExtra),
});

impl RawConstPool {
    pub(crate) fn luajit_kgc_entries(&self) -> Option<&[LuaJitKgcEntry]> {
        Some(self.extra.luajit()?.kgc_entries.as_slice())
    }

    pub(crate) fn luajit_knum_entries(&self) -> Option<&[LuaJitNumberConstEntry]> {
        Some(self.extra.luajit()?.knum_entries.as_slice())
    }

    pub(crate) fn luau_entries(&self) -> Option<&[LuauConstEntry]> {
        Some(self.extra.luau()?.entries.as_slice())
    }
}

impl RawInstr {
    pub(crate) fn pc(&self) -> u32 {
        match &self.extra {
            DialectInstrExtra::Lua51(extra) => extra.pc,
            DialectInstrExtra::Lua52(extra) => extra.pc,
            DialectInstrExtra::Lua53(extra) => extra.pc,
            DialectInstrExtra::Lua54(extra) => extra.pc,
            DialectInstrExtra::Lua55(extra) => extra.pc,
            DialectInstrExtra::LuaJit(extra) => extra.pc,
            DialectInstrExtra::Luau(extra) => extra.pc,
        }
    }

    pub(crate) fn word_len(&self) -> Option<u8> {
        match &self.extra {
            DialectInstrExtra::Lua51(extra) => Some(extra.word_len),
            DialectInstrExtra::Lua52(extra) => Some(extra.word_len),
            DialectInstrExtra::Lua53(extra) => Some(extra.word_len),
            DialectInstrExtra::Lua54(extra) => Some(extra.word_len),
            DialectInstrExtra::Lua55(extra) => Some(extra.word_len),
            DialectInstrExtra::LuaJit(_) => None,
            DialectInstrExtra::Luau(extra) => Some(extra.word_len),
        }
    }
}

macro_rules! define_raw_instr_views {
    ($($method:ident => ($opcode_method:ident, $operands_method:ident, $extra_method:ident, $opcode_ty:ty, $operands_ty:ty, $extra_ty:ty)),+ $(,)?) => {
        impl RawInstr {
            $(
                pub(crate) fn $method(&self) -> Option<($opcode_ty, &$operands_ty, $extra_ty)> {
                    Some((
                        *self.opcode.$opcode_method()?,
                        self.operands.$operands_method()?,
                        *self.extra.$extra_method()?,
                    ))
                }
            )+
        }
    };
}

define_raw_instr_views! {
    lua51 => (lua51, lua51, lua51, Lua51Opcode, Lua51Operands, Lua51InstrExtra),
    lua52 => (lua52, lua52, lua52, Lua52Opcode, Lua52Operands, Lua52InstrExtra),
    lua53 => (lua53, lua53, lua53, Lua53Opcode, Lua53Operands, Lua53InstrExtra),
    lua54 => (lua54, lua54, lua54, Lua54Opcode, Lua54Operands, Lua54InstrExtra),
    lua55 => (lua55, lua55, lua55, Lua55Opcode, Lua55Operands, Lua55InstrExtra),
    luajit => (luajit, luajit, luajit, LuaJitOpcode, LuaJitOperands, LuaJitInstrExtra),
    luau => (luau, luau, luau, LuauOpcode, LuauOperands, LuauInstrExtra),
}
