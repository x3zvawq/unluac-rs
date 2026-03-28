//! 这个文件定义 LuaJIT 专属的 raw 类型。

use crate::parser::{RawLiteralConst, RawString};

macro_rules! define_luajit_opcodes {
    ($(($name:ident, $kind:ident)),+ $(,)?) => {
        #[derive(Debug, Clone, Copy, Eq, PartialEq)]
        #[repr(u8)]
        pub enum LuaJitOpcode {
            $( $name, )+
        }

        impl LuaJitOpcode {
            pub const fn operand_kind(self) -> LuaJitOperandKind {
                match self {
                    $( Self::$name => LuaJitOperandKind::$kind, )+
                }
            }
        }

        impl TryFrom<u8> for LuaJitOpcode {
            type Error = u8;

            fn try_from(value: u8) -> Result<Self, Self::Error> {
                match value {
                    $( x if x == LuaJitOpcode::$name as u8 => Ok(LuaJitOpcode::$name), )+
                    _ => Err(value),
                }
            }
        }
    };
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum LuaJitOperandKind {
    A,
    AD,
    ABC,
}

define_luajit_opcodes!(
    (IsLt, ABC),
    (IsGe, ABC),
    (IsLe, ABC),
    (IsGt, ABC),
    (IsEqV, ABC),
    (IsNeV, ABC),
    (IsEqS, ABC),
    (IsNeS, ABC),
    (IsEqN, ABC),
    (IsNeN, ABC),
    (IsEqP, ABC),
    (IsNeP, ABC),
    (IsTC, AD),
    (IsFC, AD),
    (IsT, AD),
    (IsF, AD),
    (IsType, AD),
    (IsNum, AD),
    (Mov, AD),
    (Not, AD),
    (Unm, AD),
    (Len, AD),
    (AddVN, ABC),
    (SubVN, ABC),
    (MulVN, ABC),
    (DivVN, ABC),
    (ModVN, ABC),
    (AddNV, ABC),
    (SubNV, ABC),
    (MulNV, ABC),
    (DivNV, ABC),
    (ModNV, ABC),
    (AddVV, ABC),
    (SubVV, ABC),
    (MulVV, ABC),
    (DivVV, ABC),
    (ModVV, ABC),
    (Pow, ABC),
    (Cat, ABC),
    (KStr, AD),
    (KCData, AD),
    (KShort, AD),
    (KNum, AD),
    (KPri, AD),
    (KNil, AD),
    (UGet, AD),
    (USetV, AD),
    (USetS, AD),
    (USetN, AD),
    (USetP, AD),
    (UClose, AD),
    (FNew, AD),
    (TNew, AD),
    (TDup, AD),
    (GGet, AD),
    (GSet, AD),
    (TGetV, ABC),
    (TGetS, ABC),
    (TGetB, ABC),
    (TGetR, ABC),
    (TSetV, ABC),
    (TSetS, ABC),
    (TSetB, ABC),
    (TSetM, AD),
    (TSetR, ABC),
    (CallM, ABC),
    (Call, ABC),
    (CallMT, AD),
    (CallT, AD),
    (IterC, ABC),
    (IterN, ABC),
    (VArg, ABC),
    (IsNext, AD),
    (RetM, AD),
    (Ret, AD),
    (Ret0, AD),
    (Ret1, AD),
    (ForI, AD),
    (JForI, AD),
    (ForL, AD),
    (IForL, AD),
    (JForL, AD),
    (IterL, AD),
    (IIterL, AD),
    (JIterL, AD),
    (Loop, AD),
    (ILoop, AD),
    (JLoop, AD),
    (Jmp, AD),
    (FuncF, A),
    (IFuncF, A),
    (JFuncF, AD),
    (FuncV, A),
    (IFuncV, A),
    (JFuncV, AD),
    (FuncC, A),
    (FuncCW, A),
);

#[derive(Debug, Clone, PartialEq)]
pub enum LuaJitOperands {
    A { a: u8 },
    AD { a: u8, d: u16 },
    ABC { a: u8, b: u8, c: u8 },
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct LuaJitHeaderExtra {
    pub chunk_name: Option<RawString>,
    pub stripped: bool,
    pub uses_ffi: bool,
    pub fr2: bool,
    pub big_endian: bool,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct LuaJitProtoExtra {
    pub flags: u8,
    pub first_line: Option<u32>,
    pub line_count: Option<u32>,
    pub debug_size: u32,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LuaJitKgcEntry {
    Child {
        child_proto_index: usize,
    },
    Table(LuaJitTableConst),
    Literal {
        value: RawLiteralConst,
        literal_index: usize,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum LuaJitNumberConstEntry {
    Integer { value: i64, literal_index: usize },
    Number { value: f64, literal_index: usize },
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct LuaJitConstPoolExtra {
    pub kgc_entries: Vec<LuaJitKgcEntry>,
    pub knum_entries: Vec<LuaJitNumberConstEntry>,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct LuaJitUpvalueExtra {
    pub immutable: Vec<bool>,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct LuaJitDebugExtra {
    pub stripped: bool,
    pub debug_size: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub struct LuaJitInstrExtra {
    pub pc: u32,
    pub raw_word: u32,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LuaJitTableConst {
    pub array: Vec<LuaJitTableLiteral>,
    pub hash: Vec<LuaJitTableRecord>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LuaJitTableRecord {
    pub key: LuaJitTableLiteral,
    pub value: LuaJitTableLiteral,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LuaJitTableLiteral {
    pub value: RawLiteralConst,
    pub literal_index: usize,
}
