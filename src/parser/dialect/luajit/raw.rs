//! 这个文件定义 LuaJIT 专属的 raw 类型。

use crate::parser::dialect::opcodes::define_opcode_kind_table;
use crate::parser::{RawLiteralConst, RawString};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum LuaJitOperandKind {
    A,
    AD,
    ABC,
}

define_opcode_kind_table!(
    opcode: LuaJitOpcode,
    operand_kind: LuaJitOperandKind,
    [
        (IsLt, "ISLT", ABC),
        (IsGe, "ISGE", ABC),
        (IsLe, "ISLE", ABC),
        (IsGt, "ISGT", ABC),
        (IsEqV, "ISEQV", ABC),
        (IsNeV, "ISNEV", ABC),
        (IsEqS, "ISEQS", ABC),
        (IsNeS, "ISNES", ABC),
        (IsEqN, "ISEQN", ABC),
        (IsNeN, "ISNEN", ABC),
        (IsEqP, "ISEQP", ABC),
        (IsNeP, "ISNEP", ABC),
        (IsTC, "ISTC", AD),
        (IsFC, "ISFC", AD),
        (IsT, "IST", AD),
        (IsF, "ISF", AD),
        (IsType, "ISTYPE", AD),
        (IsNum, "ISNUM", AD),
        (Mov, "MOV", AD),
        (Not, "NOT", AD),
        (Unm, "UNM", AD),
        (Len, "LEN", AD),
        (AddVN, "ADDVN", ABC),
        (SubVN, "SUBVN", ABC),
        (MulVN, "MULVN", ABC),
        (DivVN, "DIVVN", ABC),
        (ModVN, "MODVN", ABC),
        (AddNV, "ADDNV", ABC),
        (SubNV, "SUBNV", ABC),
        (MulNV, "MULNV", ABC),
        (DivNV, "DIVNV", ABC),
        (ModNV, "MODNV", ABC),
        (AddVV, "ADDVV", ABC),
        (SubVV, "SUBVV", ABC),
        (MulVV, "MULVV", ABC),
        (DivVV, "DIVVV", ABC),
        (ModVV, "MODVV", ABC),
        (Pow, "POW", ABC),
        (Cat, "CAT", ABC),
        (KStr, "KSTR", AD),
        (KCData, "KCDATA", AD),
        (KShort, "KSHORT", AD),
        (KNum, "KNUM", AD),
        (KPri, "KPRI", AD),
        (KNil, "KNIL", AD),
        (UGet, "UGET", AD),
        (USetV, "USETV", AD),
        (USetS, "USETS", AD),
        (USetN, "USETN", AD),
        (USetP, "USETP", AD),
        (UClose, "UCLO", AD),
        (FNew, "FNEW", AD),
        (TNew, "TNEW", AD),
        (TDup, "TDUP", AD),
        (GGet, "GGET", AD),
        (GSet, "GSET", AD),
        (TGetV, "TGETV", ABC),
        (TGetS, "TGETS", ABC),
        (TGetB, "TGETB", ABC),
        (TGetR, "TGETR", ABC),
        (TSetV, "TSETV", ABC),
        (TSetS, "TSETS", ABC),
        (TSetB, "TSETB", ABC),
        (TSetM, "TSETM", AD),
        (TSetR, "TSETR", ABC),
        (CallM, "CALLM", ABC),
        (Call, "CALL", ABC),
        (CallMT, "CALLMT", AD),
        (CallT, "CALLT", AD),
        (IterC, "ITERC", ABC),
        (IterN, "ITERN", ABC),
        (VArg, "VARG", ABC),
        (IsNext, "ISNEXT", AD),
        (RetM, "RETM", AD),
        (Ret, "RET", AD),
        (Ret0, "RET0", AD),
        (Ret1, "RET1", AD),
        (ForI, "FORI", AD),
        (JForI, "JFORI", AD),
        (ForL, "FORL", AD),
        (IForL, "IFORL", AD),
        (JForL, "JFORL", AD),
        (IterL, "ITERL", AD),
        (IIterL, "IITERL", AD),
        (JIterL, "JITERL", AD),
        (Loop, "LOOP", AD),
        (ILoop, "ILOOP", AD),
        (JLoop, "JLOOP", AD),
        (Jmp, "JMP", AD),
        (FuncF, "FUNCF", A),
        (IFuncF, "IFUNCF", A),
        (JFuncF, "JFUNCF", AD),
        (FuncV, "FUNCV", A),
        (IFuncV, "IFUNCV", A),
        (JFuncV, "JFUNCV", AD),
        (FuncC, "FUNCC", A),
        (FuncCW, "FUNCCW", A),
    ]
);

impl LuaJitOpcode {
    pub(crate) fn decode_operands(self, word: u32) -> LuaJitOperands {
        let a = ((word >> 8) & 0xff) as u8;
        let d = ((word >> 16) & 0xffff) as u16;
        let c = ((word >> 16) & 0xff) as u8;
        let b = ((word >> 24) & 0xff) as u8;
        match self.operand_kind() {
            LuaJitOperandKind::A => LuaJitOperands::A { a },
            LuaJitOperandKind::AD => LuaJitOperands::AD { a, d },
            LuaJitOperandKind::ABC => LuaJitOperands::ABC { a, b, c },
        }
    }
}

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
