//! 这个文件定义 Luau 专属的 raw 类型。

use crate::parser::RawString;
use crate::parser::dialect::opcodes::define_opcode_kind_table;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum LuauOperandKind {
    None,
    A,
    AB,
    AC,
    ABC,
    AD,
    E,
}

define_opcode_kind_table!(
    opcode: LuauOpcode,
    operand_kind: LuauOperandKind,
    [
        (Nop, "NOP", None),
        (Break, "BREAK", None),
        (LoadNil, "LOADNIL", A),
        (LoadB, "LOADB", ABC),
        (LoadN, "LOADN", AD),
        (LoadK, "LOADK", AD),
        (Move, "MOVE", AB),
        (GetGlobal, "GETGLOBAL", ABC),
        (SetGlobal, "SETGLOBAL", ABC),
        (GetUpVal, "GETUPVAL", AB),
        (SetUpVal, "SETUPVAL", AB),
        (CloseUpVals, "CLOSEUPVALS", A),
        (GetImport, "GETIMPORT", AD),
        (GetTable, "GETTABLE", ABC),
        (SetTable, "SETTABLE", ABC),
        (GetTableKs, "GETTABLEKS", ABC),
        (SetTableKs, "SETTABLEKS", ABC),
        (GetTableN, "GETTABLEN", ABC),
        (SetTableN, "SETTABLEN", ABC),
        (NewClosure, "NEWCLOSURE", AD),
        (NameCall, "NAMECALL", ABC),
        (Call, "CALL", ABC),
        (Return, "RETURN", ABC),
        (Jump, "JUMP", AD),
        (JumpBack, "JUMPBACK", AD),
        (JumpIf, "JUMPIF", AD),
        (JumpIfNot, "JUMPIFNOT", AD),
        (JumpIfEq, "JUMPIFEQ", AD),
        (JumpIfLe, "JUMPIFLE", AD),
        (JumpIfLt, "JUMPIFLT", AD),
        (JumpIfNotEq, "JUMPIFNOTEQ", AD),
        (JumpIfNotLe, "JUMPIFNOTLE", AD),
        (JumpIfNotLt, "JUMPIFNOTLT", AD),
        (Add, "ADD", ABC),
        (Sub, "SUB", ABC),
        (Mul, "MUL", ABC),
        (Div, "DIV", ABC),
        (Mod, "MOD", ABC),
        (Pow, "POW", ABC),
        (AddK, "ADDK", ABC),
        (SubK, "SUBK", ABC),
        (MulK, "MULK", ABC),
        (DivK, "DIVK", ABC),
        (ModK, "MODK", ABC),
        (PowK, "POWK", ABC),
        (And, "AND", ABC),
        (Or, "OR", ABC),
        (AndK, "ANDK", ABC),
        (OrK, "ORK", ABC),
        (Concat, "CONCAT", ABC),
        (Not, "NOT", AB),
        (Minus, "MINUS", AB),
        (Length, "LENGTH", AB),
        (NewTable, "NEWTABLE", ABC),
        (DupTable, "DUPTABLE", AD),
        (SetList, "SETLIST", ABC),
        (ForNPrep, "FORNPREP", AD),
        (ForNLoop, "FORNLOOP", AD),
        (ForGLoop, "FORGLOOP", AD),
        (ForGPrepInext, "FORGPREP_INEXT", AD),
        (FastCall3, "FASTCALL3", ABC),
        (ForGPrepNext, "FORGPREP_NEXT", AD),
        (NativeCall, "NATIVECALL", None),
        (GetVarArgs, "GETVARARGS", AB),
        (DupClosure, "DUPCLOSURE", AD),
        (PrepVarArgs, "PREPVARARGS", A),
        (LoadKx, "LOADKX", ABC),
        (JumpX, "JUMPX", E),
        (FastCall, "FASTCALL", A),
        (Coverage, "COVERAGE", A),
        (Capture, "CAPTURE", ABC),
        (SubRK, "SUBRK", ABC),
        (DivRK, "DIVRK", ABC),
        (FastCall1, "FASTCALL1", A),
        (FastCall2, "FASTCALL2", ABC),
        (FastCall2K, "FASTCALL2K", ABC),
        (ForGPrep, "FORGPREP", AD),
        (JumpXEqKNil, "JUMPXEQKNIL", AD),
        (JumpXEqKB, "JUMPXEQKB", AD),
        (JumpXEqKN, "JUMPXEQKN", AD),
        (JumpXEqKS, "JUMPXEQKS", AD),
        (IDiv, "IDIV", ABC),
        (IDivK, "IDIVK", ABC),
    ]
);

impl LuauOpcode {
    pub const fn has_aux(self) -> bool {
        matches!(
            self,
            Self::GetGlobal
                | Self::SetGlobal
                | Self::GetImport
                | Self::GetTableKs
                | Self::SetTableKs
                | Self::NameCall
                | Self::JumpIfEq
                | Self::JumpIfLe
                | Self::JumpIfLt
                | Self::JumpIfNotEq
                | Self::JumpIfNotLe
                | Self::JumpIfNotLt
                | Self::NewTable
                | Self::SetList
                | Self::ForGLoop
                | Self::FastCall3
                | Self::FastCall2
                | Self::FastCall2K
                | Self::LoadKx
                | Self::JumpXEqKNil
                | Self::JumpXEqKB
                | Self::JumpXEqKN
                | Self::JumpXEqKS
        )
    }

    pub(crate) fn decode_operands(self, word: u32) -> LuauOperands {
        let a = ((word >> 8) & 0xff) as u8;
        let b = ((word >> 16) & 0xff) as u8;
        let c = ((word >> 24) & 0xff) as u8;
        match self.operand_kind() {
            LuauOperandKind::None => LuauOperands::None,
            LuauOperandKind::A => LuauOperands::A { a },
            LuauOperandKind::AB => LuauOperands::AB { a, b },
            LuauOperandKind::AC => LuauOperands::AC { a, c },
            LuauOperandKind::ABC => LuauOperands::ABC { a, b, c },
            LuauOperandKind::AD => LuauOperands::AD {
                a,
                d: (word as i32 >> 16) as i16,
            },
            LuauOperandKind::E => LuauOperands::E {
                e: (word as i32) >> 8,
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum LuauOperands {
    None,
    A { a: u8 },
    AB { a: u8, b: u8 },
    AC { a: u8, c: u8 },
    ABC { a: u8, b: u8, c: u8 },
    AD { a: u8, d: i16 },
    E { e: i32 },
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum LuauCaptureKind {
    Val = 0,
    Ref = 1,
    Upvalue = 2,
}

impl TryFrom<u8> for LuauCaptureKind {
    type Error = u8;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::Val),
            1 => Ok(Self::Ref),
            2 => Ok(Self::Upvalue),
            _ => Err(value),
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LuauTableConstEntry {
    pub key_const: u32,
    pub value_const: Option<u32>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LuauConstEntry {
    Literal {
        literal_index: usize,
    },
    Import {
        import_id: u32,
    },
    Table {
        key_consts: Vec<u32>,
    },
    TableWithConstants {
        entries: Vec<LuauTableConstEntry>,
    },
    Closure {
        proto_index: u32,
        child_proto_index: usize,
    },
    Vector {
        x: f32,
        y: f32,
        z: f32,
        w: f32,
    },
}

#[derive(Debug, Clone, Default, PartialEq)]
pub struct LuauHeaderExtra {
    pub userdata_type_names: Vec<Option<RawString>>,
}

#[derive(Debug, Clone, Default, PartialEq)]
pub struct LuauProtoExtra {
    pub flags: u8,
    pub type_info: Vec<u8>,
    pub debug_name: Option<RawString>,
}

#[derive(Debug, Clone, Default, PartialEq)]
pub struct LuauConstPoolExtra {
    pub entries: Vec<LuauConstEntry>,
}

#[derive(Debug, Clone, Default, PartialEq)]
pub struct LuauUpvalueExtra;

#[derive(Debug, Clone, Default, PartialEq)]
pub struct LuauDebugExtra {
    pub line_gap_log2: Option<u8>,
    pub local_regs: Vec<u8>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LuauInstrExtra {
    pub pc: u32,
    pub word_len: u8,
    pub aux: Option<u32>,
}
