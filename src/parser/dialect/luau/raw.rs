//! 这个文件定义 Luau 专属的 raw 类型。

use crate::parser::RawString;

macro_rules! define_luau_opcodes {
    ($($name:ident),+ $(,)?) => {
        #[derive(Debug, Clone, Copy, Eq, PartialEq)]
        #[repr(u8)]
        pub enum LuauOpcode {
            $( $name, )+
        }

        impl TryFrom<u8> for LuauOpcode {
            type Error = u8;

            fn try_from(value: u8) -> Result<Self, Self::Error> {
                match value {
                    $( x if x == LuauOpcode::$name as u8 => Ok(LuauOpcode::$name), )+
                    _ => Err(value),
                }
            }
        }
    };
}

define_luau_opcodes!(
    Nop,
    Break,
    LoadNil,
    LoadB,
    LoadN,
    LoadK,
    Move,
    GetGlobal,
    SetGlobal,
    GetUpVal,
    SetUpVal,
    CloseUpVals,
    GetImport,
    GetTable,
    SetTable,
    GetTableKs,
    SetTableKs,
    GetTableN,
    SetTableN,
    NewClosure,
    NameCall,
    Call,
    Return,
    Jump,
    JumpBack,
    JumpIf,
    JumpIfNot,
    JumpIfEq,
    JumpIfLe,
    JumpIfLt,
    JumpIfNotEq,
    JumpIfNotLe,
    JumpIfNotLt,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    AddK,
    SubK,
    MulK,
    DivK,
    ModK,
    PowK,
    And,
    Or,
    AndK,
    OrK,
    Concat,
    Not,
    Minus,
    Length,
    NewTable,
    DupTable,
    SetList,
    ForNPrep,
    ForNLoop,
    ForGLoop,
    ForGPrepInext,
    FastCall3,
    ForGPrepNext,
    NativeCall,
    GetVarArgs,
    DupClosure,
    PrepVarArgs,
    LoadKx,
    JumpX,
    FastCall,
    Coverage,
    Capture,
    SubRK,
    DivRK,
    FastCall1,
    FastCall2,
    FastCall2K,
    ForGPrep,
    JumpXEqKNil,
    JumpXEqKB,
    JumpXEqKN,
    JumpXEqKS,
    IDiv,
    IDivK,
);

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

impl LuauOpcode {
    pub const fn operand_kind(self) -> LuauOperandKind {
        match self {
            Self::Nop | Self::Break => LuauOperandKind::None,
            Self::LoadNil
            | Self::CloseUpVals
            | Self::PrepVarArgs
            | Self::FastCall
            | Self::FastCall1
            | Self::Coverage => LuauOperandKind::A,
            Self::Move
            | Self::GetUpVal
            | Self::SetUpVal
            | Self::Not
            | Self::Minus
            | Self::Length
            | Self::GetVarArgs => LuauOperandKind::AB,
            Self::GetGlobal
            | Self::SetGlobal
            | Self::GetTableKs
            | Self::SetTableKs
            | Self::NameCall
            | Self::LoadB
            | Self::LoadKx
            | Self::FastCall3
            | Self::FastCall2
            | Self::FastCall2K => LuauOperandKind::ABC,
            Self::LoadN
            | Self::LoadK
            | Self::GetImport
            | Self::NewClosure
            | Self::Jump
            | Self::JumpBack
            | Self::JumpIf
            | Self::JumpIfNot
            | Self::JumpIfEq
            | Self::JumpIfLe
            | Self::JumpIfLt
            | Self::JumpIfNotEq
            | Self::JumpIfNotLe
            | Self::JumpIfNotLt
            | Self::DupTable
            | Self::ForNPrep
            | Self::ForNLoop
            | Self::ForGLoop
            | Self::ForGPrepInext
            | Self::ForGPrepNext
            | Self::DupClosure
            | Self::JumpXEqKNil
            | Self::JumpXEqKB
            | Self::JumpXEqKN
            | Self::JumpXEqKS
            | Self::ForGPrep => LuauOperandKind::AD,
            Self::Call
            | Self::Return
            | Self::GetTable
            | Self::SetTable
            | Self::GetTableN
            | Self::SetTableN
            | Self::Add
            | Self::Sub
            | Self::Mul
            | Self::Div
            | Self::Mod
            | Self::Pow
            | Self::AddK
            | Self::SubK
            | Self::MulK
            | Self::DivK
            | Self::ModK
            | Self::PowK
            | Self::And
            | Self::Or
            | Self::AndK
            | Self::OrK
            | Self::Concat
            | Self::NewTable
            | Self::SetList
            | Self::Capture
            | Self::SubRK
            | Self::DivRK
            | Self::IDiv
            | Self::IDivK => LuauOperandKind::ABC,
            Self::JumpX => LuauOperandKind::E,
            Self::NativeCall => LuauOperandKind::None,
        }
    }

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
    Literal { literal_index: usize },
    Import { import_id: u32 },
    Table { key_consts: Vec<u32> },
    TableWithConstants { entries: Vec<LuauTableConstEntry> },
    Closure { proto_index: u32 },
    Vector { x: f32, y: f32, z: f32, w: f32 },
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
    pub child_proto_ids: Vec<u32>,
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
