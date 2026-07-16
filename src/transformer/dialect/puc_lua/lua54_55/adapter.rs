//! 这个文件把 Lua 5.4/5.5 的 typed raw 指令穷尽映射到共享 lowering 视图。
//!
//! parser 继续保留各版本独立的 opcode、operand kind 与位宽；这里只统一两个协议
//! 已确认等价的语义名。版本专属 opcode 和 operand 外形必须通过穷尽 match 显式进入
//! 共享视图，不能按字符串或数值位置猜测。

use crate::parser::{Lua54Opcode, Lua54Operands, Lua55Opcode, Lua55Operands, RawInstr};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) enum FamilyDialect {
    Lua54,
    Lua55,
}

impl FamilyDialect {
    pub(super) fn extraarg_scale(self) -> u32 {
        match self {
            Self::Lua54 => 1_u32 << 8,
            Self::Lua55 => 1_u32 << 10,
        }
    }

    pub(super) fn numeric_for_binding_offset(self) -> usize {
        match self {
            Self::Lua54 => 3,
            Self::Lua55 => 2,
        }
    }

    pub(super) fn generic_for_binding_offset(self) -> usize {
        match self {
            Self::Lua54 => 4,
            Self::Lua55 => 3,
        }
    }

    pub(super) fn generic_for_control_offset(self) -> usize {
        match self {
            Self::Lua54 => 2,
            Self::Lua55 => 3,
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(super) enum FamilyOpcode {
    Move,
    LoadI,
    LoadF,
    LoadK,
    LoadKx,
    LoadFalse,
    LFalseSkip,
    LoadTrue,
    LoadNil,
    GetUpVal,
    SetUpVal,
    GetTabUp,
    GetTable,
    GetI,
    GetField,
    SetTabUp,
    SetTable,
    SetI,
    SetField,
    NewTable,
    Self_,
    AddI,
    AddK,
    SubK,
    MulK,
    ModK,
    PowK,
    DivK,
    IdivK,
    BandK,
    BorK,
    BxorK,
    ShlI,
    ShrI,
    Add,
    Sub,
    Mul,
    Mod,
    Pow,
    Div,
    Idiv,
    Band,
    Bor,
    Bxor,
    Shl,
    Shr,
    MMBin,
    MMBinI,
    MMBinK,
    Unm,
    BNot,
    Not,
    Len,
    Concat,
    Close,
    Tbc,
    Jmp,
    Eq,
    Lt,
    Le,
    EqK,
    EqI,
    LtI,
    LeI,
    GtI,
    GeI,
    Test,
    TestSet,
    Call,
    TailCall,
    Return,
    Return0,
    Return1,
    ForLoop,
    ForPrep,
    TForPrep,
    TForCall,
    TForLoop,
    SetList,
    Closure,
    VarArg,
    GetVarg,
    ErrNNil,
    VarArgPrep,
    ExtraArg,
}

impl FamilyOpcode {
    pub(super) fn label(self) -> &'static str {
        match self {
            Self::Move => "MOVE",
            Self::LoadI => "LOADI",
            Self::LoadF => "LOADF",
            Self::LoadK => "LOADK",
            Self::LoadKx => "LOADKX",
            Self::LoadFalse => "LOADFALSE",
            Self::LFalseSkip => "LFALSESKIP",
            Self::LoadTrue => "LOADTRUE",
            Self::LoadNil => "LOADNIL",
            Self::GetUpVal => "GETUPVAL",
            Self::SetUpVal => "SETUPVAL",
            Self::GetTabUp => "GETTABUP",
            Self::GetTable => "GETTABLE",
            Self::GetI => "GETI",
            Self::GetField => "GETFIELD",
            Self::SetTabUp => "SETTABUP",
            Self::SetTable => "SETTABLE",
            Self::SetI => "SETI",
            Self::SetField => "SETFIELD",
            Self::NewTable => "NEWTABLE",
            Self::Self_ => "SELF",
            Self::AddI => "ADDI",
            Self::AddK => "ADDK",
            Self::SubK => "SUBK",
            Self::MulK => "MULK",
            Self::ModK => "MODK",
            Self::PowK => "POWK",
            Self::DivK => "DIVK",
            Self::IdivK => "IDIVK",
            Self::BandK => "BANDK",
            Self::BorK => "BORK",
            Self::BxorK => "BXORK",
            Self::ShlI => "SHLI",
            Self::ShrI => "SHRI",
            Self::Add => "ADD",
            Self::Sub => "SUB",
            Self::Mul => "MUL",
            Self::Mod => "MOD",
            Self::Pow => "POW",
            Self::Div => "DIV",
            Self::Idiv => "IDIV",
            Self::Band => "BAND",
            Self::Bor => "BOR",
            Self::Bxor => "BXOR",
            Self::Shl => "SHL",
            Self::Shr => "SHR",
            Self::MMBin => "MMBIN",
            Self::MMBinI => "MMBINI",
            Self::MMBinK => "MMBINK",
            Self::Unm => "UNM",
            Self::BNot => "BNOT",
            Self::Not => "NOT",
            Self::Len => "LEN",
            Self::Concat => "CONCAT",
            Self::Close => "CLOSE",
            Self::Tbc => "TBC",
            Self::Jmp => "JMP",
            Self::Eq => "EQ",
            Self::Lt => "LT",
            Self::Le => "LE",
            Self::EqK => "EQK",
            Self::EqI => "EQI",
            Self::LtI => "LTI",
            Self::LeI => "LEI",
            Self::GtI => "GTI",
            Self::GeI => "GEI",
            Self::Test => "TEST",
            Self::TestSet => "TESTSET",
            Self::Call => "CALL",
            Self::TailCall => "TAILCALL",
            Self::Return => "RETURN",
            Self::Return0 => "RETURN0",
            Self::Return1 => "RETURN1",
            Self::ForLoop => "FORLOOP",
            Self::ForPrep => "FORPREP",
            Self::TForPrep => "TFORPREP",
            Self::TForCall => "TFORCALL",
            Self::TForLoop => "TFORLOOP",
            Self::SetList => "SETLIST",
            Self::Closure => "CLOSURE",
            Self::VarArg => "VARARG",
            Self::GetVarg => "GETVARG",
            Self::ErrNNil => "ERRNNIL",
            Self::VarArgPrep => "VARARGPREP",
            Self::ExtraArg => "EXTRAARG",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(super) enum FamilyOperands {
    None,
    A { a: u8 },
    Ak { a: u8, k: bool },
    AB { a: u8, b: u8 },
    AC { a: u8, c: u8 },
    Abc { a: u8, b: u8, c: u8 },
    ABk { a: u8, b: u8, k: bool },
    ABCk { a: u8, b: u8, c: u8, k: bool },
    ABx { a: u8, bx: u32 },
    AsBx { a: u8, sbx: i32 },
    AsJ { sj: i32 },
    Ax { ax: u32 },
    ABsCk { a: u8, b: u8, sc: i16, k: bool },
    AsBCk { a: u8, sb: i16, c: u8, k: bool },
    AvBCk { a: u8, vb: u8, vc: u16, k: bool },
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(super) struct DecodedInstr {
    pub(super) opcode: FamilyOpcode,
    pub(super) operands: FamilyOperands,
    pub(super) pc: u32,
    pub(super) extra_arg: Option<u32>,
}

impl From<Lua54Opcode> for FamilyOpcode {
    fn from(opcode: Lua54Opcode) -> Self {
        match opcode {
            Lua54Opcode::Move => Self::Move,
            Lua54Opcode::LoadI => Self::LoadI,
            Lua54Opcode::LoadF => Self::LoadF,
            Lua54Opcode::LoadK => Self::LoadK,
            Lua54Opcode::LoadKx => Self::LoadKx,
            Lua54Opcode::LoadFalse => Self::LoadFalse,
            Lua54Opcode::LFalseSkip => Self::LFalseSkip,
            Lua54Opcode::LoadTrue => Self::LoadTrue,
            Lua54Opcode::LoadNil => Self::LoadNil,
            Lua54Opcode::GetUpVal => Self::GetUpVal,
            Lua54Opcode::SetUpVal => Self::SetUpVal,
            Lua54Opcode::GetTabUp => Self::GetTabUp,
            Lua54Opcode::GetTable => Self::GetTable,
            Lua54Opcode::GetI => Self::GetI,
            Lua54Opcode::GetField => Self::GetField,
            Lua54Opcode::SetTabUp => Self::SetTabUp,
            Lua54Opcode::SetTable => Self::SetTable,
            Lua54Opcode::SetI => Self::SetI,
            Lua54Opcode::SetField => Self::SetField,
            Lua54Opcode::NewTable => Self::NewTable,
            Lua54Opcode::Self_ => Self::Self_,
            Lua54Opcode::AddI => Self::AddI,
            Lua54Opcode::AddK => Self::AddK,
            Lua54Opcode::SubK => Self::SubK,
            Lua54Opcode::MulK => Self::MulK,
            Lua54Opcode::ModK => Self::ModK,
            Lua54Opcode::PowK => Self::PowK,
            Lua54Opcode::DivK => Self::DivK,
            Lua54Opcode::IdivK => Self::IdivK,
            Lua54Opcode::BandK => Self::BandK,
            Lua54Opcode::BorK => Self::BorK,
            Lua54Opcode::BxorK => Self::BxorK,
            Lua54Opcode::ShlI => Self::ShlI,
            Lua54Opcode::ShrI => Self::ShrI,
            Lua54Opcode::Add => Self::Add,
            Lua54Opcode::Sub => Self::Sub,
            Lua54Opcode::Mul => Self::Mul,
            Lua54Opcode::Mod => Self::Mod,
            Lua54Opcode::Pow => Self::Pow,
            Lua54Opcode::Div => Self::Div,
            Lua54Opcode::Idiv => Self::Idiv,
            Lua54Opcode::Band => Self::Band,
            Lua54Opcode::Bor => Self::Bor,
            Lua54Opcode::Bxor => Self::Bxor,
            Lua54Opcode::Shl => Self::Shl,
            Lua54Opcode::Shr => Self::Shr,
            Lua54Opcode::MMBin => Self::MMBin,
            Lua54Opcode::MMBinI => Self::MMBinI,
            Lua54Opcode::MMBinK => Self::MMBinK,
            Lua54Opcode::Unm => Self::Unm,
            Lua54Opcode::BNot => Self::BNot,
            Lua54Opcode::Not => Self::Not,
            Lua54Opcode::Len => Self::Len,
            Lua54Opcode::Concat => Self::Concat,
            Lua54Opcode::Close => Self::Close,
            Lua54Opcode::Tbc => Self::Tbc,
            Lua54Opcode::Jmp => Self::Jmp,
            Lua54Opcode::Eq => Self::Eq,
            Lua54Opcode::Lt => Self::Lt,
            Lua54Opcode::Le => Self::Le,
            Lua54Opcode::EqK => Self::EqK,
            Lua54Opcode::EqI => Self::EqI,
            Lua54Opcode::LtI => Self::LtI,
            Lua54Opcode::LeI => Self::LeI,
            Lua54Opcode::GtI => Self::GtI,
            Lua54Opcode::GeI => Self::GeI,
            Lua54Opcode::Test => Self::Test,
            Lua54Opcode::TestSet => Self::TestSet,
            Lua54Opcode::Call => Self::Call,
            Lua54Opcode::TailCall => Self::TailCall,
            Lua54Opcode::Return => Self::Return,
            Lua54Opcode::Return0 => Self::Return0,
            Lua54Opcode::Return1 => Self::Return1,
            Lua54Opcode::ForLoop => Self::ForLoop,
            Lua54Opcode::ForPrep => Self::ForPrep,
            Lua54Opcode::TForPrep => Self::TForPrep,
            Lua54Opcode::TForCall => Self::TForCall,
            Lua54Opcode::TForLoop => Self::TForLoop,
            Lua54Opcode::SetList => Self::SetList,
            Lua54Opcode::Closure => Self::Closure,
            Lua54Opcode::VarArg => Self::VarArg,
            Lua54Opcode::VarArgPrep => Self::VarArgPrep,
            Lua54Opcode::ExtraArg => Self::ExtraArg,
        }
    }
}

impl From<Lua55Opcode> for FamilyOpcode {
    fn from(opcode: Lua55Opcode) -> Self {
        match opcode {
            Lua55Opcode::Move => Self::Move,
            Lua55Opcode::LoadI => Self::LoadI,
            Lua55Opcode::LoadF => Self::LoadF,
            Lua55Opcode::LoadK => Self::LoadK,
            Lua55Opcode::LoadKx => Self::LoadKx,
            Lua55Opcode::LoadFalse => Self::LoadFalse,
            Lua55Opcode::LFalseSkip => Self::LFalseSkip,
            Lua55Opcode::LoadTrue => Self::LoadTrue,
            Lua55Opcode::LoadNil => Self::LoadNil,
            Lua55Opcode::GetUpVal => Self::GetUpVal,
            Lua55Opcode::SetUpVal => Self::SetUpVal,
            Lua55Opcode::GetTabUp => Self::GetTabUp,
            Lua55Opcode::GetTable => Self::GetTable,
            Lua55Opcode::GetI => Self::GetI,
            Lua55Opcode::GetField => Self::GetField,
            Lua55Opcode::SetTabUp => Self::SetTabUp,
            Lua55Opcode::SetTable => Self::SetTable,
            Lua55Opcode::SetI => Self::SetI,
            Lua55Opcode::SetField => Self::SetField,
            Lua55Opcode::NewTable => Self::NewTable,
            Lua55Opcode::Self_ => Self::Self_,
            Lua55Opcode::AddI => Self::AddI,
            Lua55Opcode::AddK => Self::AddK,
            Lua55Opcode::SubK => Self::SubK,
            Lua55Opcode::MulK => Self::MulK,
            Lua55Opcode::ModK => Self::ModK,
            Lua55Opcode::PowK => Self::PowK,
            Lua55Opcode::DivK => Self::DivK,
            Lua55Opcode::IdivK => Self::IdivK,
            Lua55Opcode::BandK => Self::BandK,
            Lua55Opcode::BorK => Self::BorK,
            Lua55Opcode::BxorK => Self::BxorK,
            Lua55Opcode::ShlI => Self::ShlI,
            Lua55Opcode::ShrI => Self::ShrI,
            Lua55Opcode::Add => Self::Add,
            Lua55Opcode::Sub => Self::Sub,
            Lua55Opcode::Mul => Self::Mul,
            Lua55Opcode::Mod => Self::Mod,
            Lua55Opcode::Pow => Self::Pow,
            Lua55Opcode::Div => Self::Div,
            Lua55Opcode::Idiv => Self::Idiv,
            Lua55Opcode::Band => Self::Band,
            Lua55Opcode::Bor => Self::Bor,
            Lua55Opcode::Bxor => Self::Bxor,
            Lua55Opcode::Shl => Self::Shl,
            Lua55Opcode::Shr => Self::Shr,
            Lua55Opcode::MMBin => Self::MMBin,
            Lua55Opcode::MMBinI => Self::MMBinI,
            Lua55Opcode::MMBinK => Self::MMBinK,
            Lua55Opcode::Unm => Self::Unm,
            Lua55Opcode::BNot => Self::BNot,
            Lua55Opcode::Not => Self::Not,
            Lua55Opcode::Len => Self::Len,
            Lua55Opcode::Concat => Self::Concat,
            Lua55Opcode::Close => Self::Close,
            Lua55Opcode::Tbc => Self::Tbc,
            Lua55Opcode::Jmp => Self::Jmp,
            Lua55Opcode::Eq => Self::Eq,
            Lua55Opcode::Lt => Self::Lt,
            Lua55Opcode::Le => Self::Le,
            Lua55Opcode::EqK => Self::EqK,
            Lua55Opcode::EqI => Self::EqI,
            Lua55Opcode::LtI => Self::LtI,
            Lua55Opcode::LeI => Self::LeI,
            Lua55Opcode::GtI => Self::GtI,
            Lua55Opcode::GeI => Self::GeI,
            Lua55Opcode::Test => Self::Test,
            Lua55Opcode::TestSet => Self::TestSet,
            Lua55Opcode::Call => Self::Call,
            Lua55Opcode::TailCall => Self::TailCall,
            Lua55Opcode::Return => Self::Return,
            Lua55Opcode::Return0 => Self::Return0,
            Lua55Opcode::Return1 => Self::Return1,
            Lua55Opcode::ForLoop => Self::ForLoop,
            Lua55Opcode::ForPrep => Self::ForPrep,
            Lua55Opcode::TForPrep => Self::TForPrep,
            Lua55Opcode::TForCall => Self::TForCall,
            Lua55Opcode::TForLoop => Self::TForLoop,
            Lua55Opcode::SetList => Self::SetList,
            Lua55Opcode::Closure => Self::Closure,
            Lua55Opcode::VarArg => Self::VarArg,
            Lua55Opcode::GetVarg => Self::GetVarg,
            Lua55Opcode::ErrNNil => Self::ErrNNil,
            Lua55Opcode::VarArgPrep => Self::VarArgPrep,
            Lua55Opcode::ExtraArg => Self::ExtraArg,
        }
    }
}

impl From<&Lua54Operands> for FamilyOperands {
    fn from(operands: &Lua54Operands) -> Self {
        match operands {
            Lua54Operands::None => Self::None,
            Lua54Operands::A { a } => Self::A { a: *a },
            Lua54Operands::Ak { a, k } => Self::Ak { a: *a, k: *k },
            Lua54Operands::AB { a, b } => Self::AB { a: *a, b: *b },
            Lua54Operands::AC { a, c } => Self::AC { a: *a, c: *c },
            Lua54Operands::ABk { a, b, k } => Self::ABk {
                a: *a,
                b: *b,
                k: *k,
            },
            Lua54Operands::ABCk { a, b, c, k } => Self::ABCk {
                a: *a,
                b: *b,
                c: *c,
                k: *k,
            },
            Lua54Operands::ABx { a, bx } => Self::ABx { a: *a, bx: *bx },
            Lua54Operands::AsBx { a, sbx } => Self::AsBx { a: *a, sbx: *sbx },
            Lua54Operands::AsJ { sj } => Self::AsJ { sj: *sj },
            Lua54Operands::Ax { ax } => Self::Ax { ax: *ax },
            Lua54Operands::ABsCk { a, b, sc, k } => Self::ABsCk {
                a: *a,
                b: *b,
                sc: *sc,
                k: *k,
            },
            Lua54Operands::AsBCk { a, sb, c, k } => Self::AsBCk {
                a: *a,
                sb: *sb,
                c: *c,
                k: *k,
            },
        }
    }
}

impl From<&Lua55Operands> for FamilyOperands {
    fn from(operands: &Lua55Operands) -> Self {
        match operands {
            Lua55Operands::None => Self::None,
            Lua55Operands::A { a } => Self::A { a: *a },
            Lua55Operands::Ak { a, k } => Self::Ak { a: *a, k: *k },
            Lua55Operands::AB { a, b } => Self::AB { a: *a, b: *b },
            Lua55Operands::AC { a, c } => Self::AC { a: *a, c: *c },
            Lua55Operands::ABC { a, b, c } => Self::Abc {
                a: *a,
                b: *b,
                c: *c,
            },
            Lua55Operands::ABk { a, b, k } => Self::ABk {
                a: *a,
                b: *b,
                k: *k,
            },
            Lua55Operands::ABCk { a, b, c, k } => Self::ABCk {
                a: *a,
                b: *b,
                c: *c,
                k: *k,
            },
            Lua55Operands::ABx { a, bx } => Self::ABx { a: *a, bx: *bx },
            Lua55Operands::AsBx { a, sbx } => Self::AsBx { a: *a, sbx: *sbx },
            Lua55Operands::AsJ { sj } => Self::AsJ { sj: *sj },
            Lua55Operands::Ax { ax } => Self::Ax { ax: *ax },
            Lua55Operands::ABsCk { a, b, sc, k } => Self::ABsCk {
                a: *a,
                b: *b,
                sc: *sc,
                k: *k,
            },
            Lua55Operands::AsBCk { a, sb, c, k } => Self::AsBCk {
                a: *a,
                sb: *sb,
                c: *c,
                k: *k,
            },
            Lua55Operands::AvBCk { a, vb, vc, k } => Self::AvBCk {
                a: *a,
                vb: *vb,
                vc: *vc,
                k: *k,
            },
        }
    }
}

pub(super) fn decode_instr(raw: &RawInstr, dialect: FamilyDialect) -> DecodedInstr {
    match dialect {
        FamilyDialect::Lua54 => {
            let (opcode, operands, extra) = raw
                .lua54()
                .expect("lua54 family lowerer should only decode lua54 instructions");
            DecodedInstr {
                opcode: opcode.into(),
                operands: operands.into(),
                pc: extra.pc,
                extra_arg: extra.extra_arg,
            }
        }
        FamilyDialect::Lua55 => {
            let (opcode, operands, extra) = raw
                .lua55()
                .expect("lua55 family lowerer should only decode lua55 instructions");
            DecodedInstr {
                opcode: opcode.into(),
                operands: operands.into(),
                pc: extra.pc,
                extra_arg: extra.extra_arg,
            }
        }
    }
}
