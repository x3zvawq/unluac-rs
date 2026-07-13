//! 这个文件把 Lua 5.2/5.3 的 typed raw 指令穷尽映射到共享 lowering 视图。
//!
//! parser 仍保留各版本独立的 opcode 与 operand 类型；这里只有确认一致的指令外形，
//! 新增或修改协议 opcode 时必须先通过版本 match 的穷尽检查，不能按字符串猜测语义。

use crate::parser::{Lua52Opcode, Lua52Operands, Lua53Opcode, Lua53Operands, RawInstr};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) enum FamilyDialect {
    Lua52,
    Lua53,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(super) enum FamilyOpcode {
    Move,
    LoadK,
    LoadKx,
    LoadBool,
    LoadNil,
    GetUpVal,
    GetTabUp,
    GetTable,
    SetTabUp,
    SetUpVal,
    SetTable,
    NewTable,
    Self_,
    Add,
    Sub,
    Mul,
    Div,
    Idiv,
    Mod,
    Pow,
    Band,
    Bor,
    Bxor,
    Shl,
    Shr,
    Unm,
    BNot,
    Not,
    Len,
    Concat,
    Jmp,
    Eq,
    Lt,
    Le,
    Test,
    TestSet,
    Call,
    TailCall,
    Return,
    ForLoop,
    ForPrep,
    TForCall,
    TForLoop,
    SetList,
    Closure,
    VarArg,
    ExtraArg,
}

impl FamilyOpcode {
    pub(super) fn label(self) -> &'static str {
        match self {
            Self::Move => "MOVE",
            Self::LoadK => "LOADK",
            Self::LoadKx => "LOADKX",
            Self::LoadBool => "LOADBOOL",
            Self::LoadNil => "LOADNIL",
            Self::GetUpVal => "GETUPVAL",
            Self::GetTabUp => "GETTABUP",
            Self::GetTable => "GETTABLE",
            Self::SetTabUp => "SETTABUP",
            Self::SetUpVal => "SETUPVAL",
            Self::SetTable => "SETTABLE",
            Self::NewTable => "NEWTABLE",
            Self::Self_ => "SELF",
            Self::Add => "ADD",
            Self::Sub => "SUB",
            Self::Mul => "MUL",
            Self::Div => "DIV",
            Self::Idiv => "IDIV",
            Self::Mod => "MOD",
            Self::Pow => "POW",
            Self::Band => "BAND",
            Self::Bor => "BOR",
            Self::Bxor => "BXOR",
            Self::Shl => "SHL",
            Self::Shr => "SHR",
            Self::Unm => "UNM",
            Self::BNot => "BNOT",
            Self::Not => "NOT",
            Self::Len => "LEN",
            Self::Concat => "CONCAT",
            Self::Jmp => "JMP",
            Self::Eq => "EQ",
            Self::Lt => "LT",
            Self::Le => "LE",
            Self::Test => "TEST",
            Self::TestSet => "TESTSET",
            Self::Call => "CALL",
            Self::TailCall => "TAILCALL",
            Self::Return => "RETURN",
            Self::ForLoop => "FORLOOP",
            Self::ForPrep => "FORPREP",
            Self::TForCall => "TFORCALL",
            Self::TForLoop => "TFORLOOP",
            Self::SetList => "SETLIST",
            Self::Closure => "CLOSURE",
            Self::VarArg => "VARARG",
            Self::ExtraArg => "EXTRAARG",
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(super) enum FamilyOperands {
    A { a: u8 },
    AB { a: u8, b: u16 },
    AC { a: u8, c: u16 },
    Abc { a: u8, b: u16, c: u16 },
    ABx { a: u8, bx: u32 },
    AsBx { a: u8, sbx: i32 },
    Ax { ax: u32 },
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(super) struct DecodedInstr {
    pub(super) opcode: FamilyOpcode,
    pub(super) operands: FamilyOperands,
    pub(super) pc: u32,
    pub(super) extra_arg: Option<u32>,
}

impl From<Lua52Opcode> for FamilyOpcode {
    fn from(opcode: Lua52Opcode) -> Self {
        match opcode {
            Lua52Opcode::Move => Self::Move,
            Lua52Opcode::LoadK => Self::LoadK,
            Lua52Opcode::LoadKx => Self::LoadKx,
            Lua52Opcode::LoadBool => Self::LoadBool,
            Lua52Opcode::LoadNil => Self::LoadNil,
            Lua52Opcode::GetUpVal => Self::GetUpVal,
            Lua52Opcode::GetTabUp => Self::GetTabUp,
            Lua52Opcode::GetTable => Self::GetTable,
            Lua52Opcode::SetTabUp => Self::SetTabUp,
            Lua52Opcode::SetUpVal => Self::SetUpVal,
            Lua52Opcode::SetTable => Self::SetTable,
            Lua52Opcode::NewTable => Self::NewTable,
            Lua52Opcode::Self_ => Self::Self_,
            Lua52Opcode::Add => Self::Add,
            Lua52Opcode::Sub => Self::Sub,
            Lua52Opcode::Mul => Self::Mul,
            Lua52Opcode::Div => Self::Div,
            Lua52Opcode::Mod => Self::Mod,
            Lua52Opcode::Pow => Self::Pow,
            Lua52Opcode::Unm => Self::Unm,
            Lua52Opcode::Not => Self::Not,
            Lua52Opcode::Len => Self::Len,
            Lua52Opcode::Concat => Self::Concat,
            Lua52Opcode::Jmp => Self::Jmp,
            Lua52Opcode::Eq => Self::Eq,
            Lua52Opcode::Lt => Self::Lt,
            Lua52Opcode::Le => Self::Le,
            Lua52Opcode::Test => Self::Test,
            Lua52Opcode::TestSet => Self::TestSet,
            Lua52Opcode::Call => Self::Call,
            Lua52Opcode::TailCall => Self::TailCall,
            Lua52Opcode::Return => Self::Return,
            Lua52Opcode::ForLoop => Self::ForLoop,
            Lua52Opcode::ForPrep => Self::ForPrep,
            Lua52Opcode::TForCall => Self::TForCall,
            Lua52Opcode::TForLoop => Self::TForLoop,
            Lua52Opcode::SetList => Self::SetList,
            Lua52Opcode::Closure => Self::Closure,
            Lua52Opcode::VarArg => Self::VarArg,
            Lua52Opcode::ExtraArg => Self::ExtraArg,
        }
    }
}

impl From<Lua53Opcode> for FamilyOpcode {
    fn from(opcode: Lua53Opcode) -> Self {
        match opcode {
            Lua53Opcode::Move => Self::Move,
            Lua53Opcode::LoadK => Self::LoadK,
            Lua53Opcode::LoadKx => Self::LoadKx,
            Lua53Opcode::LoadBool => Self::LoadBool,
            Lua53Opcode::LoadNil => Self::LoadNil,
            Lua53Opcode::GetUpVal => Self::GetUpVal,
            Lua53Opcode::GetTabUp => Self::GetTabUp,
            Lua53Opcode::GetTable => Self::GetTable,
            Lua53Opcode::SetTabUp => Self::SetTabUp,
            Lua53Opcode::SetUpVal => Self::SetUpVal,
            Lua53Opcode::SetTable => Self::SetTable,
            Lua53Opcode::NewTable => Self::NewTable,
            Lua53Opcode::Self_ => Self::Self_,
            Lua53Opcode::Add => Self::Add,
            Lua53Opcode::Sub => Self::Sub,
            Lua53Opcode::Mul => Self::Mul,
            Lua53Opcode::Div => Self::Div,
            Lua53Opcode::Idiv => Self::Idiv,
            Lua53Opcode::Mod => Self::Mod,
            Lua53Opcode::Pow => Self::Pow,
            Lua53Opcode::Band => Self::Band,
            Lua53Opcode::Bor => Self::Bor,
            Lua53Opcode::Bxor => Self::Bxor,
            Lua53Opcode::Shl => Self::Shl,
            Lua53Opcode::Shr => Self::Shr,
            Lua53Opcode::Unm => Self::Unm,
            Lua53Opcode::BNot => Self::BNot,
            Lua53Opcode::Not => Self::Not,
            Lua53Opcode::Len => Self::Len,
            Lua53Opcode::Concat => Self::Concat,
            Lua53Opcode::Jmp => Self::Jmp,
            Lua53Opcode::Eq => Self::Eq,
            Lua53Opcode::Lt => Self::Lt,
            Lua53Opcode::Le => Self::Le,
            Lua53Opcode::Test => Self::Test,
            Lua53Opcode::TestSet => Self::TestSet,
            Lua53Opcode::Call => Self::Call,
            Lua53Opcode::TailCall => Self::TailCall,
            Lua53Opcode::Return => Self::Return,
            Lua53Opcode::ForLoop => Self::ForLoop,
            Lua53Opcode::ForPrep => Self::ForPrep,
            Lua53Opcode::TForCall => Self::TForCall,
            Lua53Opcode::TForLoop => Self::TForLoop,
            Lua53Opcode::SetList => Self::SetList,
            Lua53Opcode::Closure => Self::Closure,
            Lua53Opcode::VarArg => Self::VarArg,
            Lua53Opcode::ExtraArg => Self::ExtraArg,
        }
    }
}

impl From<&Lua52Operands> for FamilyOperands {
    fn from(operands: &Lua52Operands) -> Self {
        match operands {
            Lua52Operands::A { a } => Self::A { a: *a },
            Lua52Operands::AB { a, b } => Self::AB { a: *a, b: *b },
            Lua52Operands::AC { a, c } => Self::AC { a: *a, c: *c },
            Lua52Operands::ABC { a, b, c } => Self::Abc {
                a: *a,
                b: *b,
                c: *c,
            },
            Lua52Operands::ABx { a, bx } => Self::ABx { a: *a, bx: *bx },
            Lua52Operands::AsBx { a, sbx } => Self::AsBx { a: *a, sbx: *sbx },
            Lua52Operands::Ax { ax } => Self::Ax { ax: *ax },
        }
    }
}

impl From<&Lua53Operands> for FamilyOperands {
    fn from(operands: &Lua53Operands) -> Self {
        match operands {
            Lua53Operands::A { a } => Self::A { a: *a },
            Lua53Operands::AB { a, b } => Self::AB { a: *a, b: *b },
            Lua53Operands::AC { a, c } => Self::AC { a: *a, c: *c },
            Lua53Operands::ABC { a, b, c } => Self::Abc {
                a: *a,
                b: *b,
                c: *c,
            },
            Lua53Operands::ABx { a, bx } => Self::ABx { a: *a, bx: *bx },
            Lua53Operands::AsBx { a, sbx } => Self::AsBx { a: *a, sbx: *sbx },
            Lua53Operands::Ax { ax } => Self::Ax { ax: *ax },
        }
    }
}

pub(super) fn decode_instr(raw: &RawInstr, dialect: FamilyDialect) -> DecodedInstr {
    match dialect {
        FamilyDialect::Lua52 => {
            let (opcode, operands, extra) = raw
                .lua52()
                .expect("lua52 family lowerer should only decode lua52 instructions");
            DecodedInstr {
                opcode: opcode.into(),
                operands: operands.into(),
                pc: extra.pc,
                extra_arg: extra.extra_arg,
            }
        }
        FamilyDialect::Lua53 => {
            let (opcode, operands, extra) = raw
                .lua53()
                .expect("lua53 family lowerer should only decode lua53 instructions");
            DecodedInstr {
                opcode: opcode.into(),
                operands: operands.into(),
                pc: extra.pc,
                extra_arg: extra.extra_arg,
            }
        }
    }
}
