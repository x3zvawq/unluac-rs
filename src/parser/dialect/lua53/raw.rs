//! 这个文件定义 Lua 5.3 专属的 raw 类型。
//!
//! Lua 5.3 基本延续了 5.2 的指令编码外形，但增加了整数除法和整套位运算 opcode，
//! 同时 header/常量池语义也出现了版本差异；这些类型需要保持独立。

/// Lua 5.3 的 opcode 命名空间，保持与虚拟机原始指令集一致。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(u8)]
pub enum Lua53Opcode {
    Move = 0,
    LoadK = 1,
    LoadKx = 2,
    LoadBool = 3,
    LoadNil = 4,
    GetUpVal = 5,
    GetTabUp = 6,
    GetTable = 7,
    SetTabUp = 8,
    SetUpVal = 9,
    SetTable = 10,
    NewTable = 11,
    Self_ = 12,
    Add = 13,
    Sub = 14,
    Mul = 15,
    Mod = 16,
    Pow = 17,
    Div = 18,
    Idiv = 19,
    Band = 20,
    Bor = 21,
    Bxor = 22,
    Shl = 23,
    Shr = 24,
    Unm = 25,
    BNot = 26,
    Not = 27,
    Len = 28,
    Concat = 29,
    Jmp = 30,
    Eq = 31,
    Lt = 32,
    Le = 33,
    Test = 34,
    TestSet = 35,
    Call = 36,
    TailCall = 37,
    Return = 38,
    ForLoop = 39,
    ForPrep = 40,
    TForCall = 41,
    TForLoop = 42,
    SetList = 43,
    Closure = 44,
    VarArg = 45,
    ExtraArg = 46,
}

impl TryFrom<u8> for Lua53Opcode {
    type Error = u8;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::Move),
            1 => Ok(Self::LoadK),
            2 => Ok(Self::LoadKx),
            3 => Ok(Self::LoadBool),
            4 => Ok(Self::LoadNil),
            5 => Ok(Self::GetUpVal),
            6 => Ok(Self::GetTabUp),
            7 => Ok(Self::GetTable),
            8 => Ok(Self::SetTabUp),
            9 => Ok(Self::SetUpVal),
            10 => Ok(Self::SetTable),
            11 => Ok(Self::NewTable),
            12 => Ok(Self::Self_),
            13 => Ok(Self::Add),
            14 => Ok(Self::Sub),
            15 => Ok(Self::Mul),
            16 => Ok(Self::Mod),
            17 => Ok(Self::Pow),
            18 => Ok(Self::Div),
            19 => Ok(Self::Idiv),
            20 => Ok(Self::Band),
            21 => Ok(Self::Bor),
            22 => Ok(Self::Bxor),
            23 => Ok(Self::Shl),
            24 => Ok(Self::Shr),
            25 => Ok(Self::Unm),
            26 => Ok(Self::BNot),
            27 => Ok(Self::Not),
            28 => Ok(Self::Len),
            29 => Ok(Self::Concat),
            30 => Ok(Self::Jmp),
            31 => Ok(Self::Eq),
            32 => Ok(Self::Lt),
            33 => Ok(Self::Le),
            34 => Ok(Self::Test),
            35 => Ok(Self::TestSet),
            36 => Ok(Self::Call),
            37 => Ok(Self::TailCall),
            38 => Ok(Self::Return),
            39 => Ok(Self::ForLoop),
            40 => Ok(Self::ForPrep),
            41 => Ok(Self::TForCall),
            42 => Ok(Self::TForLoop),
            43 => Ok(Self::SetList),
            44 => Ok(Self::Closure),
            45 => Ok(Self::VarArg),
            46 => Ok(Self::ExtraArg),
            _ => Err(value),
        }
    }
}

/// Lua 5.3 指令解码后的 operand 形态。
#[derive(Debug, Clone, PartialEq)]
pub enum Lua53Operands {
    A { a: u8 },
    AB { a: u8, b: u16 },
    AC { a: u8, c: u16 },
    ABC { a: u8, b: u16, c: u16 },
    ABx { a: u8, bx: u32 },
    AsBx { a: u8, sbx: i32 },
    Ax { ax: u32 },
}

/// Lua 5.3 header 的专属信息目前都已体现在共享字段里，这里保留扩展槽位。
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Lua53HeaderExtra;

/// Lua 5.3 仍保留原始 vararg 位图，避免更后层丢掉版本特异信息。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Lua53ProtoExtra {
    pub raw_is_vararg: u8,
}

/// Lua 5.3 常量池的版本差异已落在共享字面量标签上，这里保留扩展槽位。
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Lua53ConstPoolExtra;

/// Lua 5.3 upvalue 描述符已经落进共享层，这里保留扩展槽位。
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Lua53UpvalueExtra;

/// Lua 5.3 调试信息目前完全落在共享结构里，但保留扩展槽位。
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Lua53DebugExtra;

/// Lua 5.3 指令额外保存 raw pc 以及 `LOADKX/SETLIST` 绑定的 `EXTRAARG`。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Lua53InstrExtra {
    pub pc: u32,
    pub word_len: u8,
    pub extra_arg: Option<u32>,
}
