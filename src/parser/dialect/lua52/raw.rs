//! 这个文件定义 Lua 5.2 专属的 raw 类型。
//!
//! 这些结构和 Lua 5.2 VM 指令集直接绑定，特别是 `LOADKX` / `EXTRAARG`、
//! `GETTABUP` / `SETTABUP`、`TFORCALL` / `TFORLOOP` 的编码形状，都不应该污染
//! parser 公共层。

/// Lua 5.2 的 opcode 命名空间，保持与虚拟机原始指令集一致。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(u8)]
pub enum Lua52Opcode {
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
    Div = 16,
    Mod = 17,
    Pow = 18,
    Unm = 19,
    Not = 20,
    Len = 21,
    Concat = 22,
    Jmp = 23,
    Eq = 24,
    Lt = 25,
    Le = 26,
    Test = 27,
    TestSet = 28,
    Call = 29,
    TailCall = 30,
    Return = 31,
    ForLoop = 32,
    ForPrep = 33,
    TForCall = 34,
    TForLoop = 35,
    SetList = 36,
    Closure = 37,
    VarArg = 38,
    ExtraArg = 39,
}

impl TryFrom<u8> for Lua52Opcode {
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
            16 => Ok(Self::Div),
            17 => Ok(Self::Mod),
            18 => Ok(Self::Pow),
            19 => Ok(Self::Unm),
            20 => Ok(Self::Not),
            21 => Ok(Self::Len),
            22 => Ok(Self::Concat),
            23 => Ok(Self::Jmp),
            24 => Ok(Self::Eq),
            25 => Ok(Self::Lt),
            26 => Ok(Self::Le),
            27 => Ok(Self::Test),
            28 => Ok(Self::TestSet),
            29 => Ok(Self::Call),
            30 => Ok(Self::TailCall),
            31 => Ok(Self::Return),
            32 => Ok(Self::ForLoop),
            33 => Ok(Self::ForPrep),
            34 => Ok(Self::TForCall),
            35 => Ok(Self::TForLoop),
            36 => Ok(Self::SetList),
            37 => Ok(Self::Closure),
            38 => Ok(Self::VarArg),
            39 => Ok(Self::ExtraArg),
            _ => Err(value),
        }
    }
}

/// Lua 5.2 指令解码后的 operand 形态。
#[derive(Debug, Clone, PartialEq)]
pub enum Lua52Operands {
    A { a: u8 },
    AB { a: u8, b: u16 },
    AC { a: u8, c: u16 },
    ABC { a: u8, b: u16, c: u16 },
    ABx { a: u8, bx: u32 },
    AsBx { a: u8, sbx: i32 },
    Ax { ax: u32 },
}

/// Lua 5.2 header 额外规则目前只体现在 `LUAC_TAIL` 校验上，这里保留空结构以稳定接口。
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Lua52HeaderExtra;

/// Lua 5.2 仍保留原始 vararg 位图，避免更后层丢掉版本特异信息。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Lua52ProtoExtra {
    pub raw_is_vararg: u8,
}

/// Lua 5.2 常量池目前没有共享层之外的额外类别。
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Lua52ConstPoolExtra;

/// Lua 5.2 upvalue 描述符已经落进共享层，这里保留扩展槽位。
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Lua52UpvalueExtra;

/// Lua 5.2 调试信息目前完全落在共享结构里，但保留扩展槽位。
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Lua52DebugExtra;

/// Lua 5.2 指令额外保存 raw pc 以及 `LOADKX/SETLIST` 绑定的 `EXTRAARG`。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Lua52InstrExtra {
    pub pc: u32,
    pub word_len: u8,
    pub extra_arg: Option<u32>,
}
