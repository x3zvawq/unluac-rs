//! 这个文件定义 Lua 5.1 专属的 raw 类型。
//!
//! 它们不放进 parser 公共层，是因为这些结构天然和 Lua 5.1 VM 指令集
//! 绑定，后续支持 Lua 5.2、LuaJIT、Luau 时不会共享这套定义。

/// Lua 5.1 的 opcode 命名空间，保持与虚拟机原始指令集一致。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(u8)]
pub enum Lua51Opcode {
    Move = 0,
    LoadK = 1,
    LoadBool = 2,
    LoadNil = 3,
    GetUpVal = 4,
    GetGlobal = 5,
    GetTable = 6,
    SetGlobal = 7,
    SetUpVal = 8,
    SetTable = 9,
    NewTable = 10,
    Self_ = 11,
    Add = 12,
    Sub = 13,
    Mul = 14,
    Div = 15,
    Mod = 16,
    Pow = 17,
    Unm = 18,
    Not = 19,
    Len = 20,
    Concat = 21,
    Jmp = 22,
    Eq = 23,
    Lt = 24,
    Le = 25,
    Test = 26,
    TestSet = 27,
    Call = 28,
    TailCall = 29,
    Return = 30,
    ForLoop = 31,
    ForPrep = 32,
    TForLoop = 33,
    SetList = 34,
    Close = 35,
    Closure = 36,
    VarArg = 37,
}

impl Lua51Opcode {
    /// 暴露指令模式，是为了让调试视图和后续 lowering 能共享同一份编码事实。
    pub const fn mode(self) -> Lua51InstructionMode {
        match self {
            Self::LoadK | Self::GetGlobal | Self::SetGlobal | Self::Closure => {
                Lua51InstructionMode::ABx
            }
            Self::Jmp | Self::ForLoop | Self::ForPrep => Lua51InstructionMode::AsBx,
            _ => Lua51InstructionMode::ABC,
        }
    }
}

impl TryFrom<u8> for Lua51Opcode {
    type Error = u8;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::Move),
            1 => Ok(Self::LoadK),
            2 => Ok(Self::LoadBool),
            3 => Ok(Self::LoadNil),
            4 => Ok(Self::GetUpVal),
            5 => Ok(Self::GetGlobal),
            6 => Ok(Self::GetTable),
            7 => Ok(Self::SetGlobal),
            8 => Ok(Self::SetUpVal),
            9 => Ok(Self::SetTable),
            10 => Ok(Self::NewTable),
            11 => Ok(Self::Self_),
            12 => Ok(Self::Add),
            13 => Ok(Self::Sub),
            14 => Ok(Self::Mul),
            15 => Ok(Self::Div),
            16 => Ok(Self::Mod),
            17 => Ok(Self::Pow),
            18 => Ok(Self::Unm),
            19 => Ok(Self::Not),
            20 => Ok(Self::Len),
            21 => Ok(Self::Concat),
            22 => Ok(Self::Jmp),
            23 => Ok(Self::Eq),
            24 => Ok(Self::Lt),
            25 => Ok(Self::Le),
            26 => Ok(Self::Test),
            27 => Ok(Self::TestSet),
            28 => Ok(Self::Call),
            29 => Ok(Self::TailCall),
            30 => Ok(Self::Return),
            31 => Ok(Self::ForLoop),
            32 => Ok(Self::ForPrep),
            33 => Ok(Self::TForLoop),
            34 => Ok(Self::SetList),
            35 => Ok(Self::Close),
            36 => Ok(Self::Closure),
            37 => Ok(Self::VarArg),
            _ => Err(value),
        }
    }
}

/// Lua 5.1 指令解码后的 operand 形态。
#[derive(Debug, Clone, PartialEq)]
pub enum Lua51Operands {
    A { a: u8 },
    AB { a: u8, b: u16 },
    AC { a: u8, c: u16 },
    ABC { a: u8, b: u16, c: u16 },
    ABx { a: u8, bx: u32 },
    AsBx { a: u8, sbx: i32 },
}

/// Lua 5.1 指令编码使用的三种模式。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Lua51InstructionMode {
    ABC,
    ABx,
    AsBx,
}

/// Lua 5.1 header 目前没有额外字段，但保留空结构可以让接口保持稳定。
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Lua51HeaderExtra;

/// Lua 5.1 需要保留原始 vararg 位图，因为它不等同于简单布尔值。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Lua51ProtoExtra {
    pub raw_is_vararg: u8,
}

/// Lua 5.1 常量池目前没有共享层之外的额外类别。
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Lua51ConstPoolExtra;

/// Lua 5.1 chunk 不显式存 upvalue 描述符，但仍保留扩展槽位。
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Lua51UpvalueExtra;

/// Lua 5.1 调试信息目前完全落在共享结构里，但保留扩展槽位。
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Lua51DebugExtra;

/// Lua 5.1 指令额外保存 raw pc 和 `SETLIST` 的扩展参数。
///
/// 这样做是为了避免后续层为了拿回这些事实再次回看原始字节流。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Lua51InstrExtra {
    pub pc: u32,
    pub word_len: u8,
    pub setlist_extra_arg: Option<u32>,
}
