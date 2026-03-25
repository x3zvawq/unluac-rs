//! 这个文件定义 Lua 5.4 专属的 raw 类型。

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(u8)]
pub enum Lua54Opcode {
    Move = 0,
    LoadI = 1,
    LoadF = 2,
    LoadK = 3,
    LoadKx = 4,
    LoadFalse = 5,
    LFalseSkip = 6,
    LoadTrue = 7,
    LoadNil = 8,
    GetUpVal = 9,
    SetUpVal = 10,
    GetTabUp = 11,
    GetTable = 12,
    GetI = 13,
    GetField = 14,
    SetTabUp = 15,
    SetTable = 16,
    SetI = 17,
    SetField = 18,
    NewTable = 19,
    Self_ = 20,
    AddI = 21,
    AddK = 22,
    SubK = 23,
    MulK = 24,
    ModK = 25,
    PowK = 26,
    DivK = 27,
    IdivK = 28,
    BandK = 29,
    BorK = 30,
    BxorK = 31,
    ShrI = 32,
    ShlI = 33,
    Add = 34,
    Sub = 35,
    Mul = 36,
    Mod = 37,
    Pow = 38,
    Div = 39,
    Idiv = 40,
    Band = 41,
    Bor = 42,
    Bxor = 43,
    Shl = 44,
    Shr = 45,
    MMBin = 46,
    MMBinI = 47,
    MMBinK = 48,
    Unm = 49,
    BNot = 50,
    Not = 51,
    Len = 52,
    Concat = 53,
    Close = 54,
    Tbc = 55,
    Jmp = 56,
    Eq = 57,
    Lt = 58,
    Le = 59,
    EqK = 60,
    EqI = 61,
    LtI = 62,
    LeI = 63,
    GtI = 64,
    GeI = 65,
    Test = 66,
    TestSet = 67,
    Call = 68,
    TailCall = 69,
    Return = 70,
    Return0 = 71,
    Return1 = 72,
    ForLoop = 73,
    ForPrep = 74,
    TForPrep = 75,
    TForCall = 76,
    TForLoop = 77,
    SetList = 78,
    Closure = 79,
    VarArg = 80,
    VarArgPrep = 81,
    ExtraArg = 82,
}

impl TryFrom<u8> for Lua54Opcode {
    type Error = u8;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        use Lua54Opcode as Op;

        match value {
            0 => Ok(Op::Move),
            1 => Ok(Op::LoadI),
            2 => Ok(Op::LoadF),
            3 => Ok(Op::LoadK),
            4 => Ok(Op::LoadKx),
            5 => Ok(Op::LoadFalse),
            6 => Ok(Op::LFalseSkip),
            7 => Ok(Op::LoadTrue),
            8 => Ok(Op::LoadNil),
            9 => Ok(Op::GetUpVal),
            10 => Ok(Op::SetUpVal),
            11 => Ok(Op::GetTabUp),
            12 => Ok(Op::GetTable),
            13 => Ok(Op::GetI),
            14 => Ok(Op::GetField),
            15 => Ok(Op::SetTabUp),
            16 => Ok(Op::SetTable),
            17 => Ok(Op::SetI),
            18 => Ok(Op::SetField),
            19 => Ok(Op::NewTable),
            20 => Ok(Op::Self_),
            21 => Ok(Op::AddI),
            22 => Ok(Op::AddK),
            23 => Ok(Op::SubK),
            24 => Ok(Op::MulK),
            25 => Ok(Op::ModK),
            26 => Ok(Op::PowK),
            27 => Ok(Op::DivK),
            28 => Ok(Op::IdivK),
            29 => Ok(Op::BandK),
            30 => Ok(Op::BorK),
            31 => Ok(Op::BxorK),
            32 => Ok(Op::ShrI),
            33 => Ok(Op::ShlI),
            34 => Ok(Op::Add),
            35 => Ok(Op::Sub),
            36 => Ok(Op::Mul),
            37 => Ok(Op::Mod),
            38 => Ok(Op::Pow),
            39 => Ok(Op::Div),
            40 => Ok(Op::Idiv),
            41 => Ok(Op::Band),
            42 => Ok(Op::Bor),
            43 => Ok(Op::Bxor),
            44 => Ok(Op::Shl),
            45 => Ok(Op::Shr),
            46 => Ok(Op::MMBin),
            47 => Ok(Op::MMBinI),
            48 => Ok(Op::MMBinK),
            49 => Ok(Op::Unm),
            50 => Ok(Op::BNot),
            51 => Ok(Op::Not),
            52 => Ok(Op::Len),
            53 => Ok(Op::Concat),
            54 => Ok(Op::Close),
            55 => Ok(Op::Tbc),
            56 => Ok(Op::Jmp),
            57 => Ok(Op::Eq),
            58 => Ok(Op::Lt),
            59 => Ok(Op::Le),
            60 => Ok(Op::EqK),
            61 => Ok(Op::EqI),
            62 => Ok(Op::LtI),
            63 => Ok(Op::LeI),
            64 => Ok(Op::GtI),
            65 => Ok(Op::GeI),
            66 => Ok(Op::Test),
            67 => Ok(Op::TestSet),
            68 => Ok(Op::Call),
            69 => Ok(Op::TailCall),
            70 => Ok(Op::Return),
            71 => Ok(Op::Return0),
            72 => Ok(Op::Return1),
            73 => Ok(Op::ForLoop),
            74 => Ok(Op::ForPrep),
            75 => Ok(Op::TForPrep),
            76 => Ok(Op::TForCall),
            77 => Ok(Op::TForLoop),
            78 => Ok(Op::SetList),
            79 => Ok(Op::Closure),
            80 => Ok(Op::VarArg),
            81 => Ok(Op::VarArgPrep),
            82 => Ok(Op::ExtraArg),
            _ => Err(value),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Lua54Operands {
    None,
    A { a: u8 },
    Ak { a: u8, k: bool },
    AB { a: u8, b: u8 },
    AC { a: u8, c: u8 },
    ABk { a: u8, b: u8, k: bool },
    ABCk { a: u8, b: u8, c: u8, k: bool },
    ABx { a: u8, bx: u32 },
    AsBx { a: u8, sbx: i32 },
    AsJ { sj: i32 },
    Ax { ax: u32 },
    ABsCk { a: u8, b: u8, sc: i16, k: bool },
    AsBCk { a: u8, sb: i16, c: u8, k: bool },
}

#[derive(Debug, Clone, Default, PartialEq)]
pub struct Lua54HeaderExtra;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Lua54ProtoExtra {
    pub raw_is_vararg: u8,
}

#[derive(Debug, Clone, Default, PartialEq)]
pub struct Lua54ConstPoolExtra;

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Lua54UpvalueExtra {
    pub kinds: Vec<u8>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Lua54AbsLineInfo {
    pub pc: u32,
    pub line: u32,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Lua54DebugExtra {
    pub line_deltas: Vec<i8>,
    pub abs_line_info: Vec<Lua54AbsLineInfo>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Lua54InstrExtra {
    pub pc: u32,
    pub word_len: u8,
    pub extra_arg: Option<u32>,
}
