//! 这个文件定义 Lua 5.5 专属的 raw 类型。

use crate::parser::dialect::puc_lua::{DecodedInstructionFields55, define_puc_lua_opcodes};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Lua55OperandKind {
    None,
    A,
    Ak,
    AB,
    AC,
    ABC,
    ABk,
    ABCk,
    ABx,
    AsBx,
    AsJ,
    Ax,
    ABsCk,
    AsBCk,
    AvBCk,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Lua55ExtraWordPolicy {
    None,
    ExtraArg,
    ExtraArgIfK,
}

define_puc_lua_opcodes!(
    opcode: Lua55Opcode,
    operand_kind: Lua55OperandKind,
    extra_word_policy: Lua55ExtraWordPolicy,
    [
        (Move, "MOVE", AB),
        (LoadI, "LOADI", AsBx),
        (LoadF, "LOADF", AsBx),
        (LoadK, "LOADK", ABx),
        (LoadKx, "LOADKX", A, ExtraArg),
        (LoadFalse, "LOADFALSE", A),
        (LFalseSkip, "LFALSESKIP", A),
        (LoadTrue, "LOADTRUE", A),
        (LoadNil, "LOADNIL", AB),
        (GetUpVal, "GETUPVAL", AB),
        (SetUpVal, "SETUPVAL", AB),
        (GetTabUp, "GETTABUP", ABCk),
        (GetTable, "GETTABLE", ABCk),
        (GetI, "GETI", ABCk),
        (GetField, "GETFIELD", ABCk),
        (SetTabUp, "SETTABUP", ABCk),
        (SetTable, "SETTABLE", ABCk),
        (SetI, "SETI", ABCk),
        (SetField, "SETFIELD", ABCk),
        (NewTable, "NEWTABLE", AvBCk, ExtraArg),
        (Self_, "SELF", ABCk),
        (AddI, "ADDI", ABsCk),
        (AddK, "ADDK", ABCk),
        (SubK, "SUBK", ABCk),
        (MulK, "MULK", ABCk),
        (ModK, "MODK", ABCk),
        (PowK, "POWK", ABCk),
        (DivK, "DIVK", ABCk),
        (IdivK, "IDIVK", ABCk),
        (BandK, "BANDK", ABCk),
        (BorK, "BORK", ABCk),
        (BxorK, "BXORK", ABCk),
        (ShlI, "SHLI", ABsCk),
        (ShrI, "SHRI", ABsCk),
        (Add, "ADD", ABCk),
        (Sub, "SUB", ABCk),
        (Mul, "MUL", ABCk),
        (Mod, "MOD", ABCk),
        (Pow, "POW", ABCk),
        (Div, "DIV", ABCk),
        (Idiv, "IDIV", ABCk),
        (Band, "BAND", ABCk),
        (Bor, "BOR", ABCk),
        (Bxor, "BXOR", ABCk),
        (Shl, "SHL", ABCk),
        (Shr, "SHR", ABCk),
        (MMBin, "MMBIN", ABCk),
        (MMBinI, "MMBINI", AsBCk),
        (MMBinK, "MMBINK", ABCk),
        (Unm, "UNM", AB),
        (BNot, "BNOT", AB),
        (Not, "NOT", AB),
        (Len, "LEN", AB),
        (Concat, "CONCAT", AB),
        (Close, "CLOSE", A),
        (Tbc, "TBC", A),
        (Jmp, "JMP", AsJ),
        (Eq, "EQ", ABk),
        (Lt, "LT", ABk),
        (Le, "LE", ABk),
        (EqK, "EQK", ABk),
        (EqI, "EQI", AsBCk),
        (LtI, "LTI", AsBCk),
        (LeI, "LEI", AsBCk),
        (GtI, "GTI", AsBCk),
        (GeI, "GEI", AsBCk),
        (Test, "TEST", Ak),
        (TestSet, "TESTSET", ABk),
        (Call, "CALL", ABCk),
        (TailCall, "TAILCALL", ABCk),
        (Return, "RETURN", ABCk),
        (Return0, "RETURN0", None),
        (Return1, "RETURN1", A),
        (ForLoop, "FORLOOP", ABx),
        (ForPrep, "FORPREP", ABx),
        (TForPrep, "TFORPREP", ABx),
        (TForCall, "TFORCALL", AC),
        (TForLoop, "TFORLOOP", ABx),
        (SetList, "SETLIST", AvBCk, ExtraArgIfK),
        (Closure, "CLOSURE", ABx),
        (VarArg, "VARARG", ABCk),
        (GetVarg, "GETVARG", ABC),
        (ErrNNil, "ERRNNIL", ABx),
        (VarArgPrep, "VARARGPREP", A),
        (ExtraArg, "EXTRAARG", Ax),
    ]
);

#[derive(Debug, Clone, PartialEq)]
pub enum Lua55Operands {
    None,
    A { a: u8 },
    Ak { a: u8, k: bool },
    AB { a: u8, b: u8 },
    AC { a: u8, c: u8 },
    ABC { a: u8, b: u8, c: u8 },
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

impl Lua55Opcode {
    pub(crate) fn decode_operands(self, fields: DecodedInstructionFields55) -> Lua55Operands {
        match self.operand_kind() {
            Lua55OperandKind::None => Lua55Operands::None,
            Lua55OperandKind::A => Lua55Operands::A { a: fields.a },
            Lua55OperandKind::Ak => Lua55Operands::Ak {
                a: fields.a,
                k: fields.k,
            },
            Lua55OperandKind::AB => Lua55Operands::AB {
                a: fields.a,
                b: fields.b,
            },
            Lua55OperandKind::AC => Lua55Operands::AC {
                a: fields.a,
                c: fields.c,
            },
            Lua55OperandKind::ABC => Lua55Operands::ABC {
                a: fields.a,
                b: fields.b,
                c: fields.c,
            },
            Lua55OperandKind::ABk => Lua55Operands::ABk {
                a: fields.a,
                b: fields.b,
                k: fields.k,
            },
            Lua55OperandKind::ABCk => Lua55Operands::ABCk {
                a: fields.a,
                b: fields.b,
                c: fields.c,
                k: fields.k,
            },
            Lua55OperandKind::ABx => Lua55Operands::ABx {
                a: fields.a,
                bx: fields.bx,
            },
            Lua55OperandKind::AsBx => Lua55Operands::AsBx {
                a: fields.a,
                sbx: fields.sbx,
            },
            Lua55OperandKind::AsJ => Lua55Operands::AsJ { sj: fields.sj },
            Lua55OperandKind::Ax => Lua55Operands::Ax { ax: fields.ax },
            Lua55OperandKind::ABsCk => Lua55Operands::ABsCk {
                a: fields.a,
                b: fields.b,
                sc: fields.sc,
                k: fields.k,
            },
            Lua55OperandKind::AsBCk => Lua55Operands::AsBCk {
                a: fields.a,
                sb: fields.sb,
                c: fields.c,
                k: fields.k,
            },
            Lua55OperandKind::AvBCk => Lua55Operands::AvBCk {
                a: fields.a,
                vb: fields.vb,
                vc: fields.vc,
                k: fields.k,
            },
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq)]
pub struct Lua55HeaderExtra;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Lua55ProtoExtra {
    pub raw_flag: u8,
}

#[derive(Debug, Clone, Default, PartialEq)]
pub struct Lua55ConstPoolExtra;

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Lua55UpvalueExtra {
    pub kinds: Vec<u8>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Lua55AbsLineInfo {
    pub pc: u32,
    pub line: u32,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Lua55DebugExtra {
    pub line_deltas: Vec<i8>,
    pub abs_line_info: Vec<Lua55AbsLineInfo>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Lua55InstrExtra {
    pub pc: u32,
    pub word_len: u8,
    pub extra_arg: Option<u32>,
}
