//! 这个文件定义 Lua 5.4 专属的 raw 类型。

use crate::parser::dialect::puc_lua::{DecodedInstructionFields54, define_puc_lua_opcodes};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Lua54OperandKind {
    None,
    A,
    Ak,
    AB,
    AC,
    ABk,
    ABCk,
    ABx,
    AsBx,
    AsJ,
    Ax,
    ABsCk,
    AsBCk,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Lua54ExtraWordPolicy {
    None,
    ExtraArg,
    ExtraArgIfK,
}

define_puc_lua_opcodes!(
    opcode: Lua54Opcode,
    operand_kind: Lua54OperandKind,
    extra_word_policy: Lua54ExtraWordPolicy,
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
        (NewTable, "NEWTABLE", ABCk, ExtraArg),
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
        (ShrI, "SHRI", ABsCk),
        (ShlI, "SHLI", ABsCk),
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
        (SetList, "SETLIST", ABCk, ExtraArgIfK),
        (Closure, "CLOSURE", ABx),
        (VarArg, "VARARG", AC),
        (VarArgPrep, "VARARGPREP", A),
        (ExtraArg, "EXTRAARG", Ax),
    ]
);

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

impl Lua54Opcode {
    pub(crate) fn decode_operands(self, fields: DecodedInstructionFields54) -> Lua54Operands {
        match self.operand_kind() {
            Lua54OperandKind::None => Lua54Operands::None,
            Lua54OperandKind::A => Lua54Operands::A { a: fields.a },
            Lua54OperandKind::Ak => Lua54Operands::Ak {
                a: fields.a,
                k: fields.k,
            },
            Lua54OperandKind::AB => Lua54Operands::AB {
                a: fields.a,
                b: fields.b,
            },
            Lua54OperandKind::AC => Lua54Operands::AC {
                a: fields.a,
                c: fields.c,
            },
            Lua54OperandKind::ABk => Lua54Operands::ABk {
                a: fields.a,
                b: fields.b,
                k: fields.k,
            },
            Lua54OperandKind::ABCk => Lua54Operands::ABCk {
                a: fields.a,
                b: fields.b,
                c: fields.c,
                k: fields.k,
            },
            Lua54OperandKind::ABx => Lua54Operands::ABx {
                a: fields.a,
                bx: fields.bx,
            },
            Lua54OperandKind::AsBx => Lua54Operands::AsBx {
                a: fields.a,
                sbx: fields.sbx,
            },
            Lua54OperandKind::AsJ => Lua54Operands::AsJ { sj: fields.sj },
            Lua54OperandKind::Ax => Lua54Operands::Ax { ax: fields.ax },
            Lua54OperandKind::ABsCk => Lua54Operands::ABsCk {
                a: fields.a,
                b: fields.b,
                sc: fields.sc,
                k: fields.k,
            },
            Lua54OperandKind::AsBCk => Lua54Operands::AsBCk {
                a: fields.a,
                sb: fields.sb,
                c: fields.c,
                k: fields.k,
            },
        }
    }
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
