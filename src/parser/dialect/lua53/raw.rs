//! 这个文件定义 Lua 5.3 专属的 raw 类型。
//!
//! Lua 5.3 基本延续了 5.2 的指令编码外形，但增加了整数除法和整套位运算 opcode，
//! 同时 header/常量池语义也出现了版本差异；这些类型需要保持独立。

use crate::parser::dialect::puc_lua::{DecodedInstructionFields, define_puc_lua_opcodes};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Lua53OperandKind {
    A,
    AB,
    AC,
    ABC,
    ABx,
    AsBx,
    Ax,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Lua53ExtraWordPolicy {
    None,
    ExtraArg,
    ExtraArgIfCZero,
}

define_puc_lua_opcodes!(
    opcode: Lua53Opcode,
    operand_kind: Lua53OperandKind,
    extra_word_policy: Lua53ExtraWordPolicy,
    [
        (Move, "MOVE", AB),
        (LoadK, "LOADK", ABx),
        (LoadKx, "LOADKX", A, ExtraArg),
        (LoadBool, "LOADBOOL", ABC),
        (LoadNil, "LOADNIL", AB),
        (GetUpVal, "GETUPVAL", AB),
        (GetTabUp, "GETTABUP", ABC),
        (GetTable, "GETTABLE", ABC),
        (SetTabUp, "SETTABUP", ABC),
        (SetUpVal, "SETUPVAL", AB),
        (SetTable, "SETTABLE", ABC),
        (NewTable, "NEWTABLE", ABC),
        (Self_, "SELF", ABC),
        (Add, "ADD", ABC),
        (Sub, "SUB", ABC),
        (Mul, "MUL", ABC),
        (Mod, "MOD", ABC),
        (Pow, "POW", ABC),
        (Div, "DIV", ABC),
        (Idiv, "IDIV", ABC),
        (Band, "BAND", ABC),
        (Bor, "BOR", ABC),
        (Bxor, "BXOR", ABC),
        (Shl, "SHL", ABC),
        (Shr, "SHR", ABC),
        (Unm, "UNM", AB),
        (BNot, "BNOT", AB),
        (Not, "NOT", AB),
        (Len, "LEN", AB),
        (Concat, "CONCAT", ABC),
        (Jmp, "JMP", AsBx),
        (Eq, "EQ", ABC),
        (Lt, "LT", ABC),
        (Le, "LE", ABC),
        (Test, "TEST", AC),
        (TestSet, "TESTSET", ABC),
        (Call, "CALL", ABC),
        (TailCall, "TAILCALL", ABC),
        (Return, "RETURN", AB),
        (ForLoop, "FORLOOP", AsBx),
        (ForPrep, "FORPREP", AsBx),
        (TForCall, "TFORCALL", ABC),
        (TForLoop, "TFORLOOP", AsBx),
        (SetList, "SETLIST", ABC, ExtraArgIfCZero),
        (Closure, "CLOSURE", ABx),
        (VarArg, "VARARG", AB),
        (ExtraArg, "EXTRAARG", Ax),
    ]
);

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

impl Lua53Opcode {
    pub(crate) fn decode_operands(self, fields: DecodedInstructionFields) -> Lua53Operands {
        match self.operand_kind() {
            Lua53OperandKind::A => Lua53Operands::A { a: fields.a },
            Lua53OperandKind::AB => Lua53Operands::AB {
                a: fields.a,
                b: fields.b,
            },
            Lua53OperandKind::AC => Lua53Operands::AC {
                a: fields.a,
                c: fields.c,
            },
            Lua53OperandKind::ABC => Lua53Operands::ABC {
                a: fields.a,
                b: fields.b,
                c: fields.c,
            },
            Lua53OperandKind::ABx => Lua53Operands::ABx {
                a: fields.a,
                bx: fields.bx,
            },
            Lua53OperandKind::AsBx => Lua53Operands::AsBx {
                a: fields.a,
                sbx: fields.sbx,
            },
            Lua53OperandKind::Ax => Lua53Operands::Ax { ax: fields.ax },
        }
    }
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
