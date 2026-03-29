//! 这个文件定义 Lua 5.2 专属的 raw 类型。
//!
//! 这些结构和 Lua 5.2 VM 指令集直接绑定，特别是 `LOADKX` / `EXTRAARG`、
//! `GETTABUP` / `SETTABUP`、`TFORCALL` / `TFORLOOP` 的编码形状，都不应该污染
//! parser 公共层。

use crate::parser::dialect::puc_lua::{DecodedInstructionFields, define_puc_lua_opcodes};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Lua52OperandKind {
    A,
    AB,
    AC,
    ABC,
    ABx,
    AsBx,
    Ax,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Lua52ExtraWordPolicy {
    None,
    ExtraArg,
    ExtraArgIfCZero,
}

define_puc_lua_opcodes!(
    opcode: Lua52Opcode,
    operand_kind: Lua52OperandKind,
    extra_word_policy: Lua52ExtraWordPolicy,
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
        (Div, "DIV", ABC),
        (Mod, "MOD", ABC),
        (Pow, "POW", ABC),
        (Unm, "UNM", AB),
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

impl Lua52Opcode {
    pub(crate) fn decode_operands(self, fields: DecodedInstructionFields) -> Lua52Operands {
        match self.operand_kind() {
            Lua52OperandKind::A => Lua52Operands::A { a: fields.a },
            Lua52OperandKind::AB => Lua52Operands::AB {
                a: fields.a,
                b: fields.b,
            },
            Lua52OperandKind::AC => Lua52Operands::AC {
                a: fields.a,
                c: fields.c,
            },
            Lua52OperandKind::ABC => Lua52Operands::ABC {
                a: fields.a,
                b: fields.b,
                c: fields.c,
            },
            Lua52OperandKind::ABx => Lua52Operands::ABx {
                a: fields.a,
                bx: fields.bx,
            },
            Lua52OperandKind::AsBx => Lua52Operands::AsBx {
                a: fields.a,
                sbx: fields.sbx,
            },
            Lua52OperandKind::Ax => Lua52Operands::Ax { ax: fields.ax },
        }
    }
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
