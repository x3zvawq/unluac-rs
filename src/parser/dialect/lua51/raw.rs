//! 这个文件定义 Lua 5.1 专属的 raw 类型。
//!
//! 它们不放进 parser 公共层，是因为这些结构天然和 Lua 5.1 VM 指令集
//! 绑定，后续支持 Lua 5.2、LuaJIT、Luau 时不会共享这套定义。

use crate::parser::dialect::puc_lua::{DecodedInstructionFields, define_puc_lua_opcodes};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Lua51OperandKind {
    A,
    AB,
    AC,
    ABC,
    ABx,
    AsBx,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Lua51ExtraWordPolicy {
    None,
    SetListWordIfCZero,
}

define_puc_lua_opcodes!(
    opcode: Lua51Opcode,
    operand_kind: Lua51OperandKind,
    extra_word_policy: Lua51ExtraWordPolicy,
    [
        (Move, "MOVE", AB),
        (LoadK, "LOADK", ABx),
        (LoadBool, "LOADBOOL", ABC),
        (LoadNil, "LOADNIL", AB),
        (GetUpVal, "GETUPVAL", AB),
        (GetGlobal, "GETGLOBAL", ABx),
        (GetTable, "GETTABLE", ABC),
        (SetGlobal, "SETGLOBAL", ABx),
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
        (TForLoop, "TFORLOOP", AC),
        (SetList, "SETLIST", ABC, SetListWordIfCZero),
        (Close, "CLOSE", A),
        (Closure, "CLOSURE", ABx),
        (VarArg, "VARARG", AB),
    ]
);

impl Lua51Opcode {
    /// 暴露指令模式，是为了让调试视图和后续 lowering 能共享同一份编码事实。
    pub const fn mode(self) -> Lua51InstructionMode {
        match self.operand_kind() {
            Lua51OperandKind::ABx => Lua51InstructionMode::ABx,
            Lua51OperandKind::AsBx => Lua51InstructionMode::AsBx,
            Lua51OperandKind::A
            | Lua51OperandKind::AB
            | Lua51OperandKind::AC
            | Lua51OperandKind::ABC => Lua51InstructionMode::ABC,
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

impl Lua51Opcode {
    pub(crate) fn decode_operands(self, fields: DecodedInstructionFields) -> Lua51Operands {
        match self.operand_kind() {
            Lua51OperandKind::A => Lua51Operands::A { a: fields.a },
            Lua51OperandKind::AB => Lua51Operands::AB {
                a: fields.a,
                b: fields.b,
            },
            Lua51OperandKind::AC => Lua51Operands::AC {
                a: fields.a,
                c: fields.c,
            },
            Lua51OperandKind::ABC => Lua51Operands::ABC {
                a: fields.a,
                b: fields.b,
                c: fields.c,
            },
            Lua51OperandKind::ABx => Lua51Operands::ABx {
                a: fields.a,
                bx: fields.bx,
            },
            Lua51OperandKind::AsBx => Lua51Operands::AsBx {
                a: fields.a,
                sbx: fields.sbx,
            },
        }
    }
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
