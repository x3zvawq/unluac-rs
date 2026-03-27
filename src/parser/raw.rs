//! 这个文件定义 parser 层共享的 raw 数据模型。
//!
//! 这里刻意只保留跨 dialect 都稳定存在的抽象，以及公共层必须知道的
//! dialect 分派点；某个 dialect 专属的 opcode、operand、extra 结构
//! 会继续下沉到各自目录里，避免公共模型被单一 dialect 的细节撑大。

use super::StringEncoding;
use super::dialect::lua51::{
    Lua51ConstPoolExtra, Lua51DebugExtra, Lua51HeaderExtra, Lua51InstrExtra, Lua51Opcode,
    Lua51Operands, Lua51ProtoExtra, Lua51UpvalueExtra,
};
use super::dialect::lua52::{
    Lua52ConstPoolExtra, Lua52DebugExtra, Lua52HeaderExtra, Lua52InstrExtra, Lua52Opcode,
    Lua52Operands, Lua52ProtoExtra, Lua52UpvalueExtra,
};
use super::dialect::lua53::{
    Lua53ConstPoolExtra, Lua53DebugExtra, Lua53HeaderExtra, Lua53InstrExtra, Lua53Opcode,
    Lua53Operands, Lua53ProtoExtra, Lua53UpvalueExtra,
};
use super::dialect::lua54::{
    Lua54ConstPoolExtra, Lua54DebugExtra, Lua54HeaderExtra, Lua54InstrExtra, Lua54Opcode,
    Lua54Operands, Lua54ProtoExtra, Lua54UpvalueExtra,
};
use super::dialect::lua55::{
    Lua55ConstPoolExtra, Lua55DebugExtra, Lua55HeaderExtra, Lua55InstrExtra, Lua55Opcode,
    Lua55Operands, Lua55ProtoExtra, Lua55UpvalueExtra,
};
use super::dialect::luau::{
    LuauConstPoolExtra, LuauDebugExtra, LuauHeaderExtra, LuauInstrExtra, LuauOpcode, LuauOperands,
    LuauProtoExtra, LuauUpvalueExtra,
};

/// 一个完整解析后的 chunk。
#[derive(Debug, Clone, PartialEq)]
pub struct RawChunk {
    pub header: ChunkHeader,
    pub main: RawProto,
    pub origin: Origin,
}

/// 所有 dialect 共用的 chunk header 元数据。
#[derive(Debug, Clone, PartialEq)]
pub struct ChunkHeader {
    pub dialect: Dialect,
    pub version: DialectVersion,
    pub layout: ChunkLayout,
    pub extra: DialectHeaderExtra,
    pub origin: Origin,
}

/// chunk 级机器布局在不同 dialect family 之间并不相同。
#[derive(Debug, Clone, PartialEq)]
pub enum ChunkLayout {
    PucLua(PucLuaChunkLayout),
    Luau(LuauChunkLayout),
}

/// PUC-Lua chunk header 暴露给 parser 的布局事实。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct PucLuaChunkLayout {
    pub format: u8,
    pub endianness: Endianness,
    pub integer_size: u8,
    pub lua_integer_size: Option<u8>,
    pub size_t_size: u8,
    pub instruction_size: u8,
    pub number_size: u8,
    pub integral_number: bool,
}

/// Luau serialized bytecode 的头信息。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LuauChunkLayout {
    pub bytecode_version: u8,
    pub type_version: Option<u8>,
}

impl ChunkHeader {
    pub fn puc_lua_layout(&self) -> Option<&PucLuaChunkLayout> {
        match &self.layout {
            ChunkLayout::PucLua(layout) => Some(layout),
            ChunkLayout::Luau(_) => None,
        }
    }

    pub fn luau_layout(&self) -> Option<&LuauChunkLayout> {
        match &self.layout {
            ChunkLayout::PucLua(_) => None,
            ChunkLayout::Luau(layout) => Some(layout),
        }
    }
}

/// 当前支持的 Lua dialect family。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Dialect {
    PucLua,
    Luau,
}

/// dialect family 里的具体字节码版本。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum DialectVersion {
    Lua51,
    Lua52,
    Lua53,
    Lua54,
    Lua55,
    Luau,
}

/// header 声明的字节序。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Endianness {
    Little,
    Big,
}

/// 一个已经解析完成的函数 proto。
#[derive(Debug, Clone, PartialEq)]
pub struct RawProto {
    pub common: RawProtoCommon,
    pub extra: DialectProtoExtra,
    pub origin: Origin,
}

/// 后续各层都会消费的 proto 公共事实。
#[derive(Debug, Clone, PartialEq)]
pub struct RawProtoCommon {
    pub source: Option<RawString>,
    pub line_range: ProtoLineRange,
    pub signature: ProtoSignature,
    pub frame: ProtoFrameInfo,
    pub instructions: Vec<RawInstr>,
    pub constants: RawConstPool,
    pub upvalues: RawUpvalueInfo,
    pub debug_info: RawDebugInfo,
    pub children: Vec<RawProto>,
}

/// proto 在源码中的定义行范围。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct ProtoLineRange {
    pub defined_start: u32,
    pub defined_end: u32,
}

/// 后续层需要的函数签名信息。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct ProtoSignature {
    pub num_params: u8,
    pub is_vararg: bool,
    pub has_vararg_param_reg: bool,
    pub named_vararg_table: bool,
}

/// 后续层需要的调用帧信息。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct ProtoFrameInfo {
    pub max_stack_size: u8,
}

/// proto 的常量池。
#[derive(Debug, Clone, PartialEq)]
pub struct RawConstPool {
    pub common: RawConstPoolCommon,
    pub extra: DialectConstPoolExtra,
}

/// 多个 dialect 之间都共享的常量类别。
#[derive(Debug, Clone, PartialEq)]
pub struct RawConstPoolCommon {
    /// 这里存放所有 dialect 都能直接复用的“字面量子集”。
    ///
    /// 像 Luau 这种拥有 import/table/closure/vector 常量的 dialect，会把完整常量表
    /// 放进 `extra`，而公共层只保留后续 HIR/AST 能直接消费的字面量引用。
    pub literals: Vec<RawLiteralConst>,
}

/// 被原始指令引用的字面量常量。
#[derive(Debug, Clone, PartialEq)]
pub enum RawLiteralConst {
    Nil,
    Boolean(bool),
    Integer(i64),
    Number(f64),
    String(RawString),
}

/// parser 暴露给后续层的 upvalue 信息。
#[derive(Debug, Clone, PartialEq)]
pub struct RawUpvalueInfo {
    pub common: RawUpvalueInfoCommon,
    pub extra: DialectUpvalueExtra,
}

/// dialect 之间共享的 upvalue 公共事实。
#[derive(Debug, Clone, PartialEq)]
pub struct RawUpvalueInfoCommon {
    pub count: u8,
    pub descriptors: Vec<RawUpvalueDescriptor>,
}

/// 某些 dialect 如果显式编码了 upvalue 描述符，可以在这里填充。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct RawUpvalueDescriptor {
    pub in_stack: bool,
    pub index: u8,
}

/// proto 携带的调试信息。
#[derive(Debug, Clone, PartialEq)]
pub struct RawDebugInfo {
    pub common: RawDebugInfoCommon,
    pub extra: DialectDebugExtra,
}

/// dialect 之间共享的调试事实。
#[derive(Debug, Clone, PartialEq)]
pub struct RawDebugInfoCommon {
    pub line_info: Vec<u32>,
    pub local_vars: Vec<RawLocalVar>,
    pub upvalue_names: Vec<RawString>,
}

/// 调试信息里记录的局部变量生命周期。
#[derive(Debug, Clone, PartialEq)]
pub struct RawLocalVar {
    pub name: RawString,
    pub start_pc: u32,
    pub end_pc: u32,
}

/// 一条已经解码完成、同时保留原始来源信息的指令。
#[derive(Debug, Clone, PartialEq)]
pub struct RawInstr {
    pub opcode: RawInstrOpcode,
    pub operands: RawInstrOperands,
    pub extra: DialectInstrExtra,
    pub origin: Origin,
}

/// 各 dialect 自己的 opcode 命名空间。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum RawInstrOpcode {
    Lua51(Lua51Opcode),
    Lua52(Lua52Opcode),
    Lua53(Lua53Opcode),
    Lua54(Lua54Opcode),
    Lua55(Lua55Opcode),
    Luau(LuauOpcode),
}

/// 各 dialect 自己的 operand 形态。
#[derive(Debug, Clone, PartialEq)]
pub enum RawInstrOperands {
    Lua51(Lua51Operands),
    Lua52(Lua52Operands),
    Lua53(Lua53Operands),
    Lua54(Lua54Operands),
    Lua55(Lua55Operands),
    Luau(LuauOperands),
}

/// parser 产物关联到原始字节流的位置。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Origin {
    pub span: Span,
    pub raw_word: Option<u64>,
}

/// 原始 chunk 里的字节区间。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Span {
    pub offset: usize,
    pub size: usize,
}

/// 原始字符串字节以及一个可选的文本视图。
#[derive(Debug, Clone, PartialEq)]
pub struct RawString {
    pub bytes: Vec<u8>,
    pub text: Option<DecodedText>,
    pub origin: Origin,
}

/// 从原始字节解码出来的文本视图。
#[derive(Debug, Clone, PartialEq)]
pub struct DecodedText {
    pub encoding: StringEncoding,
    pub value: String,
}

/// 各 dialect 在 header 上附加的专属信息。
#[derive(Debug, Clone, PartialEq)]
pub enum DialectHeaderExtra {
    Lua51(Lua51HeaderExtra),
    Lua52(Lua52HeaderExtra),
    Lua53(Lua53HeaderExtra),
    Lua54(Lua54HeaderExtra),
    Lua55(Lua55HeaderExtra),
    Luau(LuauHeaderExtra),
}

/// 各 dialect 在 proto 上附加的专属信息。
#[derive(Debug, Clone, PartialEq)]
pub enum DialectProtoExtra {
    Lua51(Lua51ProtoExtra),
    Lua52(Lua52ProtoExtra),
    Lua53(Lua53ProtoExtra),
    Lua54(Lua54ProtoExtra),
    Lua55(Lua55ProtoExtra),
    Luau(LuauProtoExtra),
}

/// 各 dialect 在常量池上附加的专属信息。
#[derive(Debug, Clone, PartialEq)]
pub enum DialectConstPoolExtra {
    Lua51(Lua51ConstPoolExtra),
    Lua52(Lua52ConstPoolExtra),
    Lua53(Lua53ConstPoolExtra),
    Lua54(Lua54ConstPoolExtra),
    Lua55(Lua55ConstPoolExtra),
    Luau(LuauConstPoolExtra),
}

/// 各 dialect 在 upvalue 信息上附加的专属内容。
#[derive(Debug, Clone, PartialEq)]
pub enum DialectUpvalueExtra {
    Lua51(Lua51UpvalueExtra),
    Lua52(Lua52UpvalueExtra),
    Lua53(Lua53UpvalueExtra),
    Lua54(Lua54UpvalueExtra),
    Lua55(Lua55UpvalueExtra),
    Luau(LuauUpvalueExtra),
}

/// 各 dialect 在调试信息上附加的专属内容。
#[derive(Debug, Clone, PartialEq)]
pub enum DialectDebugExtra {
    Lua51(Lua51DebugExtra),
    Lua52(Lua52DebugExtra),
    Lua53(Lua53DebugExtra),
    Lua54(Lua54DebugExtra),
    Lua55(Lua55DebugExtra),
    Luau(LuauDebugExtra),
}

/// 各 dialect 在指令上附加的专属内容。
#[derive(Debug, Clone, PartialEq)]
pub enum DialectInstrExtra {
    Lua51(Lua51InstrExtra),
    Lua52(Lua52InstrExtra),
    Lua53(Lua53InstrExtra),
    Lua54(Lua54InstrExtra),
    Lua55(Lua55InstrExtra),
    Luau(LuauInstrExtra),
}
