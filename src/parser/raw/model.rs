//! 这个文件定义 parser raw 层的跨 dialect 通用模型。
//!
//! 这些结构表达后续阶段都会消费的稳定事实，例如 chunk/proto/instruction/source
//! origin 和保留位模式的宿主字面量；具体 opcode、operand 和 dialect extra 只通过 wrapper 字段挂接进来，
//! 避免公共模型被某个版本的协议细节撑大。
//! `RawString` 的原始字节和解码文本都是不可变共享 payload，raw tree 和后续层的
//! Clone 只复制所有权，不复制字符串内容；Luau 的平铺 proto 还通过 `Arc` 保留共享
//! 子图，避免把同一个 lexical proto 展开成指数级树。

use std::{collections::HashMap, sync::Arc};

use crate::decompile::DecompileDialect;
use crate::parser::StringEncoding;

use super::{
    DialectConstPoolExtra, DialectDebugExtra, DialectHeaderExtra, DialectInstrExtra,
    DialectProtoExtra, DialectUpvalueExtra, RawInstrOpcode, RawInstrOperands,
};

/// 一个完整解析后的 chunk。
#[derive(Debug, Clone, PartialEq)]
pub struct RawChunk {
    pub header: ChunkHeader,
    pub main: RawProto,
    pub origin: Origin,
}

impl RawChunk {
    /// 清除所有可能影响源码恢复或生成注释的调试元数据。
    ///
    /// 该操作只允许在 dialect parser 已完整解析并校验 chunk 后执行；指令、常量、
    /// upvalue 描述符和字节来源区间等运行时语义事实保持不变。
    pub(crate) fn discard_debug_metadata(&mut self) {
        if let DialectHeaderExtra::LuaJit(extra) = &mut self.header.extra {
            extra.chunk_name = None;
        }
        discard_proto_debug_metadata(&mut self.main);
    }
}

fn discard_proto_debug_metadata(root: &mut RawProto) {
    // Metadata stripping is part of the normal parse path (`strip=true`). A
    // `make_mut` walk would clone every shared edge, undoing the flat-DAG
    // contract. Rebuild the graph iteratively instead: each source address is
    // transformed once, then all incoming edges reuse the resulting `Arc`.
    let transformed = strip_proto_graph(Arc::new(root.clone()));
    // The root value is kept by the public `RawChunk` field, so a shallow clone
    // is sufficient and does not depend on the temporary Arc being unique.
    // Descendant payloads remain shared through their Arc edges.
    *root = (*transformed).clone();
}

struct StripFrame {
    source: Arc<RawProto>,
    next_child: usize,
    children: Vec<Arc<RawProto>>,
}

fn strip_proto_graph(root: Arc<RawProto>) -> Arc<RawProto> {
    let mut memo: HashMap<*const RawProto, Arc<RawProto>> = HashMap::new();
    let mut frames = vec![StripFrame {
        children: Vec::with_capacity(root.common.children.len()),
        source: root,
        next_child: 0,
    }];

    loop {
        let Some(frame) = frames.last_mut() else {
            unreachable!("the root frame is returned before the stack is empty");
        };
        if let Some(child) = frame.source.common.children.get(frame.next_child).cloned() {
            frame.next_child += 1;
            let key = Arc::as_ptr(&child);
            if let Some(transformed) = memo.get(&key) {
                frame.children.push(Arc::clone(transformed));
            } else {
                frames.push(StripFrame {
                    children: Vec::with_capacity(child.common.children.len()),
                    source: child,
                    next_child: 0,
                });
            }
            continue;
        }

        let frame = frames.pop().expect("root frame exists");
        let key = Arc::as_ptr(&frame.source);
        let mut proto = (*frame.source).clone();
        proto.common.source = None;
        proto.common.line_range = ProtoLineRange {
            defined_start: 0,
            defined_end: 0,
        };
        proto.common.debug_info.common.line_info.clear();
        proto.common.debug_info.common.local_vars.clear();
        proto.common.debug_info.common.upvalue_names.clear();
        match &mut proto.common.debug_info.extra {
            DialectDebugExtra::Lua54(extra) => *extra = Default::default(),
            DialectDebugExtra::Lua55(extra) => *extra = Default::default(),
            DialectDebugExtra::LuaJit(extra) => *extra = Default::default(),
            DialectDebugExtra::Luau(extra) => *extra = Default::default(),
            DialectDebugExtra::Lua51 | DialectDebugExtra::Lua52 | DialectDebugExtra::Lua53 => {}
        }
        match &mut proto.extra {
            DialectProtoExtra::LuaJit(extra) => {
                extra.first_line = None;
                extra.line_count = None;
                extra.debug_size = 0;
            }
            DialectProtoExtra::Luau(extra) => extra.debug_name = None,
            DialectProtoExtra::Lua51(_)
            | DialectProtoExtra::Lua52(_)
            | DialectProtoExtra::Lua53(_)
            | DialectProtoExtra::Lua54(_)
            | DialectProtoExtra::Lua55(_) => {}
        }
        proto.common.children = frame.children;
        let transformed = Arc::new(proto);
        memo.insert(key, Arc::clone(&transformed));

        if let Some(parent) = frames.last_mut() {
            parent.children.push(transformed);
        } else {
            return transformed;
        }
    }
}

/// 所有 dialect 共用的 chunk header 元数据。
#[derive(Debug, Clone, PartialEq)]
pub struct ChunkHeader {
    pub dialect: Dialect,
    pub version: DecompileDialect,
    pub layout: ChunkLayout,
    pub extra: DialectHeaderExtra,
    pub origin: Origin,
}

/// chunk 级机器布局在不同 dialect family 之间并不相同。
#[derive(Debug, Clone, PartialEq)]
pub enum ChunkLayout {
    PucLua(PucLuaChunkLayout),
    LuaJit(LuaJitChunkLayout),
    Luau(LuauChunkLayout),
}

/// PUC-Lua chunk header 固化下来的布局事实。
///
/// parser family 读取 proto 时也直接复用这份 raw header layout，避免为同一组
/// 机器布局字段再维护第二套工作态模型。
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

/// LuaJIT dump chunk 的头信息。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LuaJitChunkLayout {
    pub dump_version: u8,
    pub flags: u32,
}

impl ChunkHeader {
    pub fn puc_lua_layout(&self) -> Option<&PucLuaChunkLayout> {
        match &self.layout {
            ChunkLayout::PucLua(layout) => Some(layout),
            ChunkLayout::LuaJit(_) | ChunkLayout::Luau(_) => None,
        }
    }

    pub fn luajit_layout(&self) -> Option<&LuaJitChunkLayout> {
        match &self.layout {
            ChunkLayout::LuaJit(layout) => Some(layout),
            ChunkLayout::Luau(_) => None,
            ChunkLayout::PucLua(_) => None,
        }
    }

    pub fn luau_layout(&self) -> Option<&LuauChunkLayout> {
        match &self.layout {
            ChunkLayout::PucLua(_) | ChunkLayout::LuaJit(_) => None,
            ChunkLayout::Luau(layout) => Some(layout),
        }
    }

    pub(crate) fn luajit_fr2(&self) -> Option<bool> {
        Some(self.extra.luajit()?.fr2)
    }
}

/// 当前支持的 Lua dialect family。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Dialect {
    PucLua,
    LuaJit,
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
    /// Child protos are immutable after parsing.  Keeping each edge as an `Arc` is
    /// important for Luau's flat proto table: a `DUPCLOSURE` may reference the same
    /// serialized proto from several lexical slots, and materializing those slots must
    /// not recursively clone the entire descendant subtree.
    pub children: Vec<Arc<RawProto>>,
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
    pub legacy_arg_slot: bool,
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
    /// 像 Luau 这种拥有 import/table/closure 常量的 dialect，会把完整常量表放进
    /// `extra`；vector 属于后层需要直接消费的运行时字面量，因此归一到这里。
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
    Int64(i64),
    UInt64(u64),
    Complex { real: f64, imag: f64 },
    Vector(VectorLiteral),
}

/// Luau vector 常量的四个 IEEE-754 单精度分量。
///
/// bytecode 固定保存四个 `f32`，而宿主 VM 决定实际使用三个还是四个分量。这里保存
/// bit pattern 而不是直接保存 `f32`，避免 NaN 和负零破坏常量身份与相等性。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct VectorLiteral {
    pub components: [u32; 4],
}

impl VectorLiteral {
    pub fn from_components(components: [f32; 4]) -> Self {
        Self {
            components: components.map(f32::to_bits),
        }
    }
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
    pub upvalue_names: Vec<Option<RawString>>,
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
    pub bytes: Arc<[u8]>,
    pub text: Option<DecodedText>,
    pub origin: Origin,
}

/// 从原始字节解码出来的文本视图。
#[derive(Debug, Clone, PartialEq)]
pub struct DecodedText {
    pub encoding: StringEncoding,
    pub value: Arc<str>,
}
