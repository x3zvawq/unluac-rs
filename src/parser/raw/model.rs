//! Parser raw 层跨方言共用的 chunk、proto、指令来源与字面量模型。
//!
//! 保存原始编码事实及共享 payload，具体 opcode 和方言扩展由各自 wrapper 承载。

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use chardetng::{EncodingDetector, Iso2022JpDetection, Utf8Detection};
use encoding_rs::Encoding;

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
    pub(crate) fn discard_debug_metadata(mut self) -> Self {
        if let DialectHeaderExtra::LuaJit(extra) = &mut self.header.extra {
            extra.chunk_name = None;
        }
        self.main = Arc::unwrap_or_clone(strip_proto_graph(Arc::new(self.main)));
        self
    }

    /// 在 `StringEncoding::Auto` 模式下对整份 chunk 的非 UTF-8 文本样本做联合编码探测。
    ///
    /// 仅当聚合样本达到足够证据且命中多字节 CJK 编码时，才对不含二进制控制字节、
    /// 且可无损重编码回原始字节的字符串填充可读文本视图；单字节代码页（如 windows-1252、
    /// IBM866）绝不参与自动改写，从而保证二进制字节串零损往返。
    pub(crate) fn resolve_auto_string_encoding(mut self) -> Self {
        let Some(enc) = detect_chunk_auto_cjk_encoding(&self) else {
            return self;
        };
        let target_enc = StringEncoding::EncodingRs(enc);
        match &mut self.header.extra {
            DialectHeaderExtra::LuaJit(extra) => {
                if let Some(name) = &mut extra.chunk_name {
                    try_decode_auto_string(name, enc, target_enc);
                }
            }
            DialectHeaderExtra::Luau(extra) => {
                for name in extra.userdata_type_names.iter_mut().flatten() {
                    try_decode_auto_string(name, enc, target_enc);
                }
            }
            _ => {}
        }
        self.main =
            Arc::unwrap_or_clone(decode_auto_proto_graph(Arc::new(self.main), enc, target_enc));
        self
    }
}

fn is_auto_text_candidate(bytes: &[u8]) -> bool {
    !bytes.is_empty()
        && !bytes
            .iter()
            .any(|&b| b == 0 || (b < 0x20 && !matches!(b, b'\t' | b'\n' | b'\r')) || b == 0x7F)
}

fn is_multibyte_cjk_encoding(enc: &'static Encoding) -> bool {
    std::ptr::eq(enc, encoding_rs::GBK)
        || std::ptr::eq(enc, encoding_rs::GB18030)
        || std::ptr::eq(enc, encoding_rs::BIG5)
        || std::ptr::eq(enc, encoding_rs::SHIFT_JIS)
        || std::ptr::eq(enc, encoding_rs::EUC_JP)
        || std::ptr::eq(enc, encoding_rs::EUC_KR)
        || std::ptr::eq(enc, encoding_rs::ISO_2022_JP)
}

fn detect_chunk_auto_cjk_encoding(chunk: &RawChunk) -> Option<&'static Encoding> {
    let mut detector = EncodingDetector::new(Iso2022JpDetection::Allow);
    let mut candidate_count = 0usize;
    let mut total_bytes = 0usize;
    let mut feed_str = |s: &RawString| {
        if s.text.is_none() && is_auto_text_candidate(&s.bytes) {
            detector.feed(&s.bytes, false);
            detector.feed(b"\n", false);
            candidate_count += 1;
            total_bytes += s.bytes.len();
        }
    };

    match &chunk.header.extra {
        DialectHeaderExtra::LuaJit(extra) => {
            if let Some(name) = &extra.chunk_name {
                feed_str(name);
            }
        }
        DialectHeaderExtra::Luau(extra) => {
            for name in extra.userdata_type_names.iter().flatten() {
                feed_str(name);
            }
        }
        _ => {}
    }

    let mut visited: HashSet<*const RawProto> = HashSet::new();
    let mut stack: Vec<&RawProto> = vec![&chunk.main];
    while let Some(proto) = stack.pop() {
        if !visited.insert(proto as *const RawProto) {
            continue;
        }
        if let Some(source) = &proto.common.source {
            feed_str(source);
        }
        for lit in proto.common.constants.common.literals.iter() {
            if let RawLiteralConst::String(s) = lit {
                feed_str(s);
            }
        }
        for local in &proto.common.debug_info.common.local_vars {
            feed_str(&local.name);
        }
        for up in proto.common.debug_info.common.upvalue_names.iter().flatten() {
            feed_str(up);
        }
        if let DialectProtoExtra::Luau(extra) = &proto.extra
            && let Some(name) = &extra.debug_name
        {
            feed_str(name);
        }
        for child in &proto.common.children {
            stack.push(child.as_ref());
        }
    }

    // 单条极短字节串（例如 4 字节字面量）不足以在 Auto 模式下安全区分二进制与旧编码文本；
    // 已知编码时由调用方显式传 `-e gbk` 等参数精确解码。
    if candidate_count == 0 || (candidate_count < 2 && total_bytes < 8) {
        return None;
    }
    detector.feed(b"", true);
    let enc = detector.guess(None, Utf8Detection::Allow);
    is_multibyte_cjk_encoding(enc).then_some(enc)
}

fn try_decode_auto_string(
    raw: &mut RawString,
    enc: &'static Encoding,
    target_enc: StringEncoding,
) {
    if raw.text.is_some() || !is_auto_text_candidate(&raw.bytes) {
        return;
    }
    let Some(decoded) = enc.decode_without_bom_handling_and_without_replacement(&raw.bytes) else {
        return;
    };
    let (reencoded, _, had_encode_errors) = enc.encode(&decoded);
    if had_encode_errors || reencoded.as_ref() != raw.bytes.as_ref() {
        return;
    }
    raw.text = Some(DecodedText {
        encoding: target_enc,
        value: decoded.into(),
    });
}

fn decode_auto_proto_graph(
    root: Arc<RawProto>,
    enc: &'static Encoding,
    target_enc: StringEncoding,
) -> Arc<RawProto> {
    let mut memo: HashMap<*const RawProto, Arc<RawProto>> = HashMap::new();
    let mut frames = vec![StripFrame {
        children: Vec::with_capacity(root.common.children.len()),
        source: root,
        next_child: 0,
    }];

    loop {
        let Some(frame) = frames.last_mut() else {
            unreachable!("root frame exists");
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
        let mut proto = Arc::unwrap_or_clone(frame.source);
        if let Some(source) = &mut proto.common.source {
            try_decode_auto_string(source, enc, target_enc);
        }
        let has_undecoded_literal = proto
            .common
            .constants
            .common
            .literals
            .iter()
            .any(|lit| matches!(lit, RawLiteralConst::String(s) if s.text.is_none()));
        if has_undecoded_literal {
            let mut literals = proto.common.constants.common.literals.to_vec();
            for lit in &mut literals {
                if let RawLiteralConst::String(s) = lit {
                    try_decode_auto_string(s, enc, target_enc);
                }
            }
            proto.common.constants.common.literals = literals.into();
        }
        for local in &mut proto.common.debug_info.common.local_vars {
            try_decode_auto_string(&mut local.name, enc, target_enc);
        }
        for up in proto
            .common
            .debug_info
            .common
            .upvalue_names
            .iter_mut()
            .flatten()
        {
            try_decode_auto_string(up, enc, target_enc);
        }
        if let DialectProtoExtra::Luau(extra) = &mut proto.extra
            && let Some(name) = &mut extra.debug_name
        {
            try_decode_auto_string(name, enc, target_enc);
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

struct StripFrame {
    source: Arc<RawProto>,
    next_child: usize,
    children: Vec<Arc<RawProto>>,
}

fn strip_proto_graph(root: Arc<RawProto>) -> Arc<RawProto> {
    // ignore_debug 在完整解析后按源地址只转换一次，共享边复用结果 Arc。
    // 父 frame 始终保留旧 children，使 memo 的地址键在全部子节点查询期间有效；
    // 因而非根仍需复制一次，独占根则可在最后完成时移动载荷。
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
        let mut proto = Arc::unwrap_or_clone(frame.source);
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
    /// Lua 5.1 NEEDSARG 独立于 HASARG：入口是否实际创建旧式 arg 表。
    pub legacy_arg_table: bool,
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
    /// 解析完成后索引与载荷同时冻结，后层和 raw clone 共享同一个池。
    pub literals: Arc<[RawLiteralConst]>,
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
    /// 与 RawInstr::pc 相同的原始坐标；Luau 为包含 AUX 的 word PC，不是指令 Vec 下标。
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
