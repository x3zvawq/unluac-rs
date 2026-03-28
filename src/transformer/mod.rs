//! 这个模块承载 raw -> low-IR 的 transformer 层。
//!
//! 它位于 parser 和 CFG 之间，职责是把各个 dialect 的原始指令模式一次性
//! lowering 成统一 low-IR，并顺手建立后续排错所需的 lowering 映射。

mod common;
mod debug;
mod dialect;
mod error;

pub use common::{
    AccessBase, AccessKey, BinaryOpInstr, BinaryOpKind, BranchCond, BranchInstr, BranchOperands,
    BranchPredicate, CallInstr, CallKind, Capture, CaptureSource, CloseInstr, ClosureInstr,
    ConcatInstr, CondOperand, ConstRef, DialectCaptureExtra, ErrNilInstr, GenericForCallInstr,
    GenericForLoopInstr, GetTableInstr, GetUpvalueInstr, InstrRef, JumpInstr, LoadBoolInstr,
    LoadConstInstr, LoadIntegerInstr, LoadNilInstr, LoadNumberInstr, LowInstr, LoweredChunk,
    LoweredProto, LoweringMap, MoveInstr, NewTableInstr, NumberLiteral, NumericForInitInstr,
    NumericForLoopInstr, ProtoRef, RawInstrRef, Reg, RegRange, ResultPack, ReturnInstr,
    SetListInstr, SetTableInstr, SetUpvalueInstr, TailCallInstr, TbcInstr, UnaryOpInstr,
    UnaryOpKind, UpvalueRef, ValueOperand, ValuePack, VarArgInstr,
};
pub use debug::dump_lir;
pub use error::TransformError;

use crate::parser::{DialectVersion, RawChunk};

/// 根据 chunk 的实际 dialect 自动选择 lowering 实现。
pub fn lower_chunk(chunk: &RawChunk) -> Result<LoweredChunk, TransformError> {
    match chunk.header.version {
        DialectVersion::Lua51 => dialect::lua51::lower_chunk(chunk),
        DialectVersion::Lua52 => dialect::lua52::lower_chunk(chunk),
        DialectVersion::Lua53 => dialect::lua53::lower_chunk(chunk),
        DialectVersion::Lua54 => dialect::lua54::lower_chunk(chunk),
        DialectVersion::Lua55 => dialect::lua55::lower_chunk(chunk),
        DialectVersion::LuaJit => dialect::luajit::lower_chunk(chunk),
        DialectVersion::Luau => dialect::luau::lower_chunk(chunk),
    }
}

/// 直接按 Lua 5.1 规则 lowering，不做方言自动探测。
pub fn lower_lua51_chunk(chunk: &RawChunk) -> Result<LoweredChunk, TransformError> {
    dialect::lua51::lower_chunk(chunk)
}

/// 直接按 Lua 5.2 规则 lowering，不做方言自动探测。
pub fn lower_lua52_chunk(chunk: &RawChunk) -> Result<LoweredChunk, TransformError> {
    dialect::lua52::lower_chunk(chunk)
}

/// 直接按 Lua 5.3 规则 lowering，不做方言自动探测。
pub fn lower_lua53_chunk(chunk: &RawChunk) -> Result<LoweredChunk, TransformError> {
    dialect::lua53::lower_chunk(chunk)
}

/// 直接按 Lua 5.4 规则 lowering，不做方言自动探测。
pub fn lower_lua54_chunk(chunk: &RawChunk) -> Result<LoweredChunk, TransformError> {
    dialect::lua54::lower_chunk(chunk)
}

/// 直接按 Lua 5.5 规则 lowering，不做方言自动探测。
pub fn lower_lua55_chunk(chunk: &RawChunk) -> Result<LoweredChunk, TransformError> {
    dialect::lua55::lower_chunk(chunk)
}
