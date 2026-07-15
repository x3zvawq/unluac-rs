//! 这个模块承载 raw -> low-IR 的 transformer 层。
//!
//! 它位于 parser 和 CFG 之间，职责是把各个 dialect 的原始指令模式一次性
//! lowering 成统一 low-IR，并顺手建立后续排错所需的 lowering 映射。

mod common;
#[cfg(feature = "decompile-debug")]
mod debug;
mod dialect;
mod error;
mod format;
mod operands;
#[cfg(not(feature = "decompile-debug"))]
mod debug {
    crate::debug::define_unavailable_stage_dump!(dump_lir);
}

pub use common::{
    AccessBase, AccessKey, BinaryOpInstr, BinaryOpKind, BranchCond, BranchInstr, BranchOperands,
    BranchPredicate, CallInstr, CallKind, Capture, CaptureSource, CloseInstr, ClosureInstr,
    ConcatInstr, CondOperand, ConstRef, DialectCaptureExtra, ErrNilInstr, GenericForCallInstr,
    GenericForLoopInstr, GetTableInstr, GetTableKind, GetUpvalueInstr, InstrRef, JumpInstr,
    LoadBoolInstr, LoadConstInstr, LoadIntegerInstr, LoadNilInstr, LoadNumberInstr, LowInstr,
    LoweredChunk, LoweredProto, LoweringMap, MethodNameHint, MoveInstr, NewTableInstr,
    NumberLiteral, NumericForInitInstr, NumericForLoopInstr, ProtoRef, RawInstrRef, Reg, RegRange,
    ResultPack, ReturnInstr, SetListInstr, SetTableInstr, SetUpvalueInstr, TailCallInstr, TbcInstr,
    TbcKind, UnaryOpInstr, UnaryOpKind, UpvalueOperand, UpvalueRef, ValueOperand, ValuePack,
    VarArgInstr,
};
pub use debug::dump_lir;
pub use error::TransformError;
pub use format::format_low_instr;

use crate::decompile::{DecompileContext, DecompileDialect, DecompileError, DecompileState};

/// Transform 阶段入口：从 Parse 槽位读取 raw chunk，写回统一 low-IR。
pub(crate) fn lower_chunk(
    state: &mut DecompileState,
    _context: &DecompileContext<'_>,
) -> Result<(), DecompileError> {
    let raw_chunk = state.require_raw_chunk()?;
    state.lowered = Some(match raw_chunk.header.version {
        DecompileDialect::Auto => unreachable!("raw chunks must carry a resolved dialect"),
        DecompileDialect::Lua51 => dialect::lua51::lower_chunk(raw_chunk),
        DecompileDialect::Lua52 => dialect::lua52::lower_chunk(raw_chunk),
        DecompileDialect::Lua53 => dialect::lua53::lower_chunk(raw_chunk),
        DecompileDialect::Lua54 => dialect::lua54::lower_chunk(raw_chunk),
        DecompileDialect::Lua55 => dialect::lua55::lower_chunk(raw_chunk),
        DecompileDialect::Luajit => dialect::luajit::lower_chunk(raw_chunk),
        DecompileDialect::Luau => dialect::luau::lower_chunk(raw_chunk),
    }?);
    Ok(())
}
