//! 这个模块承载 PUC-Lua 5.x lowering 之间共享的 helper。
//!
//! 这些 helper 只负责 RK/寄存器区间/调用包这类稳定编码事实，避免 5.1 和 5.2
//! 各自复制一套样板；真正的 opcode 语义和模式识别仍留在版本目录里实现。

use crate::parser::{RawChunk, RawInstr, RawProto};
use crate::transformer::common::resolve_env_upvalues;
use crate::transformer::dialect::lowering::{
    PendingLowInstr, PendingLoweringState, TargetPlaceholder, WordCodeIndex,
};
use crate::transformer::{
    AccessBase, CallInstr, CallKind, CloseInstr, ConstRef, GenericForCallInstr, LowInstr,
    LoweredChunk, LoweredProto, LoweringMap, ProtoRef, Reg, RegRange, ResultPack, ReturnInstr,
    TailCallInstr, TbcInstr, TransformError, UpvalueRef, ValuePack,
};

pub(crate) const BITRK: u16 = 1 << 8;
pub(crate) const LFIELDS_PER_FLUSH: u32 = 50;

#[derive(Debug, Clone, Copy)]
pub(crate) struct HelperJumpInfo {
    pub(crate) helper_index: usize,
    pub(crate) jump_target: usize,
    pub(crate) fallthrough_target: usize,
    pub(crate) close_from: Option<Reg>,
    pub(crate) next_index: usize,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct GenericForPairInfo {
    pub(crate) loop_index: usize,
    pub(crate) control: Reg,
    pub(crate) bindings: RegRange,
    pub(crate) body_target: usize,
    pub(crate) exit_target: usize,
    pub(crate) next_index: usize,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct NumericForRegs {
    pub(crate) index: Reg,
    pub(crate) limit: Reg,
    pub(crate) step: Reg,
    pub(crate) binding: Reg,
}

pub(crate) struct HelperJumpAsbxSpec<
    Opcode,
    InspectHelper,
    RawPcAt,
    JumpTarget,
    EnsureTargetable,
    NextRawPc,
    OpcodeLabel,
    CloseFrom,
> {
    pub(crate) owner_opcode: Opcode,
    pub(crate) helper_jump_opcode: Opcode,
    pub(crate) inspect_helper: InspectHelper,
    pub(crate) raw_pc_at: RawPcAt,
    pub(crate) jump_target: JumpTarget,
    pub(crate) ensure_targetable_pc: EnsureTargetable,
    pub(crate) next_raw_pc: NextRawPc,
    pub(crate) opcode_label: OpcodeLabel,
    pub(crate) close_from: CloseFrom,
}

pub(crate) struct HelperJumpAsjSpec<
    Opcode,
    InspectHelper,
    RawPcAt,
    JumpTarget,
    EnsureTargetable,
    NextRawPc,
    OpcodeLabel,
> {
    pub(crate) owner_opcode: Opcode,
    pub(crate) helper_jump_opcode: Opcode,
    pub(crate) inspect_helper: InspectHelper,
    pub(crate) raw_pc_at: RawPcAt,
    pub(crate) jump_target: JumpTarget,
    pub(crate) ensure_targetable_pc: EnsureTargetable,
    pub(crate) next_raw_pc: NextRawPc,
    pub(crate) opcode_label: OpcodeLabel,
}

pub(crate) struct GenericForPairAsbxSpec<
    Opcode,
    InspectHelper,
    RawPcAt,
    JumpTarget,
    EnsureTargetable,
    NextRawPc,
    OpcodeLabel,
    ValidateLoopBase,
    BuildPair,
> {
    pub(crate) helper_loop_opcode: Opcode,
    pub(crate) inspect_helper: InspectHelper,
    pub(crate) raw_pc_at: RawPcAt,
    pub(crate) jump_target: JumpTarget,
    pub(crate) ensure_targetable_pc: EnsureTargetable,
    pub(crate) next_raw_pc: NextRawPc,
    pub(crate) opcode_label: OpcodeLabel,
    pub(crate) validate_loop_base: ValidateLoopBase,
    pub(crate) build_pair: BuildPair,
}

pub(crate) struct GenericForPairAbxSpec<
    Opcode,
    InspectHelper,
    RawPcAt,
    JumpTarget,
    EnsureTargetable,
    NextRawPc,
    OpcodeLabel,
    ValidateLoopBase,
    BuildPair,
> {
    pub(crate) helper_loop_opcode: Opcode,
    pub(crate) inspect_helper: InspectHelper,
    pub(crate) raw_pc_at: RawPcAt,
    pub(crate) jump_target: JumpTarget,
    pub(crate) ensure_targetable_pc: EnsureTargetable,
    pub(crate) next_raw_pc: NextRawPc,
    pub(crate) opcode_label: OpcodeLabel,
    pub(crate) validate_loop_base: ValidateLoopBase,
    pub(crate) build_pair: BuildPair,
}

fn lookup_following_helper<'a, RawPcAt, MissingError>(
    raw: &'a RawProto,
    word_code_index: &WordCodeIndex,
    raw_index: usize,
    raw_pc_at: RawPcAt,
    missing_error: MissingError,
) -> Result<(u32, usize, &'a RawInstr), TransformError>
where
    RawPcAt: Fn(&RawInstr) -> u32,
    MissingError: FnOnce(u32) -> TransformError,
{
    let raw_pc = raw_pc_at(&raw.common.instructions[raw_index]);
    let helper_pc = raw_pc + 1;
    let Some(helper_index) = word_code_index.raw_index_at_pc(helper_pc) else {
        return Err(missing_error(raw_pc));
    };

    Ok((raw_pc, helper_index, &raw.common.instructions[helper_index]))
}

pub(crate) fn helper_jump_asbx<
    Opcode,
    InspectHelper,
    RawPcAt,
    JumpTarget,
    EnsureTargetable,
    NextRawPc,
    OpcodeLabel,
    CloseFrom,
>(
    raw: &RawProto,
    word_code_index: &WordCodeIndex,
    raw_index: usize,
    spec: HelperJumpAsbxSpec<
        Opcode,
        InspectHelper,
        RawPcAt,
        JumpTarget,
        EnsureTargetable,
        NextRawPc,
        OpcodeLabel,
        CloseFrom,
    >,
) -> Result<HelperJumpInfo, TransformError>
where
    Opcode: Copy + Eq,
    InspectHelper: Fn(&RawInstr) -> Result<(Opcode, u32, u8, i32), TransformError>,
    RawPcAt: Fn(&RawInstr) -> u32 + Copy,
    JumpTarget: Fn(u32, u32, i32) -> Result<usize, TransformError>,
    EnsureTargetable: Fn(u32, u32) -> Result<usize, TransformError>,
    NextRawPc: Fn(usize) -> u32,
    OpcodeLabel: Fn(Opcode) -> &'static str,
    CloseFrom: Fn(u8) -> Option<Reg>,
{
    let (raw_pc, helper_index, helper_instr) =
        lookup_following_helper(raw, word_code_index, raw_index, spec.raw_pc_at, |raw_pc| {
            TransformError::MissingHelperJump {
                raw_pc,
                opcode: (spec.opcode_label)(spec.owner_opcode),
            }
        })?;
    let (helper_opcode, helper_pc, a, helper_sbx) = (spec.inspect_helper)(helper_instr)?;
    if helper_opcode != spec.helper_jump_opcode {
        return Err(TransformError::InvalidHelperJump {
            raw_pc,
            helper_pc,
            found: (spec.opcode_label)(helper_opcode),
        });
    }

    Ok(HelperJumpInfo {
        helper_index,
        jump_target: (spec.jump_target)(helper_pc, helper_pc, helper_sbx)?,
        fallthrough_target: (spec.ensure_targetable_pc)(raw_pc, (spec.next_raw_pc)(helper_index))?,
        close_from: (spec.close_from)(a),
        next_index: helper_index + 1,
    })
}

pub(crate) fn helper_jump_asj<
    Opcode,
    InspectHelper,
    RawPcAt,
    JumpTarget,
    EnsureTargetable,
    NextRawPc,
    OpcodeLabel,
>(
    raw: &RawProto,
    word_code_index: &WordCodeIndex,
    raw_index: usize,
    spec: HelperJumpAsjSpec<
        Opcode,
        InspectHelper,
        RawPcAt,
        JumpTarget,
        EnsureTargetable,
        NextRawPc,
        OpcodeLabel,
    >,
) -> Result<HelperJumpInfo, TransformError>
where
    Opcode: Copy + Eq,
    InspectHelper: Fn(&RawInstr) -> Result<(Opcode, u32, i32), TransformError>,
    RawPcAt: Fn(&RawInstr) -> u32 + Copy,
    JumpTarget: Fn(u32, u32, i32) -> Result<usize, TransformError>,
    EnsureTargetable: Fn(u32, u32) -> Result<usize, TransformError>,
    NextRawPc: Fn(usize) -> u32,
    OpcodeLabel: Fn(Opcode) -> &'static str,
{
    let (raw_pc, helper_index, helper_instr) =
        lookup_following_helper(raw, word_code_index, raw_index, spec.raw_pc_at, |raw_pc| {
            TransformError::MissingHelperJump {
                raw_pc,
                opcode: (spec.opcode_label)(spec.owner_opcode),
            }
        })?;
    let (helper_opcode, helper_pc, helper_sj) = (spec.inspect_helper)(helper_instr)?;
    if helper_opcode != spec.helper_jump_opcode {
        return Err(TransformError::InvalidHelperJump {
            raw_pc,
            helper_pc,
            found: (spec.opcode_label)(helper_opcode),
        });
    }

    Ok(HelperJumpInfo {
        helper_index,
        jump_target: (spec.jump_target)(helper_pc, helper_pc, helper_sj)?,
        fallthrough_target: (spec.ensure_targetable_pc)(raw_pc, (spec.next_raw_pc)(helper_index))?,
        close_from: None,
        next_index: helper_index + 1,
    })
}

pub(crate) fn generic_for_pair_asbx<
    Opcode,
    InspectHelper,
    RawPcAt,
    JumpTarget,
    EnsureTargetable,
    NextRawPc,
    OpcodeLabel,
    ValidateLoopBase,
    BuildPair,
>(
    raw: &RawProto,
    word_code_index: &WordCodeIndex,
    raw_index: usize,
    call_a: u8,
    result_count: usize,
    spec: GenericForPairAsbxSpec<
        Opcode,
        InspectHelper,
        RawPcAt,
        JumpTarget,
        EnsureTargetable,
        NextRawPc,
        OpcodeLabel,
        ValidateLoopBase,
        BuildPair,
    >,
) -> Result<GenericForPairInfo, TransformError>
where
    Opcode: Copy + Eq,
    InspectHelper: Fn(&RawInstr) -> Result<(Opcode, u32, u8, i32), TransformError>,
    RawPcAt: Fn(&RawInstr) -> u32 + Copy,
    JumpTarget: Fn(u32, u32, i32) -> Result<usize, TransformError>,
    EnsureTargetable: Fn(u32, u32) -> Result<usize, TransformError>,
    NextRawPc: Fn(usize) -> u32,
    OpcodeLabel: Fn(Opcode) -> &'static str,
    ValidateLoopBase: Fn(u8, u8) -> bool,
    BuildPair: Fn(u8, usize) -> (Reg, RegRange),
{
    let (raw_pc, loop_index, helper_instr) =
        lookup_following_helper(raw, word_code_index, raw_index, spec.raw_pc_at, |raw_pc| {
            TransformError::MissingGenericForLoop { raw_pc }
        })?;
    let (helper_opcode, helper_pc, loop_a, helper_sbx) = (spec.inspect_helper)(helper_instr)?;
    if helper_opcode != spec.helper_loop_opcode {
        return Err(TransformError::InvalidGenericForLoop {
            raw_pc,
            helper_pc,
            found: (spec.opcode_label)(helper_opcode),
        });
    }
    if !(spec.validate_loop_base)(loop_a, call_a) {
        return Err(TransformError::InvalidGenericForPair {
            raw_pc,
            call_base: usize::from(call_a),
            loop_control: usize::from(loop_a),
        });
    }

    let (control, bindings) = (spec.build_pair)(loop_a, result_count);
    Ok(GenericForPairInfo {
        loop_index,
        control,
        bindings,
        body_target: (spec.jump_target)(helper_pc, helper_pc, helper_sbx)?,
        exit_target: (spec.ensure_targetable_pc)(raw_pc, (spec.next_raw_pc)(loop_index))?,
        next_index: loop_index + 1,
    })
}

pub(crate) fn generic_for_pair_abx<
    Opcode,
    InspectHelper,
    RawPcAt,
    JumpTarget,
    EnsureTargetable,
    NextRawPc,
    OpcodeLabel,
    ValidateLoopBase,
    BuildPair,
>(
    raw: &RawProto,
    word_code_index: &WordCodeIndex,
    raw_index: usize,
    call_a: u8,
    result_count: usize,
    spec: GenericForPairAbxSpec<
        Opcode,
        InspectHelper,
        RawPcAt,
        JumpTarget,
        EnsureTargetable,
        NextRawPc,
        OpcodeLabel,
        ValidateLoopBase,
        BuildPair,
    >,
) -> Result<GenericForPairInfo, TransformError>
where
    Opcode: Copy + Eq,
    InspectHelper: Fn(&RawInstr) -> Result<(Opcode, u32, u8, u32), TransformError>,
    RawPcAt: Fn(&RawInstr) -> u32 + Copy,
    JumpTarget: Fn(u32, u32, u32) -> Result<usize, TransformError>,
    EnsureTargetable: Fn(u32, u32) -> Result<usize, TransformError>,
    NextRawPc: Fn(usize) -> u32,
    OpcodeLabel: Fn(Opcode) -> &'static str,
    ValidateLoopBase: Fn(u8, u8) -> bool,
    BuildPair: Fn(u8, usize) -> (Reg, RegRange),
{
    let (raw_pc, loop_index, helper_instr) =
        lookup_following_helper(raw, word_code_index, raw_index, spec.raw_pc_at, |raw_pc| {
            TransformError::MissingGenericForLoop { raw_pc }
        })?;
    let (helper_opcode, helper_pc, loop_a, bx) = (spec.inspect_helper)(helper_instr)?;
    if helper_opcode != spec.helper_loop_opcode {
        return Err(TransformError::InvalidGenericForLoop {
            raw_pc,
            helper_pc,
            found: (spec.opcode_label)(helper_opcode),
        });
    }
    if !(spec.validate_loop_base)(loop_a, call_a) {
        return Err(TransformError::InvalidGenericForPair {
            raw_pc,
            call_base: usize::from(call_a),
            loop_control: usize::from(loop_a),
        });
    }

    let (control, bindings) = (spec.build_pair)(loop_a, result_count);
    Ok(GenericForPairInfo {
        loop_index,
        control,
        bindings,
        body_target: (spec.jump_target)(helper_pc, helper_pc, bx)?,
        exit_target: (spec.ensure_targetable_pc)(raw_pc, (spec.next_raw_pc)(loop_index))?,
        next_index: loop_index + 1,
    })
}

pub(crate) fn reg_from_u8(index: u8) -> Reg {
    Reg(index as usize)
}

pub(crate) fn close_from_raw_a(a: u8) -> Option<Reg> {
    (a != 0).then(|| Reg(usize::from(a - 1)))
}

pub(crate) fn reg_from_u16(index: u16) -> Reg {
    Reg(index as usize)
}

pub(crate) fn is_k(value: u16) -> bool {
    value & BITRK != 0
}

pub(crate) fn index_k(value: u16) -> usize {
    usize::from(value & !BITRK)
}

pub(crate) fn range_len_inclusive(start: usize, end: usize) -> usize {
    end.saturating_sub(start) + 1
}

pub(crate) fn numeric_for_regs(index: Reg, binding_offset: usize) -> NumericForRegs {
    NumericForRegs {
        index,
        limit: Reg(index.index() + 1),
        step: Reg(index.index() + 2),
        binding: Reg(index.index() + binding_offset),
    }
}

pub(crate) fn emit_call(
    lowering: &mut PendingLoweringState,
    raw_index: usize,
    callee: Reg,
    args: ValuePack,
    results: ResultPack,
    kind: CallKind,
) {
    lowering.emit(
        Some(raw_index),
        vec![raw_index],
        PendingLowInstr::Ready(LowInstr::Call(CallInstr {
            callee,
            args,
            results,
            kind,
        })),
    );
}

pub(crate) fn emit_tail_call(
    lowering: &mut PendingLoweringState,
    raw_index: usize,
    callee: Reg,
    args: ValuePack,
    kind: CallKind,
    close_before: bool,
) {
    if close_before {
        lowering.emit(
            Some(raw_index),
            vec![raw_index],
            PendingLowInstr::Ready(LowInstr::Close(CloseInstr { from: Reg(0) })),
        );
        lowering.emit(
            None,
            vec![raw_index],
            PendingLowInstr::Ready(LowInstr::TailCall(TailCallInstr { callee, args, kind })),
        );
    } else {
        lowering.emit(
            Some(raw_index),
            vec![raw_index],
            PendingLowInstr::Ready(LowInstr::TailCall(TailCallInstr { callee, args, kind })),
        );
    }
}

pub(crate) fn emit_return(
    lowering: &mut PendingLoweringState,
    raw_index: usize,
    values: ValuePack,
    close_before: bool,
) {
    if close_before {
        lowering.emit(
            Some(raw_index),
            vec![raw_index],
            PendingLowInstr::Ready(LowInstr::Close(CloseInstr { from: Reg(0) })),
        );
        lowering.emit(
            None,
            vec![raw_index],
            PendingLowInstr::Ready(LowInstr::Return(ReturnInstr { values })),
        );
    } else {
        lowering.emit(
            Some(raw_index),
            vec![raw_index],
            PendingLowInstr::Ready(LowInstr::Return(ReturnInstr { values })),
        );
    }
}

pub(crate) fn emit_numeric_for_loop(
    lowering: &mut PendingLoweringState,
    raw_index: usize,
    regs: NumericForRegs,
    body_target: usize,
    exit_target: usize,
) {
    lowering.emit(
        Some(raw_index),
        vec![raw_index],
        PendingLowInstr::NumericForLoop {
            index: regs.index,
            limit: regs.limit,
            step: regs.step,
            binding: regs.binding,
            body_target: TargetPlaceholder::Raw(body_target),
            exit_target: TargetPlaceholder::Raw(exit_target),
        },
    );
}

pub(crate) fn emit_numeric_for_init(
    lowering: &mut PendingLoweringState,
    raw_index: usize,
    regs: NumericForRegs,
    body_target: usize,
    exit_target: usize,
) {
    lowering.emit(
        Some(raw_index),
        vec![raw_index],
        PendingLowInstr::NumericForInit {
            index: regs.index,
            limit: regs.limit,
            step: regs.step,
            binding: regs.binding,
            body_target: TargetPlaceholder::Raw(body_target),
            exit_target: TargetPlaceholder::Raw(exit_target),
        },
    );
}

pub(crate) fn emit_generic_for_call(
    lowering: &mut PendingLoweringState,
    raw_index: usize,
    state_start: Reg,
    result_start_offset: usize,
    result_count: usize,
) {
    lowering.emit(
        Some(raw_index),
        vec![raw_index],
        PendingLowInstr::Ready(LowInstr::GenericForCall(GenericForCallInstr {
            state: RegRange::new(state_start, 3),
            results: ResultPack::Fixed(RegRange::new(
                Reg(state_start.index() + result_start_offset),
                result_count,
            )),
        })),
    );
}

pub(crate) fn emit_generic_for_loop(lowering: &mut PendingLoweringState, pair: GenericForPairInfo) {
    lowering.emit(
        Some(pair.loop_index),
        vec![pair.loop_index],
        PendingLowInstr::GenericForLoop {
            control: pair.control,
            bindings: pair.bindings,
            body_target: TargetPlaceholder::Raw(pair.body_target),
            exit_target: TargetPlaceholder::Raw(pair.exit_target),
        },
    );
}

pub(crate) fn emit_tforprep(
    lowering: &mut PendingLoweringState,
    raw_index: usize,
    tbc_reg: Reg,
    call_target: usize,
) {
    lowering.emit(
        Some(raw_index),
        vec![raw_index],
        PendingLowInstr::Ready(LowInstr::Tbc(TbcInstr { reg: tbc_reg })),
    );
    lowering.emit(
        None,
        vec![raw_index],
        PendingLowInstr::Jump {
            target: TargetPlaceholder::Raw(call_target),
        },
    );
}

pub(crate) fn call_args_pack(a: u8, b: u16) -> ValuePack {
    if b == 0 {
        ValuePack::Open(Reg(usize::from(a) + 1))
    } else {
        ValuePack::Fixed(RegRange::new(Reg(usize::from(a) + 1), usize::from(b - 1)))
    }
}

pub(crate) fn call_result_pack(a: u8, c: u16) -> ResultPack {
    match c {
        0 => ResultPack::Open(reg_from_u8(a)),
        1 => ResultPack::Ignore,
        _ => ResultPack::Fixed(RegRange::new(reg_from_u8(a), usize::from(c - 1))),
    }
}

pub(crate) fn return_pack(a: u8, b: u16) -> ValuePack {
    if b == 0 {
        ValuePack::Open(reg_from_u8(a))
    } else {
        ValuePack::Fixed(RegRange::new(reg_from_u8(a), usize::from(b - 1)))
    }
}

/// 共享 5.2+ PUC-Lua family 的 chunk 壳组装。
pub(crate) fn lower_chunk_with_env(
    chunk: &RawChunk,
    lower_proto: fn(&RawProto, Option<&[bool]>) -> Result<LoweredProto, TransformError>,
) -> Result<LoweredChunk, TransformError> {
    Ok(LoweredChunk {
        header: chunk.header.clone(),
        main: lower_proto(&chunk.main, None)?,
        origin: chunk.origin,
    })
}

/// 共享 `_ENV` 传播和子 proto 递归 lowering 骨架。
pub(crate) fn prepare_env_lowering(
    raw: &RawProto,
    parent_env_upvalues: Option<&[bool]>,
    lower_proto: fn(&RawProto, Option<&[bool]>) -> Result<LoweredProto, TransformError>,
) -> Result<(Vec<bool>, Vec<LoweredProto>), TransformError> {
    let env_upvalues = resolve_env_upvalues(raw, parent_env_upvalues);
    let children = raw
        .common
        .children
        .iter()
        .map(|child| lower_proto(child, Some(&env_upvalues)))
        .collect::<Result<Vec<_>, _>>()?;
    Ok((env_upvalues, children))
}

/// 共享 `LoweredProto` 组装壳，避免 5.2+ 每个版本重复复制元数据拼装代码。
pub(crate) fn finish_lowered_proto(
    raw: &RawProto,
    children: Vec<LoweredProto>,
    instrs: Vec<LowInstr>,
    lowering_map: LoweringMap,
) -> LoweredProto {
    LoweredProto {
        source: raw.common.source.clone(),
        line_range: raw.common.line_range,
        signature: raw.common.signature,
        frame: raw.common.frame,
        constants: raw.common.constants.clone(),
        upvalues: raw.common.upvalues.clone(),
        debug_info: raw.common.debug_info.clone(),
        children,
        instrs,
        lowering_map,
        origin: raw.origin,
    }
}

pub(crate) fn checked_const_ref(
    raw: &RawProto,
    raw_pc: u32,
    index: usize,
) -> Result<ConstRef, TransformError> {
    let const_count = raw.common.constants.common.literals.len();
    if index >= const_count {
        return Err(TransformError::InvalidConstRef {
            raw_pc,
            const_index: index,
            const_count,
        });
    }
    Ok(ConstRef(index))
}

pub(crate) fn checked_upvalue_ref(
    raw: &RawProto,
    raw_pc: u32,
    index: usize,
) -> Result<UpvalueRef, TransformError> {
    let upvalue_count = raw.common.upvalues.common.count as usize;
    if index >= upvalue_count {
        return Err(TransformError::InvalidUpvalueRef {
            raw_pc,
            upvalue_index: index,
            upvalue_count,
        });
    }
    Ok(UpvalueRef(index))
}

pub(crate) fn access_base_for_upvalue(
    raw: &RawProto,
    env_upvalues: &[bool],
    raw_pc: u32,
    index: usize,
) -> Result<AccessBase, TransformError> {
    let upvalue = checked_upvalue_ref(raw, raw_pc, index)?;
    Ok(if env_upvalues.get(index).copied().unwrap_or(false) {
        AccessBase::Env
    } else {
        AccessBase::Upvalue(upvalue)
    })
}

pub(crate) fn checked_proto_ref(
    raw: &RawProto,
    raw_pc: u32,
    index: usize,
) -> Result<ProtoRef, TransformError> {
    let child_count = raw.common.children.len();
    if index >= child_count {
        return Err(TransformError::InvalidProtoRef {
            raw_pc,
            proto_index: index,
            child_count,
        });
    }
    Ok(ProtoRef(index))
}

pub(crate) fn jump_target_forward_bx(
    word_code_index: &WordCodeIndex,
    raw_pc: u32,
    base_pc: u32,
    bx: u32,
) -> Result<usize, TransformError> {
    let target_pc = i64::from(base_pc) + 1 + i64::from(bx);
    word_code_index.ensure_valid_jump_pc(raw_pc, target_pc)
}
