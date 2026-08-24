//! 提供 PUC-Lua 寄存器/常量操作数、调用 pack、proto 组装和跳转边界辅助；依赖 parser raw proto 与 lowering state，不负责 opcode family 分派；例如解析 RK 常量、构造 open result pack 并校验 jump target。

use std::sync::Arc;

use super::*;

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

pub(crate) fn rk_value_operand(
    raw: &RawProto,
    raw_pc: u32,
    rk: u16,
) -> Result<ValueOperand, TransformError> {
    if is_k(rk) {
        Ok(ValueOperand::Const(checked_const_ref(
            raw,
            raw_pc,
            index_k(rk),
        )?))
    } else {
        Ok(ValueOperand::Reg(reg_from_u16(rk)))
    }
}

pub(crate) fn rk_access_key(
    raw: &RawProto,
    raw_pc: u32,
    rk: u16,
) -> Result<AccessKey, TransformError> {
    if is_k(rk) {
        Ok(AccessKey::Const(checked_const_ref(
            raw,
            raw_pc,
            index_k(rk),
        )?))
    } else {
        Ok(AccessKey::Reg(reg_from_u16(rk)))
    }
}

pub(crate) fn rk_cond_operand(
    raw: &RawProto,
    raw_pc: u32,
    rk: u16,
) -> Result<CondOperand, TransformError> {
    if is_k(rk) {
        Ok(CondOperand::Const(checked_const_ref(
            raw,
            raw_pc,
            index_k(rk),
        )?))
    } else {
        Ok(CondOperand::Reg(reg_from_u16(rk)))
    }
}

pub(crate) fn k_value_operand(
    raw: &RawProto,
    raw_pc: u32,
    operand: u8,
    k: bool,
) -> Result<ValueOperand, TransformError> {
    if k {
        Ok(ValueOperand::Const(checked_const_ref(
            raw,
            raw_pc,
            operand as usize,
        )?))
    } else {
        Ok(ValueOperand::Reg(reg_from_u8(operand)))
    }
}

pub(crate) fn immediate_cond_operand(operand: i16, is_float: bool) -> CondOperand {
    if is_float {
        CondOperand::Number(NumberLiteral::from_f64(f64::from(operand)))
    } else {
        CondOperand::Integer(i64::from(operand))
    }
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
    method_name: Option<MethodNameHint>,
) {
    lowering.emit(
        Some(raw_index),
        vec![raw_index],
        PendingLowInstr::Ready(LowInstr::Call(CallInstr {
            callee,
            args,
            results,
            kind,
            method_name,
        })),
    );
}

pub(crate) fn emit_tail_call(
    lowering: &mut PendingLoweringState,
    raw_index: usize,
    callee: Reg,
    args: ValuePack,
    kind: CallKind,
    method_name: Option<MethodNameHint>,
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
            PendingLowInstr::Ready(LowInstr::TailCall(TailCallInstr {
                callee,
                args,
                kind,
                method_name,
            })),
        );
    } else {
        lowering.emit(
            Some(raw_index),
            vec![raw_index],
            PendingLowInstr::Ready(LowInstr::TailCall(TailCallInstr {
                callee,
                args,
                kind,
                method_name,
            })),
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
    control_offset: usize,
    result_start_offset: usize,
    result_count: usize,
) {
    lowering.emit(
        Some(raw_index),
        vec![raw_index],
        PendingLowInstr::Ready(LowInstr::GenericForCall(GenericForCallInstr {
            iterator: state_start,
            state: Reg(state_start.index() + 1),
            control: Reg(state_start.index() + control_offset),
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
            control_target: pair.control,
            bindings: pair.bindings,
            body_target: TargetPlaceholder::Raw(pair.body_target),
            exit_target: TargetPlaceholder::Raw(pair.exit_target),
        },
    );
}

pub(crate) fn emit_generic_for_prep(
    lowering: &mut PendingLoweringState,
    raw_index: usize,
    prep: GenericForPrepInstr,
    call_target: usize,
) {
    lowering.emit(
        Some(raw_index),
        vec![raw_index],
        PendingLowInstr::Ready(LowInstr::GenericForPrep(prep)),
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
) -> Result<(Vec<bool>, Vec<Arc<LoweredProto>>), TransformError> {
    let env_upvalues = resolve_env_upvalues(raw, parent_env_upvalues);
    let children = raw
        .common
        .children
        .iter()
        .map(|child| lower_proto(child, Some(&env_upvalues)).map(Arc::new))
        .collect::<Result<Vec<_>, _>>()?;
    Ok((env_upvalues, children))
}

/// 共享 `LoweredProto` 组装壳，避免 5.2+ 每个版本重复复制元数据拼装代码。
pub(crate) fn finish_lowered_proto(
    raw: &RawProto,
    children: Vec<Arc<LoweredProto>>,
    instrs: Vec<LowInstr>,
    lowering_map: LoweringMap,
) -> LoweredProto {
    LoweredProto {
        source: raw.common.source.clone(),
        debug_name: raw.extra.luau().and_then(|extra| extra.debug_name.clone()),
        line_range: raw.common.line_range,
        signature: raw.common.signature,
        frame: raw.common.frame,
        constants: raw.common.constants.clone(),
        upvalues: raw.common.upvalues.clone(),
        debug_info: raw.common.debug_info.clone(),
        debug_locals: crate::transformer::common::normalize_debug_locals(raw),
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
    Ok(match upvalue_operand(raw, env_upvalues, raw_pc, index)? {
        UpvalueOperand::Env => AccessBase::Env,
        UpvalueOperand::Upvalue(upvalue) => AccessBase::Upvalue(upvalue),
    })
}

pub(crate) fn upvalue_operand(
    raw: &RawProto,
    env_upvalues: &[bool],
    raw_pc: u32,
    index: usize,
) -> Result<UpvalueOperand, TransformError> {
    let upvalue = checked_upvalue_ref(raw, raw_pc, index)?;
    Ok(if env_upvalues.get(index).copied().unwrap_or(false) {
        UpvalueOperand::Env
    } else {
        UpvalueOperand::Upvalue(upvalue)
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

pub(crate) fn jump_target_back_bx(
    word_code_index: &WordCodeIndex,
    raw_pc: u32,
    base_pc: u32,
    bx: u32,
) -> Result<usize, TransformError> {
    let target_pc = i64::from(base_pc) + 1 - i64::from(bx);
    word_code_index.ensure_valid_jump_pc(raw_pc, target_pc)
}

pub(crate) fn jump_target_sbx(
    word_code_index: &WordCodeIndex,
    raw_pc: u32,
    base_pc: u32,
    sbx: i32,
) -> Result<usize, TransformError> {
    let target_pc = i64::from(base_pc) + 1 + i64::from(sbx);
    word_code_index.ensure_valid_jump_pc(raw_pc, target_pc)
}

pub(crate) fn jump_target_sj(
    word_code_index: &WordCodeIndex,
    raw_pc: u32,
    base_pc: u32,
    sj: i32,
) -> Result<usize, TransformError> {
    let target_pc = i64::from(base_pc) + 1 + i64::from(sj);
    word_code_index.ensure_valid_jump_pc(raw_pc, target_pc)
}
