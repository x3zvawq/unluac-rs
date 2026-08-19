//! 这个模块承载 PUC-Lua 5.x lowering 之间共享的 helper。
//!
//! 这里同时挂载协议语义确实一致的 family lowerer；版本目录仍负责选择协议，
//! 共享实现只消费 parser 已经区分好的 typed raw 指令。

pub(crate) mod lua52_53;
pub(crate) mod lua54_55;

use crate::parser::{RawChunk, RawInstr, RawProto};
use crate::transformer::common::resolve_env_upvalues;
use crate::transformer::dialect::lowering::{
    PendingLowInstr, PendingLoweringState, TargetPlaceholder, WordCodeIndex,
};
use crate::transformer::{
    AccessBase, AccessKey, BinaryOpKind, CallInstr, CallKind, CloseInstr, CondOperand, ConstRef,
    GenericForCallInstr, GenericForPrepInstr, LowInstr, LoweredChunk, LoweredProto, LoweringMap,
    MethodNameHint, NumberLiteral, ProtoRef, Reg, RegRange, ResultPack, ReturnInstr, TailCallInstr,
    TransformError, UpvalueOperand, UpvalueRef, ValueOperand, ValuePack,
};

pub(crate) const BITRK: u16 = 1 << 8;
pub(crate) const LFIELDS_PER_FLUSH: u32 = 50;
const TM_ADD_EVENT: u8 = 6;

#[derive(Debug, Clone, Copy)]
pub(crate) struct BinaryHelperShape<Operand> {
    pub(crate) helper_index: usize,
    pub(crate) op: BinaryOpKind,
    pub(crate) operand: Operand,
    pub(crate) flipped: bool,
}

pub(crate) struct MetamethodBinarySpec<Opcode, InspectHelper, OpcodeLabel> {
    pub(crate) owner_opcode: Opcode,
    pub(crate) helper_opcode: Opcode,
    pub(crate) inspect_helper: InspectHelper,
    pub(crate) opcode_label: OpcodeLabel,
}

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

pub(crate) fn immediate_binary_shape<Opcode, InspectHelper, OpcodeLabel>(
    raw: &RawProto,
    word_code_index: &WordCodeIndex,
    raw_index: usize,
    encoded_op: BinaryOpKind,
    encoded_reg: u8,
    immediate: i16,
    spec: MetamethodBinarySpec<Opcode, InspectHelper, OpcodeLabel>,
) -> Result<BinaryHelperShape<i16>, TransformError>
where
    Opcode: Copy + Eq,
    InspectHelper: Fn(&RawInstr) -> Result<(Opcode, u32, u8, i16, u8, bool), TransformError>,
    OpcodeLabel: Fn(Opcode) -> &'static str,
{
    metamethod_binary_shape(
        raw,
        word_code_index,
        raw_index,
        encoded_reg,
        spec,
        |op, helper_immediate, flipped| {
            let same_immediate = i32::from(helper_immediate) == i32::from(immediate);
            let negated_immediate = i32::from(helper_immediate) == -i32::from(immediate);
            match (encoded_op, op, flipped) {
                (BinaryOpKind::Add, BinaryOpKind::Add, _) => same_immediate,
                (BinaryOpKind::Add, BinaryOpKind::Sub, false) => negated_immediate,
                (BinaryOpKind::Shl, BinaryOpKind::Shl, true) => same_immediate,
                (BinaryOpKind::Shr, BinaryOpKind::Shr, false) => same_immediate,
                (BinaryOpKind::Shr, BinaryOpKind::Shl, false) => negated_immediate,
                _ => false,
            }
        },
    )
}

pub(crate) fn constant_binary_shape<Opcode, InspectHelper, OpcodeLabel>(
    raw: &RawProto,
    word_code_index: &WordCodeIndex,
    raw_index: usize,
    op: BinaryOpKind,
    encoded_reg: u8,
    encoded_const: u8,
    spec: MetamethodBinarySpec<Opcode, InspectHelper, OpcodeLabel>,
) -> Result<BinaryHelperShape<u8>, TransformError>
where
    Opcode: Copy + Eq,
    InspectHelper: Fn(&RawInstr) -> Result<(Opcode, u32, u8, u8, u8, bool), TransformError>,
    OpcodeLabel: Fn(Opcode) -> &'static str,
{
    metamethod_binary_shape(
        raw,
        word_code_index,
        raw_index,
        encoded_reg,
        spec,
        |helper_op, helper_const, _flipped| helper_op == op && helper_const == encoded_const,
    )
}

pub(crate) fn register_binary_shape<Opcode, InspectHelper, OpcodeLabel>(
    raw: &RawProto,
    word_code_index: &WordCodeIndex,
    raw_index: usize,
    op: BinaryOpKind,
    encoded_lhs: u8,
    encoded_rhs: u8,
    spec: MetamethodBinarySpec<Opcode, InspectHelper, OpcodeLabel>,
) -> Result<BinaryHelperShape<u8>, TransformError>
where
    Opcode: Copy + Eq,
    InspectHelper: Fn(&RawInstr) -> Result<(Opcode, u32, u8, u8, u8, bool), TransformError>,
    OpcodeLabel: Fn(Opcode) -> &'static str,
{
    metamethod_binary_shape(
        raw,
        word_code_index,
        raw_index,
        encoded_lhs,
        spec,
        |helper_op, helper_rhs, flipped| helper_op == op && helper_rhs == encoded_rhs && !flipped,
    )
}

fn metamethod_binary_shape<Opcode, Operand, InspectHelper, OpcodeLabel, Validate>(
    raw: &RawProto,
    word_code_index: &WordCodeIndex,
    raw_index: usize,
    encoded_reg: u8,
    spec: MetamethodBinarySpec<Opcode, InspectHelper, OpcodeLabel>,
    validate: Validate,
) -> Result<BinaryHelperShape<Operand>, TransformError>
where
    Opcode: Copy + Eq,
    Operand: Copy,
    InspectHelper: Fn(&RawInstr) -> Result<(Opcode, u32, u8, Operand, u8, bool), TransformError>,
    OpcodeLabel: Fn(Opcode) -> &'static str,
    Validate: FnOnce(BinaryOpKind, Operand, bool) -> bool,
{
    let MetamethodBinarySpec {
        owner_opcode,
        helper_opcode,
        inspect_helper,
        opcode_label,
    } = spec;
    let owner_opcode_label = opcode_label(owner_opcode);
    let (raw_pc, helper_index, helper_instr) =
        lookup_following_helper(raw, word_code_index, raw_index, RawInstr::pc, |raw_pc| {
            TransformError::MissingMetamethodHelper {
                raw_pc,
                opcode: owner_opcode_label,
            }
        })?;
    let (found_opcode, helper_pc, helper_reg, operand, event, flipped) =
        inspect_helper(helper_instr)?;
    if found_opcode != helper_opcode {
        return Err(TransformError::InvalidMetamethodHelper {
            raw_pc,
            helper_pc,
            opcode: owner_opcode_label,
            found: opcode_label(found_opcode),
        });
    }
    let Some(op) = metamethod_event_op(event) else {
        return Err(inconsistent_metamethod_helper(
            raw_pc,
            helper_pc,
            owner_opcode_label,
        ));
    };
    if helper_reg != encoded_reg || !validate(op, operand, flipped) {
        return Err(inconsistent_metamethod_helper(
            raw_pc,
            helper_pc,
            owner_opcode_label,
        ));
    }

    Ok(BinaryHelperShape {
        helper_index,
        op,
        operand,
        flipped,
    })
}

fn inconsistent_metamethod_helper(
    raw_pc: u32,
    helper_pc: u32,
    opcode: &'static str,
) -> TransformError {
    TransformError::InconsistentMetamethodHelper {
        raw_pc,
        helper_pc,
        opcode,
    }
}

fn metamethod_event_op(event: u8) -> Option<BinaryOpKind> {
    match event.checked_sub(TM_ADD_EVENT)? {
        0 => Some(BinaryOpKind::Add),
        1 => Some(BinaryOpKind::Sub),
        2 => Some(BinaryOpKind::Mul),
        3 => Some(BinaryOpKind::Mod),
        4 => Some(BinaryOpKind::Pow),
        5 => Some(BinaryOpKind::Div),
        6 => Some(BinaryOpKind::FloorDiv),
        7 => Some(BinaryOpKind::BitAnd),
        8 => Some(BinaryOpKind::BitOr),
        9 => Some(BinaryOpKind::BitXor),
        10 => Some(BinaryOpKind::Shl),
        11 => Some(BinaryOpKind::Shr),
        _ => None,
    }
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

mod operands;
pub(crate) use operands::*;
