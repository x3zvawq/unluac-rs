//! 这个文件唯一负责 Lua 5.2/5.3 共有的 low-IR lowering 语义。
//! parser typed opcode 的差异留给 adapter；这里统一处理 EXTRAARG、环境、跳转和调用等共有协议。

use crate::parser::{RawChunk, RawInstr, RawProto};
use crate::transformer::dialect::lowering::{
    PendingLowInstr, PendingLoweringState, PendingMethodHints, TargetPlaceholder, WordCodeIndex,
    instr_pc, instr_word_len, next_raw_pc, raw_pc_at, resolve_pending_instr_with,
};
use crate::transformer::dialect::puc_lua::{
    GenericForPairAsbxSpec, GenericForPairInfo as GenericForPair, HelperJumpAsbxSpec,
    HelperJumpInfo as HelperJump, LFIELDS_PER_FLUSH,
    access_base_for_upvalue as shared_access_base_for_upvalue, call_args_pack, call_result_pack,
    checked_const_ref, checked_proto_ref, checked_upvalue_ref, close_from_raw_a, emit_call,
    emit_generic_for_call, emit_generic_for_loop, emit_numeric_for_init, emit_numeric_for_loop,
    emit_return, emit_tail_call, finish_lowered_proto, generic_for_pair_asbx, helper_jump_asbx,
    jump_target_sbx, lower_chunk_with_env, numeric_for_regs, prepare_env_lowering,
    range_len_inclusive, reg_from_u8, reg_from_u16, return_pack, rk_access_key, rk_cond_operand,
    rk_value_operand, upvalue_operand as shared_upvalue_operand,
};
use crate::transformer::operands::define_operand_expecters;
use crate::transformer::{
    AccessBase, BinaryOpInstr, BinaryOpKind, BranchCond, BranchPredicate, Capture, CaptureSource,
    CloseInstr, ClosureInstr, ConcatInstr, CondOperand, ConstRef, GetTableInstr, GetTableKind,
    GetUpvalueInstr, InstrRef, LoadBoolInstr, LoadConstInstr, LoadNilInstr, LowInstr, LoweredChunk,
    LoweredProto, LoweringMap, MoveInstr, NewTableInstr, ProtoRef, Reg, RegRange, ResultPack,
    SetListInstr, SetTableInstr, SetTableKind, SetUpvalueInstr, TransformError, UnaryOpInstr,
    UnaryOpKind, UpvalueRef, ValueOperand, ValuePack, VarArgInstr, instantiate_closure_children,
};

mod adapter;
mod opcode;

pub(crate) use adapter::FamilyDialect;
use adapter::{FamilyOpcode, FamilyOperands, decode_instr};

pub(crate) fn lower_chunk(
    chunk: &RawChunk,
    dialect: FamilyDialect,
) -> Result<LoweredChunk, TransformError> {
    let lower_proto = match dialect {
        FamilyDialect::Lua52 => lower_lua52_proto,
        FamilyDialect::Lua53 => lower_lua53_proto,
    };
    lower_chunk_with_env(chunk, lower_proto)
}

fn lower_lua52_proto(
    raw: &RawProto,
    parent_env_upvalues: Option<&[bool]>,
) -> Result<LoweredProto, TransformError> {
    lower_proto(raw, parent_env_upvalues, FamilyDialect::Lua52)
}

fn lower_lua53_proto(
    raw: &RawProto,
    parent_env_upvalues: Option<&[bool]>,
) -> Result<LoweredProto, TransformError> {
    lower_proto(raw, parent_env_upvalues, FamilyDialect::Lua53)
}

fn lower_proto(
    raw: &RawProto,
    parent_env_upvalues: Option<&[bool]>,
    dialect: FamilyDialect,
) -> Result<LoweredProto, TransformError> {
    let child_lowerer = match dialect {
        FamilyDialect::Lua52 => lower_lua52_proto,
        FamilyDialect::Lua53 => lower_lua53_proto,
    };
    let (env_upvalues, children) = prepare_env_lowering(raw, parent_env_upvalues, child_lowerer)?;
    let mut lowerer = ProtoLowerer::new(raw, env_upvalues, dialect);
    let (mut instrs, lowering_map) = lowerer.lower()?;
    let children = instantiate_closure_children(&mut instrs, children);

    Ok(finish_lowered_proto(raw, children, instrs, lowering_map))
}

struct ProtoLowerer<'a> {
    raw: &'a RawProto,
    dialect: FamilyDialect,
    env_upvalues: Vec<bool>,
    lowering: PendingLoweringState,
    pending_methods: PendingMethodHints,
    word_code_index: WordCodeIndex,
}

impl<'a> ProtoLowerer<'a> {
    fn new(raw: &'a RawProto, env_upvalues: Vec<bool>, dialect: FamilyDialect) -> Self {
        let raw_instr_count = raw.common.instructions.len();
        let method_slots = usize::from(raw.common.frame.max_stack_size).saturating_add(2);
        let word_code_index = WordCodeIndex::from_raw(raw, instr_pc, instr_word_len);

        Self {
            raw,
            dialect,
            env_upvalues,
            lowering: PendingLoweringState::new(raw_instr_count),
            pending_methods: PendingMethodHints::new(method_slots),
            word_code_index,
        }
    }

    fn finish(&self) -> Result<(Vec<LowInstr>, LoweringMap), TransformError> {
        self.lowering.finish(
            self.raw,
            |owner_raw, pending| self.resolve_pending_instr(owner_raw, pending),
            instr_pc,
            |raw_index| {
                let pc = raw_pc_at(self.raw, raw_index) as usize;
                self.raw.common.debug_info.common.line_info.get(pc).copied()
            },
        )
    }

    fn resolve_pending_instr(
        &self,
        owner_raw: usize,
        pending: &PendingLowInstr,
    ) -> Result<LowInstr, TransformError> {
        let owner_pc = raw_pc_at(self.raw, owner_raw);
        resolve_pending_instr_with(pending, |target| self.resolve_target(owner_pc, target))
    }

    fn resolve_target(
        &self,
        owner_pc: u32,
        target: TargetPlaceholder,
    ) -> Result<InstrRef, TransformError> {
        self.lowering.resolve_target(owner_pc, target, |raw_index| {
            raw_pc_at(self.raw, raw_index) as usize
        })
    }

    fn emit(
        &mut self,
        owner_raw: Option<usize>,
        raw_indices: Vec<usize>,
        instr: PendingLowInstr,
    ) -> usize {
        self.lowering.emit(owner_raw, raw_indices, instr)
    }

    fn const_ref(&self, raw_pc: u32, index: usize) -> Result<ConstRef, TransformError> {
        checked_const_ref(self.raw, raw_pc, index)
    }

    fn upvalue_ref(&self, raw_pc: u32, index: usize) -> Result<UpvalueRef, TransformError> {
        checked_upvalue_ref(self.raw, raw_pc, index)
    }

    fn proto_ref(&self, raw_pc: u32, index: usize) -> Result<ProtoRef, TransformError> {
        checked_proto_ref(self.raw, raw_pc, index)
    }

    fn extra_arg(
        &self,
        raw_pc: u32,
        opcode: FamilyOpcode,
        extra_arg: Option<u32>,
    ) -> Result<u32, TransformError> {
        extra_arg.ok_or(TransformError::MissingExtraArg {
            raw_pc,
            opcode: opcode.label(),
        })
    }

    fn ensure_targetable_pc(&self, raw_pc: u32, target_pc: u32) -> Result<usize, TransformError> {
        self.word_code_index.ensure_targetable_pc(raw_pc, target_pc)
    }

    fn helper_jump(
        &self,
        raw_index: usize,
        opcode: FamilyOpcode,
    ) -> Result<HelperJump, TransformError> {
        let inspect_helper = match self.dialect {
            FamilyDialect::Lua52 => inspect_lua52_asbx_helper,
            FamilyDialect::Lua53 => inspect_lua53_asbx_helper,
        };
        helper_jump_asbx(
            self.raw,
            &self.word_code_index,
            raw_index,
            HelperJumpAsbxSpec {
                owner_opcode: opcode,
                helper_jump_opcode: FamilyOpcode::Jmp,
                inspect_helper,
                raw_pc_at: instr_pc,
                jump_target: |raw_pc, base_pc, sbx| {
                    jump_target_sbx(&self.word_code_index, raw_pc, base_pc, sbx)
                },
                ensure_targetable_pc: |raw_pc, target_pc| {
                    self.ensure_targetable_pc(raw_pc, target_pc)
                },
                next_raw_pc: |index| next_raw_pc(self.raw, index),
                opcode_label: FamilyOpcode::label,
                close_from: close_from_raw_a,
            },
        )
    }

    fn generic_for_pair(
        &self,
        raw_index: usize,
        call_a: u8,
        result_count: u16,
    ) -> Result<GenericForPair, TransformError> {
        let inspect_helper = match self.dialect {
            FamilyDialect::Lua52 => inspect_lua52_asbx_helper,
            FamilyDialect::Lua53 => inspect_lua53_asbx_helper,
        };
        generic_for_pair_asbx(
            self.raw,
            &self.word_code_index,
            raw_index,
            call_a,
            usize::from(result_count),
            GenericForPairAsbxSpec {
                helper_loop_opcode: FamilyOpcode::TForLoop,
                inspect_helper,
                raw_pc_at: instr_pc,
                jump_target: |raw_pc, base_pc, sbx| {
                    jump_target_sbx(&self.word_code_index, raw_pc, base_pc, sbx)
                },
                ensure_targetable_pc: |raw_pc, target_pc| {
                    self.ensure_targetable_pc(raw_pc, target_pc)
                },
                next_raw_pc: |index| next_raw_pc(self.raw, index),
                opcode_label: FamilyOpcode::label,
                validate_loop_base: |loop_a, call_a| usize::from(loop_a) == usize::from(call_a) + 2,
                build_pair: |loop_a, result_count| {
                    let control = reg_from_u8(loop_a);
                    (
                        control,
                        RegRange::new(Reg(control.index() + 1), result_count),
                    )
                },
            },
        )
    }
}

fn opcode_at(raw: &RawProto, index: usize, dialect: FamilyDialect) -> FamilyOpcode {
    decode_instr(&raw.common.instructions[index], dialect).opcode
}

fn inspect_family_asbx_helper(
    raw: &RawInstr,
    dialect: FamilyDialect,
) -> Result<(FamilyOpcode, u32, u8, i32), TransformError> {
    let decoded = decode_instr(raw, dialect);
    let (a, sbx) = expect_asbx(decoded.pc, decoded.opcode, &decoded.operands)?;
    Ok((decoded.opcode, decoded.pc, a, sbx))
}

fn inspect_lua52_asbx_helper(
    raw: &RawInstr,
) -> Result<(FamilyOpcode, u32, u8, i32), TransformError> {
    inspect_family_asbx_helper(raw, FamilyDialect::Lua52)
}

fn inspect_lua53_asbx_helper(
    raw: &RawInstr,
) -> Result<(FamilyOpcode, u32, u8, i32), TransformError> {
    inspect_family_asbx_helper(raw, FamilyDialect::Lua53)
}

fn unary_op_kind(opcode: FamilyOpcode) -> UnaryOpKind {
    match opcode {
        FamilyOpcode::Unm => UnaryOpKind::Neg,
        FamilyOpcode::BNot => UnaryOpKind::BitNot,
        FamilyOpcode::Not => UnaryOpKind::Not,
        FamilyOpcode::Len => UnaryOpKind::Length,
        _ => unreachable!("only unary opcodes should reach unary_op_kind"),
    }
}

fn binary_op_kind(opcode: FamilyOpcode) -> BinaryOpKind {
    match opcode {
        FamilyOpcode::Add => BinaryOpKind::Add,
        FamilyOpcode::Sub => BinaryOpKind::Sub,
        FamilyOpcode::Mul => BinaryOpKind::Mul,
        FamilyOpcode::Div => BinaryOpKind::Div,
        FamilyOpcode::Idiv => BinaryOpKind::FloorDiv,
        FamilyOpcode::Mod => BinaryOpKind::Mod,
        FamilyOpcode::Pow => BinaryOpKind::Pow,
        FamilyOpcode::Band => BinaryOpKind::BitAnd,
        FamilyOpcode::Bor => BinaryOpKind::BitOr,
        FamilyOpcode::Bxor => BinaryOpKind::BitXor,
        FamilyOpcode::Shl => BinaryOpKind::Shl,
        FamilyOpcode::Shr => BinaryOpKind::Shr,
        _ => unreachable!("only arithmetic/bitwise opcodes should reach binary_op_kind"),
    }
}

fn branch_predicate(opcode: FamilyOpcode) -> BranchPredicate {
    match opcode {
        FamilyOpcode::Eq => BranchPredicate::Eq,
        FamilyOpcode::Lt => BranchPredicate::Lt,
        FamilyOpcode::Le => BranchPredicate::Le,
        _ => unreachable!("only compare opcodes should reach branch_predicate"),
    }
}

define_operand_expecters! {
    opcode = FamilyOpcode,
    operands = FamilyOperands,
    label = FamilyOpcode::label,
    fn expect_a("A") -> u8 {
        FamilyOperands::A { a } => *a
    }
    fn expect_ab("AB") -> (u8, u16) {
        FamilyOperands::AB { a, b } => (*a, *b)
    }
    fn expect_ac("AC") -> (u8, u16) {
        FamilyOperands::AC { a, c } => (*a, *c)
    }
    fn expect_abc("ABC") -> (u8, u16, u16) {
        FamilyOperands::Abc { a, b, c } => (*a, *b, *c)
    }
    fn expect_abx("ABx") -> (u8, u32) {
        FamilyOperands::ABx { a, bx } => (*a, *bx)
    }
    fn expect_asbx("AsBx") -> (u8, i32) {
        FamilyOperands::AsBx { a, sbx } => (*a, *sbx)
    }
}
