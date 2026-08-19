//! 这个文件唯一负责 Lua 5.4/5.5 共有的 low-IR lowering 语义。
//!
//! parser typed opcode 与 operand 宽度差异留给 adapter；这里统一处理
//! immediates、metamethod helper、close/TBC、for 布局、EXTRAARG 与调用协议。

use crate::parser::{RawChunk, RawInstr, RawProto};
use crate::transformer::dialect::lowering::{
    PendingLowInstr, PendingLoweringState, PendingMethodHints, TargetPlaceholder, WordCodeIndex,
    instr_pc, instr_word_len, next_raw_pc, raw_pc_at, resolve_pending_instr_with,
};
use crate::transformer::dialect::puc_lua::{
    GenericForPairAbxSpec, GenericForPairInfo as GenericForPair, HelperJumpAsjSpec,
    HelperJumpInfo as HelperJump, MetamethodBinarySpec,
    access_base_for_upvalue as shared_access_base_for_upvalue, call_args_pack, call_result_pack,
    checked_const_ref, checked_proto_ref, checked_upvalue_ref, constant_binary_shape, emit_call,
    emit_generic_for_call, emit_generic_for_loop, emit_generic_for_prep, emit_numeric_for_init,
    emit_numeric_for_loop, emit_return, emit_tail_call, finish_lowered_proto, generic_for_pair_abx,
    helper_jump_asj, immediate_binary_shape, immediate_cond_operand, jump_target_back_bx,
    jump_target_forward_bx, jump_target_sj, k_value_operand, lower_chunk_with_env,
    numeric_for_regs, prepare_env_lowering, range_len_inclusive, reg_from_u8,
    register_binary_shape, return_pack, upvalue_operand as shared_upvalue_operand,
};
use crate::transformer::operands::define_operand_expecters;
use crate::transformer::{
    AccessBase, AccessKey, BinaryOpInstr, BinaryOpKind, BranchCond, BranchPredicate, Capture,
    CaptureSource, CloseInstr, ClosureInstr, ConcatInstr, CondOperand, ConstRef, ErrNilInstr,
    GenericForPrepInstr, GetTableInstr, GetTableKind, GetUpvalueInstr, InstrRef, LoadBoolInstr,
    LoadConstInstr, LoadIntegerInstr, LoadNilInstr, LoadNumberInstr, LowInstr, LoweredChunk,
    LoweredProto, LoweringMap, MoveInstr, NewTableInstr, ProtoRef, Reg, RegRange, ResultPack,
    SetListInstr, SetTableInstr, SetTableKind, SetUpvalueInstr, TbcInstr, TransformError,
    UnaryOpInstr, UnaryOpKind, UpvalueRef, ValueOperand, ValuePack, VarArgInstr,
    instantiate_closure_children,
};

mod adapter;
mod boolean_load;
mod opcode;

pub(crate) use adapter::FamilyDialect;
use adapter::{FamilyOpcode, FamilyOperands, decode_instr};

pub(crate) fn lower_chunk(
    chunk: &RawChunk,
    dialect: FamilyDialect,
) -> Result<LoweredChunk, TransformError> {
    let lower_proto = match dialect {
        FamilyDialect::Lua54 => lower_lua54_proto,
        FamilyDialect::Lua55 => lower_lua55_proto,
    };
    lower_chunk_with_env(chunk, lower_proto)
}

fn lower_lua54_proto(
    raw: &RawProto,
    parent_env_upvalues: Option<&[bool]>,
) -> Result<LoweredProto, TransformError> {
    lower_proto(raw, parent_env_upvalues, FamilyDialect::Lua54)
}

fn lower_lua55_proto(
    raw: &RawProto,
    parent_env_upvalues: Option<&[bool]>,
) -> Result<LoweredProto, TransformError> {
    lower_proto(raw, parent_env_upvalues, FamilyDialect::Lua55)
}

fn lower_proto(
    raw: &RawProto,
    parent_env_upvalues: Option<&[bool]>,
    dialect: FamilyDialect,
) -> Result<LoweredProto, TransformError> {
    let child_lowerer = match dialect {
        FamilyDialect::Lua54 => lower_lua54_proto,
        FamilyDialect::Lua55 => lower_lua55_proto,
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
        let method_slots = usize::from(raw.common.frame.max_stack_size).saturating_add(4);
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

    fn access_key(&self, raw_pc: u32, operand: u8, k: bool) -> Result<AccessKey, TransformError> {
        if k {
            Ok(AccessKey::Const(self.const_ref(raw_pc, operand as usize)?))
        } else {
            Ok(AccessKey::Reg(reg_from_u8(operand)))
        }
    }

    fn table_operands(
        &self,
        raw_pc: u32,
        opcode: FamilyOpcode,
        operands: &FamilyOperands,
    ) -> Result<(u8, u8, u16, bool), TransformError> {
        match self.dialect {
            FamilyDialect::Lua54 => {
                let (a, b, c, k) = expect_abck(raw_pc, opcode, operands)?;
                Ok((a, b, u16::from(c), k))
            }
            FamilyDialect::Lua55 => expect_avbck(raw_pc, opcode, operands),
        }
    }

    fn ensure_targetable_pc(&self, raw_pc: u32, target_pc: u32) -> Result<usize, TransformError> {
        self.word_code_index.ensure_targetable_pc(raw_pc, target_pc)
    }

    fn helper_jump(
        &self,
        raw_index: usize,
        opcode: FamilyOpcode,
    ) -> Result<HelperJump, TransformError> {
        helper_jump_asj(
            self.raw,
            &self.word_code_index,
            raw_index,
            HelperJumpAsjSpec {
                owner_opcode: opcode,
                helper_jump_opcode: FamilyOpcode::Jmp,
                inspect_helper: match self.dialect {
                    FamilyDialect::Lua54 => inspect_lua54_asj_helper,
                    FamilyDialect::Lua55 => inspect_lua55_asj_helper,
                },
                raw_pc_at: instr_pc,
                jump_target: |raw_pc, base_pc, sj| {
                    jump_target_sj(&self.word_code_index, raw_pc, base_pc, sj)
                },
                ensure_targetable_pc: |raw_pc, target_pc| {
                    self.ensure_targetable_pc(raw_pc, target_pc)
                },
                next_raw_pc: |index| next_raw_pc(self.raw, index),
                opcode_label: FamilyOpcode::label,
            },
        )
    }

    fn generic_for_pair(
        &self,
        raw_index: usize,
        call_a: u8,
        result_count: u8,
    ) -> Result<GenericForPair, TransformError> {
        let binding_offset = self.dialect.generic_for_binding_offset();
        generic_for_pair_abx(
            self.raw,
            &self.word_code_index,
            raw_index,
            call_a,
            usize::from(result_count),
            GenericForPairAbxSpec {
                helper_loop_opcode: FamilyOpcode::TForLoop,
                inspect_helper: match self.dialect {
                    FamilyDialect::Lua54 => inspect_lua54_abx_helper,
                    FamilyDialect::Lua55 => inspect_lua55_abx_helper,
                },
                raw_pc_at: instr_pc,
                jump_target: |raw_pc, base_pc, bx| {
                    jump_target_back_bx(&self.word_code_index, raw_pc, base_pc, bx)
                },
                ensure_targetable_pc: |raw_pc, target_pc| {
                    self.ensure_targetable_pc(raw_pc, target_pc)
                },
                next_raw_pc: |index| next_raw_pc(self.raw, index),
                opcode_label: FamilyOpcode::label,
                validate_loop_base: |loop_a, call_a| loop_a == call_a,
                build_pair: |loop_a, result_count| {
                    (
                        Reg(usize::from(loop_a) + self.dialect.generic_for_control_offset()),
                        RegRange::new(Reg(usize::from(loop_a) + binding_offset), result_count),
                    )
                },
            },
        )
    }
}

fn inspect_lua54_asj_helper(raw: &RawInstr) -> Result<(FamilyOpcode, u32, i32), TransformError> {
    inspect_asj_helper(raw, FamilyDialect::Lua54)
}

fn inspect_lua55_asj_helper(raw: &RawInstr) -> Result<(FamilyOpcode, u32, i32), TransformError> {
    inspect_asj_helper(raw, FamilyDialect::Lua55)
}

fn inspect_asj_helper(
    raw: &RawInstr,
    dialect: FamilyDialect,
) -> Result<(FamilyOpcode, u32, i32), TransformError> {
    let extra = decode_instr(raw, dialect);
    let opcode = extra.opcode;
    let operands = &extra.operands;
    let sj = expect_asj(extra.pc, opcode, operands)?;
    Ok((opcode, extra.pc, sj))
}

fn inspect_lua54_abx_helper(
    raw: &RawInstr,
) -> Result<(FamilyOpcode, u32, u8, u32), TransformError> {
    inspect_abx_helper(raw, FamilyDialect::Lua54)
}

fn inspect_lua55_abx_helper(
    raw: &RawInstr,
) -> Result<(FamilyOpcode, u32, u8, u32), TransformError> {
    inspect_abx_helper(raw, FamilyDialect::Lua55)
}

fn inspect_abx_helper(
    raw: &RawInstr,
    dialect: FamilyDialect,
) -> Result<(FamilyOpcode, u32, u8, u32), TransformError> {
    let extra = decode_instr(raw, dialect);
    let opcode = extra.opcode;
    let operands = &extra.operands;
    let (a, bx) = expect_abx(extra.pc, opcode, operands)?;
    Ok((opcode, extra.pc, a, bx))
}

fn inspect_lua54_asbck_helper(
    raw: &RawInstr,
) -> Result<(FamilyOpcode, u32, u8, i16, u8, bool), TransformError> {
    inspect_asbck_helper(raw, FamilyDialect::Lua54)
}

fn inspect_lua55_asbck_helper(
    raw: &RawInstr,
) -> Result<(FamilyOpcode, u32, u8, i16, u8, bool), TransformError> {
    inspect_asbck_helper(raw, FamilyDialect::Lua55)
}

fn inspect_asbck_helper(
    raw: &RawInstr,
    dialect: FamilyDialect,
) -> Result<(FamilyOpcode, u32, u8, i16, u8, bool), TransformError> {
    let extra = decode_instr(raw, dialect);
    let opcode = extra.opcode;
    let operands = &extra.operands;
    let (a, sb, c, k) = expect_asbck(extra.pc, opcode, operands)?;
    Ok((opcode, extra.pc, a, sb, c, k))
}

fn inspect_lua54_abck_helper(
    raw: &RawInstr,
) -> Result<(FamilyOpcode, u32, u8, u8, u8, bool), TransformError> {
    inspect_abck_helper(raw, FamilyDialect::Lua54)
}

fn inspect_lua55_abck_helper(
    raw: &RawInstr,
) -> Result<(FamilyOpcode, u32, u8, u8, u8, bool), TransformError> {
    inspect_abck_helper(raw, FamilyDialect::Lua55)
}

fn inspect_abck_helper(
    raw: &RawInstr,
    dialect: FamilyDialect,
) -> Result<(FamilyOpcode, u32, u8, u8, u8, bool), TransformError> {
    let extra = decode_instr(raw, dialect);
    let opcode = extra.opcode;
    let operands = &extra.operands;
    let (a, b, c, k) = expect_abck(extra.pc, opcode, operands)?;
    Ok((opcode, extra.pc, a, b, c, k))
}

fn opcode_at(raw: &RawProto, index: usize, dialect: FamilyDialect) -> FamilyOpcode {
    decode_instr(&raw.common.instructions[index], dialect).opcode
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
        FamilyOpcode::AddI | FamilyOpcode::AddK | FamilyOpcode::Add => BinaryOpKind::Add,
        FamilyOpcode::SubK | FamilyOpcode::Sub => BinaryOpKind::Sub,
        FamilyOpcode::MulK | FamilyOpcode::Mul => BinaryOpKind::Mul,
        FamilyOpcode::DivK | FamilyOpcode::Div => BinaryOpKind::Div,
        FamilyOpcode::IdivK | FamilyOpcode::Idiv => BinaryOpKind::FloorDiv,
        FamilyOpcode::ModK | FamilyOpcode::Mod => BinaryOpKind::Mod,
        FamilyOpcode::PowK | FamilyOpcode::Pow => BinaryOpKind::Pow,
        FamilyOpcode::BandK | FamilyOpcode::Band => BinaryOpKind::BitAnd,
        FamilyOpcode::BorK | FamilyOpcode::Bor => BinaryOpKind::BitOr,
        FamilyOpcode::BxorK | FamilyOpcode::Bxor => BinaryOpKind::BitXor,
        FamilyOpcode::ShlI | FamilyOpcode::Shl => BinaryOpKind::Shl,
        FamilyOpcode::ShrI | FamilyOpcode::Shr => BinaryOpKind::Shr,
        _ => unreachable!("only arithmetic/bitwise opcodes should reach binary_op_kind"),
    }
}

fn branch_predicate(opcode: FamilyOpcode) -> BranchPredicate {
    match opcode {
        FamilyOpcode::Eq | FamilyOpcode::EqK | FamilyOpcode::EqI => BranchPredicate::Eq,
        FamilyOpcode::Lt | FamilyOpcode::LtI | FamilyOpcode::GtI => BranchPredicate::Lt,
        FamilyOpcode::Le | FamilyOpcode::LeI | FamilyOpcode::GeI => BranchPredicate::Le,
        _ => unreachable!("only compare opcodes should reach branch_predicate"),
    }
}

fn compare_immediate_shape(
    opcode: FamilyOpcode,
    reg: Reg,
    immediate: CondOperand,
) -> (BranchPredicate, CondOperand, CondOperand) {
    match opcode {
        FamilyOpcode::EqI | FamilyOpcode::LtI | FamilyOpcode::LeI => {
            (branch_predicate(opcode), CondOperand::Reg(reg), immediate)
        }
        FamilyOpcode::GtI => (BranchPredicate::Lt, immediate, CondOperand::Reg(reg)),
        FamilyOpcode::GeI => (BranchPredicate::Le, immediate, CondOperand::Reg(reg)),
        _ => unreachable!("only compare-immediate opcodes should reach compare_immediate_shape"),
    }
}

define_operand_expecters! {
    opcode = FamilyOpcode,
    operands = FamilyOperands,
    label = FamilyOpcode::label,
    fn expect_a("A") -> u8 {
        FamilyOperands::A { a } => *a
    }
    fn expect_ak("Ak") -> (u8, bool) {
        FamilyOperands::Ak { a, k } => (*a, *k)
    }
    fn expect_ab("AB") -> (u8, u8) {
        FamilyOperands::AB { a, b } => (*a, *b)
    }
    fn expect_ac("AC") -> (u8, u8) {
        FamilyOperands::AC { a, c } => (*a, *c)
    }
    fn expect_abc("ABC") -> (u8, u8, u8) {
        FamilyOperands::Abc { a, b, c } => (*a, *b, *c)
    }
    fn expect_abk("ABk") -> (u8, u8, bool) {
        FamilyOperands::ABk { a, b, k } => (*a, *b, *k)
    }
    fn expect_abck("ABCk") -> (u8, u8, u8, bool) {
        FamilyOperands::ABCk { a, b, c, k } => (*a, *b, *c, *k)
    }
    fn expect_abx("ABx") -> (u8, u32) {
        FamilyOperands::ABx { a, bx } => (*a, *bx)
    }
    fn expect_asbx("AsBx") -> (u8, i32) {
        FamilyOperands::AsBx { a, sbx } => (*a, *sbx)
    }
    fn expect_asj("AsJ") -> i32 {
        FamilyOperands::AsJ { sj } => *sj
    }
    fn expect_absck("ABsCk") -> (u8, u8, i16, bool) {
        FamilyOperands::ABsCk { a, b, sc, k } => (*a, *b, *sc, *k)
    }
    fn expect_asbck("AsBCk") -> (u8, i16, u8, bool) {
        FamilyOperands::AsBCk { a, sb, c, k } => (*a, *sb, *c, *k)
    }
    fn expect_avbck("AvBCk") -> (u8, u8, u16, bool) {
        FamilyOperands::AvBCk { a, vb, vc, k } => (*a, *vb, *vc, *k)
    }
}
