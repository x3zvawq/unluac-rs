//! 这个文件实现 Lua 5.5 到统一 low-IR 的 lowering。
//!
//! 相比 5.3，这里除了延续 `_ENV/upvalue table` 识别、`LOADKX/EXTRAARG` 这类路径外，
//! 还需要显式处理 5.4 新增的 immediates、整数 key、`RETURN/TAILCALL` close 语义、
//! `LFALSESKIP` 布尔物化，以及 `TFORPREP` 带来的额外控制流节点。

use crate::parser::{Lua55Opcode, Lua55Operands, RawChunk, RawInstr, RawProto};
use crate::transformer::dialect::lowering::{
    PendingLowInstr, PendingLoweringState, PendingMethodHints, TargetPlaceholder, WordCodeIndex,
    instr_pc, instr_word_len, resolve_pending_instr_with,
};
use crate::transformer::dialect::puc_lua::{
    GenericForPairAbxSpec, GenericForPairInfo as GenericForPair, HelperJumpAsjSpec,
    HelperJumpInfo as HelperJump, access_base_for_upvalue as shared_access_base_for_upvalue,
    call_args_pack, call_result_pack, checked_const_ref, checked_proto_ref, checked_upvalue_ref,
    emit_call, emit_generic_for_call, emit_generic_for_loop, emit_numeric_for_init,
    emit_numeric_for_loop, emit_return, emit_tail_call, emit_tforprep, finish_lowered_proto,
    generic_for_pair_abx, helper_jump_asj, jump_target_forward_bx, lower_chunk_with_env,
    numeric_for_regs, prepare_env_lowering, range_len_inclusive, reg_from_u8, return_pack,
};
use crate::transformer::operands::define_operand_expecters;
use crate::transformer::{
    AccessBase, AccessKey, BinaryOpInstr, BinaryOpKind, BranchCond, BranchOperands,
    BranchPredicate, CallKind, Capture, CaptureSource, CloseInstr, ClosureInstr, ConcatInstr,
    CondOperand, ConstRef, DialectCaptureExtra, ErrNilInstr, GetTableInstr, GetUpvalueInstr,
    InstrRef, LoadBoolInstr, LoadConstInstr, LoadIntegerInstr, LoadNilInstr, LoadNumberInstr,
    LowInstr, LoweredChunk, LoweredProto, LoweringMap, MoveInstr, NewTableInstr, NumberLiteral,
    ProtoRef, Reg, RegRange, ResultPack, SetListInstr, SetTableInstr, SetUpvalueInstr, TbcInstr,
    TransformError, UnaryOpInstr, UnaryOpKind, UpvalueRef, ValueOperand, ValuePack, VarArgInstr,
};

const EXTRAARG_SCALE_10: u32 = 1_u32 << 10;

pub(crate) fn lower_chunk(chunk: &RawChunk) -> Result<LoweredChunk, TransformError> {
    lower_chunk_with_env(chunk, lower_proto)
}

fn lower_proto(
    raw: &RawProto,
    parent_env_upvalues: Option<&[bool]>,
) -> Result<LoweredProto, TransformError> {
    let (env_upvalues, children) = prepare_env_lowering(raw, parent_env_upvalues, lower_proto)?;
    let mut lowerer = ProtoLowerer::new(raw, env_upvalues);
    let (instrs, lowering_map) = lowerer.lower()?;

    Ok(finish_lowered_proto(raw, children, instrs, lowering_map))
}

struct ProtoLowerer<'a> {
    raw: &'a RawProto,
    env_upvalues: Vec<bool>,
    lowering: PendingLoweringState,
    pending_methods: PendingMethodHints,
    word_code_index: WordCodeIndex,
}

impl<'a> ProtoLowerer<'a> {
    fn new(raw: &'a RawProto, env_upvalues: Vec<bool>) -> Self {
        let raw_instr_count = raw.common.instructions.len();
        let method_slots = usize::from(raw.common.frame.max_stack_size).saturating_add(4);
        let word_code_index = WordCodeIndex::from_raw(raw, instr_pc, instr_word_len);

        Self {
            raw,
            env_upvalues,
            lowering: PendingLoweringState::new(raw_instr_count),
            pending_methods: PendingMethodHints::new(method_slots),
            word_code_index,
        }
    }

    fn lower(&mut self) -> Result<(Vec<LowInstr>, LoweringMap), TransformError> {
        let mut raw_index = 0_usize;

        while raw_index < self.raw.common.instructions.len() {
            let raw_instr = &self.raw.common.instructions[raw_index];
            let (opcode, operands, extra) = raw_instr
                .lua55()
                .expect("lua55 lowerer should only decode lua55 instructions");
            let raw_pc = extra.pc;

            match opcode {
                Lua55Opcode::Move => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Move(MoveInstr {
                            dst,
                            src: reg_from_u8(b),
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::LoadI => {
                    let (a, sbx) = expect_asbx(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadInteger(LoadIntegerInstr {
                            dst,
                            value: i64::from(sbx),
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::LoadF => {
                    let (a, sbx) = expect_asbx(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadNumber(LoadNumberInstr {
                            dst,
                            value: f64::from(sbx),
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::LoadK => {
                    let (a, bx) = expect_abx(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadConst(LoadConstInstr {
                            dst,
                            value: self.const_ref(raw_pc, bx as usize)?,
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::LoadKx => {
                    let a = expect_a(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadConst(LoadConstInstr {
                            dst,
                            value: self.const_ref(
                                raw_pc,
                                self.extra_arg(raw_pc, opcode, extra.extra_arg)? as usize,
                            )?,
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::LoadFalse => {
                    let a = expect_a(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadBool(LoadBoolInstr {
                            dst,
                            value: false,
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::LFalseSkip => {
                    let a = expect_a(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadBool(LoadBoolInstr {
                            dst,
                            value: false,
                        })),
                    );
                    self.clear_all_method_hints();
                    self.emit(
                        None,
                        vec![raw_index],
                        PendingLowInstr::Jump {
                            target: TargetPlaceholder::Raw(
                                self.ensure_targetable_pc(raw_pc, raw_pc + 2)?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                Lua55Opcode::LoadTrue => {
                    let a = expect_a(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadBool(LoadBoolInstr {
                            dst,
                            value: true,
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::LoadNil => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    let len = range_len_inclusive(usize::from(a), usize::from(a) + usize::from(b));
                    let dst = RegRange::new(reg_from_u8(a), len);
                    self.invalidate_written_range(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadNil(LoadNilInstr { dst })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::GetUpVal => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetUpvalue(GetUpvalueInstr {
                            dst,
                            src: self.upvalue_ref(raw_pc, b as usize)?,
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::GetTabUp => {
                    let (a, b, c, _) = expect_abck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst,
                            base: shared_access_base_for_upvalue(
                                self.raw,
                                &self.env_upvalues,
                                raw_pc,
                                b as usize,
                            )?,
                            key: AccessKey::Const(self.const_ref(raw_pc, c as usize)?),
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::GetTable => {
                    let (a, b, c, _) = expect_abck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst,
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Reg(reg_from_u8(c)),
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::GetI => {
                    let (a, b, c, _) = expect_abck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst,
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Integer(i64::from(c)),
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::GetField => {
                    let (a, b, c, _) = expect_abck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst,
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Const(self.const_ref(raw_pc, c as usize)?),
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::GetVarg => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst,
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Reg(reg_from_u8(c)),
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::SetTabUp => {
                    let (a, b, c, k) = expect_abck(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: shared_access_base_for_upvalue(
                                self.raw,
                                &self.env_upvalues,
                                raw_pc,
                                a as usize,
                            )?,
                            key: AccessKey::Const(self.const_ref(raw_pc, b as usize)?),
                            value: self.value_operand(raw_pc, c, k)?,
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::SetUpVal => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetUpvalue(SetUpvalueInstr {
                            dst: self.upvalue_ref(raw_pc, b as usize)?,
                            src: reg_from_u8(a),
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::SetTable => {
                    let (a, b, c, k) = expect_abck(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Reg(reg_from_u8(a)),
                            key: AccessKey::Reg(reg_from_u8(b)),
                            value: self.value_operand(raw_pc, c, k)?,
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::SetI => {
                    let (a, b, c, k) = expect_abck(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Reg(reg_from_u8(a)),
                            key: AccessKey::Integer(i64::from(b)),
                            value: self.value_operand(raw_pc, c, k)?,
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::SetField => {
                    let (a, b, c, k) = expect_abck(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Reg(reg_from_u8(a)),
                            key: AccessKey::Const(self.const_ref(raw_pc, b as usize)?),
                            value: self.value_operand(raw_pc, c, k)?,
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::ErrNNil => {
                    let (a, bx) = expect_abx(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::ErrNil(ErrNilInstr {
                            subject: reg_from_u8(a),
                            name: if bx == 0 {
                                None
                            } else {
                                Some(self.const_ref(raw_pc, (bx - 1) as usize)?)
                            },
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::NewTable => {
                    let (a, _, _, _) = expect_avbck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::NewTable(NewTableInstr { dst })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::Self_ => {
                    let (a, b, c, _k) = expect_abck(raw_pc, opcode, operands)?;
                    let callee = reg_from_u8(a);
                    let self_arg = Reg(callee.index() + 1);
                    let method_name = self.const_ref(raw_pc, c as usize)?;
                    self.invalidate_written_reg(callee);
                    self.invalidate_written_reg(self_arg);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Move(MoveInstr {
                            dst: self_arg,
                            src: reg_from_u8(b),
                        })),
                    );
                    self.emit(
                        None,
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst: callee,
                            base: AccessBase::Reg(reg_from_u8(b)),
                            // Lua 5.5 的 `SELF` 沿用了 ABCk 外壳，但字段名仍然总是来自
                            // 常量表；`luac -l` 也会直接把第三操作数解读成常量索引，
                            // 不再像 5.4 那样依赖显式 `k` 标记。
                            // 这里如果继续复用通用 `access_key(c, k)`，像 `obj:next()`
                            // 这样的调用就会被误降成 `obj[rX]()`，后面整个 method/
                            // field 恢复都会跑偏。
                            key: AccessKey::Const(method_name),
                        })),
                    );
                    self.set_pending_method(callee, self_arg, Some(method_name));
                    raw_index += 1;
                }
                Lua55Opcode::AddI => {
                    let (a, b, sc, _) = expect_absck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::BinaryOp(BinaryOpInstr {
                            dst,
                            op: BinaryOpKind::Add,
                            lhs: ValueOperand::Reg(reg_from_u8(b)),
                            rhs: ValueOperand::Integer(i64::from(sc)),
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::AddK
                | Lua55Opcode::SubK
                | Lua55Opcode::MulK
                | Lua55Opcode::ModK
                | Lua55Opcode::PowK
                | Lua55Opcode::DivK
                | Lua55Opcode::IdivK
                | Lua55Opcode::BandK
                | Lua55Opcode::BorK
                | Lua55Opcode::BxorK => {
                    let (a, b, c, _) = expect_abck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::BinaryOp(BinaryOpInstr {
                            dst,
                            op: binary_op_kind(opcode),
                            lhs: ValueOperand::Reg(reg_from_u8(b)),
                            rhs: ValueOperand::Const(self.const_ref(raw_pc, c as usize)?),
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::ShrI | Lua55Opcode::ShlI => {
                    let (a, b, sc, _) = expect_absck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    let (lhs, rhs) = match opcode {
                        Lua55Opcode::ShrI => (
                            ValueOperand::Reg(reg_from_u8(b)),
                            ValueOperand::Integer(i64::from(sc)),
                        ),
                        Lua55Opcode::ShlI => (
                            ValueOperand::Integer(i64::from(sc)),
                            ValueOperand::Reg(reg_from_u8(b)),
                        ),
                        _ => unreachable!("only shift-immediate opcodes should reach this branch"),
                    };
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::BinaryOp(BinaryOpInstr {
                            dst,
                            op: binary_op_kind(opcode),
                            lhs,
                            rhs,
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::Add
                | Lua55Opcode::Sub
                | Lua55Opcode::Mul
                | Lua55Opcode::Mod
                | Lua55Opcode::Pow
                | Lua55Opcode::Div
                | Lua55Opcode::Idiv
                | Lua55Opcode::Band
                | Lua55Opcode::Bor
                | Lua55Opcode::Bxor
                | Lua55Opcode::Shl
                | Lua55Opcode::Shr => {
                    let (a, b, c, _) = expect_abck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::BinaryOp(BinaryOpInstr {
                            dst,
                            op: binary_op_kind(opcode),
                            lhs: ValueOperand::Reg(reg_from_u8(b)),
                            rhs: ValueOperand::Reg(reg_from_u8(c)),
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::MMBin | Lua55Opcode::MMBinI | Lua55Opcode::MMBinK => {
                    raw_index += 1;
                }
                Lua55Opcode::Unm | Lua55Opcode::BNot | Lua55Opcode::Not | Lua55Opcode::Len => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::UnaryOp(UnaryOpInstr {
                            dst,
                            op: unary_op_kind(opcode),
                            src: reg_from_u8(b),
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::Concat => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Concat(ConcatInstr {
                            dst,
                            src: RegRange::new(reg_from_u8(a), usize::from(b)),
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::Close => {
                    self.clear_all_method_hints();
                    let a = expect_a(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Close(CloseInstr {
                            from: reg_from_u8(a),
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::Tbc => {
                    let a = expect_a(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Tbc(TbcInstr {
                            reg: reg_from_u8(a),
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::Jmp => {
                    self.clear_all_method_hints();
                    let sj = expect_asj(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Jump {
                            target: TargetPlaceholder::Raw(
                                self.jump_target_sj(raw_pc, extra.pc, sj)?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                Lua55Opcode::Eq | Lua55Opcode::Lt | Lua55Opcode::Le => {
                    self.clear_all_method_hints();
                    let (a, b, k) = expect_abk(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let cond = BranchCond {
                        predicate: branch_predicate(opcode),
                        operands: BranchOperands::Binary(
                            CondOperand::Reg(reg_from_u8(a)),
                            CondOperand::Reg(reg_from_u8(b)),
                        ),
                        negated: !k,
                    };

                    self.emit(
                        Some(raw_index),
                        vec![raw_index, helper.helper_index],
                        PendingLowInstr::Branch {
                            cond,
                            then_target: TargetPlaceholder::Raw(helper.jump_target),
                            else_target: TargetPlaceholder::Raw(helper.fallthrough_target),
                        },
                    );
                    raw_index = helper.next_index;
                }
                Lua55Opcode::EqK => {
                    self.clear_all_method_hints();
                    let (a, b, k) = expect_abk(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let cond = BranchCond {
                        predicate: BranchPredicate::Eq,
                        operands: BranchOperands::Binary(
                            CondOperand::Reg(reg_from_u8(a)),
                            CondOperand::Const(self.const_ref(raw_pc, b as usize)?),
                        ),
                        negated: !k,
                    };

                    self.emit(
                        Some(raw_index),
                        vec![raw_index, helper.helper_index],
                        PendingLowInstr::Branch {
                            cond,
                            then_target: TargetPlaceholder::Raw(helper.jump_target),
                            else_target: TargetPlaceholder::Raw(helper.fallthrough_target),
                        },
                    );
                    raw_index = helper.next_index;
                }
                Lua55Opcode::EqI
                | Lua55Opcode::LtI
                | Lua55Opcode::LeI
                | Lua55Opcode::GtI
                | Lua55Opcode::GeI => {
                    self.clear_all_method_hints();
                    let (a, sb, c, k) = expect_asbck(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let rhs = self.compare_immediate(sb, c != 0);
                    let (predicate, lhs, rhs) =
                        compare_immediate_shape(opcode, reg_from_u8(a), rhs);
                    let cond = BranchCond {
                        predicate,
                        operands: BranchOperands::Binary(lhs, rhs),
                        negated: !k,
                    };

                    self.emit(
                        Some(raw_index),
                        vec![raw_index, helper.helper_index],
                        PendingLowInstr::Branch {
                            cond,
                            then_target: TargetPlaceholder::Raw(helper.jump_target),
                            else_target: TargetPlaceholder::Raw(helper.fallthrough_target),
                        },
                    );
                    raw_index = helper.next_index;
                }
                Lua55Opcode::Test => {
                    self.clear_all_method_hints();
                    let (a, k) = expect_ak(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let cond = BranchCond {
                        predicate: BranchPredicate::Truthy,
                        operands: BranchOperands::Unary(CondOperand::Reg(reg_from_u8(a))),
                        negated: !k,
                    };

                    self.emit(
                        Some(raw_index),
                        vec![raw_index, helper.helper_index],
                        PendingLowInstr::Branch {
                            cond,
                            then_target: TargetPlaceholder::Raw(helper.jump_target),
                            else_target: TargetPlaceholder::Raw(helper.fallthrough_target),
                        },
                    );
                    raw_index = helper.next_index;
                }
                Lua55Opcode::TestSet => {
                    self.clear_all_method_hints();
                    let (a, b, k) = expect_abk(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let cond = BranchCond {
                        predicate: BranchPredicate::Truthy,
                        operands: BranchOperands::Unary(CondOperand::Reg(reg_from_u8(b))),
                        negated: !k,
                    };

                    if a == b {
                        self.emit(
                            Some(raw_index),
                            vec![raw_index, helper.helper_index],
                            PendingLowInstr::Branch {
                                cond,
                                then_target: TargetPlaceholder::Raw(helper.jump_target),
                                else_target: TargetPlaceholder::Raw(helper.fallthrough_target),
                            },
                        );
                    } else {
                        let move_low = self.lowering.next_low_index();
                        self.emit(
                            Some(raw_index),
                            vec![raw_index, helper.helper_index],
                            PendingLowInstr::Branch {
                                cond,
                                then_target: TargetPlaceholder::Low(move_low),
                                else_target: TargetPlaceholder::Raw(helper.fallthrough_target),
                            },
                        );
                        self.emit(
                            None,
                            vec![raw_index],
                            PendingLowInstr::Ready(LowInstr::Move(MoveInstr {
                                dst: reg_from_u8(a),
                                src: reg_from_u8(b),
                            })),
                        );
                        self.emit(
                            None,
                            vec![raw_index, helper.helper_index],
                            PendingLowInstr::Jump {
                                target: TargetPlaceholder::Raw(helper.jump_target),
                            },
                        );
                    }

                    raw_index = helper.next_index;
                }
                Lua55Opcode::Call => {
                    let (a, b, c, _) = expect_abck(raw_pc, opcode, operands)?;
                    let (kind, method_name) = self.take_call_info(reg_from_u8(a), u16::from(b));
                    self.clear_all_method_hints();
                    emit_call(
                        &mut self.lowering,
                        raw_index,
                        reg_from_u8(a),
                        call_args_pack(a, u16::from(b)),
                        call_result_pack(a, u16::from(c)),
                        kind,
                        method_name,
                    );
                    raw_index += 1;
                }
                Lua55Opcode::TailCall => {
                    let (a, b, _, k) = expect_abck(raw_pc, opcode, operands)?;
                    let (kind, method_name) = self.take_call_info(reg_from_u8(a), u16::from(b));
                    self.clear_all_method_hints();
                    emit_tail_call(
                        &mut self.lowering,
                        raw_index,
                        reg_from_u8(a),
                        call_args_pack(a, u16::from(b)),
                        kind,
                        method_name,
                        k,
                    );
                    raw_index += 1;
                }
                Lua55Opcode::Return => {
                    let (a, b, _, k) = expect_abck(raw_pc, opcode, operands)?;
                    self.clear_all_method_hints();
                    emit_return(
                        &mut self.lowering,
                        raw_index,
                        return_pack(a, u16::from(b)),
                        k,
                    );
                    raw_index += 1;
                }
                Lua55Opcode::Return0 => {
                    self.clear_all_method_hints();
                    emit_return(
                        &mut self.lowering,
                        raw_index,
                        ValuePack::Fixed(RegRange::new(Reg(0), 0)),
                        false,
                    );
                    raw_index += 1;
                }
                Lua55Opcode::Return1 => {
                    let a = expect_a(raw_pc, opcode, operands)?;
                    self.clear_all_method_hints();
                    emit_return(
                        &mut self.lowering,
                        raw_index,
                        ValuePack::Fixed(RegRange::new(reg_from_u8(a), 1)),
                        false,
                    );
                    raw_index += 1;
                }
                Lua55Opcode::ForLoop => {
                    self.clear_all_method_hints();
                    let (a, bx) = expect_abx(raw_pc, opcode, operands)?;
                    // Lua 5.5 的 numeric-for 体里会直接复用 A+2 这格作为当前 binding；
                    // 如果继续沿用 5.4 的 A+3，循环体里读到的就会是旧 step 槽位。
                    let regs = numeric_for_regs(reg_from_u8(a), 2);
                    let body_target = self.jump_target_back_bx(raw_pc, extra.pc, bx)?;
                    let exit_target =
                        self.ensure_targetable_pc(raw_pc, self.next_raw_pc(raw_index))?;
                    emit_numeric_for_loop(
                        &mut self.lowering,
                        raw_index,
                        regs,
                        body_target,
                        exit_target,
                    );
                    raw_index += 1;
                }
                Lua55Opcode::ForPrep => {
                    self.clear_all_method_hints();
                    let (a, bx) = expect_abx(raw_pc, opcode, operands)?;
                    let loop_raw =
                        jump_target_forward_bx(&self.word_code_index, raw_pc, extra.pc, bx)?;
                    let target_opcode = opcode_at(self.raw, loop_raw);
                    if target_opcode != Lua55Opcode::ForLoop {
                        return Err(TransformError::InvalidNumericForPair {
                            raw_pc,
                            target_raw: raw_pc_at(self.raw, loop_raw) as usize,
                            found: target_opcode.label(),
                        });
                    }
                    let regs = numeric_for_regs(reg_from_u8(a), 2);
                    let body_target =
                        self.ensure_targetable_pc(raw_pc, self.next_raw_pc(raw_index))?;
                    let exit_target =
                        self.ensure_targetable_pc(raw_pc, self.next_raw_pc(loop_raw))?;
                    emit_numeric_for_init(
                        &mut self.lowering,
                        raw_index,
                        regs,
                        body_target,
                        exit_target,
                    );
                    raw_index += 1;
                }
                Lua55Opcode::TForPrep => {
                    self.clear_all_method_hints();
                    let (a, bx) = expect_abx(raw_pc, opcode, operands)?;
                    let tbc_reg = Reg(usize::from(a) + 3);
                    let call_target =
                        jump_target_forward_bx(&self.word_code_index, raw_pc, extra.pc, bx)?;
                    emit_tforprep(&mut self.lowering, raw_index, tbc_reg, call_target);
                    raw_index += 1;
                }
                Lua55Opcode::TForCall => {
                    self.clear_all_method_hints();
                    let (a, c) = expect_ac(raw_pc, opcode, operands)?;
                    let pair = self.generic_for_pair(raw_index, a, c)?;
                    let state_start = reg_from_u8(a);
                    // Lua 5.5 的 generic-for 结果区间会直接落在 A+3 开始，
                    // 也就是与 5.4 不同，不再额外空出一格给循环体里的绑定。
                    // 如果继续沿用 5.4 的 A+4，后面的 HIR 会把隐藏 close 槽位
                    // 错当成源码里的第一个迭代变量。
                    emit_generic_for_call(
                        &mut self.lowering,
                        raw_index,
                        state_start,
                        3,
                        usize::from(c),
                    );
                    emit_generic_for_loop(&mut self.lowering, pair);
                    raw_index = pair.next_index;
                }
                Lua55Opcode::TForLoop => {
                    return Err(TransformError::InvalidGenericForLoop {
                        raw_pc,
                        helper_pc: raw_pc,
                        found: opcode.label(),
                    });
                }
                Lua55Opcode::SetList => {
                    let (a, b, c, k) = expect_avbck(raw_pc, opcode, operands)?;
                    let base_index = u32::from(c)
                        + if k {
                            self.extra_arg(raw_pc, opcode, extra.extra_arg)? * EXTRAARG_SCALE_10
                        } else {
                            0
                        };
                    let values = if b == 0 {
                        ValuePack::Open(Reg(usize::from(a) + 1))
                    } else {
                        ValuePack::Fixed(RegRange::new(Reg(usize::from(a) + 1), usize::from(b)))
                    };
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetList(SetListInstr {
                            base: reg_from_u8(a),
                            values,
                            start_index: base_index + 1,
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::Closure => {
                    let (a, bx) = expect_abx(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    let proto = self.proto_ref(raw_pc, bx as usize)?;
                    let child = &self.raw.common.children[proto.index()];
                    let captures = child
                        .common
                        .upvalues
                        .common
                        .descriptors
                        .iter()
                        .map(|descriptor| {
                            let source = if descriptor.in_stack {
                                CaptureSource::Reg(Reg(descriptor.index as usize))
                            } else {
                                CaptureSource::Upvalue(
                                    self.upvalue_ref(raw_pc, descriptor.index as usize)?,
                                )
                            };
                            Ok(Capture {
                                source,
                                extra: DialectCaptureExtra::None,
                            })
                        })
                        .collect::<Result<Vec<_>, TransformError>>()?;

                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Closure(ClosureInstr {
                            dst,
                            proto,
                            captures,
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::VarArg => {
                    let (a, _, c, _) = expect_abck(raw_pc, opcode, operands)?;
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::VarArg(VarArgInstr {
                            results: if c == 0 {
                                ResultPack::Open(reg_from_u8(a))
                            } else {
                                ResultPack::Fixed(RegRange::new(reg_from_u8(a), usize::from(c - 1)))
                            },
                        })),
                    );
                    raw_index += 1;
                }
                Lua55Opcode::VarArgPrep => {
                    raw_index += 1;
                }
                Lua55Opcode::ExtraArg => {
                    return Err(TransformError::UnexpectedStandaloneExtraArg { raw_pc });
                }
            }
        }

        self.finish()
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
        opcode: Lua55Opcode,
        extra_arg: Option<u32>,
    ) -> Result<u32, TransformError> {
        extra_arg.ok_or(TransformError::MissingExtraArg {
            raw_pc,
            opcode: opcode.label(),
        })
    }

    fn value_operand(
        &self,
        raw_pc: u32,
        operand: u8,
        k: bool,
    ) -> Result<ValueOperand, TransformError> {
        if k {
            Ok(ValueOperand::Const(
                self.const_ref(raw_pc, operand as usize)?,
            ))
        } else {
            Ok(ValueOperand::Reg(reg_from_u8(operand)))
        }
    }

    fn compare_immediate(&self, operand: i16, is_float: bool) -> CondOperand {
        if is_float {
            CondOperand::Number(NumberLiteral::from_f64(f64::from(operand)))
        } else {
            CondOperand::Integer(i64::from(operand))
        }
    }

    fn jump_target_sj(&self, raw_pc: u32, base_pc: u32, sj: i32) -> Result<usize, TransformError> {
        let target_pc = i64::from(base_pc) + 1 + i64::from(sj);
        self.ensure_targetable_jump_pc(raw_pc, target_pc)
    }

    fn jump_target_back_bx(
        &self,
        raw_pc: u32,
        base_pc: u32,
        bx: u32,
    ) -> Result<usize, TransformError> {
        let target_pc = i64::from(base_pc) + 1 - i64::from(bx);
        self.ensure_targetable_jump_pc(raw_pc, target_pc)
    }

    fn ensure_targetable_jump_pc(
        &self,
        raw_pc: u32,
        target_pc: i64,
    ) -> Result<usize, TransformError> {
        self.word_code_index.ensure_valid_jump_pc(raw_pc, target_pc)
    }

    fn ensure_targetable_pc(&self, raw_pc: u32, target_pc: u32) -> Result<usize, TransformError> {
        self.word_code_index.ensure_targetable_pc(raw_pc, target_pc)
    }

    fn helper_jump(
        &self,
        raw_index: usize,
        opcode: Lua55Opcode,
    ) -> Result<HelperJump, TransformError> {
        helper_jump_asj(
            self.raw,
            &self.word_code_index,
            raw_index,
            HelperJumpAsjSpec {
                owner_opcode: opcode,
                helper_jump_opcode: Lua55Opcode::Jmp,
                inspect_helper: inspect_lua55_asj_helper,
                raw_pc_at: instr_pc,
                jump_target: |raw_pc, base_pc, sj| self.jump_target_sj(raw_pc, base_pc, sj),
                ensure_targetable_pc: |raw_pc, target_pc| {
                    self.ensure_targetable_pc(raw_pc, target_pc)
                },
                next_raw_pc: |index| self.next_raw_pc(index),
                opcode_label: Lua55Opcode::label,
            },
        )
    }

    fn generic_for_pair(
        &self,
        raw_index: usize,
        call_a: u8,
        result_count: u8,
    ) -> Result<GenericForPair, TransformError> {
        generic_for_pair_abx(
            self.raw,
            &self.word_code_index,
            raw_index,
            call_a,
            usize::from(result_count),
            GenericForPairAbxSpec {
                helper_loop_opcode: Lua55Opcode::TForLoop,
                inspect_helper: inspect_lua55_abx_helper,
                raw_pc_at: instr_pc,
                jump_target: |raw_pc, base_pc, bx| self.jump_target_back_bx(raw_pc, base_pc, bx),
                ensure_targetable_pc: |raw_pc, target_pc| {
                    self.ensure_targetable_pc(raw_pc, target_pc)
                },
                next_raw_pc: |index| self.next_raw_pc(index),
                opcode_label: Lua55Opcode::label,
                validate_loop_base: |loop_a, call_a| loop_a == call_a,
                build_pair: |loop_a, result_count| {
                    (
                        Reg(usize::from(loop_a) + 2),
                        RegRange::new(Reg(usize::from(loop_a) + 3), result_count),
                    )
                },
            },
        )
    }

    fn next_raw_pc(&self, raw_index: usize) -> u32 {
        let instr = &self.raw.common.instructions[raw_index];
        instr.pc() + u32::from(instr_word_len(instr))
    }

    fn set_pending_method(&mut self, callee: Reg, self_arg: Reg, method_name: Option<ConstRef>) {
        self.pending_methods.set(callee, self_arg, method_name);
    }

    fn take_call_info(
        &mut self,
        callee: Reg,
        raw_b: u16,
    ) -> (CallKind, Option<crate::transformer::MethodNameHint>) {
        self.pending_methods.call_info(callee, raw_b)
    }

    fn invalidate_written_reg(&mut self, reg: Reg) {
        self.pending_methods.invalidate_reg(reg);
    }

    fn invalidate_written_range(&mut self, range: RegRange) {
        self.pending_methods.invalidate_range(range);
    }

    fn clear_all_method_hints(&mut self) {
        self.pending_methods.clear();
    }
}

fn inspect_lua55_asj_helper(raw: &RawInstr) -> Result<(Lua55Opcode, u32, i32), TransformError> {
    let (opcode, operands, extra) = raw
        .lua55()
        .expect("lua55 lowerer should only decode lua55 instructions");
    let sj = expect_asj(extra.pc, opcode, operands)?;
    Ok((opcode, extra.pc, sj))
}

fn inspect_lua55_abx_helper(raw: &RawInstr) -> Result<(Lua55Opcode, u32, u8, u32), TransformError> {
    let (opcode, operands, extra) = raw
        .lua55()
        .expect("lua55 lowerer should only decode lua55 instructions");
    let (a, bx) = expect_abx(extra.pc, opcode, operands)?;
    Ok((opcode, extra.pc, a, bx))
}

fn raw_pc_at(raw: &RawProto, index: usize) -> u32 {
    raw.common.instructions[index].pc()
}

fn opcode_at(raw: &RawProto, index: usize) -> Lua55Opcode {
    raw.common.instructions[index]
        .lua55()
        .expect("lua55 lowerer should only decode lua55 instructions")
        .0
}

fn unary_op_kind(opcode: Lua55Opcode) -> UnaryOpKind {
    match opcode {
        Lua55Opcode::Unm => UnaryOpKind::Neg,
        Lua55Opcode::BNot => UnaryOpKind::BitNot,
        Lua55Opcode::Not => UnaryOpKind::Not,
        Lua55Opcode::Len => UnaryOpKind::Length,
        _ => unreachable!("only unary opcodes should reach unary_op_kind"),
    }
}

fn binary_op_kind(opcode: Lua55Opcode) -> BinaryOpKind {
    match opcode {
        Lua55Opcode::AddI | Lua55Opcode::AddK | Lua55Opcode::Add => BinaryOpKind::Add,
        Lua55Opcode::SubK | Lua55Opcode::Sub => BinaryOpKind::Sub,
        Lua55Opcode::MulK | Lua55Opcode::Mul => BinaryOpKind::Mul,
        Lua55Opcode::DivK | Lua55Opcode::Div => BinaryOpKind::Div,
        Lua55Opcode::IdivK | Lua55Opcode::Idiv => BinaryOpKind::FloorDiv,
        Lua55Opcode::ModK | Lua55Opcode::Mod => BinaryOpKind::Mod,
        Lua55Opcode::PowK | Lua55Opcode::Pow => BinaryOpKind::Pow,
        Lua55Opcode::BandK | Lua55Opcode::Band => BinaryOpKind::BitAnd,
        Lua55Opcode::BorK | Lua55Opcode::Bor => BinaryOpKind::BitOr,
        Lua55Opcode::BxorK | Lua55Opcode::Bxor => BinaryOpKind::BitXor,
        Lua55Opcode::ShlI | Lua55Opcode::Shl => BinaryOpKind::Shl,
        Lua55Opcode::ShrI | Lua55Opcode::Shr => BinaryOpKind::Shr,
        _ => unreachable!("only arithmetic/bitwise opcodes should reach binary_op_kind"),
    }
}

fn branch_predicate(opcode: Lua55Opcode) -> BranchPredicate {
    match opcode {
        Lua55Opcode::Eq | Lua55Opcode::EqK | Lua55Opcode::EqI => BranchPredicate::Eq,
        Lua55Opcode::Lt | Lua55Opcode::LtI | Lua55Opcode::GtI => BranchPredicate::Lt,
        Lua55Opcode::Le | Lua55Opcode::LeI | Lua55Opcode::GeI => BranchPredicate::Le,
        _ => unreachable!("only compare opcodes should reach branch_predicate"),
    }
}

fn compare_immediate_shape(
    opcode: Lua55Opcode,
    reg: Reg,
    immediate: CondOperand,
) -> (BranchPredicate, CondOperand, CondOperand) {
    match opcode {
        Lua55Opcode::EqI | Lua55Opcode::LtI | Lua55Opcode::LeI => {
            (branch_predicate(opcode), CondOperand::Reg(reg), immediate)
        }
        Lua55Opcode::GtI => (BranchPredicate::Lt, immediate, CondOperand::Reg(reg)),
        Lua55Opcode::GeI => (BranchPredicate::Le, immediate, CondOperand::Reg(reg)),
        _ => unreachable!("only compare-immediate opcodes should reach compare_immediate_shape"),
    }
}

define_operand_expecters! {
    opcode = Lua55Opcode,
    operands = Lua55Operands,
    label = Lua55Opcode::label,
    fn expect_a("A") -> u8 {
        Lua55Operands::A { a } => *a
    }
    fn expect_ak("Ak") -> (u8, bool) {
        Lua55Operands::Ak { a, k } => (*a, *k)
    }
    fn expect_ab("AB") -> (u8, u8) {
        Lua55Operands::AB { a, b } => (*a, *b)
    }
    fn expect_ac("AC") -> (u8, u8) {
        Lua55Operands::AC { a, c } => (*a, *c)
    }
    fn expect_abc("ABC") -> (u8, u8, u8) {
        Lua55Operands::ABC { a, b, c } => (*a, *b, *c)
    }
    fn expect_abk("ABk") -> (u8, u8, bool) {
        Lua55Operands::ABk { a, b, k } => (*a, *b, *k)
    }
    fn expect_abck("ABCk") -> (u8, u8, u8, bool) {
        Lua55Operands::ABCk { a, b, c, k } => (*a, *b, *c, *k)
    }
    fn expect_abx("ABx") -> (u8, u32) {
        Lua55Operands::ABx { a, bx } => (*a, *bx)
    }
    fn expect_asbx("AsBx") -> (u8, i32) {
        Lua55Operands::AsBx { a, sbx } => (*a, *sbx)
    }
    fn expect_asj("AsJ") -> i32 {
        Lua55Operands::AsJ { sj } => *sj
    }
    fn expect_absck("ABsCk") -> (u8, u8, i16, bool) {
        Lua55Operands::ABsCk { a, b, sc, k } => (*a, *b, *sc, *k)
    }
    fn expect_asbck("AsBCk") -> (u8, i16, u8, bool) {
        Lua55Operands::AsBCk { a, sb, c, k } => (*a, *sb, *c, *k)
    }
    fn expect_avbck("AvBCk") -> (u8, u8, u16, bool) {
        Lua55Operands::AvBCk { a, vb, vc, k } => (*a, *vb, *vc, *k)
    }
}
