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

    fn lower(&mut self) -> Result<(Vec<LowInstr>, LoweringMap), TransformError> {
        let mut raw_index = 0_usize;

        while raw_index < self.raw.common.instructions.len() {
            let raw_instr = &self.raw.common.instructions[raw_index];
            let extra = decode_instr(raw_instr, self.dialect);
            let opcode = extra.opcode;
            let operands = &extra.operands;
            let raw_pc = extra.pc;

            match opcode {
                FamilyOpcode::Move => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Move(MoveInstr {
                            dst,
                            src: reg_from_u16(b),
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::LoadK => {
                    let (a, bx) = expect_abx(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
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
                FamilyOpcode::LoadKx => {
                    let a = expect_a(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
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
                FamilyOpcode::LoadBool => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadBool(LoadBoolInstr {
                            dst,
                            value: b != 0,
                        })),
                    );

                    if c != 0 {
                        self.pending_methods.clear();
                        self.emit(
                            None,
                            vec![raw_index],
                            PendingLowInstr::Jump {
                                target: TargetPlaceholder::Raw(
                                    self.ensure_targetable_pc(raw_pc, raw_pc + 2)?,
                                ),
                            },
                        );
                    }

                    raw_index += 1;
                }
                FamilyOpcode::LoadNil => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    let len = range_len_inclusive(usize::from(a), usize::from(a) + usize::from(b));
                    let dst = RegRange::new(reg_from_u8(a), len);
                    self.pending_methods.invalidate_range(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadNil(LoadNilInstr { dst })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::GetUpVal => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetUpvalue(GetUpvalueInstr {
                            dst,
                            src: shared_upvalue_operand(
                                self.raw,
                                &self.env_upvalues,
                                raw_pc,
                                b as usize,
                            )?,
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::GetTabUp => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
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
                            key: rk_access_key(self.raw, raw_pc, c)?,
                            kind: GetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::GetTable => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst,
                            base: AccessBase::Reg(reg_from_u16(b)),
                            key: rk_access_key(self.raw, raw_pc, c)?,
                            kind: GetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::SetTabUp => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
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
                            key: rk_access_key(self.raw, raw_pc, b)?,
                            value: rk_value_operand(self.raw, raw_pc, c)?,
                            kind: SetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::SetUpVal => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetUpvalue(SetUpvalueInstr {
                            dst: shared_upvalue_operand(
                                self.raw,
                                &self.env_upvalues,
                                raw_pc,
                                b as usize,
                            )?,
                            src: ValueOperand::Reg(reg_from_u8(a)),
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::SetTable => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Reg(reg_from_u8(a)),
                            key: rk_access_key(self.raw, raw_pc, b)?,
                            value: rk_value_operand(self.raw, raw_pc, c)?,
                            kind: SetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::NewTable => {
                    let (a, _, _) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::NewTable(NewTableInstr { dst })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::Self_ => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let callee = reg_from_u8(a);
                    let self_arg = Reg(callee.index() + 1);
                    let method_key = rk_access_key(self.raw, raw_pc, c)?;
                    let method_name = match method_key {
                        crate::transformer::AccessKey::Const(const_ref) => Some(const_ref),
                        _ => None,
                    };
                    self.pending_methods.invalidate_reg(callee);
                    self.pending_methods.invalidate_reg(self_arg);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Move(MoveInstr {
                            dst: self_arg,
                            src: reg_from_u16(b),
                        })),
                    );
                    self.emit(
                        None,
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst: callee,
                            base: AccessBase::Reg(self_arg),
                            key: method_key,
                            kind: GetTableKind::Method,
                        })),
                    );
                    self.pending_methods
                        .set(callee, self_arg, method_name, None);
                    raw_index += 1;
                }
                FamilyOpcode::Add
                | FamilyOpcode::Sub
                | FamilyOpcode::Mul
                | FamilyOpcode::Mod
                | FamilyOpcode::Pow
                | FamilyOpcode::Div
                | FamilyOpcode::Idiv
                | FamilyOpcode::Band
                | FamilyOpcode::Bor
                | FamilyOpcode::Bxor
                | FamilyOpcode::Shl
                | FamilyOpcode::Shr => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::BinaryOp(BinaryOpInstr {
                            dst,
                            op: binary_op_kind(opcode),
                            lhs: rk_value_operand(self.raw, raw_pc, b)?,
                            rhs: rk_value_operand(self.raw, raw_pc, c)?,
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::Unm | FamilyOpcode::BNot | FamilyOpcode::Not | FamilyOpcode::Len => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::UnaryOp(UnaryOpInstr {
                            dst,
                            op: unary_op_kind(opcode),
                            src: reg_from_u16(b),
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::Concat => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Concat(ConcatInstr {
                            dst,
                            src: RegRange::new(
                                reg_from_u16(b),
                                range_len_inclusive(b as usize, c as usize),
                            ),
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::Jmp => {
                    let (a, sbx) = expect_asbx(raw_pc, opcode, operands)?;
                    let target = TargetPlaceholder::Raw(jump_target_sbx(
                        &self.word_code_index,
                        raw_pc,
                        extra.pc,
                        sbx,
                    )?);

                    if let Some(close_from) = close_from_raw_a(a) {
                        self.emit(
                            Some(raw_index),
                            vec![raw_index],
                            PendingLowInstr::Ready(LowInstr::Close(CloseInstr {
                                from: close_from,
                            })),
                        );
                        self.emit(None, vec![raw_index], PendingLowInstr::Jump { target });
                    } else {
                        self.emit(
                            Some(raw_index),
                            vec![raw_index],
                            PendingLowInstr::Jump { target },
                        );
                    }
                    raw_index += 1;
                }
                FamilyOpcode::Eq | FamilyOpcode::Lt | FamilyOpcode::Le => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let cond = BranchCond::compare(
                        branch_predicate(opcode),
                        rk_cond_operand(self.raw, raw_pc, b)?,
                        rk_cond_operand(self.raw, raw_pc, c)?,
                        a == 0,
                    );

                    let then_target = if helper.close_from.is_some() {
                        TargetPlaceholder::Low(self.lowering.next_low_index())
                    } else {
                        TargetPlaceholder::Raw(helper.jump_target)
                    };
                    self.emit(
                        Some(raw_index),
                        vec![raw_index, helper.helper_index],
                        PendingLowInstr::Branch {
                            cond,
                            then_target,
                            else_target: TargetPlaceholder::Raw(helper.fallthrough_target),
                        },
                    );
                    if let Some(close_from) = helper.close_from {
                        self.emit(
                            None,
                            vec![raw_index, helper.helper_index],
                            PendingLowInstr::Ready(LowInstr::Close(CloseInstr {
                                from: close_from,
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
                FamilyOpcode::Test => {
                    let (a, c) = expect_ac(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let cond = BranchCond::truthy(CondOperand::Reg(reg_from_u8(a)), c == 0);

                    let then_target = if helper.close_from.is_some() {
                        TargetPlaceholder::Low(self.lowering.next_low_index())
                    } else {
                        TargetPlaceholder::Raw(helper.jump_target)
                    };
                    self.emit(
                        Some(raw_index),
                        vec![raw_index, helper.helper_index],
                        PendingLowInstr::Branch {
                            cond,
                            then_target,
                            else_target: TargetPlaceholder::Raw(helper.fallthrough_target),
                        },
                    );
                    if let Some(close_from) = helper.close_from {
                        self.emit(
                            None,
                            vec![raw_index, helper.helper_index],
                            PendingLowInstr::Ready(LowInstr::Close(CloseInstr {
                                from: close_from,
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
                FamilyOpcode::TestSet => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let cond = BranchCond::truthy(CondOperand::Reg(reg_from_u16(b)), c == 0);

                    if usize::from(a) == usize::from(b) {
                        let then_target = if helper.close_from.is_some() {
                            TargetPlaceholder::Low(self.lowering.next_low_index())
                        } else {
                            TargetPlaceholder::Raw(helper.jump_target)
                        };
                        self.emit(
                            Some(raw_index),
                            vec![raw_index, helper.helper_index],
                            PendingLowInstr::Branch {
                                cond,
                                then_target,
                                else_target: TargetPlaceholder::Raw(helper.fallthrough_target),
                            },
                        );
                        if let Some(close_from) = helper.close_from {
                            self.emit(
                                None,
                                vec![raw_index, helper.helper_index],
                                PendingLowInstr::Ready(LowInstr::Close(CloseInstr {
                                    from: close_from,
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
                    } else {
                        self.pending_methods.invalidate_reg(reg_from_u8(a));
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
                                src: reg_from_u16(b),
                            })),
                        );
                        if let Some(close_from) = helper.close_from {
                            self.emit(
                                None,
                                vec![raw_index, helper.helper_index],
                                PendingLowInstr::Ready(LowInstr::Close(CloseInstr {
                                    from: close_from,
                                })),
                            );
                        }
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
                FamilyOpcode::Call => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let results = call_result_pack(a, c);
                    let callee = reg_from_u8(a);
                    let (kind, method_name) = self.pending_methods.consume_call_info(
                        callee,
                        Reg(callee.index() + 1),
                        b != 1,
                        results,
                    );
                    emit_call(
                        &mut self.lowering,
                        raw_index,
                        callee,
                        call_args_pack(a, b),
                        results,
                        kind,
                        method_name,
                    );
                    raw_index += 1;
                }
                FamilyOpcode::TailCall => {
                    let (a, b, _) = expect_abc(raw_pc, opcode, operands)?;
                    let callee = reg_from_u8(a);
                    let (kind, method_name) = self.pending_methods.consume_call_info(
                        callee,
                        Reg(callee.index() + 1),
                        b != 1,
                        ResultPack::Ignore,
                    );
                    emit_tail_call(
                        &mut self.lowering,
                        raw_index,
                        callee,
                        call_args_pack(a, b),
                        kind,
                        method_name,
                        false,
                    );
                    raw_index += 1;
                }
                FamilyOpcode::Return => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    self.pending_methods.clear();
                    emit_return(&mut self.lowering, raw_index, return_pack(a, b), false);
                    raw_index += 1;
                }
                FamilyOpcode::ForLoop => {
                    self.pending_methods.clear();
                    let (a, sbx) = expect_asbx(raw_pc, opcode, operands)?;
                    let regs = numeric_for_regs(reg_from_u8(a), 3);
                    let body_target =
                        jump_target_sbx(&self.word_code_index, raw_pc, extra.pc, sbx)?;
                    let exit_target =
                        self.ensure_targetable_pc(raw_pc, next_raw_pc(self.raw, raw_index))?;
                    emit_numeric_for_loop(
                        &mut self.lowering,
                        raw_index,
                        regs,
                        body_target,
                        exit_target,
                    );
                    raw_index += 1;
                }
                FamilyOpcode::ForPrep => {
                    self.pending_methods.clear();
                    let (a, sbx) = expect_asbx(raw_pc, opcode, operands)?;
                    let target_raw = jump_target_sbx(&self.word_code_index, raw_pc, extra.pc, sbx)?;
                    let target_opcode = opcode_at(self.raw, target_raw, self.dialect);
                    if target_opcode != FamilyOpcode::ForLoop {
                        return Err(TransformError::InvalidNumericForPair {
                            raw_pc,
                            target_raw: raw_pc_at(self.raw, target_raw) as usize,
                            found: target_opcode.label(),
                        });
                    }
                    let regs = numeric_for_regs(reg_from_u8(a), 3);
                    let body_target =
                        self.ensure_targetable_pc(raw_pc, next_raw_pc(self.raw, raw_index))?;
                    let exit_target =
                        self.ensure_targetable_pc(raw_pc, next_raw_pc(self.raw, target_raw))?;
                    emit_numeric_for_init(
                        &mut self.lowering,
                        raw_index,
                        regs,
                        body_target,
                        exit_target,
                    );
                    raw_index += 1;
                }
                FamilyOpcode::TForCall => {
                    self.pending_methods.clear();
                    let (a, _, c) = expect_abc(raw_pc, opcode, operands)?;
                    let pair = self.generic_for_pair(raw_index, a, c)?;
                    let state_start = reg_from_u8(a);
                    emit_generic_for_call(
                        &mut self.lowering,
                        raw_index,
                        state_start,
                        2,
                        3,
                        usize::from(c),
                    );
                    emit_generic_for_loop(&mut self.lowering, pair);
                    raw_index = pair.next_index;
                }
                FamilyOpcode::TForLoop => {
                    return Err(TransformError::InvalidGenericForLoop {
                        raw_pc,
                        helper_pc: raw_pc,
                        found: opcode.label(),
                    });
                }
                FamilyOpcode::SetList => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let list_chunk = if c == 0 {
                        self.extra_arg(raw_pc, opcode, extra.extra_arg)?
                    } else {
                        u32::from(c)
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
                            start_index: ((list_chunk.saturating_sub(1)) * LFIELDS_PER_FLUSH) + 1,
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::Closure => {
                    let (a, bx) = expect_abx(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
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
                                CaptureSource::ByReference(Reg(descriptor.index as usize))
                            } else {
                                CaptureSource::Upvalue(
                                    self.upvalue_ref(raw_pc, descriptor.index as usize)?,
                                )
                            };
                            Ok(Capture { source })
                        })
                        .collect::<Result<Vec<_>, TransformError>>()?;

                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Closure(ClosureInstr {
                            dst,
                            proto,
                            captures,
                            creation: crate::transformer::ClosureCreation::Fresh,
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::VarArg => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    self.pending_methods.clear();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::VarArg(VarArgInstr {
                            results: if b == 0 {
                                ResultPack::Open(reg_from_u8(a))
                            } else {
                                ResultPack::Fixed(RegRange::new(reg_from_u8(a), usize::from(b - 1)))
                            },
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::ExtraArg => {
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
