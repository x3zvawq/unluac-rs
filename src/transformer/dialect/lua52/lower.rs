//! 这个文件实现 Lua 5.2 到统一 low-IR 的 lowering。
//!
//! 这里最需要显式处理的 5.2 差异有三类：
//! 1. raw pc 仍然按“字”计数，但 parser 会把 `LOADKX/EXTRAARG`、`SETLIST/EXTRAARG`
//!    折成一个逻辑指令，所以跳转解析不能再偷用 logical index。
//! 2. `GETTABUP/SETTABUP` 的 base 可能是普通 upvalue table，也可能是词法 `_ENV`；
//!    本层要把后者直接恢复成 `AccessBase::Env`，不能把这层语义继续拖给 HIR 猜。
//! 3. `JMP(A)` 和 test helper `JMP` 可能自带 close 语义，本层必须把它显式拆成
//!    `Close + Jump`，后续 CFG/SSA 才能看见真实副作用。

use crate::parser::{Lua52Opcode, Lua52Operands, RawChunk, RawInstr, RawProto};
use crate::transformer::dialect::lowering::{
    PendingLowInstr, PendingLoweringState, PendingMethodHints, TargetPlaceholder, WordCodeIndex,
    instr_pc, instr_word_len, resolve_pending_instr_with,
};
use crate::transformer::dialect::puc_lua::{
    GenericForPairAsbxSpec, GenericForPairInfo as GenericForPair, HelperJumpAsbxSpec,
    HelperJumpInfo as HelperJump, LFIELDS_PER_FLUSH,
    access_base_for_upvalue as shared_access_base_for_upvalue, call_args_pack, call_result_pack,
    checked_const_ref, checked_proto_ref, checked_upvalue_ref, close_from_raw_a, emit_call,
    emit_generic_for_call, emit_generic_for_loop, emit_numeric_for_init, emit_numeric_for_loop,
    emit_return, emit_tail_call, finish_lowered_proto, generic_for_pair_asbx, helper_jump_asbx,
    index_k, is_k, lower_chunk_with_env, numeric_for_regs, prepare_env_lowering,
    range_len_inclusive, reg_from_u8, reg_from_u16, return_pack,
};
use crate::transformer::operands::define_operand_expecters;
use crate::transformer::{
    AccessBase, AccessKey, BinaryOpInstr, BinaryOpKind, BranchCond, BranchOperands,
    BranchPredicate, CallKind, Capture, CaptureSource, CloseInstr, ClosureInstr, ConcatInstr,
    CondOperand, ConstRef, DialectCaptureExtra, GetTableInstr, GetUpvalueInstr, InstrRef,
    LoadBoolInstr, LoadConstInstr, LoadNilInstr, LowInstr, LoweredChunk, LoweredProto, LoweringMap,
    MoveInstr, NewTableInstr, ProtoRef, Reg, RegRange, ResultPack, SetListInstr, SetTableInstr,
    SetUpvalueInstr, TransformError, UnaryOpInstr, UnaryOpKind, UpvalueRef, ValueOperand,
    ValuePack, VarArgInstr,
};

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
        let method_slots = usize::from(raw.common.frame.max_stack_size).saturating_add(2);
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
                .lua52()
                .expect("lua52 lowerer should only decode lua52 instructions");
            let raw_pc = extra.pc;

            match opcode {
                Lua52Opcode::Move => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
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
                Lua52Opcode::LoadK => {
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
                Lua52Opcode::LoadKx => {
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
                Lua52Opcode::LoadBool => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadBool(LoadBoolInstr {
                            dst,
                            value: b != 0,
                        })),
                    );

                    if c != 0 {
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
                    }

                    raw_index += 1;
                }
                Lua52Opcode::LoadNil => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    let len = range_len_inclusive(usize::from(a), usize::from(b));
                    let dst = RegRange::new(reg_from_u8(a), len);
                    self.invalidate_written_range(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadNil(LoadNilInstr { dst })),
                    );
                    raw_index += 1;
                }
                Lua52Opcode::GetUpVal => {
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
                Lua52Opcode::GetTabUp => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
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
                            key: self.access_key(raw_pc, c)?,
                        })),
                    );
                    raw_index += 1;
                }
                Lua52Opcode::GetTable => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst,
                            base: AccessBase::Reg(reg_from_u16(b)),
                            key: self.access_key(raw_pc, c)?,
                        })),
                    );
                    raw_index += 1;
                }
                Lua52Opcode::SetTabUp => {
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
                            key: self.access_key(raw_pc, b)?,
                            value: self.value_operand(raw_pc, c)?,
                        })),
                    );
                    raw_index += 1;
                }
                Lua52Opcode::SetUpVal => {
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
                Lua52Opcode::SetTable => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Reg(reg_from_u8(a)),
                            key: self.access_key(raw_pc, b)?,
                            value: self.value_operand(raw_pc, c)?,
                        })),
                    );
                    raw_index += 1;
                }
                Lua52Opcode::NewTable => {
                    let (a, _, _) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::NewTable(NewTableInstr { dst })),
                    );
                    raw_index += 1;
                }
                Lua52Opcode::Self_ => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let callee = reg_from_u8(a);
                    let self_arg = Reg(callee.index() + 1);
                    let method_key = self.access_key(raw_pc, c)?;
                    let method_name = match method_key {
                        crate::transformer::AccessKey::Const(const_ref) => Some(const_ref),
                        _ => None,
                    };
                    self.invalidate_written_reg(callee);
                    self.invalidate_written_reg(self_arg);
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
                            base: AccessBase::Reg(reg_from_u16(b)),
                            key: method_key,
                        })),
                    );
                    self.set_pending_method(callee, self_arg, method_name);
                    raw_index += 1;
                }
                Lua52Opcode::Add
                | Lua52Opcode::Sub
                | Lua52Opcode::Mul
                | Lua52Opcode::Div
                | Lua52Opcode::Mod
                | Lua52Opcode::Pow => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::BinaryOp(BinaryOpInstr {
                            dst,
                            op: binary_op_kind(opcode),
                            lhs: self.value_operand(raw_pc, b)?,
                            rhs: self.value_operand(raw_pc, c)?,
                        })),
                    );
                    raw_index += 1;
                }
                Lua52Opcode::Unm | Lua52Opcode::Not | Lua52Opcode::Len => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
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
                Lua52Opcode::Concat => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
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
                Lua52Opcode::Jmp => {
                    self.clear_all_method_hints();
                    let (a, sbx) = expect_asbx(raw_pc, opcode, operands)?;
                    let target = TargetPlaceholder::Raw(self.jump_target(raw_pc, extra.pc, sbx)?);

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
                Lua52Opcode::Eq | Lua52Opcode::Lt | Lua52Opcode::Le => {
                    self.clear_all_method_hints();
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let cond = BranchCond {
                        predicate: branch_predicate(opcode),
                        operands: BranchOperands::Binary(
                            self.cond_operand(raw_pc, b)?,
                            self.cond_operand(raw_pc, c)?,
                        ),
                        negated: a == 0,
                    };

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
                Lua52Opcode::Test => {
                    self.clear_all_method_hints();
                    let (a, c) = expect_ac(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let cond = BranchCond {
                        predicate: BranchPredicate::Truthy,
                        operands: BranchOperands::Unary(CondOperand::Reg(reg_from_u8(a))),
                        negated: c == 0,
                    };

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
                Lua52Opcode::TestSet => {
                    self.clear_all_method_hints();
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let cond = BranchCond {
                        predicate: BranchPredicate::Truthy,
                        operands: BranchOperands::Unary(CondOperand::Reg(reg_from_u16(b))),
                        negated: c == 0,
                    };

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
                Lua52Opcode::Call => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let (kind, method_name) = self.take_call_info(reg_from_u8(a), b);
                    self.clear_all_method_hints();
                    emit_call(
                        &mut self.lowering,
                        raw_index,
                        reg_from_u8(a),
                        call_args_pack(a, b),
                        call_result_pack(a, c),
                        kind,
                        method_name,
                    );
                    raw_index += 1;
                }
                Lua52Opcode::TailCall => {
                    let (a, b, _) = expect_abc(raw_pc, opcode, operands)?;
                    let (kind, method_name) = self.take_call_info(reg_from_u8(a), b);
                    self.clear_all_method_hints();
                    emit_tail_call(
                        &mut self.lowering,
                        raw_index,
                        reg_from_u8(a),
                        call_args_pack(a, b),
                        kind,
                        method_name,
                        false,
                    );
                    raw_index += 1;
                }
                Lua52Opcode::Return => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    self.clear_all_method_hints();
                    emit_return(&mut self.lowering, raw_index, return_pack(a, b), false);
                    raw_index += 1;
                }
                Lua52Opcode::ForLoop => {
                    self.clear_all_method_hints();
                    let (a, sbx) = expect_asbx(raw_pc, opcode, operands)?;
                    let regs = numeric_for_regs(reg_from_u8(a), 3);
                    let body_target = self.jump_target(raw_pc, extra.pc, sbx)?;
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
                Lua52Opcode::ForPrep => {
                    self.clear_all_method_hints();
                    let (a, sbx) = expect_asbx(raw_pc, opcode, operands)?;
                    let target_raw = self.jump_target(raw_pc, extra.pc, sbx)?;
                    let target_opcode = opcode_at(self.raw, target_raw);
                    if target_opcode != Lua52Opcode::ForLoop {
                        return Err(TransformError::InvalidNumericForPair {
                            raw_pc,
                            target_raw: raw_pc_at(self.raw, target_raw) as usize,
                            found: target_opcode.label(),
                        });
                    }
                    let regs = numeric_for_regs(reg_from_u8(a), 3);
                    let body_target =
                        self.ensure_targetable_pc(raw_pc, self.next_raw_pc(raw_index))?;
                    let exit_target =
                        self.ensure_targetable_pc(raw_pc, self.next_raw_pc(target_raw))?;
                    emit_numeric_for_init(
                        &mut self.lowering,
                        raw_index,
                        regs,
                        body_target,
                        exit_target,
                    );
                    raw_index += 1;
                }
                Lua52Opcode::TForCall => {
                    self.clear_all_method_hints();
                    let (a, _, c) = expect_abc(raw_pc, opcode, operands)?;
                    let pair = self.generic_for_pair(raw_index, a, c)?;
                    let state_start = reg_from_u8(a);
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
                Lua52Opcode::TForLoop => {
                    return Err(TransformError::InvalidGenericForLoop {
                        raw_pc,
                        helper_pc: raw_pc,
                        found: opcode.label(),
                    });
                }
                Lua52Opcode::SetList => {
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
                Lua52Opcode::Closure => {
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
                Lua52Opcode::VarArg => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    self.clear_all_method_hints();
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
                Lua52Opcode::ExtraArg => {
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
                self.raw
                    .common
                    .debug_info
                    .common
                    .line_info
                    .get(raw_index)
                    .copied()
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
        opcode: Lua52Opcode,
        extra_arg: Option<u32>,
    ) -> Result<u32, TransformError> {
        extra_arg.ok_or(TransformError::MissingExtraArg {
            raw_pc,
            opcode: opcode.label(),
        })
    }

    fn value_operand(&self, raw_pc: u32, rk: u16) -> Result<ValueOperand, TransformError> {
        if is_k(rk) {
            Ok(ValueOperand::Const(self.const_ref(raw_pc, index_k(rk))?))
        } else {
            Ok(ValueOperand::Reg(reg_from_u16(rk)))
        }
    }

    fn access_key(&self, raw_pc: u32, rk: u16) -> Result<AccessKey, TransformError> {
        if is_k(rk) {
            Ok(AccessKey::Const(self.const_ref(raw_pc, index_k(rk))?))
        } else {
            Ok(AccessKey::Reg(reg_from_u16(rk)))
        }
    }

    fn cond_operand(&self, raw_pc: u32, rk: u16) -> Result<CondOperand, TransformError> {
        if is_k(rk) {
            Ok(CondOperand::Const(self.const_ref(raw_pc, index_k(rk))?))
        } else {
            Ok(CondOperand::Reg(reg_from_u16(rk)))
        }
    }

    fn jump_target(&self, raw_pc: u32, base_pc: u32, sbx: i32) -> Result<usize, TransformError> {
        let target_pc = i64::from(base_pc) + 1 + i64::from(sbx);
        self.word_code_index.ensure_valid_jump_pc(raw_pc, target_pc)
    }

    fn ensure_targetable_pc(&self, raw_pc: u32, target_pc: u32) -> Result<usize, TransformError> {
        self.word_code_index.ensure_targetable_pc(raw_pc, target_pc)
    }

    fn helper_jump(
        &self,
        raw_index: usize,
        opcode: Lua52Opcode,
    ) -> Result<HelperJump, TransformError> {
        helper_jump_asbx(
            self.raw,
            &self.word_code_index,
            raw_index,
            HelperJumpAsbxSpec {
                owner_opcode: opcode,
                helper_jump_opcode: Lua52Opcode::Jmp,
                inspect_helper: inspect_lua52_asbx_helper,
                raw_pc_at: instr_pc,
                jump_target: |raw_pc, base_pc, sbx| self.jump_target(raw_pc, base_pc, sbx),
                ensure_targetable_pc: |raw_pc, target_pc| {
                    self.ensure_targetable_pc(raw_pc, target_pc)
                },
                next_raw_pc: |index| self.next_raw_pc(index),
                opcode_label: Lua52Opcode::label,
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
        generic_for_pair_asbx(
            self.raw,
            &self.word_code_index,
            raw_index,
            call_a,
            usize::from(result_count),
            GenericForPairAsbxSpec {
                helper_loop_opcode: Lua52Opcode::TForLoop,
                inspect_helper: inspect_lua52_asbx_helper,
                raw_pc_at: instr_pc,
                jump_target: |raw_pc, base_pc, sbx| self.jump_target(raw_pc, base_pc, sbx),
                ensure_targetable_pc: |raw_pc, target_pc| {
                    self.ensure_targetable_pc(raw_pc, target_pc)
                },
                next_raw_pc: |index| self.next_raw_pc(index),
                opcode_label: Lua52Opcode::label,
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

    fn next_raw_pc(&self, raw_index: usize) -> u32 {
        let instr = &self.raw.common.instructions[raw_index];
        instr.pc() + u32::from(instr_word_len(instr))
    }

    fn set_pending_method(
        &mut self,
        callee: Reg,
        self_arg: Reg,
        method_name: Option<crate::transformer::ConstRef>,
    ) {
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

fn raw_pc_at(raw: &RawProto, index: usize) -> u32 {
    raw.common.instructions[index].pc()
}

fn opcode_at(raw: &RawProto, index: usize) -> Lua52Opcode {
    raw.common.instructions[index]
        .lua52()
        .expect("lua52 lowerer should only decode lua52 instructions")
        .0
}

fn inspect_lua52_asbx_helper(
    raw: &RawInstr,
) -> Result<(Lua52Opcode, u32, u8, i32), TransformError> {
    let (opcode, operands, extra) = raw
        .lua52()
        .expect("lua52 lowerer should only decode lua52 instructions");
    let (a, sbx) = expect_asbx(extra.pc, opcode, operands)?;
    Ok((opcode, extra.pc, a, sbx))
}

fn unary_op_kind(opcode: Lua52Opcode) -> UnaryOpKind {
    match opcode {
        Lua52Opcode::Unm => UnaryOpKind::Neg,
        Lua52Opcode::Not => UnaryOpKind::Not,
        Lua52Opcode::Len => UnaryOpKind::Length,
        _ => unreachable!("only unary opcodes should reach unary_op_kind"),
    }
}

fn binary_op_kind(opcode: Lua52Opcode) -> BinaryOpKind {
    match opcode {
        Lua52Opcode::Add => BinaryOpKind::Add,
        Lua52Opcode::Sub => BinaryOpKind::Sub,
        Lua52Opcode::Mul => BinaryOpKind::Mul,
        Lua52Opcode::Div => BinaryOpKind::Div,
        Lua52Opcode::Mod => BinaryOpKind::Mod,
        Lua52Opcode::Pow => BinaryOpKind::Pow,
        _ => unreachable!("only arithmetic opcodes should reach binary_op_kind"),
    }
}

fn branch_predicate(opcode: Lua52Opcode) -> BranchPredicate {
    match opcode {
        Lua52Opcode::Eq => BranchPredicate::Eq,
        Lua52Opcode::Lt => BranchPredicate::Lt,
        Lua52Opcode::Le => BranchPredicate::Le,
        _ => unreachable!("only compare opcodes should reach branch_predicate"),
    }
}

define_operand_expecters! {
    opcode = Lua52Opcode,
    operands = Lua52Operands,
    label = Lua52Opcode::label,
    fn expect_a("A") -> u8 {
        Lua52Operands::A { a } => *a
    }
    fn expect_ab("AB") -> (u8, u16) {
        Lua52Operands::AB { a, b } => (*a, *b)
    }
    fn expect_ac("AC") -> (u8, u16) {
        Lua52Operands::AC { a, c } => (*a, *c)
    }
    fn expect_abc("ABC") -> (u8, u16, u16) {
        Lua52Operands::ABC { a, b, c } => (*a, *b, *c)
    }
    fn expect_abx("ABx") -> (u8, u32) {
        Lua52Operands::ABx { a, bx } => (*a, *bx)
    }
    fn expect_asbx("AsBx") -> (u8, i32) {
        Lua52Operands::AsBx { a, sbx } => (*a, *sbx)
    }
}
