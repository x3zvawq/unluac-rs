//! 将 Luau opcode dispatch 降低为共享 LowInstr；依赖 ProtoLowerer 的协议辅助，不负责 chunk 递归和最终映射校验；例如处理多字 AUX、跳转、for 与 closure capture。

use super::*;

impl<'a> ProtoLowerer<'a> {
    pub(super) fn lower(&mut self) -> Result<(Vec<LowInstr>, LoweringMap), TransformError> {
        let mut raw_index = 0_usize;

        while raw_index < self.raw.common.instructions.len() {
            let raw_instr = &self.raw.common.instructions[raw_index];
            let (opcode, operands, extra) = raw_instr
                .luau()
                .expect("luau lowerer should only decode luau instructions");
            let raw_pc = extra.pc;

            match opcode {
                LuauOpcode::Break | LuauOpcode::NativeCall => {
                    return Err(TransformError::UnsupportedOpcode {
                        raw_pc,
                        opcode: opcode.label(),
                    });
                }
                LuauOpcode::Nop
                | LuauOpcode::PrepVarArgs
                | LuauOpcode::Coverage
                | LuauOpcode::FastCall
                | LuauOpcode::FastCall1
                | LuauOpcode::FastCall2
                | LuauOpcode::FastCall2K
                | LuauOpcode::FastCall3 => {
                    self.lower_noop_or_fastcall(raw_index, raw_pc, opcode, operands, extra)?;
                    raw_index += 1;
                }
                LuauOpcode::Move => {
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
                LuauOpcode::LoadNil => {
                    let a = expect_a(raw_pc, opcode, operands)?;
                    let dst = RegRange::new(reg_from_u8(a), 1);
                    self.invalidate_written_range(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadNil(LoadNilInstr { dst })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::LoadB => {
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
                                    self.jump_target(raw_pc, i32::from(c))?,
                                ),
                            },
                        );
                    }
                    raw_index += 1;
                }
                LuauOpcode::LoadN => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadInteger(LoadIntegerInstr {
                            dst,
                            value: i64::from(d),
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::LoadK => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadConst(LoadConstInstr {
                            dst,
                            value: self.literal_const_ref(raw_pc, d as usize)?,
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::LoadKx => {
                    let a = expect_a(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadConst(LoadConstInstr {
                            dst,
                            value: self
                                .literal_const_ref(raw_pc, aux_u24(raw_pc, opcode, extra)?)?,
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::GetImport => {
                    let (a, _) = expect_ad(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    let path = self.import_path(raw_pc, extra)?;
                    self.invalidate_written_reg(dst);

                    for (segment_index, key) in path.into_iter().enumerate() {
                        let base = if segment_index == 0 {
                            AccessBase::Env
                        } else {
                            AccessBase::Reg(dst)
                        };
                        self.emit(
                            (segment_index == 0).then_some(raw_index),
                            vec![raw_index],
                            PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                                dst,
                                base,
                                key: AccessKey::Const(key),
                                kind: GetTableKind::Import,
                            })),
                        );
                    }

                    raw_index += 1;
                }
                LuauOpcode::GetGlobal => {
                    let (a, _) = expect_ac(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst,
                            base: AccessBase::Env,
                            key: AccessKey::Const(
                                self.string_const_ref(raw_pc, aux_u24(raw_pc, opcode, extra)?)?,
                            ),
                            kind: GetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::SetGlobal => {
                    let (a, _) = expect_ac(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Env,
                            key: AccessKey::Const(
                                self.string_const_ref(raw_pc, aux_u24(raw_pc, opcode, extra)?)?,
                            ),
                            value: ValueOperand::Reg(reg_from_u8(a)),
                            kind: SetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::GetUpVal => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetUpvalue(GetUpvalueInstr {
                            dst,
                            src: self.upvalue_ref(raw_pc, b as usize)?.into(),
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::SetUpVal => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetUpvalue(SetUpvalueInstr {
                            dst: self.upvalue_ref(raw_pc, b as usize)?.into(),
                            src: ValueOperand::Reg(reg_from_u8(a)),
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::GetTable => {
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
                            kind: GetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::SetTable => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Reg(reg_from_u8(c)),
                            value: ValueOperand::Reg(reg_from_u8(a)),
                            kind: SetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::GetTableKs => {
                    let (a, b, _) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst,
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Const(
                                self.string_const_ref(raw_pc, aux_u24(raw_pc, opcode, extra)?)?,
                            ),
                            kind: GetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::SetTableKs => {
                    let (a, b, _) = expect_abc(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Const(
                                self.string_const_ref(raw_pc, aux_u24(raw_pc, opcode, extra)?)?,
                            ),
                            value: ValueOperand::Reg(reg_from_u8(a)),
                            kind: SetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::GetTableN => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst,
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Integer(i64::from(c) + 1),
                            kind: GetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::SetTableN => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Integer(i64::from(c) + 1),
                            value: ValueOperand::Reg(reg_from_u8(a)),
                            kind: SetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::NewTable => {
                    let (a, _) = expect_ab(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::NewTable(NewTableInstr { dst })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::DupTable => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::NewTable(NewTableInstr { dst })),
                    );
                    self.emit_dup_table_template(raw_pc, raw_index, dst, d as usize)?;
                    raw_index += 1;
                }
                LuauOpcode::NameCall => {
                    let (a, b, _) = expect_abc(raw_pc, opcode, operands)?;
                    let callee = reg_from_u8(a);
                    let base = reg_from_u8(b);
                    let self_arg = Reg(callee.index() + 1);
                    let method_name =
                        self.string_const_ref(raw_pc, aux_u24(raw_pc, opcode, extra)?)?;
                    self.invalidate_written_reg(callee);
                    self.invalidate_written_reg(self_arg);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Move(MoveInstr {
                            dst: self_arg,
                            src: base,
                        })),
                    );
                    self.emit(
                        None,
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst: callee,
                            base: AccessBase::Reg(self_arg),
                            key: AccessKey::Const(method_name),
                            kind: GetTableKind::Method,
                        })),
                    );
                    self.set_pending_method(callee, self_arg, Some(method_name));
                    raw_index += 1;
                }
                LuauOpcode::Call => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let (result_pack, consumed_extra_raw) =
                        self.fold_single_result_call_move(raw_index, a, c)?;
                    let (kind, method_name) =
                        self.take_call_info(reg_from_u8(a), u16::from(b), result_pack);
                    let kind = if let Some(fastcall) = self.pending_fastcall_calls[raw_index].take()
                    {
                        if kind != CallKind::Normal {
                            return Err(TransformError::UnexpectedOperands {
                                raw_pc,
                                opcode: opcode.label(),
                                expected: "FASTCALL fallback CALL without method setup",
                            });
                        }
                        let Some(args) =
                            fastcall.freeze(reg_from_u8(a), call_args_pack(a, u16::from(b)))
                        else {
                            return Err(TransformError::UnexpectedOperands {
                                raw_pc,
                                opcode: opcode.label(),
                                expected: "CALL argument pack matching FASTCALL operands",
                            });
                        };
                        CallKind::FastCall(args)
                    } else {
                        kind
                    };
                    self.emit(
                        Some(raw_index),
                        if let Some(extra_raw) = consumed_extra_raw {
                            vec![raw_index, extra_raw]
                        } else {
                            vec![raw_index]
                        },
                        PendingLowInstr::Ready(LowInstr::Call(CallInstr {
                            callee: reg_from_u8(a),
                            args: call_args_pack(a, u16::from(b)),
                            results: result_pack,
                            kind,
                            method_name,
                        })),
                    );
                    raw_index += if consumed_extra_raw.is_some() { 2 } else { 1 };
                }
                LuauOpcode::Return => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Return(ReturnInstr {
                            values: return_pack(a, u16::from(b)),
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::Jump | LuauOpcode::JumpBack => {
                    let (_, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Jump {
                            target: TargetPlaceholder::Raw(self.jump_target(raw_pc, i32::from(d))?),
                        },
                    );
                    raw_index += 1;
                }
                LuauOpcode::JumpIf => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Branch {
                            cond: BranchCond::truthy(CondOperand::Reg(reg_from_u8(a)), false),
                            then_target: TargetPlaceholder::Raw(
                                self.jump_target(raw_pc, i32::from(d))?,
                            ),
                            else_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_pc(raw_pc, self.next_raw_pc(raw_index))?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                LuauOpcode::JumpIfNot => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Branch {
                            cond: BranchCond::truthy(CondOperand::Reg(reg_from_u8(a)), true),
                            then_target: TargetPlaceholder::Raw(
                                self.jump_target(raw_pc, i32::from(d))?,
                            ),
                            else_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_pc(raw_pc, self.next_raw_pc(raw_index))?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                LuauOpcode::JumpIfEq
                | LuauOpcode::JumpIfLe
                | LuauOpcode::JumpIfLt
                | LuauOpcode::JumpIfNotEq
                | LuauOpcode::JumpIfNotLe
                | LuauOpcode::JumpIfNotLt => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Branch {
                            cond: BranchCond::compare(
                                compare_predicate(opcode),
                                CondOperand::Reg(reg_from_u8(a)),
                                CondOperand::Reg(reg_from_u8(aux_reg(raw_pc, opcode, extra)?)),
                                compare_negated(opcode),
                            ),
                            then_target: TargetPlaceholder::Raw(
                                self.jump_target(raw_pc, i32::from(d))?,
                            ),
                            else_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_pc(raw_pc, self.next_raw_pc(raw_index))?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                LuauOpcode::JumpXEqKN => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let aux = required_aux(raw_pc, opcode, extra)?;
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Branch {
                            cond: BranchCond::compare(
                                BranchPredicate::Eq,
                                CondOperand::Reg(reg_from_u8(a)),
                                CondOperand::Const(
                                    self.literal_const_ref(raw_pc, (aux & 0x00ff_ffff) as usize)?,
                                ),
                                aux_not(aux),
                            ),
                            then_target: TargetPlaceholder::Raw(
                                self.jump_target(raw_pc, i32::from(d))?,
                            ),
                            else_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_pc(raw_pc, self.next_raw_pc(raw_index))?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                LuauOpcode::JumpXEqKS => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let aux = required_aux(raw_pc, opcode, extra)?;
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Branch {
                            cond: BranchCond::compare(
                                BranchPredicate::Eq,
                                CondOperand::Reg(reg_from_u8(a)),
                                CondOperand::Const(
                                    self.string_const_ref(raw_pc, (aux & 0x00ff_ffff) as usize)?,
                                ),
                                aux_not(aux),
                            ),
                            then_target: TargetPlaceholder::Raw(
                                self.jump_target(raw_pc, i32::from(d))?,
                            ),
                            else_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_pc(raw_pc, self.next_raw_pc(raw_index))?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                LuauOpcode::JumpXEqKB => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let aux = required_aux(raw_pc, opcode, extra)?;
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Branch {
                            cond: BranchCond::compare(
                                BranchPredicate::Eq,
                                CondOperand::Reg(reg_from_u8(a)),
                                CondOperand::Boolean((aux & 1) != 0),
                                aux_not(aux),
                            ),
                            then_target: TargetPlaceholder::Raw(
                                self.jump_target(raw_pc, i32::from(d))?,
                            ),
                            else_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_pc(raw_pc, self.next_raw_pc(raw_index))?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                LuauOpcode::JumpXEqKNil => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let aux = required_aux(raw_pc, opcode, extra)?;
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Branch {
                            cond: BranchCond::compare(
                                BranchPredicate::Eq,
                                CondOperand::Reg(reg_from_u8(a)),
                                CondOperand::Nil,
                                aux_not(aux),
                            ),
                            then_target: TargetPlaceholder::Raw(
                                self.jump_target(raw_pc, i32::from(d))?,
                            ),
                            else_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_pc(raw_pc, self.next_raw_pc(raw_index))?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                LuauOpcode::Add
                | LuauOpcode::Sub
                | LuauOpcode::Mul
                | LuauOpcode::Div
                | LuauOpcode::Mod
                | LuauOpcode::Pow
                | LuauOpcode::IDiv => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
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
                LuauOpcode::AddK
                | LuauOpcode::SubK
                | LuauOpcode::MulK
                | LuauOpcode::DivK
                | LuauOpcode::ModK
                | LuauOpcode::PowK
                | LuauOpcode::IDivK => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::BinaryOp(BinaryOpInstr {
                            dst,
                            op: binary_op_kind(opcode),
                            lhs: ValueOperand::Reg(reg_from_u8(b)),
                            rhs: ValueOperand::Const(self.literal_const_ref(raw_pc, c as usize)?),
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::SubRK | LuauOpcode::DivRK => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::BinaryOp(BinaryOpInstr {
                            dst,
                            op: binary_op_kind(opcode),
                            lhs: ValueOperand::Const(self.literal_const_ref(raw_pc, b as usize)?),
                            rhs: ValueOperand::Reg(reg_from_u8(c)),
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::Concat => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Concat(ConcatInstr {
                            dst,
                            src: RegRange::new(
                                reg_from_u8(b),
                                range_len_inclusive(usize::from(b), usize::from(c)),
                            ),
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::Or => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    let lhs = reg_from_u8(b);
                    self.invalidate_written_reg(dst);
                    self.emit_logical_select(
                        raw_index,
                        lhs,
                        dst,
                        LogicalSelectValue::Reg(lhs),
                        LogicalSelectValue::Reg(reg_from_u8(c)),
                    );
                    raw_index += 1;
                }
                LuauOpcode::And => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    let lhs = reg_from_u8(b);
                    self.invalidate_written_reg(dst);
                    self.emit_logical_select(
                        raw_index,
                        lhs,
                        dst,
                        LogicalSelectValue::Reg(reg_from_u8(c)),
                        LogicalSelectValue::Reg(lhs),
                    );
                    raw_index += 1;
                }
                LuauOpcode::AndK => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    let lhs = reg_from_u8(b);
                    self.invalidate_written_reg(dst);
                    self.emit_logical_select(
                        raw_index,
                        lhs,
                        dst,
                        LogicalSelectValue::Const(self.literal_const_ref(raw_pc, c as usize)?),
                        LogicalSelectValue::Reg(lhs),
                    );
                    raw_index += 1;
                }
                LuauOpcode::OrK => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    let src = reg_from_u8(b);
                    self.invalidate_written_reg(dst);
                    self.emit_logical_select(
                        raw_index,
                        src,
                        dst,
                        LogicalSelectValue::Reg(src),
                        LogicalSelectValue::Const(self.literal_const_ref(raw_pc, c as usize)?),
                    );
                    raw_index += 1;
                }
                LuauOpcode::Not | LuauOpcode::Minus | LuauOpcode::Length => {
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
                LuauOpcode::SetList => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let values = if c == 0 {
                        ValuePack::Open(reg_from_u8(b))
                    } else {
                        ValuePack::Fixed(RegRange::new(
                            reg_from_u8(b),
                            range_len_inclusive(
                                usize::from(b),
                                usize::from(b) + usize::from(c) - 2,
                            ),
                        ))
                    };
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetList(SetListInstr {
                            base: reg_from_u8(a),
                            values,
                            start_index: required_aux(raw_pc, opcode, extra)?,
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::GetVarArgs => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    self.invalidate_vararg_results(a, b);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::VarArg(VarArgInstr {
                            results: call_result_pack(a, u16::from(b)),
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::CloseUpVals => {
                    let a = expect_a(raw_pc, opcode, operands)?;
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Close(CloseInstr {
                            from: reg_from_u8(a),
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::NewClosure => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    let proto = self.proto_ref(raw_pc, d as usize)?;
                    let capture_count = usize::from(
                        self.raw.common.children[proto.index()]
                            .common
                            .upvalues
                            .common
                            .count,
                    );
                    self.invalidate_written_reg(dst);
                    let (captures, raw_indices) =
                        self.decode_closure_captures(raw_index, raw_pc, capture_count)?;
                    self.emit(
                        Some(raw_index),
                        raw_indices,
                        PendingLowInstr::Ready(LowInstr::Closure(ClosureInstr {
                            dst,
                            proto,
                            captures,
                            creation: ClosureCreation::Fresh,
                        })),
                    );
                    raw_index += 1 + capture_count;
                }
                LuauOpcode::DupClosure => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    let proto = self.proto_ref_for_closure_const(raw_pc, d as usize)?;
                    let capture_count = usize::from(
                        self.raw.common.children[proto.index()]
                            .common
                            .upvalues
                            .common
                            .count,
                    );
                    self.invalidate_written_reg(dst);
                    let (captures, raw_indices) =
                        self.decode_closure_captures(raw_index, raw_pc, capture_count)?;
                    let shared = SharedClosureRef(d as usize);
                    self.emit(
                        Some(raw_index),
                        raw_indices,
                        PendingLowInstr::Ready(LowInstr::Closure(ClosureInstr {
                            dst,
                            proto,
                            captures,
                            creation: ClosureCreation::Reusable(shared),
                        })),
                    );
                    raw_index += 1 + capture_count;
                }
                LuauOpcode::Capture => {
                    return Err(TransformError::InvalidClosureCapture {
                        raw_pc,
                        capture_pc: raw_pc,
                        found: opcode.label(),
                    });
                }
                LuauOpcode::ForNPrep => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let limit = reg_from_u8(a);
                    let step = Reg(limit.index() + 1);
                    let index = Reg(limit.index() + 2);
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::NumericForInit {
                            index,
                            limit,
                            step,
                            binding: index,
                            body_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_pc(raw_pc, self.next_raw_pc(raw_index))?,
                            ),
                            exit_target: TargetPlaceholder::Raw(
                                self.jump_target(raw_pc, i32::from(d))?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                LuauOpcode::ForNLoop => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let limit = reg_from_u8(a);
                    let step = Reg(limit.index() + 1);
                    let index = Reg(limit.index() + 2);
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::NumericForLoop {
                            index,
                            limit,
                            step,
                            binding: index,
                            body_target: TargetPlaceholder::Raw(
                                self.jump_target(raw_pc, i32::from(d))?,
                            ),
                            exit_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_pc(raw_pc, self.next_raw_pc(raw_index))?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                LuauOpcode::ForGPrep | LuauOpcode::ForGPrepInext | LuauOpcode::ForGPrepNext => {
                    let (_, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Jump {
                            target: TargetPlaceholder::Raw(self.jump_target(raw_pc, i32::from(d))?),
                        },
                    );
                    raw_index += 1;
                }
                LuauOpcode::ForGLoop => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let aux = required_aux(raw_pc, opcode, extra)?;
                    let var_count = (aux & 0xff) as usize;
                    if var_count == 0 {
                        return Err(TransformError::UnexpectedOperands {
                            raw_pc,
                            opcode: opcode.label(),
                            expected: "AUX variable count in 1..=255",
                        });
                    }
                    let iterator = reg_from_u8(a);
                    let bindings = RegRange::new(Reg(iterator.index() + 3), var_count);
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GenericForCall(GenericForCallInstr {
                            iterator,
                            state: Reg(iterator.index() + 1),
                            control: Reg(iterator.index() + 2),
                            results: ResultPack::Fixed(bindings),
                        })),
                    );
                    self.emit(
                        None,
                        vec![raw_index],
                        PendingLowInstr::GenericForLoop {
                            control_target: Reg(iterator.index() + 2),
                            bindings,
                            body_target: TargetPlaceholder::Raw(
                                self.jump_target(raw_pc, i32::from(d))?,
                            ),
                            exit_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_pc(raw_pc, self.next_raw_pc(raw_index))?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                LuauOpcode::JumpX => {
                    // JUMPX 是 Luau 的 24-bit 扩展 JUMP，operand 形态是 `E`，offset 范围比
                    // 普通 JUMP 大但语义完全一致；按普通无条件跳转处理即可。
                    let e = expect_e(raw_pc, opcode, operands)?;
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Jump {
                            target: TargetPlaceholder::Raw(self.jump_target(raw_pc, e)?),
                        },
                    );
                    raw_index += 1;
                }
            }
        }

        if let Some(raw_index) = self.pending_fastcall_calls.iter().position(Option::is_some) {
            return Err(TransformError::UnexpectedOperands {
                raw_pc: self.raw.common.instructions[raw_index].pc(),
                opcode: "CALL",
                expected: "FASTCALL protocol consumed exactly once",
            });
        }

        self.finish()
    }
}
