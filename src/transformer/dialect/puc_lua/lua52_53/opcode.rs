//! 将 Lua 5.2/5.3 opcode dispatch 降低为共享 LowInstr；依赖 adapter、环境和跳转辅助，不负责 proto 递归；例如处理 EXTRAARG、环境访问、goto/for 与调用协议。

use super::*;

impl<'a> ProtoLowerer<'a> {
    pub(super) fn lower(&mut self) -> Result<(Vec<LowInstr>, LoweringMap), TransformError> {
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
}
