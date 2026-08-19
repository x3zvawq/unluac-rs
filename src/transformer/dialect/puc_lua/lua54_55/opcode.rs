//! 将 Lua 5.4/5.5 opcode dispatch 降低为共享 LowInstr；依赖 adapter 和 ProtoLowerer 辅助，不负责 chunk 递归；例如处理 TBC、metamethod helper 与 for 协议。

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
                            src: reg_from_u8(b),
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::LoadI => {
                    let (a, sbx) = expect_asbx(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
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
                FamilyOpcode::LoadF => {
                    let (a, sbx) = expect_asbx(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
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
                FamilyOpcode::LoadFalse | FamilyOpcode::LFalseSkip | FamilyOpcode::LoadTrue => {
                    self.lower_boolean_constant(raw_index, raw_pc, opcode, operands)?;
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
                    let (a, b, c, _) = expect_abck(raw_pc, opcode, operands)?;
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
                            key: AccessKey::Const(self.const_ref(raw_pc, c as usize)?),
                            kind: GetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::GetTable => {
                    let (a, b, c, _) = expect_abck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
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
                FamilyOpcode::GetI => {
                    let (a, b, c, _) = expect_abck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst,
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Integer(i64::from(c)),
                            kind: GetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::GetField => {
                    let (a, b, c, _) = expect_abck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst,
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Const(self.const_ref(raw_pc, c as usize)?),
                            kind: GetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::GetVarg => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
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
                FamilyOpcode::SetTabUp => {
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
                            value: k_value_operand(self.raw, raw_pc, c, k)?,
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
                    let (a, b, c, k) = expect_abck(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Reg(reg_from_u8(a)),
                            key: AccessKey::Reg(reg_from_u8(b)),
                            value: k_value_operand(self.raw, raw_pc, c, k)?,
                            kind: SetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::SetI => {
                    let (a, b, c, k) = expect_abck(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Reg(reg_from_u8(a)),
                            key: AccessKey::Integer(i64::from(b)),
                            value: k_value_operand(self.raw, raw_pc, c, k)?,
                            kind: SetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::SetField => {
                    let (a, b, c, k) = expect_abck(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Reg(reg_from_u8(a)),
                            key: AccessKey::Const(self.const_ref(raw_pc, b as usize)?),
                            value: k_value_operand(self.raw, raw_pc, c, k)?,
                            kind: SetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::ErrNNil => {
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
                FamilyOpcode::NewTable => {
                    let (a, _, _, _) = self.table_operands(raw_pc, opcode, operands)?;
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
                    let (a, b, c, k) = expect_abck(raw_pc, opcode, operands)?;
                    let callee = reg_from_u8(a);
                    let self_arg = Reg(callee.index() + 1);
                    let method_key = match self.dialect {
                        FamilyDialect::Lua54 => self.access_key(raw_pc, c, k)?,
                        FamilyDialect::Lua55 => {
                            AccessKey::Const(self.const_ref(raw_pc, c as usize)?)
                        }
                    };
                    let method_name = match method_key {
                        AccessKey::Const(const_ref) => Some(const_ref),
                        AccessKey::Reg(_) | AccessKey::Integer(_) => None,
                    };
                    self.pending_methods.invalidate_reg(callee);
                    self.pending_methods.invalidate_reg(self_arg);
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
                            base: AccessBase::Reg(self_arg),
                            key: method_key,
                            kind: GetTableKind::Method,
                        })),
                    );
                    self.pending_methods
                        .set(callee, self_arg, method_name, None);
                    raw_index += 1;
                }
                FamilyOpcode::AddI | FamilyOpcode::ShrI | FamilyOpcode::ShlI => {
                    let (a, b, sc, _) = expect_absck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    let shape = immediate_binary_shape(
                        self.raw,
                        &self.word_code_index,
                        raw_index,
                        binary_op_kind(opcode),
                        b,
                        sc,
                        MetamethodBinarySpec {
                            owner_opcode: opcode,
                            helper_opcode: FamilyOpcode::MMBinI,
                            inspect_helper: match self.dialect {
                                FamilyDialect::Lua54 => inspect_lua54_asbck_helper,
                                FamilyDialect::Lua55 => inspect_lua55_asbck_helper,
                            },
                            opcode_label: FamilyOpcode::label,
                        },
                    )?;
                    let reg = ValueOperand::Reg(reg_from_u8(b));
                    let immediate = ValueOperand::Integer(i64::from(shape.operand));
                    let (lhs, rhs) = if shape.flipped {
                        (immediate, reg)
                    } else {
                        (reg, immediate)
                    };
                    self.pending_methods.invalidate_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index, shape.helper_index],
                        PendingLowInstr::Ready(LowInstr::BinaryOp(BinaryOpInstr {
                            dst,
                            op: shape.op,
                            lhs,
                            rhs,
                        })),
                    );
                    raw_index = shape.helper_index + 1;
                }
                FamilyOpcode::AddK
                | FamilyOpcode::SubK
                | FamilyOpcode::MulK
                | FamilyOpcode::ModK
                | FamilyOpcode::PowK
                | FamilyOpcode::DivK
                | FamilyOpcode::IdivK
                | FamilyOpcode::BandK
                | FamilyOpcode::BorK
                | FamilyOpcode::BxorK => {
                    let (a, b, c, _) = expect_abck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    let op = binary_op_kind(opcode);
                    let shape = constant_binary_shape(
                        self.raw,
                        &self.word_code_index,
                        raw_index,
                        op,
                        b,
                        c,
                        MetamethodBinarySpec {
                            owner_opcode: opcode,
                            helper_opcode: FamilyOpcode::MMBinK,
                            inspect_helper: match self.dialect {
                                FamilyDialect::Lua54 => inspect_lua54_abck_helper,
                                FamilyDialect::Lua55 => inspect_lua55_abck_helper,
                            },
                            opcode_label: FamilyOpcode::label,
                        },
                    )?;
                    let reg = ValueOperand::Reg(reg_from_u8(b));
                    let constant = ValueOperand::Const(self.const_ref(raw_pc, c as usize)?);
                    let (lhs, rhs) = if shape.flipped {
                        (constant, reg)
                    } else {
                        (reg, constant)
                    };
                    self.pending_methods.invalidate_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index, shape.helper_index],
                        PendingLowInstr::Ready(LowInstr::BinaryOp(BinaryOpInstr {
                            dst,
                            op,
                            lhs,
                            rhs,
                        })),
                    );
                    raw_index = shape.helper_index + 1;
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
                    let (a, b, c, _) = expect_abck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    let op = binary_op_kind(opcode);
                    let shape = register_binary_shape(
                        self.raw,
                        &self.word_code_index,
                        raw_index,
                        op,
                        b,
                        c,
                        MetamethodBinarySpec {
                            owner_opcode: opcode,
                            helper_opcode: FamilyOpcode::MMBin,
                            inspect_helper: match self.dialect {
                                FamilyDialect::Lua54 => inspect_lua54_abck_helper,
                                FamilyDialect::Lua55 => inspect_lua55_abck_helper,
                            },
                            opcode_label: FamilyOpcode::label,
                        },
                    )?;
                    self.pending_methods.invalidate_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index, shape.helper_index],
                        PendingLowInstr::Ready(LowInstr::BinaryOp(BinaryOpInstr {
                            dst,
                            op,
                            lhs: ValueOperand::Reg(reg_from_u8(b)),
                            rhs: ValueOperand::Reg(reg_from_u8(c)),
                        })),
                    );
                    raw_index = shape.helper_index + 1;
                }
                FamilyOpcode::MMBin | FamilyOpcode::MMBinI | FamilyOpcode::MMBinK => {
                    return Err(TransformError::UnexpectedStandaloneMetamethodHelper {
                        raw_pc,
                        opcode: opcode.label(),
                    });
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
                            src: reg_from_u8(b),
                        })),
                    );
                    raw_index += 1;
                }
                FamilyOpcode::Concat => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.pending_methods.invalidate_reg(dst);
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
                FamilyOpcode::Close => {
                    self.pending_methods.clear();
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
                FamilyOpcode::Tbc => {
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
                FamilyOpcode::Jmp => {
                    let sj = expect_asj(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Jump {
                            target: TargetPlaceholder::Raw(jump_target_sj(
                                &self.word_code_index,
                                raw_pc,
                                extra.pc,
                                sj,
                            )?),
                        },
                    );
                    raw_index += 1;
                }
                FamilyOpcode::Eq | FamilyOpcode::Lt | FamilyOpcode::Le => {
                    let (a, b, k) = expect_abk(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let cond = BranchCond::compare(
                        branch_predicate(opcode),
                        CondOperand::Reg(reg_from_u8(a)),
                        CondOperand::Reg(reg_from_u8(b)),
                        !k,
                    );

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
                FamilyOpcode::EqK => {
                    let (a, b, k) = expect_abk(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let cond = BranchCond::compare(
                        BranchPredicate::Eq,
                        CondOperand::Reg(reg_from_u8(a)),
                        CondOperand::Const(self.const_ref(raw_pc, b as usize)?),
                        !k,
                    );

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
                FamilyOpcode::EqI
                | FamilyOpcode::LtI
                | FamilyOpcode::LeI
                | FamilyOpcode::GtI
                | FamilyOpcode::GeI => {
                    let (a, sb, c, k) = expect_asbck(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let rhs = immediate_cond_operand(sb, c != 0);
                    let (predicate, lhs, rhs) =
                        compare_immediate_shape(opcode, reg_from_u8(a), rhs);
                    let cond = BranchCond::compare(predicate, lhs, rhs, !k);

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
                FamilyOpcode::Test => {
                    let (a, k) = expect_ak(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let cond = BranchCond::truthy(CondOperand::Reg(reg_from_u8(a)), !k);

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
                FamilyOpcode::TestSet => {
                    let (a, b, k) = expect_abk(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let cond = BranchCond::truthy(CondOperand::Reg(reg_from_u8(b)), !k);

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
                FamilyOpcode::Call => {
                    let (a, b, c, _) = expect_abck(raw_pc, opcode, operands)?;
                    let results = call_result_pack(a, u16::from(c));
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
                        call_args_pack(a, u16::from(b)),
                        results,
                        kind,
                        method_name,
                    );
                    raw_index += 1;
                }
                FamilyOpcode::TailCall => {
                    let (a, b, _, k) = expect_abck(raw_pc, opcode, operands)?;
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
                        call_args_pack(a, u16::from(b)),
                        kind,
                        method_name,
                        k,
                    );
                    raw_index += 1;
                }
                FamilyOpcode::Return => {
                    let (a, b, _, k) = expect_abck(raw_pc, opcode, operands)?;
                    self.pending_methods.clear();
                    emit_return(
                        &mut self.lowering,
                        raw_index,
                        return_pack(a, u16::from(b)),
                        k,
                    );
                    raw_index += 1;
                }
                FamilyOpcode::Return0 => {
                    self.pending_methods.clear();
                    emit_return(
                        &mut self.lowering,
                        raw_index,
                        ValuePack::Fixed(RegRange::new(Reg(0), 0)),
                        false,
                    );
                    raw_index += 1;
                }
                FamilyOpcode::Return1 => {
                    let a = expect_a(raw_pc, opcode, operands)?;
                    self.pending_methods.clear();
                    emit_return(
                        &mut self.lowering,
                        raw_index,
                        ValuePack::Fixed(RegRange::new(reg_from_u8(a), 1)),
                        false,
                    );
                    raw_index += 1;
                }
                FamilyOpcode::ForLoop => {
                    self.pending_methods.clear();
                    let (a, bx) = expect_abx(raw_pc, opcode, operands)?;
                    let regs =
                        numeric_for_regs(reg_from_u8(a), self.dialect.numeric_for_binding_offset());
                    let body_target =
                        jump_target_back_bx(&self.word_code_index, raw_pc, extra.pc, bx)?;
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
                    let (a, bx) = expect_abx(raw_pc, opcode, operands)?;
                    let loop_raw =
                        jump_target_forward_bx(&self.word_code_index, raw_pc, extra.pc, bx)?;
                    let target_opcode = opcode_at(self.raw, loop_raw, self.dialect);
                    if target_opcode != FamilyOpcode::ForLoop {
                        return Err(TransformError::InvalidNumericForPair {
                            raw_pc,
                            target_raw: raw_pc_at(self.raw, loop_raw) as usize,
                            found: target_opcode.label(),
                        });
                    }
                    let regs =
                        numeric_for_regs(reg_from_u8(a), self.dialect.numeric_for_binding_offset());
                    let body_target =
                        self.ensure_targetable_pc(raw_pc, next_raw_pc(self.raw, raw_index))?;
                    let exit_target =
                        self.ensure_targetable_pc(raw_pc, next_raw_pc(self.raw, loop_raw))?;
                    emit_numeric_for_init(
                        &mut self.lowering,
                        raw_index,
                        regs,
                        body_target,
                        exit_target,
                    );
                    raw_index += 1;
                }
                FamilyOpcode::TForPrep => {
                    self.pending_methods.clear();
                    let (a, bx) = expect_abx(raw_pc, opcode, operands)?;
                    let iterator = reg_from_u8(a);
                    let control_source = Reg(iterator.index() + 2);
                    let closing_source = Reg(iterator.index() + 3);
                    let (control_target, closing_target) = match self.dialect {
                        FamilyDialect::Lua54 => (control_source, closing_source),
                        FamilyDialect::Lua55 => (closing_source, control_source),
                    };
                    let call_target =
                        jump_target_forward_bx(&self.word_code_index, raw_pc, extra.pc, bx)?;
                    emit_generic_for_prep(
                        &mut self.lowering,
                        raw_index,
                        GenericForPrepInstr {
                            iterator,
                            state: Reg(iterator.index() + 1),
                            control_source,
                            closing_source,
                            control_target,
                            closing_target,
                        },
                        call_target,
                    );
                    raw_index += 1;
                }
                FamilyOpcode::TForCall => {
                    self.pending_methods.clear();
                    let (a, c) = expect_ac(raw_pc, opcode, operands)?;
                    let pair = self.generic_for_pair(raw_index, a, c)?;
                    let state_start = reg_from_u8(a);
                    emit_generic_for_call(
                        &mut self.lowering,
                        raw_index,
                        state_start,
                        self.dialect.generic_for_control_offset(),
                        self.dialect.generic_for_binding_offset(),
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
                    let (a, b, c, k) = self.table_operands(raw_pc, opcode, operands)?;
                    let base_index = u32::from(c)
                        + if k {
                            self.extra_arg(raw_pc, opcode, extra.extra_arg)?
                                * self.dialect.extraarg_scale()
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
                    let (a, c) = match self.dialect {
                        FamilyDialect::Lua54 => expect_ac(raw_pc, opcode, operands)?,
                        FamilyDialect::Lua55 => {
                            let (a, _, c, _) = expect_abck(raw_pc, opcode, operands)?;
                            (a, c)
                        }
                    };
                    self.pending_methods.clear();
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
                FamilyOpcode::VarArgPrep => {
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
