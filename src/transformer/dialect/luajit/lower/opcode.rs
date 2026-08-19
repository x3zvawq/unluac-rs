//! 将 LuaJIT opcode dispatch 降低为共享 LowInstr；依赖 ProtoLowerer 的常量/跳转辅助，不负责 chunk 递归与最终映射校验；例如把 ISLT、CALLM、TFORL 等指令写入 pending lowering。

use super::*;

impl<'a> ProtoLowerer<'a> {
    pub(super) fn lower(&mut self) -> Result<(Vec<LowInstr>, LoweringMap), TransformError> {
        let mut raw_index = 0_usize;

        while raw_index < self.raw.common.instructions.len() {
            let raw_instr = &self.raw.common.instructions[raw_index];
            let (opcode, operands, extra) = raw_instr
                .luajit()
                .expect("luajit lowerer should only decode luajit instructions");
            let raw_pc = extra.pc;
            self.invalidate_bypassed_at(raw_index);

            match opcode {
                LuaJitOpcode::IsType | LuaJitOpcode::IsNum => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let kind = lua_jit_type_guard_kind(raw_pc, opcode, d)?;
                    if kind.normalizes_subject() {
                        self.invalidate_written_reg(reg_from_u8(a));
                    }
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::TypeGuard(TypeGuardInstr {
                            subject: reg_from_u8(a),
                            kind,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::Mov => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.invalidate_written_reg(reg_from_u8(a));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Move(MoveInstr {
                            dst: reg_from_u8(a),
                            src: reg_from_u16(d),
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::Not | LuaJitOpcode::Unm | LuaJitOpcode::Len => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.invalidate_written_reg(reg_from_u8(a));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::UnaryOp(UnaryOpInstr {
                            dst: reg_from_u8(a),
                            op: unary_op_kind(opcode),
                            src: reg_from_u16(d),
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::AddVN
                | LuaJitOpcode::SubVN
                | LuaJitOpcode::MulVN
                | LuaJitOpcode::DivVN
                | LuaJitOpcode::ModVN
                | LuaJitOpcode::AddVV
                | LuaJitOpcode::SubVV
                | LuaJitOpcode::MulVV
                | LuaJitOpcode::DivVV
                | LuaJitOpcode::ModVV
                | LuaJitOpcode::Pow => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    self.invalidate_written_reg(reg_from_u8(a));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::BinaryOp(BinaryOpInstr {
                            dst: reg_from_u8(a),
                            op: binary_op_kind(opcode),
                            lhs: ValueOperand::Reg(reg_from_u8(b)),
                            rhs: if matches!(
                                opcode,
                                LuaJitOpcode::AddVN
                                    | LuaJitOpcode::SubVN
                                    | LuaJitOpcode::MulVN
                                    | LuaJitOpcode::DivVN
                                    | LuaJitOpcode::ModVN
                            ) {
                                ValueOperand::Const(self.knum_const_ref(raw_pc, usize::from(c))?)
                            } else {
                                ValueOperand::Reg(reg_from_u8(c))
                            },
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::AddNV
                | LuaJitOpcode::SubNV
                | LuaJitOpcode::MulNV
                | LuaJitOpcode::DivNV
                | LuaJitOpcode::ModNV => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    self.invalidate_written_reg(reg_from_u8(a));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::BinaryOp(BinaryOpInstr {
                            dst: reg_from_u8(a),
                            op: binary_op_kind(opcode),
                            lhs: ValueOperand::Const(self.knum_const_ref(raw_pc, usize::from(c))?),
                            rhs: ValueOperand::Reg(reg_from_u8(b)),
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::Cat => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    self.invalidate_written_reg(reg_from_u8(a));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Concat(ConcatInstr {
                            dst: reg_from_u8(a),
                            src: RegRange::new(
                                reg_from_u8(b),
                                range_len_inclusive(usize::from(b), usize::from(c)),
                            ),
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::KStr => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.invalidate_written_reg(reg_from_u8(a));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadConst(LoadConstInstr {
                            dst: reg_from_u8(a),
                            value: self.kgc_string_const_ref(raw_pc, usize::from(d))?,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::KCData => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.invalidate_written_reg(reg_from_u8(a));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadConst(LoadConstInstr {
                            dst: reg_from_u8(a),
                            value: self.kgc_literal_const_ref(raw_pc, usize::from(d))?,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::KShort => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.invalidate_written_reg(reg_from_u8(a));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadInteger(LoadIntegerInstr {
                            dst: reg_from_u8(a),
                            value: i64::from(i16::from_ne_bytes(d.to_ne_bytes())),
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::KNum => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.invalidate_written_reg(reg_from_u8(a));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadConst(LoadConstInstr {
                            dst: reg_from_u8(a),
                            value: self.knum_const_ref(raw_pc, usize::from(d))?,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::KPri => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.invalidate_written_reg(reg_from_u8(a));
                    match d {
                        BCDUMP_KPRI_NIL => {
                            self.emit(
                                Some(raw_index),
                                vec![raw_index],
                                PendingLowInstr::Ready(LowInstr::LoadNil(LoadNilInstr {
                                    dst: RegRange::new(reg_from_u8(a), 1),
                                })),
                            );
                        }
                        BCDUMP_KPRI_FALSE | BCDUMP_KPRI_TRUE => {
                            self.emit(
                                Some(raw_index),
                                vec![raw_index],
                                PendingLowInstr::Ready(LowInstr::LoadBool(LoadBoolInstr {
                                    dst: reg_from_u8(a),
                                    value: d == BCDUMP_KPRI_TRUE,
                                })),
                            );
                        }
                        _ => {
                            return Err(TransformError::UnsupportedOpcode {
                                raw_pc,
                                opcode: opcode.label(),
                            });
                        }
                    }
                    raw_index += 1;
                }
                LuaJitOpcode::KNil => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let len = range_len_inclusive(usize::from(a), usize::from(d));
                    self.invalidate_written_range(RegRange::new(reg_from_u8(a), len));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::LoadNil(LoadNilInstr {
                            dst: RegRange::new(reg_from_u8(a), len),
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::UGet => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.invalidate_written_reg(reg_from_u8(a));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetUpvalue(GetUpvalueInstr {
                            dst: reg_from_u8(a),
                            src: self.upvalue_ref(raw_pc, usize::from(d))?.into(),
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::USetV => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetUpvalue(SetUpvalueInstr {
                            dst: self.upvalue_ref(raw_pc, usize::from(a))?.into(),
                            src: ValueOperand::Reg(reg_from_u16(d)),
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::USetS => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetUpvalue(SetUpvalueInstr {
                            dst: self.upvalue_ref(raw_pc, usize::from(a))?.into(),
                            src: ValueOperand::Const(
                                self.kgc_string_const_ref(raw_pc, usize::from(d))?,
                            ),
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::USetN => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetUpvalue(SetUpvalueInstr {
                            dst: self.upvalue_ref(raw_pc, usize::from(a))?.into(),
                            src: ValueOperand::Const(self.knum_const_ref(raw_pc, usize::from(d))?),
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::USetP => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let src = match d {
                        BCDUMP_KPRI_NIL => ValueOperand::Nil,
                        BCDUMP_KPRI_FALSE => ValueOperand::Boolean(false),
                        BCDUMP_KPRI_TRUE => ValueOperand::Boolean(true),
                        _ => {
                            return Err(TransformError::UnsupportedOpcode {
                                raw_pc,
                                opcode: opcode.label(),
                            });
                        }
                    };
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetUpvalue(SetUpvalueInstr {
                            dst: self.upvalue_ref(raw_pc, usize::from(a))?.into(),
                            src,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::FNew => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.invalidate_written_reg(reg_from_u8(a));
                    let proto = self.proto_ref_from_kgc_child(raw_pc, usize::from(d))?;
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
                            dst: reg_from_u8(a),
                            proto,
                            captures,
                            creation: crate::transformer::ClosureCreation::Fresh,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::TNew => {
                    let (a, _) = expect_ad(raw_pc, opcode, operands)?;
                    self.invalidate_written_reg(reg_from_u8(a));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::NewTable(NewTableInstr {
                            dst: reg_from_u8(a),
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::TDup => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    let table = self.table_const(raw_pc, usize::from(d))?.clone();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::NewTable(NewTableInstr { dst })),
                    );
                    for (index, literal) in table.array.iter().enumerate() {
                        if matches!(literal.value, RawLiteralConst::Nil) {
                            continue;
                        }
                        self.emit(
                            None,
                            vec![raw_index],
                            PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                                base: AccessBase::Reg(dst),
                                key: AccessKey::Integer(index as i64),
                                value: self.table_literal_value(literal),
                                kind: SetTableKind::Normal,
                            })),
                        );
                    }
                    for record in &table.hash {
                        if matches!(record.value.value, RawLiteralConst::Nil) {
                            continue;
                        }
                        self.emit(
                            None,
                            vec![raw_index],
                            PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                                base: AccessBase::Reg(dst),
                                key: self.table_literal_key(&record.key),
                                value: self.table_literal_value(&record.value),
                                kind: SetTableKind::Normal,
                            })),
                        );
                    }
                    raw_index += 1;
                }
                LuaJitOpcode::GGet => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.invalidate_written_reg(reg_from_u8(a));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst: reg_from_u8(a),
                            base: AccessBase::Env,
                            key: AccessKey::Const(
                                self.kgc_string_const_ref(raw_pc, usize::from(d))?,
                            ),
                            kind: GetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::GSet => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Env,
                            key: AccessKey::Const(
                                self.kgc_string_const_ref(raw_pc, usize::from(d))?,
                            ),
                            value: ValueOperand::Reg(reg_from_u8(a)),
                            kind: SetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::TGetV | LuaJitOpcode::TGetR => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    let method = if opcode == LuaJitOpcode::TGetV {
                        self.large_method_setup(raw_index, a, b, c)?
                    } else {
                        None
                    };
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst,
                            base: AccessBase::Reg(
                                method.map_or(reg_from_u8(b), |setup| setup.self_arg),
                            ),
                            key: method.map_or(AccessKey::Reg(reg_from_u8(c)), |setup| {
                                AccessKey::Const(setup.method_name)
                            }),
                            kind: if opcode == LuaJitOpcode::TGetR {
                                GetTableKind::Raw
                            } else if method.is_some() {
                                GetTableKind::Method
                            } else {
                                GetTableKind::Normal
                            },
                        })),
                    );
                    if let Some(setup) = method {
                        self.pending_methods.set(
                            dst,
                            setup.self_arg,
                            Some(setup.method_name),
                            Some(raw_index),
                        );
                    }
                    raw_index += 1;
                }
                LuaJitOpcode::TGetS => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    let method_name = self.kgc_string_const_ref(raw_pc, usize::from(c))?;
                    let method = self.short_method_setup(raw_index, a, b, method_name)?;
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst,
                            base: AccessBase::Reg(
                                method.map_or(reg_from_u8(b), |setup| setup.self_arg),
                            ),
                            key: AccessKey::Const(method_name),
                            kind: if method.is_some() {
                                GetTableKind::Method
                            } else {
                                GetTableKind::Normal
                            },
                        })),
                    );
                    if let Some(setup) = method {
                        self.pending_methods.set(
                            dst,
                            setup.self_arg,
                            Some(setup.method_name),
                            Some(raw_index),
                        );
                    }
                    raw_index += 1;
                }
                LuaJitOpcode::TGetB => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    self.invalidate_written_reg(reg_from_u8(a));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst: reg_from_u8(a),
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Integer(i64::from(c)),
                            kind: GetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::TSetV | LuaJitOpcode::TSetR => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Reg(reg_from_u8(c)),
                            value: ValueOperand::Reg(reg_from_u8(a)),
                            kind: if opcode == LuaJitOpcode::TSetR {
                                SetTableKind::Raw
                            } else {
                                SetTableKind::Normal
                            },
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::TSetS => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Const(
                                self.kgc_string_const_ref(raw_pc, usize::from(c))?,
                            ),
                            value: ValueOperand::Reg(reg_from_u8(a)),
                            kind: SetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::TSetB => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Integer(i64::from(c)),
                            value: ValueOperand::Reg(reg_from_u8(a)),
                            kind: SetTableKind::Normal,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::TSetM => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let start_index = self.tsetm_start_index(raw_pc, usize::from(d))?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetList(SetListInstr {
                            base: Reg(usize::from(a).saturating_sub(1)),
                            values: ValuePack::Open(reg_from_u8(a)),
                            start_index,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::Call => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let callee = reg_from_u8(a);
                    let results = call_results_pack(a, b);
                    let (kind, method_name) = self.pending_methods.consume_call_info(
                        callee,
                        self.call_arg_start(a),
                        c != 1,
                        results,
                    );
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Call(CallInstr {
                            callee,
                            args: self.call_args_pack(a, c),
                            results,
                            kind,
                            method_name,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::CallM => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let callee = reg_from_u8(a);
                    let first_arg = self.call_arg_start(a);
                    let results = call_results_pack(a, b);
                    let (kind, method_name) =
                        self.pending_methods
                            .consume_call_info(callee, first_arg, c != 0, results);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Call(CallInstr {
                            callee,
                            args: ValuePack::Open(first_arg),
                            results,
                            kind,
                            method_name,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::CallT => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let callee = reg_from_u8(a);
                    let (kind, method_name) = self.pending_methods.consume_call_info(
                        callee,
                        self.call_arg_start(a),
                        d != 1,
                        ResultPack::Ignore,
                    );
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::TailCall(TailCallInstr {
                            callee,
                            args: self.tail_call_args_pack(a, d),
                            kind,
                            method_name,
                        })),
                    );
                    self.pending_methods.clear();
                    raw_index += 1;
                }
                LuaJitOpcode::CallMT => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let callee = reg_from_u8(a);
                    let first_arg = self.call_arg_start(a);
                    let (kind, method_name) = self.pending_methods.consume_call_info(
                        callee,
                        first_arg,
                        d != 0,
                        ResultPack::Ignore,
                    );
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::TailCall(TailCallInstr {
                            callee,
                            args: ValuePack::Open(first_arg),
                            kind,
                            method_name,
                        })),
                    );
                    self.pending_methods.clear();
                    raw_index += 1;
                }
                LuaJitOpcode::VArg => {
                    let (a, b, _) = expect_abc(raw_pc, opcode, operands)?;
                    self.invalidate_result_pack(call_results_pack(a, b));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::VarArg(VarArgInstr {
                            results: call_results_pack(a, b),
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::Ret => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.pending_methods.clear();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Return(ReturnInstr {
                            values: return_pack(a, d),
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::RetM => {
                    let (a, _d) = expect_ad(raw_pc, opcode, operands)?;
                    self.pending_methods.clear();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Return(ReturnInstr {
                            values: ValuePack::Open(reg_from_u8(a)),
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::Ret0 => {
                    let _ = expect_ad(raw_pc, opcode, operands)?;
                    self.pending_methods.clear();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Return(ReturnInstr {
                            values: ValuePack::Fixed(RegRange::new(Reg(0), 0)),
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::Ret1 => {
                    let (a, _d) = expect_ad(raw_pc, opcode, operands)?;
                    self.pending_methods.clear();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Return(ReturnInstr {
                            values: ValuePack::Fixed(RegRange::new(reg_from_u8(a), 1)),
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::ForI | LuaJitOpcode::JForI => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let exit_target = self.jump_target(raw_pc, raw_index, d)?;
                    if exit_target == 0 {
                        return Err(TransformError::InvalidJumpTarget {
                            raw_pc,
                            target_raw: exit_target,
                            instr_count: self.raw.common.instructions.len(),
                        });
                    }
                    let loop_raw = exit_target - 1;
                    let loop_opcode = opcode_at(self.raw, loop_raw);
                    if !matches!(
                        loop_opcode,
                        LuaJitOpcode::ForL | LuaJitOpcode::IForL | LuaJitOpcode::JForL
                    ) {
                        return Err(TransformError::InvalidNumericForPair {
                            raw_pc,
                            target_raw: loop_raw,
                            found: loop_opcode.label(),
                        });
                    }
                    let index = reg_from_u8(a);
                    self.invalidate_written_reg(index);
                    self.invalidate_written_reg(Reg(index.index() + 3));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::NumericForInit {
                            index,
                            limit: Reg(index.index() + 1),
                            step: Reg(index.index() + 2),
                            binding: Reg(index.index() + 3),
                            body_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_raw(raw_pc, raw_index + 1)?,
                            ),
                            exit_target: TargetPlaceholder::Raw(exit_target),
                        },
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::JForL => {
                    return Err(TransformError::UnsupportedOpcode {
                        raw_pc,
                        opcode: opcode.label(),
                    });
                }
                LuaJitOpcode::ForL | LuaJitOpcode::IForL => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let index = reg_from_u8(a);
                    self.invalidate_written_reg(index);
                    self.invalidate_written_reg(Reg(index.index() + 3));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::NumericForLoop {
                            index,
                            limit: Reg(index.index() + 1),
                            step: Reg(index.index() + 2),
                            binding: Reg(index.index() + 3),
                            body_target: TargetPlaceholder::Raw(
                                self.jump_target(raw_pc, raw_index, d)?,
                            ),
                            exit_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_raw(raw_pc, raw_index + 1)?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::IterC | LuaJitOpcode::IterN => {
                    let (a, b, _c) = expect_abc(raw_pc, opcode, operands)?;
                    let helper = self.iter_loop(raw_index, usize::from(b))?;
                    self.invalidate_bypassed_at(helper.helper_index);
                    let iterator = Reg(usize::from(a).saturating_sub(3));
                    self.invalidate_result_pack(ResultPack::Fixed(RegRange::new(
                        reg_from_u8(a),
                        usize::from(b.saturating_sub(1)),
                    )));
                    self.invalidate_written_reg(Reg(usize::from(a).saturating_sub(1)));
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GenericForCall(GenericForCallInstr {
                            iterator,
                            state: Reg(iterator.index() + 1),
                            control: Reg(iterator.index() + 2),
                            results: ResultPack::Fixed(RegRange::new(
                                reg_from_u8(a),
                                usize::from(b.saturating_sub(1)),
                            )),
                        })),
                    );
                    self.emit(
                        None,
                        vec![raw_index, helper.helper_index],
                        PendingLowInstr::GenericForLoop {
                            control_target: Reg(usize::from(a).saturating_sub(1)),
                            bindings: RegRange::new(
                                reg_from_u8(a),
                                usize::from(b.saturating_sub(1)),
                            ),
                            body_target: TargetPlaceholder::Raw(helper.body_target),
                            exit_target: TargetPlaceholder::Raw(helper.exit_target),
                        },
                    );
                    raw_index += 2;
                }
                LuaJitOpcode::Jmp | LuaJitOpcode::IsNext => {
                    // ISNEXT 是 LuaJIT 在 `for k,v in next, t do` 这种"标准 next 迭代器"专门
                    // 化时替换的初始 JMP，operand 形态与 JMP 完全一致 —— 它告诉 JIT 后面紧跟
                    // 的 ITERN 已经被验证为标准 next。对反编译而言它就是个普通的前向跳转，按
                    // JMP 处理即可，不需要单独建模。
                    let (_, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Jump {
                            target: TargetPlaceholder::Raw(self.jump_target(raw_pc, raw_index, d)?),
                        },
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::UClose => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Close(CloseInstr {
                            from: reg_from_u8(a),
                        })),
                    );
                    let target = self.jump_target(raw_pc, raw_index, d)?;
                    if target != raw_index + 1 {
                        self.emit(
                            None,
                            vec![raw_index],
                            PendingLowInstr::Jump {
                                target: TargetPlaceholder::Raw(target),
                            },
                        );
                    }
                    raw_index += 1;
                }
                LuaJitOpcode::IsLt
                | LuaJitOpcode::IsGe
                | LuaJitOpcode::IsLe
                | LuaJitOpcode::IsGt
                | LuaJitOpcode::IsEqV
                | LuaJitOpcode::IsNeV
                | LuaJitOpcode::IsEqS
                | LuaJitOpcode::IsNeS
                | LuaJitOpcode::IsEqN
                | LuaJitOpcode::IsNeN
                | LuaJitOpcode::IsEqP
                | LuaJitOpcode::IsNeP => {
                    let helper = self.helper_jump(raw_index, opcode)?;
                    self.invalidate_bypassed_at(helper.helper_index);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index, helper.helper_index],
                        PendingLowInstr::Branch {
                            cond: self.compare_cond(raw_pc, opcode, operands)?,
                            then_target: TargetPlaceholder::Raw(helper.jump_target),
                            else_target: TargetPlaceholder::Raw(helper.fallthrough_target),
                        },
                    );
                    raw_index += 2;
                }
                LuaJitOpcode::IsT | LuaJitOpcode::IsF => {
                    let helper = self.helper_jump(raw_index, opcode)?;
                    self.invalidate_bypassed_at(helper.helper_index);
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let _ = a;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index, helper.helper_index],
                        PendingLowInstr::Branch {
                            cond: BranchCond::truthy(
                                CondOperand::Reg(reg_from_u16(d)),
                                matches!(opcode, LuaJitOpcode::IsF),
                            ),
                            then_target: TargetPlaceholder::Raw(helper.jump_target),
                            else_target: TargetPlaceholder::Raw(helper.fallthrough_target),
                        },
                    );
                    raw_index += 2;
                }
                LuaJitOpcode::IsTC | LuaJitOpcode::IsFC => {
                    let helper = self.helper_jump(raw_index, opcode)?;
                    self.invalidate_bypassed_at(helper.helper_index);
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    if a != NO_REG && a != (d as u8) {
                        self.invalidate_written_reg(reg_from_u8(a));
                    }
                    if a == NO_REG || a == (d as u8) {
                        self.emit(
                            Some(raw_index),
                            vec![raw_index, helper.helper_index],
                            PendingLowInstr::Branch {
                                cond: BranchCond::truthy(
                                    CondOperand::Reg(reg_from_u16(d)),
                                    matches!(opcode, LuaJitOpcode::IsFC),
                                ),
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
                                cond: BranchCond::truthy(
                                    CondOperand::Reg(reg_from_u16(d)),
                                    matches!(opcode, LuaJitOpcode::IsFC),
                                ),
                                then_target: TargetPlaceholder::Low(move_low),
                                else_target: TargetPlaceholder::Raw(helper.fallthrough_target),
                            },
                        );
                        self.emit(
                            None,
                            vec![raw_index],
                            PendingLowInstr::Ready(LowInstr::Move(MoveInstr {
                                dst: reg_from_u8(a),
                                src: reg_from_u16(d),
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
                    raw_index += 2;
                }
                LuaJitOpcode::JLoop => {
                    return Err(TransformError::UnsupportedOpcode {
                        raw_pc,
                        opcode: opcode.label(),
                    });
                }
                LuaJitOpcode::Loop | LuaJitOpcode::ILoop => {
                    self.mark_raw_target(raw_index);
                    raw_index += 1;
                }
                _ => {
                    return Err(TransformError::UnsupportedOpcode {
                        raw_pc,
                        opcode: opcode.label(),
                    });
                }
            }
        }

        self.finish()
    }
}
