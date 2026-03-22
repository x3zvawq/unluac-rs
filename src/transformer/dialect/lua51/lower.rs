//! 这个文件实现 Lua 5.1 到统一 low-IR 的 lowering。
//!
//! Lua 5.1 里最麻烦的地方不是普通一对一转译，而是 `TEST/TESTSET` 配合 helper
//! `JMP`、`CLOSURE` 后置 capture、`FORPREP/FORLOOP` 和 `TFORLOOP` 这类模式型
//! 指令。这里一次性把这些模式吃干净，避免后续 CFG 再去理解方言细节。

use crate::parser::{
    DialectInstrExtra, Lua51InstrExtra, Lua51Opcode, Lua51Operands, RawChunk, RawInstr,
    RawInstrOpcode, RawInstrOperands, RawProto,
};
use crate::transformer::{
    AccessBase, AccessKey, BinaryOpInstr, BinaryOpKind, BranchCond, BranchInstr, BranchOperands,
    BranchPredicate, CallInstr, CallKind, Capture, CaptureSource, CloseInstr, ClosureInstr,
    CondOperand, ConcatInstr, ConstRef, DialectCaptureExtra, GenericForCallInstr,
    GenericForLoopInstr, GetTableInstr, GetUpvalueInstr, InstrRef, JumpInstr, LoadBoolInstr,
    LoadConstInstr, LoadNilInstr, LowInstr, LoweredChunk, LoweredProto, LoweringMap, MoveInstr,
    NewTableInstr, NumericForInitInstr, NumericForLoopInstr, ProtoRef, RawInstrRef, Reg,
    RegRange, ResultPack, ReturnInstr, SetListInstr, SetTableInstr, SetUpvalueInstr,
    TailCallInstr, TransformError, UnaryOpInstr, UnaryOpKind, UpvalueRef, ValueOperand,
    ValuePack, VarArgInstr,
};

const BITRK: u16 = 1 << 8;
const LFIELDS_PER_FLUSH: u32 = 50;

pub(crate) fn lower_chunk(chunk: &RawChunk) -> Result<LoweredChunk, TransformError> {
    Ok(LoweredChunk {
        header: chunk.header.clone(),
        main: lower_proto(&chunk.main)?,
        origin: chunk.origin,
    })
}

fn lower_proto(raw: &RawProto) -> Result<LoweredProto, TransformError> {
    let children = raw
        .common
        .children
        .iter()
        .map(lower_proto)
        .collect::<Result<Vec<_>, _>>()?;
    let mut lowerer = ProtoLowerer::new(raw);
    let (instrs, lowering_map) = lowerer.lower()?;

    Ok(LoweredProto {
        source: raw.common.source.clone(),
        line_range: raw.common.line_range,
        signature: raw.common.signature,
        frame: raw.common.frame,
        constants: raw.common.constants.clone(),
        upvalues: raw.common.upvalues.clone(),
        debug_info: raw.common.debug_info.clone(),
        children,
        instrs,
        lowering_map,
        origin: raw.origin,
    })
}

struct ProtoLowerer<'a> {
    raw: &'a RawProto,
    emitted: Vec<EmittedInstr>,
    raw_target_low: Vec<Option<usize>>,
    raw_to_low: Vec<Vec<InstrRef>>,
    pending_methods: Vec<Option<Reg>>,
}

#[derive(Debug, Clone)]
struct EmittedInstr {
    raw_indices: Vec<usize>,
    instr: PendingLowInstr,
}

#[derive(Debug, Clone)]
enum PendingLowInstr {
    Ready(LowInstr),
    Jump {
        target: TargetPlaceholder,
    },
    Branch {
        cond: BranchCond,
        then_target: TargetPlaceholder,
        else_target: TargetPlaceholder,
    },
    NumericForInit {
        index: Reg,
        limit: Reg,
        step: Reg,
        body_target: TargetPlaceholder,
        exit_target: TargetPlaceholder,
    },
    NumericForLoop {
        index: Reg,
        limit: Reg,
        step: Reg,
        body_target: TargetPlaceholder,
        exit_target: TargetPlaceholder,
    },
    GenericForLoop {
        control: RegRange,
        body_target: TargetPlaceholder,
        exit_target: TargetPlaceholder,
    },
}

#[derive(Debug, Clone, Copy)]
enum TargetPlaceholder {
    Raw(usize),
    Low(usize),
}

impl<'a> ProtoLowerer<'a> {
    fn new(raw: &'a RawProto) -> Self {
        let raw_instr_count = raw.common.instructions.len();
        let method_slots = usize::from(raw.common.frame.max_stack_size).saturating_add(2);

        Self {
            raw,
            emitted: Vec::new(),
            raw_target_low: vec![None; raw_instr_count],
            raw_to_low: vec![Vec::new(); raw_instr_count],
            pending_methods: vec![None; method_slots],
        }
    }

    fn lower(&mut self) -> Result<(Vec<LowInstr>, LoweringMap), TransformError> {
        let mut raw_index = 0_usize;

        while raw_index < self.raw.common.instructions.len() {
            let raw_instr = &self.raw.common.instructions[raw_index];
            let (opcode, operands, extra) = decode_lua51(raw_instr);
            let raw_pc = extra.pc;

            match opcode {
                Lua51Opcode::Move => {
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
                Lua51Opcode::LoadK => {
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
                Lua51Opcode::LoadBool => {
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
                        let target_raw = self.ensure_targetable_raw(raw_pc, raw_index + 2)?;
                        self.emit(
                            None,
                            vec![raw_index],
                            PendingLowInstr::Jump {
                                target: TargetPlaceholder::Raw(target_raw),
                            },
                        );
                    }

                    raw_index += 1;
                }
                Lua51Opcode::LoadNil => {
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
                Lua51Opcode::GetUpVal => {
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
                Lua51Opcode::GetGlobal => {
                    let (a, bx) = expect_abx(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst,
                            base: AccessBase::Env,
                            key: AccessKey::Const(self.const_ref(raw_pc, bx as usize)?),
                        })),
                    );
                    raw_index += 1;
                }
                Lua51Opcode::GetTable => {
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
                Lua51Opcode::SetGlobal => {
                    let (a, bx) = expect_abx(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Env,
                            key: AccessKey::Const(self.const_ref(raw_pc, bx as usize)?),
                            value: ValueOperand::Reg(reg_from_u8(a)),
                        })),
                    );
                    raw_index += 1;
                }
                Lua51Opcode::SetUpVal => {
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
                Lua51Opcode::SetTable => {
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
                Lua51Opcode::NewTable => {
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
                Lua51Opcode::Self_ => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let callee = reg_from_u8(a);
                    let self_arg = Reg(callee.index() + 1);
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
                            key: self.access_key(raw_pc, c)?,
                        })),
                    );
                    self.set_pending_method(callee, self_arg);
                    raw_index += 1;
                }
                Lua51Opcode::Add
                | Lua51Opcode::Sub
                | Lua51Opcode::Mul
                | Lua51Opcode::Div
                | Lua51Opcode::Mod
                | Lua51Opcode::Pow => {
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
                Lua51Opcode::Unm | Lua51Opcode::Not | Lua51Opcode::Len => {
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
                Lua51Opcode::Concat => {
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
                Lua51Opcode::Jmp => {
                    self.clear_all_method_hints();
                    let (_, sbx) = expect_asbx(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Jump {
                            target: TargetPlaceholder::Raw(
                                self.jump_target(raw_pc, raw_index, sbx)?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                Lua51Opcode::Eq | Lua51Opcode::Lt | Lua51Opcode::Le => {
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
                    self.emit(
                        Some(raw_index),
                        vec![raw_index, helper.helper_index],
                        PendingLowInstr::Branch {
                            cond,
                            then_target: TargetPlaceholder::Raw(helper.jump_target),
                            else_target: TargetPlaceholder::Raw(helper.fallthrough_target),
                        },
                    );
                    raw_index += 2;
                }
                Lua51Opcode::Test => {
                    self.clear_all_method_hints();
                    let (a, c) = expect_ac(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let cond = BranchCond {
                        predicate: BranchPredicate::Truthy,
                        operands: BranchOperands::Unary(CondOperand::Reg(reg_from_u8(a))),
                        negated: c == 0,
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
                    raw_index += 2;
                }
                Lua51Opcode::TestSet => {
                    self.clear_all_method_hints();
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let cond = BranchCond {
                        predicate: BranchPredicate::Truthy,
                        operands: BranchOperands::Unary(CondOperand::Reg(reg_from_u16(b))),
                        negated: c == 0,
                    };

                    if usize::from(a) == usize::from(b) {
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
                        let move_low = self.emitted.len() + 1;
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
                Lua51Opcode::Call => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let kind = self.take_call_kind(reg_from_u8(a), b);
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Call(CallInstr {
                            callee: reg_from_u8(a),
                            args: call_args_pack(a, b),
                            results: call_result_pack(a, c),
                            kind,
                        })),
                    );
                    raw_index += 1;
                }
                Lua51Opcode::TailCall => {
                    let (a, b, _) = expect_abc(raw_pc, opcode, operands)?;
                    let kind = self.take_call_kind(reg_from_u8(a), b);
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::TailCall(TailCallInstr {
                            callee: reg_from_u8(a),
                            args: call_args_pack(a, b),
                            kind,
                        })),
                    );
                    raw_index += 1;
                }
                Lua51Opcode::Return => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Return(ReturnInstr {
                            values: return_pack(a, b),
                        })),
                    );
                    raw_index += 1;
                }
                Lua51Opcode::ForLoop => {
                    self.clear_all_method_hints();
                    let (a, sbx) = expect_asbx(raw_pc, opcode, operands)?;
                    let index = reg_from_u8(a);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::NumericForLoop {
                            index,
                            limit: Reg(index.index() + 1),
                            step: Reg(index.index() + 2),
                            body_target: TargetPlaceholder::Raw(
                                self.jump_target(raw_pc, raw_index, sbx)?,
                            ),
                            exit_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_raw(raw_pc, raw_index + 1)?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                Lua51Opcode::ForPrep => {
                    self.clear_all_method_hints();
                    let (a, sbx) = expect_asbx(raw_pc, opcode, operands)?;
                    let target_raw = self.jump_target(raw_pc, raw_index, sbx)?;
                    let target_opcode = opcode_at(self.raw, target_raw);
                    if target_opcode != Lua51Opcode::ForLoop {
                        return Err(TransformError::InvalidNumericForPair {
                            raw_pc,
                            target_raw,
                            found: opcode_label(target_opcode),
                        });
                    }

                    let index = reg_from_u8(a);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::NumericForInit {
                            index,
                            limit: Reg(index.index() + 1),
                            step: Reg(index.index() + 2),
                            body_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_raw(raw_pc, raw_index + 1)?,
                            ),
                            exit_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_raw(raw_pc, target_raw + 1)?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                Lua51Opcode::TForLoop => {
                    self.clear_all_method_hints();
                    let (a, c) = expect_ac(raw_pc, opcode, operands)?;
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let state_start = reg_from_u8(a);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GenericForCall(GenericForCallInstr {
                            state: RegRange::new(state_start, 3),
                            results: ResultPack::Fixed(RegRange::new(
                                Reg(state_start.index() + 3),
                                usize::from(c),
                            )),
                        })),
                    );
                    self.emit(
                        None,
                        vec![raw_index, helper.helper_index],
                        PendingLowInstr::GenericForLoop {
                            control: RegRange::new(
                                Reg(state_start.index() + 2),
                                usize::from(c) + 1,
                            ),
                            body_target: TargetPlaceholder::Raw(helper.jump_target),
                            exit_target: TargetPlaceholder::Raw(helper.fallthrough_target),
                        },
                    );
                    raw_index += 2;
                }
                Lua51Opcode::SetList => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let list_chunk = if c == 0 {
                        extra.setlist_extra_arg.unwrap_or(0)
                    } else {
                        u32::from(c)
                    };
                    let values = if b == 0 {
                        ValuePack::Open(Reg(usize::from(a) + 1))
                    } else {
                        ValuePack::Fixed(RegRange::new(
                            Reg(usize::from(a) + 1),
                            usize::from(b),
                        ))
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
                Lua51Opcode::Close => {
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
                Lua51Opcode::Closure => {
                    let (a, bx) = expect_abx(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    let proto = self.proto_ref(raw_pc, bx as usize)?;
                    let capture_count = usize::from(
                        self.raw.common.children[proto.index()]
                            .common
                            .upvalues
                            .common
                            .count,
                    );
                    let mut captures = Vec::with_capacity(capture_count);
                    let mut raw_indices = vec![raw_index];

                    for capture_index in 0..capture_count {
                        let capture_raw = raw_index + 1 + capture_index;
                        let Some(raw_capture_instr) = self.raw.common.instructions.get(capture_raw)
                        else {
                            return Err(TransformError::MissingClosureCapture {
                                raw_pc,
                                capture_index,
                            });
                        };
                        let (capture_opcode, capture_operands, capture_extra) =
                            decode_lua51(raw_capture_instr);
                        raw_indices.push(capture_raw);

                        let source = match capture_opcode {
                            Lua51Opcode::Move => {
                                let (_, b) =
                                    expect_ab(capture_extra.pc, capture_opcode, capture_operands)?;
                                CaptureSource::Reg(reg_from_u16(b))
                            }
                            Lua51Opcode::GetUpVal => {
                                let (_, b) =
                                    expect_ab(capture_extra.pc, capture_opcode, capture_operands)?;
                                CaptureSource::Upvalue(
                                    self.upvalue_ref(capture_extra.pc, b as usize)?,
                                )
                            }
                            _ => {
                                return Err(TransformError::InvalidClosureCapture {
                                    raw_pc,
                                    capture_pc: capture_extra.pc,
                                    found: opcode_label(capture_opcode),
                                });
                            }
                        };

                        captures.push(Capture {
                            source,
                            extra: DialectCaptureExtra::None,
                        });
                    }

                    self.emit(
                        Some(raw_index),
                        raw_indices,
                        PendingLowInstr::Ready(LowInstr::Closure(ClosureInstr {
                            dst,
                            proto,
                            captures,
                        })),
                    );
                    raw_index += 1 + capture_count;
                }
                Lua51Opcode::VarArg => {
                    let (a, b) = expect_ab(raw_pc, opcode, operands)?;
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::VarArg(VarArgInstr {
                            results: if b == 0 {
                                ResultPack::Open(reg_from_u8(a))
                            } else {
                                ResultPack::Fixed(RegRange::new(reg_from_u8(a), usize::from(b)))
                            },
                        })),
                    );
                    raw_index += 1;
                }
            }
        }

        self.finish()
    }

    fn finish(&self) -> Result<(Vec<LowInstr>, LoweringMap), TransformError> {
        let instrs = self
            .emitted
            .iter()
            .map(|emitted| {
                let owner_raw = emitted.raw_indices.first().copied().unwrap_or(0);
                self.resolve_pending_instr(owner_raw, &emitted.instr)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let low_to_raw = self
            .emitted
            .iter()
            .map(|emitted| emitted.raw_indices.iter().copied().map(RawInstrRef).collect())
            .collect::<Vec<Vec<RawInstrRef>>>();
        let pc_map = self
            .emitted
            .iter()
            .map(|emitted| {
                emitted
                    .raw_indices
                    .iter()
                    .copied()
                    .map(|raw_index| raw_pc(&self.raw.common.instructions[raw_index]))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let line_hints = self
            .emitted
            .iter()
            .map(|emitted| {
                emitted.raw_indices.iter().find_map(|raw_index| {
                    self.raw
                        .common
                        .debug_info
                        .common
                        .line_info
                        .get(*raw_index)
                        .copied()
                })
            })
            .collect::<Vec<_>>();

        Ok((
            instrs,
            LoweringMap {
                low_to_raw,
                raw_to_low: self.raw_to_low.clone(),
                pc_map,
                line_hints,
            },
        ))
    }

    fn resolve_pending_instr(
        &self,
        owner_raw: usize,
        pending: &PendingLowInstr,
    ) -> Result<LowInstr, TransformError> {
        let owner_pc = raw_pc(&self.raw.common.instructions[owner_raw]);

        match pending {
            PendingLowInstr::Ready(instr) => Ok(instr.clone()),
            PendingLowInstr::Jump { target } => Ok(LowInstr::Jump(JumpInstr {
                target: self.resolve_target(owner_pc, *target)?,
            })),
            PendingLowInstr::Branch {
                cond,
                then_target,
                else_target,
            } => Ok(LowInstr::Branch(BranchInstr {
                cond: *cond,
                then_target: self.resolve_target(owner_pc, *then_target)?,
                else_target: self.resolve_target(owner_pc, *else_target)?,
            })),
            PendingLowInstr::NumericForInit {
                index,
                limit,
                step,
                body_target,
                exit_target,
            } => Ok(LowInstr::NumericForInit(NumericForInitInstr {
                index: *index,
                limit: *limit,
                step: *step,
                body_target: self.resolve_target(owner_pc, *body_target)?,
                exit_target: self.resolve_target(owner_pc, *exit_target)?,
            })),
            PendingLowInstr::NumericForLoop {
                index,
                limit,
                step,
                body_target,
                exit_target,
            } => Ok(LowInstr::NumericForLoop(NumericForLoopInstr {
                index: *index,
                limit: *limit,
                step: *step,
                body_target: self.resolve_target(owner_pc, *body_target)?,
                exit_target: self.resolve_target(owner_pc, *exit_target)?,
            })),
            PendingLowInstr::GenericForLoop {
                control,
                body_target,
                exit_target,
            } => Ok(LowInstr::GenericForLoop(GenericForLoopInstr {
                control: *control,
                body_target: self.resolve_target(owner_pc, *body_target)?,
                exit_target: self.resolve_target(owner_pc, *exit_target)?,
            })),
        }
    }

    fn resolve_target(
        &self,
        owner_pc: u32,
        target: TargetPlaceholder,
    ) -> Result<InstrRef, TransformError> {
        match target {
            TargetPlaceholder::Low(index) => Ok(InstrRef(index)),
            TargetPlaceholder::Raw(raw_index) => {
                let Some(low_index) = self.raw_target_low[raw_index] else {
                    return Err(TransformError::UntargetableRawInstruction {
                        raw_pc: owner_pc,
                        target_raw: raw_index,
                    });
                };
                Ok(InstrRef(low_index))
            }
        }
    }

    fn emit(
        &mut self,
        owner_raw: Option<usize>,
        raw_indices: Vec<usize>,
        instr: PendingLowInstr,
    ) -> usize {
        let low_index = self.emitted.len();

        if let Some(owner_raw) = owner_raw
            && self.raw_target_low[owner_raw].is_none()
        {
            self.raw_target_low[owner_raw] = Some(low_index);
        }

        for raw_index in &raw_indices {
            self.raw_to_low[*raw_index].push(InstrRef(low_index));
        }

        self.emitted.push(EmittedInstr { raw_indices, instr });
        low_index
    }

    fn const_ref(&self, raw_pc: u32, index: usize) -> Result<ConstRef, TransformError> {
        let const_count = self.raw.common.constants.common.literals.len();
        if index >= const_count {
            return Err(TransformError::InvalidConstRef {
                raw_pc,
                const_index: index,
                const_count,
            });
        }
        Ok(ConstRef(index))
    }

    fn upvalue_ref(&self, raw_pc: u32, index: usize) -> Result<UpvalueRef, TransformError> {
        let upvalue_count = self.raw.common.upvalues.common.count as usize;
        if index >= upvalue_count {
            return Err(TransformError::InvalidUpvalueRef {
                raw_pc,
                upvalue_index: index,
                upvalue_count,
            });
        }
        Ok(UpvalueRef(index))
    }

    fn proto_ref(&self, raw_pc: u32, index: usize) -> Result<ProtoRef, TransformError> {
        let child_count = self.raw.common.children.len();
        if index >= child_count {
            return Err(TransformError::InvalidProtoRef {
                raw_pc,
                proto_index: index,
                child_count,
            });
        }
        Ok(ProtoRef(index))
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

    fn jump_target(
        &self,
        raw_pc: u32,
        raw_index: usize,
        sbx: i32,
    ) -> Result<usize, TransformError> {
        let target = raw_index as i64 + 1 + i64::from(sbx);
        if target < 0 || target >= self.raw.common.instructions.len() as i64 {
            return Err(TransformError::InvalidJumpTarget {
                raw_pc,
                target_raw: target.max(0) as usize,
                instr_count: self.raw.common.instructions.len(),
            });
        }
        Ok(target as usize)
    }

    fn ensure_targetable_raw(
        &self,
        raw_pc: u32,
        target_raw: usize,
    ) -> Result<usize, TransformError> {
        if target_raw >= self.raw.common.instructions.len() {
            return Err(TransformError::InvalidJumpTarget {
                raw_pc,
                target_raw,
                instr_count: self.raw.common.instructions.len(),
            });
        }
        Ok(target_raw)
    }

    fn helper_jump(
        &self,
        raw_index: usize,
        opcode: Lua51Opcode,
    ) -> Result<HelperJump, TransformError> {
        let raw_pc = raw_pc(&self.raw.common.instructions[raw_index]);
        let helper_index = raw_index + 1;
        let Some(helper_instr) = self.raw.common.instructions.get(helper_index) else {
            return Err(TransformError::MissingHelperJump {
                raw_pc,
                opcode: opcode_label(opcode),
            });
        };
        let (helper_opcode, helper_operands, helper_extra) = decode_lua51(helper_instr);
        if helper_opcode != Lua51Opcode::Jmp {
            return Err(TransformError::InvalidHelperJump {
                raw_pc,
                helper_pc: helper_extra.pc,
                found: opcode_label(helper_opcode),
            });
        }
        let (_, helper_sbx) = expect_asbx(helper_extra.pc, helper_opcode, helper_operands)?;

        Ok(HelperJump {
            helper_index,
            jump_target: self.jump_target(helper_extra.pc, helper_index, helper_sbx)?,
            fallthrough_target: self.ensure_targetable_raw(raw_pc, raw_index + 2)?,
        })
    }

    fn set_pending_method(&mut self, callee: Reg, self_arg: Reg) {
        if callee.index() < self.pending_methods.len() {
            self.pending_methods[callee.index()] = Some(self_arg);
        }
    }

    fn take_call_kind(&mut self, callee: Reg, raw_b: u16) -> CallKind {
        if raw_b == 1 {
            return CallKind::Normal;
        }

        match self.pending_methods.get(callee.index()).and_then(|value| *value) {
            Some(self_arg) if self_arg == Reg(callee.index() + 1) => CallKind::Method,
            _ => CallKind::Normal,
        }
    }

    fn invalidate_written_reg(&mut self, reg: Reg) {
        for (callee, pending) in self.pending_methods.iter_mut().enumerate() {
            let Some(self_arg) = *pending else {
                continue;
            };
            if callee == reg.index() || self_arg.index() == reg.index() {
                *pending = None;
            }
        }
    }

    fn invalidate_written_range(&mut self, range: RegRange) {
        for offset in 0..range.len {
            self.invalidate_written_reg(Reg(range.start.index() + offset));
        }
    }

    fn clear_all_method_hints(&mut self) {
        self.pending_methods.fill(None);
    }
}

#[derive(Debug, Clone, Copy)]
struct HelperJump {
    helper_index: usize,
    jump_target: usize,
    fallthrough_target: usize,
}

fn decode_lua51(raw: &RawInstr) -> (Lua51Opcode, &Lua51Operands, Lua51InstrExtra) {
    let RawInstrOpcode::Lua51(opcode) = raw.opcode;
    let RawInstrOperands::Lua51(ref operands) = raw.operands;
    let DialectInstrExtra::Lua51(extra) = raw.extra;
    (opcode, operands, extra)
}

fn raw_pc(raw: &RawInstr) -> u32 {
    let DialectInstrExtra::Lua51(extra) = raw.extra;
    extra.pc
}

fn opcode_at(raw: &RawProto, index: usize) -> Lua51Opcode {
    let (opcode, _, _) = decode_lua51(&raw.common.instructions[index]);
    opcode
}

fn reg_from_u8(index: u8) -> Reg {
    Reg(index as usize)
}

fn reg_from_u16(index: u16) -> Reg {
    Reg(index as usize)
}

fn is_k(value: u16) -> bool {
    value & BITRK != 0
}

fn index_k(value: u16) -> usize {
    usize::from(value & !BITRK)
}

fn range_len_inclusive(start: usize, end: usize) -> usize {
    end.saturating_sub(start) + 1
}

fn call_args_pack(a: u8, b: u16) -> ValuePack {
    if b == 0 {
        ValuePack::Open(Reg(usize::from(a) + 1))
    } else {
        ValuePack::Fixed(RegRange::new(Reg(usize::from(a) + 1), usize::from(b - 1)))
    }
}

fn call_result_pack(a: u8, c: u16) -> ResultPack {
    match c {
        0 => ResultPack::Open(reg_from_u8(a)),
        1 => ResultPack::Ignore,
        _ => ResultPack::Fixed(RegRange::new(reg_from_u8(a), usize::from(c - 1))),
    }
}

fn return_pack(a: u8, b: u16) -> ValuePack {
    if b == 0 {
        ValuePack::Open(reg_from_u8(a))
    } else {
        ValuePack::Fixed(RegRange::new(reg_from_u8(a), usize::from(b - 1)))
    }
}

fn unary_op_kind(opcode: Lua51Opcode) -> UnaryOpKind {
    match opcode {
        Lua51Opcode::Unm => UnaryOpKind::Neg,
        Lua51Opcode::Not => UnaryOpKind::Not,
        Lua51Opcode::Len => UnaryOpKind::Length,
        _ => unreachable!("only unary opcodes should reach unary_op_kind"),
    }
}

fn binary_op_kind(opcode: Lua51Opcode) -> BinaryOpKind {
    match opcode {
        Lua51Opcode::Add => BinaryOpKind::Add,
        Lua51Opcode::Sub => BinaryOpKind::Sub,
        Lua51Opcode::Mul => BinaryOpKind::Mul,
        Lua51Opcode::Div => BinaryOpKind::Div,
        Lua51Opcode::Mod => BinaryOpKind::Mod,
        Lua51Opcode::Pow => BinaryOpKind::Pow,
        _ => unreachable!("only arithmetic opcodes should reach binary_op_kind"),
    }
}

fn branch_predicate(opcode: Lua51Opcode) -> BranchPredicate {
    match opcode {
        Lua51Opcode::Eq => BranchPredicate::Eq,
        Lua51Opcode::Lt => BranchPredicate::Lt,
        Lua51Opcode::Le => BranchPredicate::Le,
        _ => unreachable!("only compare opcodes should reach branch_predicate"),
    }
}

fn expect_a(
    raw_pc: u32,
    opcode: Lua51Opcode,
    operands: &Lua51Operands,
) -> Result<u8, TransformError> {
    match operands {
        Lua51Operands::A { a } => Ok(*a),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "A",
        }),
    }
}

fn expect_ab(
    raw_pc: u32,
    opcode: Lua51Opcode,
    operands: &Lua51Operands,
) -> Result<(u8, u16), TransformError> {
    match operands {
        Lua51Operands::AB { a, b } => Ok((*a, *b)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "AB",
        }),
    }
}

fn expect_ac(
    raw_pc: u32,
    opcode: Lua51Opcode,
    operands: &Lua51Operands,
) -> Result<(u8, u16), TransformError> {
    match operands {
        Lua51Operands::AC { a, c } => Ok((*a, *c)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "AC",
        }),
    }
}

fn expect_abc(
    raw_pc: u32,
    opcode: Lua51Opcode,
    operands: &Lua51Operands,
) -> Result<(u8, u16, u16), TransformError> {
    match operands {
        Lua51Operands::ABC { a, b, c } => Ok((*a, *b, *c)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "ABC",
        }),
    }
}

fn expect_abx(
    raw_pc: u32,
    opcode: Lua51Opcode,
    operands: &Lua51Operands,
) -> Result<(u8, u32), TransformError> {
    match operands {
        Lua51Operands::ABx { a, bx } => Ok((*a, *bx)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "ABx",
        }),
    }
}

fn expect_asbx(
    raw_pc: u32,
    opcode: Lua51Opcode,
    operands: &Lua51Operands,
) -> Result<(u8, i32), TransformError> {
    match operands {
        Lua51Operands::AsBx { a, sbx } => Ok((*a, *sbx)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "AsBx",
        }),
    }
}

fn opcode_label(opcode: Lua51Opcode) -> &'static str {
    match opcode {
        Lua51Opcode::Move => "MOVE",
        Lua51Opcode::LoadK => "LOADK",
        Lua51Opcode::LoadBool => "LOADBOOL",
        Lua51Opcode::LoadNil => "LOADNIL",
        Lua51Opcode::GetUpVal => "GETUPVAL",
        Lua51Opcode::GetGlobal => "GETGLOBAL",
        Lua51Opcode::GetTable => "GETTABLE",
        Lua51Opcode::SetGlobal => "SETGLOBAL",
        Lua51Opcode::SetUpVal => "SETUPVAL",
        Lua51Opcode::SetTable => "SETTABLE",
        Lua51Opcode::NewTable => "NEWTABLE",
        Lua51Opcode::Self_ => "SELF",
        Lua51Opcode::Add => "ADD",
        Lua51Opcode::Sub => "SUB",
        Lua51Opcode::Mul => "MUL",
        Lua51Opcode::Div => "DIV",
        Lua51Opcode::Mod => "MOD",
        Lua51Opcode::Pow => "POW",
        Lua51Opcode::Unm => "UNM",
        Lua51Opcode::Not => "NOT",
        Lua51Opcode::Len => "LEN",
        Lua51Opcode::Concat => "CONCAT",
        Lua51Opcode::Jmp => "JMP",
        Lua51Opcode::Eq => "EQ",
        Lua51Opcode::Lt => "LT",
        Lua51Opcode::Le => "LE",
        Lua51Opcode::Test => "TEST",
        Lua51Opcode::TestSet => "TESTSET",
        Lua51Opcode::Call => "CALL",
        Lua51Opcode::TailCall => "TAILCALL",
        Lua51Opcode::Return => "RETURN",
        Lua51Opcode::ForLoop => "FORLOOP",
        Lua51Opcode::ForPrep => "FORPREP",
        Lua51Opcode::TForLoop => "TFORLOOP",
        Lua51Opcode::SetList => "SETLIST",
        Lua51Opcode::Close => "CLOSE",
        Lua51Opcode::Closure => "CLOSURE",
        Lua51Opcode::VarArg => "VARARG",
    }
}
