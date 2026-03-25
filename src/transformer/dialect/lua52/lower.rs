//! 这个文件实现 Lua 5.2 到统一 low-IR 的 lowering。
//!
//! 这里最需要显式处理的 5.2 差异有三类：
//! 1. raw pc 仍然按“字”计数，但 parser 会把 `LOADKX/EXTRAARG`、`SETLIST/EXTRAARG`
//!    折成一个逻辑指令，所以跳转解析不能再偷用 logical index。
//! 2. `GETTABUP/SETTABUP` 的 base 是 upvalue table，本层要直接落成
//!    `AccessBase::Upvalue`，不能伪造中间寄存器。
//! 3. `JMP(A)` 和 test helper `JMP` 可能自带 close 语义，本层必须把它显式拆成
//!    `Close + Jump`，后续 CFG/SSA 才能看见真实副作用。

use std::collections::BTreeMap;

use crate::parser::{
    DialectInstrExtra, Lua52InstrExtra, Lua52Opcode, Lua52Operands, RawChunk, RawInstr,
    RawInstrOpcode, RawInstrOperands, RawProto,
};
use crate::transformer::dialect::puc_lua::{
    LFIELDS_PER_FLUSH, call_args_pack, call_result_pack, index_k, is_k, range_len_inclusive,
    reg_from_u8, reg_from_u16, return_pack,
};
use crate::transformer::{
    AccessBase, AccessKey, BinaryOpInstr, BinaryOpKind, BranchCond, BranchInstr, BranchOperands,
    BranchPredicate, CallInstr, CallKind, Capture, CaptureSource, CloseInstr, ClosureInstr,
    ConcatInstr, CondOperand, ConstRef, DialectCaptureExtra, GenericForCallInstr,
    GenericForLoopInstr, GetTableInstr, GetUpvalueInstr, InstrRef, JumpInstr, LoadBoolInstr,
    LoadConstInstr, LoadNilInstr, LowInstr, LoweredChunk, LoweredProto, LoweringMap, MoveInstr,
    NewTableInstr, NumericForInitInstr, NumericForLoopInstr, ProtoRef, RawInstrRef, Reg, RegRange,
    ResultPack, ReturnInstr, SetListInstr, SetTableInstr, SetUpvalueInstr, TailCallInstr,
    TransformError, UnaryOpInstr, UnaryOpKind, UpvalueRef, ValueOperand, ValuePack, VarArgInstr,
};

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
    raw_pc_to_index: BTreeMap<u32, usize>,
    raw_word_count: usize,
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
        binding: Reg,
        body_target: TargetPlaceholder,
        exit_target: TargetPlaceholder,
    },
    NumericForLoop {
        index: Reg,
        limit: Reg,
        step: Reg,
        binding: Reg,
        body_target: TargetPlaceholder,
        exit_target: TargetPlaceholder,
    },
    GenericForLoop {
        control: Reg,
        bindings: RegRange,
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
        let mut raw_pc_to_index = BTreeMap::new();
        let mut raw_word_count = 0_usize;

        for (index, instr) in raw.common.instructions.iter().enumerate() {
            let pc = raw_pc(instr);
            raw_pc_to_index.insert(pc, index);
            raw_word_count = raw_word_count.max((pc + u32::from(word_len(instr))) as usize);
        }

        Self {
            raw,
            emitted: Vec::new(),
            raw_target_low: vec![None; raw_instr_count],
            raw_to_low: vec![Vec::new(); raw_instr_count],
            pending_methods: vec![None; method_slots],
            raw_pc_to_index,
            raw_word_count,
        }
    }

    fn lower(&mut self) -> Result<(Vec<LowInstr>, LoweringMap), TransformError> {
        let mut raw_index = 0_usize;

        while raw_index < self.raw.common.instructions.len() {
            let raw_instr = &self.raw.common.instructions[raw_index];
            let (opcode, operands, extra) = decode_lua52(raw_instr);
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
                            base: AccessBase::Upvalue(self.upvalue_ref(raw_pc, b as usize)?),
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
                            base: AccessBase::Upvalue(self.upvalue_ref(raw_pc, a as usize)?),
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
                        TargetPlaceholder::Low(self.emitted.len() + 1)
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
                        TargetPlaceholder::Low(self.emitted.len() + 1)
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
                            TargetPlaceholder::Low(self.emitted.len() + 1)
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
                Lua52Opcode::TailCall => {
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
                Lua52Opcode::Return => {
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
                Lua52Opcode::ForLoop => {
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
                            binding: Reg(index.index() + 3),
                            body_target: TargetPlaceholder::Raw(
                                self.jump_target(raw_pc, extra.pc, sbx)?,
                            ),
                            exit_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_pc(raw_pc, self.next_raw_pc(raw_index))?,
                            ),
                        },
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
                            binding: Reg(index.index() + 3),
                            body_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_pc(raw_pc, self.next_raw_pc(raw_index))?,
                            ),
                            exit_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_pc(raw_pc, self.next_raw_pc(target_raw))?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                Lua52Opcode::TForCall => {
                    self.clear_all_method_hints();
                    let (a, _, c) = expect_abc(raw_pc, opcode, operands)?;
                    let pair = self.generic_for_pair(raw_index, a, c)?;
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
                        Some(pair.loop_index),
                        vec![pair.loop_index],
                        PendingLowInstr::GenericForLoop {
                            control: pair.control,
                            bindings: pair.bindings,
                            body_target: TargetPlaceholder::Raw(pair.body_target),
                            exit_target: TargetPlaceholder::Raw(pair.exit_target),
                        },
                    );
                    raw_index = pair.next_index;
                }
                Lua52Opcode::TForLoop => {
                    return Err(TransformError::InvalidGenericForLoop {
                        raw_pc,
                        helper_pc: raw_pc,
                        found: opcode_label(opcode),
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
            .map(|emitted| {
                emitted
                    .raw_indices
                    .iter()
                    .copied()
                    .map(RawInstrRef)
                    .collect()
            })
            .collect::<Vec<Vec<RawInstrRef>>>();
        let pc_map = self
            .emitted
            .iter()
            .map(|emitted| {
                emitted
                    .raw_indices
                    .iter()
                    .copied()
                    .map(|index| raw_pc_at(self.raw, index))
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
        let owner_pc = raw_pc_at(self.raw, owner_raw);

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
                binding,
                body_target,
                exit_target,
            } => Ok(LowInstr::NumericForInit(NumericForInitInstr {
                index: *index,
                limit: *limit,
                step: *step,
                binding: *binding,
                body_target: self.resolve_target(owner_pc, *body_target)?,
                exit_target: self.resolve_target(owner_pc, *exit_target)?,
            })),
            PendingLowInstr::NumericForLoop {
                index,
                limit,
                step,
                binding,
                body_target,
                exit_target,
            } => Ok(LowInstr::NumericForLoop(NumericForLoopInstr {
                index: *index,
                limit: *limit,
                step: *step,
                binding: *binding,
                body_target: self.resolve_target(owner_pc, *body_target)?,
                exit_target: self.resolve_target(owner_pc, *exit_target)?,
            })),
            PendingLowInstr::GenericForLoop {
                control,
                bindings,
                body_target,
                exit_target,
            } => Ok(LowInstr::GenericForLoop(GenericForLoopInstr {
                control: *control,
                bindings: *bindings,
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
                        target_raw: raw_pc_at(self.raw, raw_index) as usize,
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

        if let Some(owner_raw) = owner_raw {
            if self.raw_target_low[owner_raw].is_none() {
                self.raw_target_low[owner_raw] = Some(low_index);
            }
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

    fn extra_arg(
        &self,
        raw_pc: u32,
        opcode: Lua52Opcode,
        extra_arg: Option<u32>,
    ) -> Result<u32, TransformError> {
        extra_arg.ok_or(TransformError::MissingExtraArg {
            raw_pc,
            opcode: opcode_label(opcode),
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
        if target_pc < 0 || target_pc >= self.raw_word_count as i64 {
            return Err(TransformError::InvalidJumpTarget {
                raw_pc,
                target_raw: target_pc.max(0) as usize,
                instr_count: self.raw_word_count,
            });
        }
        self.ensure_targetable_pc(raw_pc, target_pc as u32)
    }

    fn ensure_targetable_pc(&self, raw_pc: u32, target_pc: u32) -> Result<usize, TransformError> {
        if target_pc as usize >= self.raw_word_count {
            return Err(TransformError::InvalidJumpTarget {
                raw_pc,
                target_raw: target_pc as usize,
                instr_count: self.raw_word_count,
            });
        }

        self.raw_pc_to_index.get(&target_pc).copied().ok_or(
            TransformError::UntargetableRawInstruction {
                raw_pc,
                target_raw: target_pc as usize,
            },
        )
    }

    fn helper_jump(
        &self,
        raw_index: usize,
        opcode: Lua52Opcode,
    ) -> Result<HelperJump, TransformError> {
        let raw_pc = raw_pc_at(self.raw, raw_index);
        let helper_pc = raw_pc + 1;
        let Some(helper_index) = self.raw_pc_to_index.get(&helper_pc).copied() else {
            return Err(TransformError::MissingHelperJump {
                raw_pc,
                opcode: opcode_label(opcode),
            });
        };
        let helper_instr = &self.raw.common.instructions[helper_index];
        let (helper_opcode, helper_operands, helper_extra) = decode_lua52(helper_instr);
        if helper_opcode != Lua52Opcode::Jmp {
            return Err(TransformError::InvalidHelperJump {
                raw_pc,
                helper_pc: helper_extra.pc,
                found: opcode_label(helper_opcode),
            });
        }
        let (a, helper_sbx) = expect_asbx(helper_extra.pc, helper_opcode, helper_operands)?;

        Ok(HelperJump {
            helper_index,
            jump_target: self.jump_target(helper_extra.pc, helper_extra.pc, helper_sbx)?,
            fallthrough_target: self
                .ensure_targetable_pc(raw_pc, self.next_raw_pc(helper_index))?,
            close_from: close_from_raw_a(a),
            next_index: helper_index + 1,
        })
    }

    fn generic_for_pair(
        &self,
        raw_index: usize,
        call_a: u8,
        result_count: u16,
    ) -> Result<GenericForPair, TransformError> {
        let raw_pc = raw_pc_at(self.raw, raw_index);
        let helper_pc = raw_pc + 1;
        let Some(loop_index) = self.raw_pc_to_index.get(&helper_pc).copied() else {
            return Err(TransformError::MissingGenericForLoop { raw_pc });
        };
        let helper_instr = &self.raw.common.instructions[loop_index];
        let (helper_opcode, helper_operands, helper_extra) = decode_lua52(helper_instr);
        if helper_opcode != Lua52Opcode::TForLoop {
            return Err(TransformError::InvalidGenericForLoop {
                raw_pc,
                helper_pc: helper_extra.pc,
                found: opcode_label(helper_opcode),
            });
        }
        let (loop_a, helper_sbx) = expect_asbx(helper_extra.pc, helper_opcode, helper_operands)?;
        if usize::from(loop_a) != usize::from(call_a) + 2 {
            return Err(TransformError::InvalidGenericForPair {
                raw_pc,
                call_base: usize::from(call_a),
                loop_control: usize::from(loop_a),
            });
        }

        let control = reg_from_u8(loop_a);
        Ok(GenericForPair {
            loop_index,
            control,
            bindings: RegRange::new(Reg(control.index() + 1), usize::from(result_count)),
            body_target: self.jump_target(helper_extra.pc, helper_extra.pc, helper_sbx)?,
            exit_target: self.ensure_targetable_pc(raw_pc, self.next_raw_pc(loop_index))?,
            next_index: loop_index + 1,
        })
    }

    fn next_raw_pc(&self, raw_index: usize) -> u32 {
        let instr = &self.raw.common.instructions[raw_index];
        raw_pc(instr) + u32::from(word_len(instr))
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

        match self
            .pending_methods
            .get(callee.index())
            .and_then(|value| *value)
        {
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
    close_from: Option<Reg>,
    next_index: usize,
}

#[derive(Debug, Clone, Copy)]
struct GenericForPair {
    loop_index: usize,
    control: Reg,
    bindings: RegRange,
    body_target: usize,
    exit_target: usize,
    next_index: usize,
}

fn decode_lua52(raw: &RawInstr) -> (Lua52Opcode, &Lua52Operands, Lua52InstrExtra) {
    let RawInstrOpcode::Lua52(opcode) = raw.opcode else {
        unreachable!("lua52 lowerer should only decode lua52 opcodes");
    };
    let RawInstrOperands::Lua52(ref operands) = raw.operands else {
        unreachable!("lua52 lowerer should only decode lua52 operands");
    };
    let DialectInstrExtra::Lua52(extra) = raw.extra else {
        unreachable!("lua52 lowerer should only decode lua52 instruction extras");
    };
    (opcode, operands, extra)
}

fn raw_pc(raw: &RawInstr) -> u32 {
    let DialectInstrExtra::Lua52(extra) = raw.extra else {
        unreachable!("lua52 lowerer should only decode lua52 instruction extras");
    };
    extra.pc
}

fn word_len(raw: &RawInstr) -> u8 {
    let DialectInstrExtra::Lua52(extra) = raw.extra else {
        unreachable!("lua52 lowerer should only decode lua52 instruction extras");
    };
    extra.word_len
}

fn raw_pc_at(raw: &RawProto, index: usize) -> u32 {
    raw_pc(&raw.common.instructions[index])
}

fn opcode_at(raw: &RawProto, index: usize) -> Lua52Opcode {
    let (opcode, _, _) = decode_lua52(&raw.common.instructions[index]);
    opcode
}

fn close_from_raw_a(a: u8) -> Option<Reg> {
    if a == 0 {
        None
    } else {
        Some(Reg(usize::from(a - 1)))
    }
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

fn opcode_label(opcode: Lua52Opcode) -> &'static str {
    match opcode {
        Lua52Opcode::Move => "MOVE",
        Lua52Opcode::LoadK => "LOADK",
        Lua52Opcode::LoadKx => "LOADKX",
        Lua52Opcode::LoadBool => "LOADBOOL",
        Lua52Opcode::LoadNil => "LOADNIL",
        Lua52Opcode::GetUpVal => "GETUPVAL",
        Lua52Opcode::GetTabUp => "GETTABUP",
        Lua52Opcode::GetTable => "GETTABLE",
        Lua52Opcode::SetTabUp => "SETTABUP",
        Lua52Opcode::SetUpVal => "SETUPVAL",
        Lua52Opcode::SetTable => "SETTABLE",
        Lua52Opcode::NewTable => "NEWTABLE",
        Lua52Opcode::Self_ => "SELF",
        Lua52Opcode::Add => "ADD",
        Lua52Opcode::Sub => "SUB",
        Lua52Opcode::Mul => "MUL",
        Lua52Opcode::Div => "DIV",
        Lua52Opcode::Mod => "MOD",
        Lua52Opcode::Pow => "POW",
        Lua52Opcode::Unm => "UNM",
        Lua52Opcode::Not => "NOT",
        Lua52Opcode::Len => "LEN",
        Lua52Opcode::Concat => "CONCAT",
        Lua52Opcode::Jmp => "JMP",
        Lua52Opcode::Eq => "EQ",
        Lua52Opcode::Lt => "LT",
        Lua52Opcode::Le => "LE",
        Lua52Opcode::Test => "TEST",
        Lua52Opcode::TestSet => "TESTSET",
        Lua52Opcode::Call => "CALL",
        Lua52Opcode::TailCall => "TAILCALL",
        Lua52Opcode::Return => "RETURN",
        Lua52Opcode::ForLoop => "FORLOOP",
        Lua52Opcode::ForPrep => "FORPREP",
        Lua52Opcode::TForCall => "TFORCALL",
        Lua52Opcode::TForLoop => "TFORLOOP",
        Lua52Opcode::SetList => "SETLIST",
        Lua52Opcode::Closure => "CLOSURE",
        Lua52Opcode::VarArg => "VARARG",
        Lua52Opcode::ExtraArg => "EXTRAARG",
    }
}

fn expect_a(
    raw_pc: u32,
    opcode: Lua52Opcode,
    operands: &Lua52Operands,
) -> Result<u8, TransformError> {
    match operands {
        Lua52Operands::A { a } => Ok(*a),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "A",
        }),
    }
}

fn expect_ab(
    raw_pc: u32,
    opcode: Lua52Opcode,
    operands: &Lua52Operands,
) -> Result<(u8, u16), TransformError> {
    match operands {
        Lua52Operands::AB { a, b } => Ok((*a, *b)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "AB",
        }),
    }
}

fn expect_ac(
    raw_pc: u32,
    opcode: Lua52Opcode,
    operands: &Lua52Operands,
) -> Result<(u8, u16), TransformError> {
    match operands {
        Lua52Operands::AC { a, c } => Ok((*a, *c)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "AC",
        }),
    }
}

fn expect_abc(
    raw_pc: u32,
    opcode: Lua52Opcode,
    operands: &Lua52Operands,
) -> Result<(u8, u16, u16), TransformError> {
    match operands {
        Lua52Operands::ABC { a, b, c } => Ok((*a, *b, *c)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "ABC",
        }),
    }
}

fn expect_abx(
    raw_pc: u32,
    opcode: Lua52Opcode,
    operands: &Lua52Operands,
) -> Result<(u8, u32), TransformError> {
    match operands {
        Lua52Operands::ABx { a, bx } => Ok((*a, *bx)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "ABx",
        }),
    }
}

fn expect_asbx(
    raw_pc: u32,
    opcode: Lua52Opcode,
    operands: &Lua52Operands,
) -> Result<(u8, i32), TransformError> {
    match operands {
        Lua52Operands::AsBx { a, sbx } => Ok((*a, *sbx)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "AsBx",
        }),
    }
}
