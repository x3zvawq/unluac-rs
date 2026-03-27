//! 这个文件实现 Luau bytecode 到统一 low-IR 的 lowering。
//!
//! Luau 的 parser 已经把“多字指令 / AUX / capture helper / 平铺 proto”这些字节级细节
//! 折进 raw 层了；这里专注做语义恢复，把它翻成项目里既有的 CFG/HIR/AST 管线能理解
//! 的稳定 low-IR 契约。

use std::collections::BTreeMap;

use crate::parser::{
    DialectConstPoolExtra, DialectInstrExtra, DialectProtoExtra, LuauCaptureKind, LuauConstEntry,
    LuauInstrExtra, LuauOpcode, LuauOperands, LuauProtoExtra, RawChunk, RawInstr, RawInstrOpcode,
    RawInstrOperands, RawLiteralConst, RawProto,
};
use crate::transformer::dialect::puc_lua::{
    call_args_pack, call_result_pack, range_len_inclusive, reg_from_u8, return_pack,
};
use crate::transformer::{
    AccessBase, AccessKey, BinaryOpInstr, BinaryOpKind, BranchCond, BranchInstr, BranchOperands,
    BranchPredicate, CallInstr, CallKind, Capture, CaptureSource, CloseInstr, ClosureInstr,
    ConcatInstr, CondOperand, ConstRef, DialectCaptureExtra, GenericForCallInstr,
    GenericForLoopInstr, GetTableInstr, GetUpvalueInstr, InstrRef, JumpInstr, LoadBoolInstr,
    LoadConstInstr, LoadIntegerInstr, LoadNilInstr, LowInstr, LoweredChunk, LoweredProto,
    LoweringMap, MoveInstr, NewTableInstr, NumericForInitInstr, NumericForLoopInstr, ProtoRef,
    RawInstrRef, Reg, RegRange, ResultPack, ReturnInstr, SetListInstr, SetTableInstr,
    SetUpvalueInstr, TransformError, UnaryOpInstr, UnaryOpKind, UpvalueRef, ValueOperand,
    ValuePack, VarArgInstr,
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

#[derive(Debug, Clone, Copy)]
enum LogicalSelectValue {
    Reg(Reg),
    Const(ConstRef),
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
            let (opcode, operands, extra) = decode_luau(raw_instr);
            let raw_pc = extra.pc;

            match opcode {
                LuauOpcode::Nop
                | LuauOpcode::Break
                | LuauOpcode::PrepVarArgs
                | LuauOpcode::Coverage
                | LuauOpcode::FastCall
                | LuauOpcode::FastCall1
                | LuauOpcode::FastCall2
                | LuauOpcode::FastCall2K
                | LuauOpcode::FastCall3 => {
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
                            src: self.upvalue_ref(raw_pc, b as usize)?,
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
                            dst: self.upvalue_ref(raw_pc, b as usize)?,
                            src: reg_from_u8(a),
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
                        })),
                    );
                    raw_index += 1;
                }
                LuauOpcode::NewTable => {
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
                            base: AccessBase::Reg(base),
                            key: AccessKey::Const(
                                self.string_const_ref(raw_pc, aux_u24(raw_pc, opcode, extra)?)?,
                            ),
                        })),
                    );
                    self.set_pending_method(callee, self_arg);
                    raw_index += 1;
                }
                LuauOpcode::Call => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    let kind = self.take_call_kind(reg_from_u8(a), u16::from(b));
                    self.clear_all_method_hints();
                    let (result_pack, consumed_extra_raw) =
                        self.fold_single_result_call_move(raw_index, a, c)?;
                    if let ResultPack::Fixed(range) = result_pack {
                        self.invalidate_written_range(range);
                    }
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
                        })),
                    );
                    raw_index += if consumed_extra_raw.is_some() { 2 } else { 1 };
                }
                LuauOpcode::Return => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    debug_assert_eq!(c, 0, "luau return should leave C unused");
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
                            cond: BranchCond {
                                predicate: BranchPredicate::Truthy,
                                operands: BranchOperands::Unary(CondOperand::Reg(reg_from_u8(a))),
                                negated: false,
                            },
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
                            cond: BranchCond {
                                predicate: BranchPredicate::Truthy,
                                operands: BranchOperands::Unary(CondOperand::Reg(reg_from_u8(a))),
                                negated: true,
                            },
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
                            cond: BranchCond {
                                predicate: compare_predicate(opcode),
                                operands: BranchOperands::Binary(
                                    CondOperand::Reg(reg_from_u8(a)),
                                    CondOperand::Reg(reg_from_u8(aux_reg(raw_pc, opcode, extra)?)),
                                ),
                                negated: compare_negated(opcode),
                            },
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
                            cond: BranchCond {
                                predicate: BranchPredicate::Eq,
                                operands: BranchOperands::Binary(
                                    CondOperand::Reg(reg_from_u8(a)),
                                    CondOperand::Const(
                                        self.literal_const_ref(
                                            raw_pc,
                                            (aux & 0x00ff_ffff) as usize,
                                        )?,
                                    ),
                                ),
                                negated: aux_not(aux),
                            },
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
                            cond: BranchCond {
                                predicate: BranchPredicate::Eq,
                                operands: BranchOperands::Binary(
                                    CondOperand::Reg(reg_from_u8(a)),
                                    CondOperand::Const(
                                        self.string_const_ref(
                                            raw_pc,
                                            (aux & 0x00ff_ffff) as usize,
                                        )?,
                                    ),
                                ),
                                negated: aux_not(aux),
                            },
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
                            cond: BranchCond {
                                predicate: BranchPredicate::Eq,
                                operands: BranchOperands::Binary(
                                    CondOperand::Reg(reg_from_u8(a)),
                                    CondOperand::Boolean((aux & 1) != 0),
                                ),
                                negated: aux_not(aux),
                            },
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
                            cond: BranchCond {
                                predicate: BranchPredicate::Eq,
                                operands: BranchOperands::Binary(
                                    CondOperand::Reg(reg_from_u8(a)),
                                    CondOperand::Nil,
                                ),
                                negated: aux_not(aux),
                            },
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
                LuauOpcode::Capture => {
                    return Err(TransformError::InvalidClosureCapture {
                        raw_pc,
                        capture_pc: raw_pc,
                        found: opcode_label(opcode),
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
                    let state = RegRange::new(reg_from_u8(a), 3);
                    let bindings = RegRange::new(Reg(state.start.index() + 3), var_count);
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GenericForCall(GenericForCallInstr {
                            state,
                            results: ResultPack::Fixed(bindings),
                        })),
                    );
                    self.emit(
                        None,
                        vec![raw_index],
                        PendingLowInstr::GenericForLoop {
                            control: Reg(state.start.index() + 2),
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
                _ => {
                    return Err(TransformError::UnsupportedDialect {
                        version: crate::parser::DialectVersion::Luau,
                    });
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

    fn literal_const_ref(&self, raw_pc: u32, index: usize) -> Result<ConstRef, TransformError> {
        match self.const_entry(raw_pc, index)? {
            LuauConstEntry::Literal { literal_index } => Ok(ConstRef(*literal_index)),
            _ => Err(TransformError::InvalidConstRef {
                raw_pc,
                const_index: index,
                const_count: self.const_entries().len(),
            }),
        }
    }

    fn string_const_ref(&self, raw_pc: u32, index: usize) -> Result<ConstRef, TransformError> {
        let const_ref = self.literal_const_ref(raw_pc, index)?;
        match self
            .raw
            .common
            .constants
            .common
            .literals
            .get(const_ref.index())
        {
            Some(RawLiteralConst::String(_)) => Ok(const_ref),
            _ => Err(TransformError::InvalidConstRef {
                raw_pc,
                const_index: index,
                const_count: self.const_entries().len(),
            }),
        }
    }

    fn const_entries(&self) -> &[LuauConstEntry] {
        match &self.raw.common.constants.extra {
            DialectConstPoolExtra::Luau(extra) => &extra.entries,
            _ => unreachable!("luau lowerer should only receive luau constant pools"),
        }
    }

    fn const_entry(&self, raw_pc: u32, index: usize) -> Result<&LuauConstEntry, TransformError> {
        self.const_entries()
            .get(index)
            .ok_or(TransformError::InvalidConstRef {
                raw_pc,
                const_index: index,
                const_count: self.const_entries().len(),
            })
    }

    fn upvalue_ref(&self, raw_pc: u32, index: usize) -> Result<UpvalueRef, TransformError> {
        let upvalue_count = usize::from(self.raw.common.upvalues.common.count);
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

    fn proto_ref_for_closure_const(
        &self,
        raw_pc: u32,
        const_index: usize,
    ) -> Result<ProtoRef, TransformError> {
        let LuauConstEntry::Closure { proto_index } = self.const_entry(raw_pc, const_index)? else {
            return Err(TransformError::InvalidConstRef {
                raw_pc,
                const_index,
                const_count: self.const_entries().len(),
            });
        };
        let child_ids = match &self.raw.extra {
            DialectProtoExtra::Luau(LuauProtoExtra {
                child_proto_ids, ..
            }) => child_proto_ids,
            _ => unreachable!("luau lowerer should only receive luau proto extras"),
        };
        let Some(child_index) = child_ids
            .iter()
            .position(|child_id| child_id == proto_index)
        else {
            return Err(TransformError::InvalidProtoRef {
                raw_pc,
                proto_index: *proto_index as usize,
                child_count: child_ids.len(),
            });
        };
        Ok(ProtoRef(child_index))
    }

    fn import_path(
        &self,
        raw_pc: u32,
        extra: LuauInstrExtra,
    ) -> Result<Vec<ConstRef>, TransformError> {
        let aux = required_aux(raw_pc, LuauOpcode::GetImport, extra)?;
        let count = (aux >> 30) as usize;
        let ids = [
            ((aux >> 20) & 0x3ff) as usize,
            ((aux >> 10) & 0x3ff) as usize,
            (aux & 0x3ff) as usize,
        ];
        (0..count)
            .map(|slot| self.string_const_ref(raw_pc, ids[slot]))
            .collect()
    }

    fn decode_closure_captures(
        &self,
        raw_index: usize,
        raw_pc: u32,
        capture_count: usize,
    ) -> Result<(Vec<Capture>, Vec<usize>), TransformError> {
        let mut captures = Vec::with_capacity(capture_count);
        let mut raw_indices = vec![raw_index];

        for capture_index in 0..capture_count {
            let capture_raw = raw_index + 1 + capture_index;
            let Some(raw_capture_instr) = self.raw.common.instructions.get(capture_raw) else {
                return Err(TransformError::MissingClosureCapture {
                    raw_pc,
                    capture_index,
                });
            };
            let (capture_opcode, capture_operands, capture_extra) = decode_luau(raw_capture_instr);
            raw_indices.push(capture_raw);
            if capture_opcode != LuauOpcode::Capture {
                return Err(TransformError::InvalidClosureCapture {
                    raw_pc,
                    capture_pc: capture_extra.pc,
                    found: opcode_label(capture_opcode),
                });
            }

            let (kind_raw, source_raw) = expect_capture(capture_extra.pc, capture_operands)?;
            let kind = LuauCaptureKind::try_from(kind_raw).map_err(|_| {
                TransformError::InvalidClosureCapture {
                    raw_pc,
                    capture_pc: capture_extra.pc,
                    found: opcode_label(capture_opcode),
                }
            })?;
            let source = match kind {
                LuauCaptureKind::Val | LuauCaptureKind::Ref => {
                    CaptureSource::Reg(reg_from_u8(source_raw))
                }
                LuauCaptureKind::Upvalue => {
                    CaptureSource::Upvalue(self.upvalue_ref(capture_extra.pc, source_raw as usize)?)
                }
            };
            captures.push(Capture {
                source,
                extra: DialectCaptureExtra::None,
            });
        }

        Ok((captures, raw_indices))
    }

    fn fold_single_result_call_move(
        &self,
        _raw_index: usize,
        call_a: u8,
        call_c: u8,
    ) -> Result<(ResultPack, Option<usize>), TransformError> {
        // Luau 的单结果调用常见形状是 `CALL A ...; MOVE dst, A`。
        //
        // 这里如果把后面的 MOVE 折进 CALL，low-IR 就会错误地宣称“结果只定义在 dst”，
        // 但 VM 语义上结果其实仍然留在寄存器 A 里，后续代码完全可能继续读取 A。
        // `nested_closure_factory` / `multi_assign_rotation` 这类 common case 正是因此把
        // “刚产生的闭包/旋转值”读回成旧值。相比之下，保留真实的 CALL + MOVE 形状虽然
        // 机械一点，但能让 dataflow/SSA 忠实看到两个寄存器身份，后面的 simplify 再去
        // 按需收敛就安全得多。
        Ok((call_result_pack(call_a, u16::from(call_c)), None))
    }

    fn jump_target(&self, raw_pc: u32, offset: i32) -> Result<usize, TransformError> {
        let target_pc = i64::from(raw_pc) + 1 + i64::from(offset);
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
        if raw_b <= 1 {
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

    fn invalidate_vararg_results(&mut self, a: u8, b: u8) {
        match call_result_pack(a, u16::from(b)) {
            ResultPack::Fixed(range) => self.invalidate_written_range(range),
            ResultPack::Open(reg) => self.invalidate_written_reg(reg),
            ResultPack::Ignore => {}
        }
    }

    fn clear_all_method_hints(&mut self) {
        self.pending_methods.fill(None);
    }

    fn emit_logical_select(
        &mut self,
        raw_index: usize,
        condition: Reg,
        dst: Reg,
        truthy_value: LogicalSelectValue,
        falsy_value: LogicalSelectValue,
    ) {
        let branch_low = self.emitted.len();
        let truthy_low = branch_low + 1;
        let jump_low = branch_low + 2;
        let falsy_low = branch_low + 3;
        let after_low = branch_low + 4;

        self.emit(
            Some(raw_index),
            vec![raw_index],
            PendingLowInstr::Branch {
                cond: BranchCond {
                    predicate: BranchPredicate::Truthy,
                    operands: BranchOperands::Unary(CondOperand::Reg(condition)),
                    negated: false,
                },
                then_target: TargetPlaceholder::Low(truthy_low),
                else_target: TargetPlaceholder::Low(falsy_low),
            },
        );
        self.emit_logical_select_value(raw_index, dst, truthy_value);
        self.emit(
            None,
            vec![raw_index],
            PendingLowInstr::Jump {
                target: TargetPlaceholder::Low(after_low),
            },
        );
        self.emit_logical_select_value(raw_index, dst, falsy_value);
        debug_assert_eq!(jump_low + 1, falsy_low);
    }

    fn emit_logical_select_value(&mut self, raw_index: usize, dst: Reg, value: LogicalSelectValue) {
        let instr = match value {
            LogicalSelectValue::Reg(src) => LowInstr::Move(MoveInstr { dst, src }),
            LogicalSelectValue::Const(value) => LowInstr::LoadConst(LoadConstInstr { dst, value }),
        };
        self.emit(None, vec![raw_index], PendingLowInstr::Ready(instr));
    }

    fn emit_dup_table_template(
        &mut self,
        raw_pc: u32,
        raw_index: usize,
        dst: Reg,
        const_index: usize,
    ) -> Result<(), TransformError> {
        match self.const_entry(raw_pc, const_index)?.clone() {
            LuauConstEntry::Table { .. } => Ok(()),
            LuauConstEntry::TableWithConstants { entries } => {
                for entry in entries {
                    let Some(value_const) = entry.value_const else {
                        continue;
                    };
                    self.emit(
                        None,
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Reg(dst),
                            key: AccessKey::Const(
                                self.literal_const_ref(raw_pc, entry.key_const as usize)?,
                            ),
                            value: ValueOperand::Const(
                                self.literal_const_ref(raw_pc, value_const as usize)?,
                            ),
                        })),
                    );
                }
                Ok(())
            }
            _ => Err(TransformError::InvalidConstRef {
                raw_pc,
                const_index,
                const_count: self.const_entries().len(),
            }),
        }
    }
}

fn decode_luau(raw: &RawInstr) -> (LuauOpcode, &LuauOperands, LuauInstrExtra) {
    let RawInstrOpcode::Luau(opcode) = raw.opcode else {
        unreachable!("luau lowerer should only decode luau opcodes");
    };
    let RawInstrOperands::Luau(ref operands) = raw.operands else {
        unreachable!("luau lowerer should only decode luau operands");
    };
    let DialectInstrExtra::Luau(extra) = raw.extra else {
        unreachable!("luau lowerer should only decode luau extras");
    };
    (opcode, operands, extra)
}

fn raw_pc(raw: &RawInstr) -> u32 {
    let DialectInstrExtra::Luau(extra) = raw.extra else {
        unreachable!("luau lowerer should only decode luau extras");
    };
    extra.pc
}

fn word_len(raw: &RawInstr) -> u8 {
    let DialectInstrExtra::Luau(extra) = raw.extra else {
        unreachable!("luau lowerer should only decode luau extras");
    };
    extra.word_len
}

fn raw_pc_at(raw: &RawProto, index: usize) -> u32 {
    raw_pc(&raw.common.instructions[index])
}

fn required_aux(
    raw_pc: u32,
    opcode: LuauOpcode,
    extra: LuauInstrExtra,
) -> Result<u32, TransformError> {
    extra.aux.ok_or(TransformError::MissingExtraArg {
        raw_pc,
        opcode: opcode_label(opcode),
    })
}

fn aux_u24(
    raw_pc: u32,
    opcode: LuauOpcode,
    extra: LuauInstrExtra,
) -> Result<usize, TransformError> {
    Ok((required_aux(raw_pc, opcode, extra)? & 0x00ff_ffff) as usize)
}

fn aux_reg(raw_pc: u32, opcode: LuauOpcode, extra: LuauInstrExtra) -> Result<u8, TransformError> {
    let aux = required_aux(raw_pc, opcode, extra)?;
    u8::try_from(aux & 0xff).map_err(|_| TransformError::MissingExtraArg {
        raw_pc,
        opcode: opcode_label(opcode),
    })
}

fn aux_not(aux: u32) -> bool {
    (aux >> 31) != 0
}

fn unary_op_kind(opcode: LuauOpcode) -> UnaryOpKind {
    match opcode {
        LuauOpcode::Not => UnaryOpKind::Not,
        LuauOpcode::Minus => UnaryOpKind::Neg,
        LuauOpcode::Length => UnaryOpKind::Length,
        _ => unreachable!("only unary luau opcodes should reach unary_op_kind"),
    }
}

fn binary_op_kind(opcode: LuauOpcode) -> BinaryOpKind {
    match opcode {
        LuauOpcode::Add | LuauOpcode::AddK => BinaryOpKind::Add,
        LuauOpcode::Sub | LuauOpcode::SubK | LuauOpcode::SubRK => BinaryOpKind::Sub,
        LuauOpcode::Mul | LuauOpcode::MulK => BinaryOpKind::Mul,
        LuauOpcode::Div | LuauOpcode::DivK | LuauOpcode::DivRK => BinaryOpKind::Div,
        LuauOpcode::Mod | LuauOpcode::ModK => BinaryOpKind::Mod,
        LuauOpcode::Pow | LuauOpcode::PowK => BinaryOpKind::Pow,
        LuauOpcode::IDiv | LuauOpcode::IDivK => BinaryOpKind::FloorDiv,
        _ => unreachable!("only binary luau opcodes should reach binary_op_kind"),
    }
}

fn compare_predicate(opcode: LuauOpcode) -> BranchPredicate {
    match opcode {
        LuauOpcode::JumpIfEq | LuauOpcode::JumpIfNotEq => BranchPredicate::Eq,
        LuauOpcode::JumpIfLe | LuauOpcode::JumpIfNotLe => BranchPredicate::Le,
        LuauOpcode::JumpIfLt | LuauOpcode::JumpIfNotLt => BranchPredicate::Lt,
        _ => unreachable!("only compare opcodes should reach compare_predicate"),
    }
}

fn compare_negated(opcode: LuauOpcode) -> bool {
    matches!(
        opcode,
        LuauOpcode::JumpIfNotEq | LuauOpcode::JumpIfNotLe | LuauOpcode::JumpIfNotLt
    )
}

fn opcode_label(opcode: LuauOpcode) -> &'static str {
    match opcode {
        LuauOpcode::Nop => "NOP",
        LuauOpcode::Break => "BREAK",
        LuauOpcode::LoadNil => "LOADNIL",
        LuauOpcode::LoadB => "LOADB",
        LuauOpcode::LoadN => "LOADN",
        LuauOpcode::LoadK => "LOADK",
        LuauOpcode::Move => "MOVE",
        LuauOpcode::GetGlobal => "GETGLOBAL",
        LuauOpcode::SetGlobal => "SETGLOBAL",
        LuauOpcode::GetUpVal => "GETUPVAL",
        LuauOpcode::SetUpVal => "SETUPVAL",
        LuauOpcode::CloseUpVals => "CLOSEUPVALS",
        LuauOpcode::GetImport => "GETIMPORT",
        LuauOpcode::GetTable => "GETTABLE",
        LuauOpcode::SetTable => "SETTABLE",
        LuauOpcode::GetTableKs => "GETTABLEKS",
        LuauOpcode::SetTableKs => "SETTABLEKS",
        LuauOpcode::GetTableN => "GETTABLEN",
        LuauOpcode::SetTableN => "SETTABLEN",
        LuauOpcode::NewClosure => "NEWCLOSURE",
        LuauOpcode::NameCall => "NAMECALL",
        LuauOpcode::Call => "CALL",
        LuauOpcode::Return => "RETURN",
        LuauOpcode::Jump => "JUMP",
        LuauOpcode::JumpBack => "JUMPBACK",
        LuauOpcode::JumpIf => "JUMPIF",
        LuauOpcode::JumpIfNot => "JUMPIFNOT",
        LuauOpcode::JumpIfEq => "JUMPIFEQ",
        LuauOpcode::JumpIfLe => "JUMPIFLE",
        LuauOpcode::JumpIfLt => "JUMPIFLT",
        LuauOpcode::JumpIfNotEq => "JUMPIFNOTEQ",
        LuauOpcode::JumpIfNotLe => "JUMPIFNOTLE",
        LuauOpcode::JumpIfNotLt => "JUMPIFNOTLT",
        LuauOpcode::Add => "ADD",
        LuauOpcode::Sub => "SUB",
        LuauOpcode::Mul => "MUL",
        LuauOpcode::Div => "DIV",
        LuauOpcode::Mod => "MOD",
        LuauOpcode::Pow => "POW",
        LuauOpcode::AddK => "ADDK",
        LuauOpcode::SubK => "SUBK",
        LuauOpcode::MulK => "MULK",
        LuauOpcode::DivK => "DIVK",
        LuauOpcode::ModK => "MODK",
        LuauOpcode::PowK => "POWK",
        LuauOpcode::And => "AND",
        LuauOpcode::Or => "OR",
        LuauOpcode::AndK => "ANDK",
        LuauOpcode::OrK => "ORK",
        LuauOpcode::Concat => "CONCAT",
        LuauOpcode::Not => "NOT",
        LuauOpcode::Minus => "MINUS",
        LuauOpcode::Length => "LENGTH",
        LuauOpcode::NewTable => "NEWTABLE",
        LuauOpcode::DupTable => "DUPTABLE",
        LuauOpcode::SetList => "SETLIST",
        LuauOpcode::ForNPrep => "FORNPREP",
        LuauOpcode::ForNLoop => "FORNLOOP",
        LuauOpcode::ForGLoop => "FORGLOOP",
        LuauOpcode::ForGPrepInext => "FORGPREP_INEXT",
        LuauOpcode::FastCall3 => "FASTCALL3",
        LuauOpcode::ForGPrepNext => "FORGPREP_NEXT",
        LuauOpcode::NativeCall => "NATIVECALL",
        LuauOpcode::GetVarArgs => "GETVARARGS",
        LuauOpcode::DupClosure => "DUPCLOSURE",
        LuauOpcode::PrepVarArgs => "PREPVARARGS",
        LuauOpcode::LoadKx => "LOADKX",
        LuauOpcode::JumpX => "JUMPX",
        LuauOpcode::FastCall => "FASTCALL",
        LuauOpcode::Coverage => "COVERAGE",
        LuauOpcode::Capture => "CAPTURE",
        LuauOpcode::SubRK => "SUBRK",
        LuauOpcode::DivRK => "DIVRK",
        LuauOpcode::FastCall1 => "FASTCALL1",
        LuauOpcode::FastCall2 => "FASTCALL2",
        LuauOpcode::FastCall2K => "FASTCALL2K",
        LuauOpcode::ForGPrep => "FORGPREP",
        LuauOpcode::JumpXEqKNil => "JUMPXEQKNIL",
        LuauOpcode::JumpXEqKB => "JUMPXEQKB",
        LuauOpcode::JumpXEqKN => "JUMPXEQKN",
        LuauOpcode::JumpXEqKS => "JUMPXEQKS",
        LuauOpcode::IDiv => "IDIV",
        LuauOpcode::IDivK => "IDIVK",
    }
}

fn expect_a(
    raw_pc: u32,
    opcode: LuauOpcode,
    operands: &LuauOperands,
) -> Result<u8, TransformError> {
    match operands {
        LuauOperands::A { a } => Ok(*a),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "A",
        }),
    }
}

fn expect_ab(
    raw_pc: u32,
    opcode: LuauOpcode,
    operands: &LuauOperands,
) -> Result<(u8, u8), TransformError> {
    match operands {
        LuauOperands::AB { a, b } => Ok((*a, *b)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "AB",
        }),
    }
}

fn expect_abc(
    raw_pc: u32,
    opcode: LuauOpcode,
    operands: &LuauOperands,
) -> Result<(u8, u8, u8), TransformError> {
    match operands {
        LuauOperands::ABC { a, b, c } => Ok((*a, *b, *c)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "ABC",
        }),
    }
}

fn expect_ac(
    raw_pc: u32,
    opcode: LuauOpcode,
    operands: &LuauOperands,
) -> Result<(u8, u8), TransformError> {
    match operands {
        LuauOperands::AC { a, c } => Ok((*a, *c)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "AC",
        }),
    }
}

fn expect_ad(
    raw_pc: u32,
    opcode: LuauOpcode,
    operands: &LuauOperands,
) -> Result<(u8, i16), TransformError> {
    match operands {
        LuauOperands::AD { a, d } => Ok((*a, *d)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "AD",
        }),
    }
}

fn expect_capture(raw_pc: u32, operands: &LuauOperands) -> Result<(u8, u8), TransformError> {
    match operands {
        LuauOperands::ABC { a, b, .. } => Ok((*a, *b)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: "CAPTURE",
            expected: "ABC",
        }),
    }
}
