//! 这个文件实现 Lua 5.4 到统一 low-IR 的 lowering。
//!
//! 相比 5.3，这里除了延续 `_ENV/upvalue table`、`LOADKX/EXTRAARG` 这类路径外，
//! 还需要显式处理 5.4 新增的 immediates、整数 key、`RETURN/TAILCALL` close 语义、
//! `LFALSESKIP` 布尔物化，以及 `TFORPREP` 带来的额外控制流节点。

use std::collections::BTreeMap;

use crate::parser::{
    DialectInstrExtra, Lua54InstrExtra, Lua54Opcode, Lua54Operands, RawChunk, RawInstr,
    RawInstrOpcode, RawInstrOperands, RawProto,
};
use crate::transformer::dialect::puc_lua::{
    call_args_pack, call_result_pack, range_len_inclusive, reg_from_u8, return_pack,
};
use crate::transformer::{
    AccessBase, AccessKey, BinaryOpInstr, BinaryOpKind, BranchCond, BranchInstr, BranchOperands,
    BranchPredicate, CallInstr, CallKind, Capture, CaptureSource, CloseInstr, ClosureInstr,
    ConcatInstr, CondOperand, ConstRef, DialectCaptureExtra, GenericForCallInstr,
    GenericForLoopInstr, GetTableInstr, GetUpvalueInstr, InstrRef, JumpInstr, LoadBoolInstr,
    LoadConstInstr, LoadIntegerInstr, LoadNilInstr, LoadNumberInstr, LowInstr, LoweredChunk,
    LoweredProto, LoweringMap, MoveInstr, NewTableInstr, NumberLiteral, NumericForInitInstr,
    NumericForLoopInstr, ProtoRef, RawInstrRef, Reg, RegRange, ResultPack, ReturnInstr,
    SetListInstr, SetTableInstr, SetUpvalueInstr, TailCallInstr, TbcInstr, TransformError,
    UnaryOpInstr, UnaryOpKind, UpvalueRef, ValueOperand, ValuePack, VarArgInstr,
};

const EXTRAARG_SCALE_8: u32 = 1_u32 << 8;

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
        let method_slots = usize::from(raw.common.frame.max_stack_size).saturating_add(4);
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
            let (opcode, operands, extra) = decode_lua54(raw_instr);
            let raw_pc = extra.pc;

            match opcode {
                Lua54Opcode::Move => {
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
                Lua54Opcode::LoadI => {
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
                Lua54Opcode::LoadF => {
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
                Lua54Opcode::LoadK => {
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
                Lua54Opcode::LoadKx => {
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
                Lua54Opcode::LoadFalse => {
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
                Lua54Opcode::LFalseSkip => {
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
                Lua54Opcode::LoadTrue => {
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
                Lua54Opcode::LoadNil => {
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
                Lua54Opcode::GetUpVal => {
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
                Lua54Opcode::GetTabUp => {
                    let (a, b, c, _) = expect_abck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst,
                            base: AccessBase::Upvalue(self.upvalue_ref(raw_pc, b as usize)?),
                            key: AccessKey::Const(self.const_ref(raw_pc, c as usize)?),
                        })),
                    );
                    raw_index += 1;
                }
                Lua54Opcode::GetTable => {
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
                Lua54Opcode::GetI => {
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
                Lua54Opcode::GetField => {
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
                Lua54Opcode::SetTabUp => {
                    let (a, b, c, k) = expect_abck(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::SetTable(SetTableInstr {
                            base: AccessBase::Upvalue(self.upvalue_ref(raw_pc, a as usize)?),
                            key: AccessKey::Const(self.const_ref(raw_pc, b as usize)?),
                            value: self.value_operand(raw_pc, c, k)?,
                        })),
                    );
                    raw_index += 1;
                }
                Lua54Opcode::SetUpVal => {
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
                Lua54Opcode::SetTable => {
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
                Lua54Opcode::SetI => {
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
                Lua54Opcode::SetField => {
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
                Lua54Opcode::NewTable => {
                    let (a, _, _, _) = expect_abck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::NewTable(NewTableInstr { dst })),
                    );
                    raw_index += 1;
                }
                Lua54Opcode::Self_ => {
                    let (a, b, c, k) = expect_abck(raw_pc, opcode, operands)?;
                    let callee = reg_from_u8(a);
                    let self_arg = Reg(callee.index() + 1);
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
                            key: self.access_key(raw_pc, c, k)?,
                        })),
                    );
                    self.set_pending_method(callee, self_arg);
                    raw_index += 1;
                }
                Lua54Opcode::AddI => {
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
                Lua54Opcode::AddK
                | Lua54Opcode::SubK
                | Lua54Opcode::MulK
                | Lua54Opcode::ModK
                | Lua54Opcode::PowK
                | Lua54Opcode::DivK
                | Lua54Opcode::IdivK
                | Lua54Opcode::BandK
                | Lua54Opcode::BorK
                | Lua54Opcode::BxorK => {
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
                Lua54Opcode::ShrI | Lua54Opcode::ShlI => {
                    let (a, b, sc, _) = expect_absck(raw_pc, opcode, operands)?;
                    let dst = reg_from_u8(a);
                    self.invalidate_written_reg(dst);
                    let (lhs, rhs) = match opcode {
                        Lua54Opcode::ShrI => (
                            ValueOperand::Reg(reg_from_u8(b)),
                            ValueOperand::Integer(i64::from(sc)),
                        ),
                        Lua54Opcode::ShlI => (
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
                Lua54Opcode::Add
                | Lua54Opcode::Sub
                | Lua54Opcode::Mul
                | Lua54Opcode::Mod
                | Lua54Opcode::Pow
                | Lua54Opcode::Div
                | Lua54Opcode::Idiv
                | Lua54Opcode::Band
                | Lua54Opcode::Bor
                | Lua54Opcode::Bxor
                | Lua54Opcode::Shl
                | Lua54Opcode::Shr => {
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
                Lua54Opcode::MMBin | Lua54Opcode::MMBinI | Lua54Opcode::MMBinK => {
                    raw_index += 1;
                }
                Lua54Opcode::Unm | Lua54Opcode::BNot | Lua54Opcode::Not | Lua54Opcode::Len => {
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
                Lua54Opcode::Concat => {
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
                Lua54Opcode::Close => {
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
                Lua54Opcode::Tbc => {
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
                Lua54Opcode::Jmp => {
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
                Lua54Opcode::Eq | Lua54Opcode::Lt | Lua54Opcode::Le => {
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
                Lua54Opcode::EqK => {
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
                Lua54Opcode::EqI
                | Lua54Opcode::LtI
                | Lua54Opcode::LeI
                | Lua54Opcode::GtI
                | Lua54Opcode::GeI => {
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
                Lua54Opcode::Test => {
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
                Lua54Opcode::TestSet => {
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
                Lua54Opcode::Call => {
                    let (a, b, c, _) = expect_abck(raw_pc, opcode, operands)?;
                    let kind = self.take_call_kind(reg_from_u8(a), u16::from(b));
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Call(CallInstr {
                            callee: reg_from_u8(a),
                            args: call_args_pack(a, u16::from(b)),
                            results: call_result_pack(a, u16::from(c)),
                            kind,
                        })),
                    );
                    raw_index += 1;
                }
                Lua54Opcode::TailCall => {
                    let (a, b, _, k) = expect_abck(raw_pc, opcode, operands)?;
                    let kind = self.take_call_kind(reg_from_u8(a), u16::from(b));
                    self.clear_all_method_hints();
                    if k {
                        self.emit(
                            Some(raw_index),
                            vec![raw_index],
                            PendingLowInstr::Ready(LowInstr::Close(CloseInstr { from: Reg(0) })),
                        );
                        self.emit(
                            None,
                            vec![raw_index],
                            PendingLowInstr::Ready(LowInstr::TailCall(TailCallInstr {
                                callee: reg_from_u8(a),
                                args: call_args_pack(a, u16::from(b)),
                                kind,
                            })),
                        );
                    } else {
                        self.emit(
                            Some(raw_index),
                            vec![raw_index],
                            PendingLowInstr::Ready(LowInstr::TailCall(TailCallInstr {
                                callee: reg_from_u8(a),
                                args: call_args_pack(a, u16::from(b)),
                                kind,
                            })),
                        );
                    }
                    raw_index += 1;
                }
                Lua54Opcode::Return => {
                    let (a, b, _, k) = expect_abck(raw_pc, opcode, operands)?;
                    self.clear_all_method_hints();
                    if k {
                        self.emit(
                            Some(raw_index),
                            vec![raw_index],
                            PendingLowInstr::Ready(LowInstr::Close(CloseInstr { from: Reg(0) })),
                        );
                        self.emit(
                            None,
                            vec![raw_index],
                            PendingLowInstr::Ready(LowInstr::Return(ReturnInstr {
                                values: return_pack(a, u16::from(b)),
                            })),
                        );
                    } else {
                        self.emit(
                            Some(raw_index),
                            vec![raw_index],
                            PendingLowInstr::Ready(LowInstr::Return(ReturnInstr {
                                values: return_pack(a, u16::from(b)),
                            })),
                        );
                    }
                    raw_index += 1;
                }
                Lua54Opcode::Return0 => {
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Return(ReturnInstr {
                            values: ValuePack::Fixed(RegRange::new(Reg(0), 0)),
                        })),
                    );
                    raw_index += 1;
                }
                Lua54Opcode::Return1 => {
                    let a = expect_a(raw_pc, opcode, operands)?;
                    self.clear_all_method_hints();
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Return(ReturnInstr {
                            values: ValuePack::Fixed(RegRange::new(reg_from_u8(a), 1)),
                        })),
                    );
                    raw_index += 1;
                }
                Lua54Opcode::ForLoop => {
                    self.clear_all_method_hints();
                    let (a, bx) = expect_abx(raw_pc, opcode, operands)?;
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
                                self.jump_target_back_bx(raw_pc, extra.pc, bx)?,
                            ),
                            exit_target: TargetPlaceholder::Raw(
                                self.ensure_targetable_pc(raw_pc, self.next_raw_pc(raw_index))?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                Lua54Opcode::ForPrep => {
                    self.clear_all_method_hints();
                    let (a, bx) = expect_abx(raw_pc, opcode, operands)?;
                    let loop_raw = self.for_prep_loop_target(raw_pc, extra.pc, bx)?;
                    let target_opcode = opcode_at(self.raw, loop_raw);
                    if target_opcode != Lua54Opcode::ForLoop {
                        return Err(TransformError::InvalidNumericForPair {
                            raw_pc,
                            target_raw: raw_pc_at(self.raw, loop_raw) as usize,
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
                                self.ensure_targetable_pc(raw_pc, self.next_raw_pc(loop_raw))?,
                            ),
                        },
                    );
                    raw_index += 1;
                }
                Lua54Opcode::TForPrep => {
                    self.clear_all_method_hints();
                    let (a, bx) = expect_abx(raw_pc, opcode, operands)?;
                    let tbc_reg = Reg(usize::from(a) + 3);
                    let call_target = self.tforprep_call_target(raw_pc, extra.pc, bx)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Tbc(TbcInstr { reg: tbc_reg })),
                    );
                    self.emit(
                        None,
                        vec![raw_index],
                        PendingLowInstr::Jump {
                            target: TargetPlaceholder::Raw(call_target),
                        },
                    );
                    raw_index += 1;
                }
                Lua54Opcode::TForCall => {
                    self.clear_all_method_hints();
                    let (a, c) = expect_ac(raw_pc, opcode, operands)?;
                    let pair = self.generic_for_pair(raw_index, a, c)?;
                    let state_start = reg_from_u8(a);
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GenericForCall(GenericForCallInstr {
                            state: RegRange::new(state_start, 3),
                            results: ResultPack::Fixed(RegRange::new(
                                Reg(state_start.index() + 4),
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
                Lua54Opcode::TForLoop => {
                    return Err(TransformError::InvalidGenericForLoop {
                        raw_pc,
                        helper_pc: raw_pc,
                        found: opcode_label(opcode),
                    });
                }
                Lua54Opcode::SetList => {
                    let (a, b, c, k) = expect_abck(raw_pc, opcode, operands)?;
                    let base_index = u32::from(c)
                        + if k {
                            self.extra_arg(raw_pc, opcode, extra.extra_arg)? * EXTRAARG_SCALE_8
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
                Lua54Opcode::Closure => {
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
                Lua54Opcode::VarArg => {
                    let (a, c) = expect_ac(raw_pc, opcode, operands)?;
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
                Lua54Opcode::VarArgPrep => {
                    raw_index += 1;
                }
                Lua54Opcode::ExtraArg => {
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
                    let pc = raw_pc_at(self.raw, *raw_index) as usize;
                    self.raw.common.debug_info.common.line_info.get(pc).copied()
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
        opcode: Lua54Opcode,
        extra_arg: Option<u32>,
    ) -> Result<u32, TransformError> {
        extra_arg.ok_or(TransformError::MissingExtraArg {
            raw_pc,
            opcode: opcode_label(opcode),
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

    fn access_key(&self, raw_pc: u32, operand: u8, k: bool) -> Result<AccessKey, TransformError> {
        if k {
            Ok(AccessKey::Const(self.const_ref(raw_pc, operand as usize)?))
        } else {
            Ok(AccessKey::Reg(reg_from_u8(operand)))
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

    fn for_prep_loop_target(
        &self,
        raw_pc: u32,
        base_pc: u32,
        bx: u32,
    ) -> Result<usize, TransformError> {
        let target_pc = i64::from(base_pc) + 1 + i64::from(bx);
        self.ensure_targetable_jump_pc(raw_pc, target_pc)
    }

    fn tforprep_call_target(
        &self,
        raw_pc: u32,
        base_pc: u32,
        bx: u32,
    ) -> Result<usize, TransformError> {
        let target_pc = i64::from(base_pc) + 1 + i64::from(bx);
        self.ensure_targetable_jump_pc(raw_pc, target_pc)
    }

    fn ensure_targetable_jump_pc(
        &self,
        raw_pc: u32,
        target_pc: i64,
    ) -> Result<usize, TransformError> {
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
        opcode: Lua54Opcode,
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
        let (helper_opcode, helper_operands, helper_extra) = decode_lua54(helper_instr);
        if helper_opcode != Lua54Opcode::Jmp {
            return Err(TransformError::InvalidHelperJump {
                raw_pc,
                helper_pc: helper_extra.pc,
                found: opcode_label(helper_opcode),
            });
        }
        let helper_sj = expect_asj(helper_extra.pc, helper_opcode, helper_operands)?;

        Ok(HelperJump {
            helper_index,
            jump_target: self.jump_target_sj(helper_extra.pc, helper_extra.pc, helper_sj)?,
            fallthrough_target: self
                .ensure_targetable_pc(raw_pc, self.next_raw_pc(helper_index))?,
            next_index: helper_index + 1,
        })
    }

    fn generic_for_pair(
        &self,
        raw_index: usize,
        call_a: u8,
        result_count: u8,
    ) -> Result<GenericForPair, TransformError> {
        let raw_pc = raw_pc_at(self.raw, raw_index);
        let helper_pc = raw_pc + 1;
        let Some(loop_index) = self.raw_pc_to_index.get(&helper_pc).copied() else {
            return Err(TransformError::MissingGenericForLoop { raw_pc });
        };
        let helper_instr = &self.raw.common.instructions[loop_index];
        let (helper_opcode, helper_operands, helper_extra) = decode_lua54(helper_instr);
        if helper_opcode != Lua54Opcode::TForLoop {
            return Err(TransformError::InvalidGenericForLoop {
                raw_pc,
                helper_pc: helper_extra.pc,
                found: opcode_label(helper_opcode),
            });
        }
        let (loop_a, bx) = expect_abx(helper_extra.pc, helper_opcode, helper_operands)?;
        if loop_a != call_a {
            return Err(TransformError::InvalidGenericForPair {
                raw_pc,
                call_base: usize::from(call_a),
                loop_control: usize::from(loop_a),
            });
        }

        Ok(GenericForPair {
            loop_index,
            control: Reg(usize::from(loop_a) + 2),
            bindings: RegRange::new(Reg(usize::from(loop_a) + 4), usize::from(result_count)),
            body_target: self.jump_target_back_bx(helper_extra.pc, helper_extra.pc, bx)?,
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

fn decode_lua54(raw: &RawInstr) -> (Lua54Opcode, &Lua54Operands, Lua54InstrExtra) {
    let RawInstrOpcode::Lua54(opcode) = raw.opcode else {
        unreachable!("lua54 lowerer should only decode lua54 opcodes");
    };
    let RawInstrOperands::Lua54(ref operands) = raw.operands else {
        unreachable!("lua54 lowerer should only decode lua54 operands");
    };
    let DialectInstrExtra::Lua54(extra) = raw.extra else {
        unreachable!("lua54 lowerer should only decode lua54 instruction extras");
    };
    (opcode, operands, extra)
}

fn raw_pc(raw: &RawInstr) -> u32 {
    let DialectInstrExtra::Lua54(extra) = raw.extra else {
        unreachable!("lua54 lowerer should only decode lua54 instruction extras");
    };
    extra.pc
}

fn word_len(raw: &RawInstr) -> u8 {
    let DialectInstrExtra::Lua54(extra) = raw.extra else {
        unreachable!("lua54 lowerer should only decode lua54 instruction extras");
    };
    extra.word_len
}

fn raw_pc_at(raw: &RawProto, index: usize) -> u32 {
    raw_pc(&raw.common.instructions[index])
}

fn opcode_at(raw: &RawProto, index: usize) -> Lua54Opcode {
    let (opcode, _, _) = decode_lua54(&raw.common.instructions[index]);
    opcode
}

fn unary_op_kind(opcode: Lua54Opcode) -> UnaryOpKind {
    match opcode {
        Lua54Opcode::Unm => UnaryOpKind::Neg,
        Lua54Opcode::BNot => UnaryOpKind::BitNot,
        Lua54Opcode::Not => UnaryOpKind::Not,
        Lua54Opcode::Len => UnaryOpKind::Length,
        _ => unreachable!("only unary opcodes should reach unary_op_kind"),
    }
}

fn binary_op_kind(opcode: Lua54Opcode) -> BinaryOpKind {
    match opcode {
        Lua54Opcode::AddI | Lua54Opcode::AddK | Lua54Opcode::Add => BinaryOpKind::Add,
        Lua54Opcode::SubK | Lua54Opcode::Sub => BinaryOpKind::Sub,
        Lua54Opcode::MulK | Lua54Opcode::Mul => BinaryOpKind::Mul,
        Lua54Opcode::DivK | Lua54Opcode::Div => BinaryOpKind::Div,
        Lua54Opcode::IdivK | Lua54Opcode::Idiv => BinaryOpKind::FloorDiv,
        Lua54Opcode::ModK | Lua54Opcode::Mod => BinaryOpKind::Mod,
        Lua54Opcode::PowK | Lua54Opcode::Pow => BinaryOpKind::Pow,
        Lua54Opcode::BandK | Lua54Opcode::Band => BinaryOpKind::BitAnd,
        Lua54Opcode::BorK | Lua54Opcode::Bor => BinaryOpKind::BitOr,
        Lua54Opcode::BxorK | Lua54Opcode::Bxor => BinaryOpKind::BitXor,
        Lua54Opcode::ShlI | Lua54Opcode::Shl => BinaryOpKind::Shl,
        Lua54Opcode::ShrI | Lua54Opcode::Shr => BinaryOpKind::Shr,
        _ => unreachable!("only arithmetic/bitwise opcodes should reach binary_op_kind"),
    }
}

fn branch_predicate(opcode: Lua54Opcode) -> BranchPredicate {
    match opcode {
        Lua54Opcode::Eq | Lua54Opcode::EqK | Lua54Opcode::EqI => BranchPredicate::Eq,
        Lua54Opcode::Lt | Lua54Opcode::LtI | Lua54Opcode::GtI => BranchPredicate::Lt,
        Lua54Opcode::Le | Lua54Opcode::LeI | Lua54Opcode::GeI => BranchPredicate::Le,
        _ => unreachable!("only compare opcodes should reach branch_predicate"),
    }
}

fn compare_immediate_shape(
    opcode: Lua54Opcode,
    reg: Reg,
    immediate: CondOperand,
) -> (BranchPredicate, CondOperand, CondOperand) {
    match opcode {
        Lua54Opcode::EqI | Lua54Opcode::LtI | Lua54Opcode::LeI => {
            (branch_predicate(opcode), CondOperand::Reg(reg), immediate)
        }
        Lua54Opcode::GtI => (BranchPredicate::Lt, immediate, CondOperand::Reg(reg)),
        Lua54Opcode::GeI => (BranchPredicate::Le, immediate, CondOperand::Reg(reg)),
        _ => unreachable!("only compare-immediate opcodes should reach compare_immediate_shape"),
    }
}

fn opcode_label(opcode: Lua54Opcode) -> &'static str {
    match opcode {
        Lua54Opcode::Move => "MOVE",
        Lua54Opcode::LoadI => "LOADI",
        Lua54Opcode::LoadF => "LOADF",
        Lua54Opcode::LoadK => "LOADK",
        Lua54Opcode::LoadKx => "LOADKX",
        Lua54Opcode::LoadFalse => "LOADFALSE",
        Lua54Opcode::LFalseSkip => "LFALSESKIP",
        Lua54Opcode::LoadTrue => "LOADTRUE",
        Lua54Opcode::LoadNil => "LOADNIL",
        Lua54Opcode::GetUpVal => "GETUPVAL",
        Lua54Opcode::SetUpVal => "SETUPVAL",
        Lua54Opcode::GetTabUp => "GETTABUP",
        Lua54Opcode::GetTable => "GETTABLE",
        Lua54Opcode::GetI => "GETI",
        Lua54Opcode::GetField => "GETFIELD",
        Lua54Opcode::SetTabUp => "SETTABUP",
        Lua54Opcode::SetTable => "SETTABLE",
        Lua54Opcode::SetI => "SETI",
        Lua54Opcode::SetField => "SETFIELD",
        Lua54Opcode::NewTable => "NEWTABLE",
        Lua54Opcode::Self_ => "SELF",
        Lua54Opcode::AddI => "ADDI",
        Lua54Opcode::AddK => "ADDK",
        Lua54Opcode::SubK => "SUBK",
        Lua54Opcode::MulK => "MULK",
        Lua54Opcode::ModK => "MODK",
        Lua54Opcode::PowK => "POWK",
        Lua54Opcode::DivK => "DIVK",
        Lua54Opcode::IdivK => "IDIVK",
        Lua54Opcode::BandK => "BANDK",
        Lua54Opcode::BorK => "BORK",
        Lua54Opcode::BxorK => "BXORK",
        Lua54Opcode::ShrI => "SHRI",
        Lua54Opcode::ShlI => "SHLI",
        Lua54Opcode::Add => "ADD",
        Lua54Opcode::Sub => "SUB",
        Lua54Opcode::Mul => "MUL",
        Lua54Opcode::Mod => "MOD",
        Lua54Opcode::Pow => "POW",
        Lua54Opcode::Div => "DIV",
        Lua54Opcode::Idiv => "IDIV",
        Lua54Opcode::Band => "BAND",
        Lua54Opcode::Bor => "BOR",
        Lua54Opcode::Bxor => "BXOR",
        Lua54Opcode::Shl => "SHL",
        Lua54Opcode::Shr => "SHR",
        Lua54Opcode::MMBin => "MMBIN",
        Lua54Opcode::MMBinI => "MMBINI",
        Lua54Opcode::MMBinK => "MMBINK",
        Lua54Opcode::Unm => "UNM",
        Lua54Opcode::BNot => "BNOT",
        Lua54Opcode::Not => "NOT",
        Lua54Opcode::Len => "LEN",
        Lua54Opcode::Concat => "CONCAT",
        Lua54Opcode::Close => "CLOSE",
        Lua54Opcode::Tbc => "TBC",
        Lua54Opcode::Jmp => "JMP",
        Lua54Opcode::Eq => "EQ",
        Lua54Opcode::Lt => "LT",
        Lua54Opcode::Le => "LE",
        Lua54Opcode::EqK => "EQK",
        Lua54Opcode::EqI => "EQI",
        Lua54Opcode::LtI => "LTI",
        Lua54Opcode::LeI => "LEI",
        Lua54Opcode::GtI => "GTI",
        Lua54Opcode::GeI => "GEI",
        Lua54Opcode::Test => "TEST",
        Lua54Opcode::TestSet => "TESTSET",
        Lua54Opcode::Call => "CALL",
        Lua54Opcode::TailCall => "TAILCALL",
        Lua54Opcode::Return => "RETURN",
        Lua54Opcode::Return0 => "RETURN0",
        Lua54Opcode::Return1 => "RETURN1",
        Lua54Opcode::ForLoop => "FORLOOP",
        Lua54Opcode::ForPrep => "FORPREP",
        Lua54Opcode::TForPrep => "TFORPREP",
        Lua54Opcode::TForCall => "TFORCALL",
        Lua54Opcode::TForLoop => "TFORLOOP",
        Lua54Opcode::SetList => "SETLIST",
        Lua54Opcode::Closure => "CLOSURE",
        Lua54Opcode::VarArg => "VARARG",
        Lua54Opcode::VarArgPrep => "VARARGPREP",
        Lua54Opcode::ExtraArg => "EXTRAARG",
    }
}

fn expect_a(
    raw_pc: u32,
    opcode: Lua54Opcode,
    operands: &Lua54Operands,
) -> Result<u8, TransformError> {
    match operands {
        Lua54Operands::A { a } => Ok(*a),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "A",
        }),
    }
}

fn expect_ak(
    raw_pc: u32,
    opcode: Lua54Opcode,
    operands: &Lua54Operands,
) -> Result<(u8, bool), TransformError> {
    match operands {
        Lua54Operands::Ak { a, k } => Ok((*a, *k)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "Ak",
        }),
    }
}

fn expect_ab(
    raw_pc: u32,
    opcode: Lua54Opcode,
    operands: &Lua54Operands,
) -> Result<(u8, u8), TransformError> {
    match operands {
        Lua54Operands::AB { a, b } => Ok((*a, *b)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "AB",
        }),
    }
}

fn expect_ac(
    raw_pc: u32,
    opcode: Lua54Opcode,
    operands: &Lua54Operands,
) -> Result<(u8, u8), TransformError> {
    match operands {
        Lua54Operands::AC { a, c } => Ok((*a, *c)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "AC",
        }),
    }
}

fn expect_abk(
    raw_pc: u32,
    opcode: Lua54Opcode,
    operands: &Lua54Operands,
) -> Result<(u8, u8, bool), TransformError> {
    match operands {
        Lua54Operands::ABk { a, b, k } => Ok((*a, *b, *k)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "ABk",
        }),
    }
}

fn expect_abck(
    raw_pc: u32,
    opcode: Lua54Opcode,
    operands: &Lua54Operands,
) -> Result<(u8, u8, u8, bool), TransformError> {
    match operands {
        Lua54Operands::ABCk { a, b, c, k } => Ok((*a, *b, *c, *k)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "ABCk",
        }),
    }
}

fn expect_abx(
    raw_pc: u32,
    opcode: Lua54Opcode,
    operands: &Lua54Operands,
) -> Result<(u8, u32), TransformError> {
    match operands {
        Lua54Operands::ABx { a, bx } => Ok((*a, *bx)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "ABx",
        }),
    }
}

fn expect_asbx(
    raw_pc: u32,
    opcode: Lua54Opcode,
    operands: &Lua54Operands,
) -> Result<(u8, i32), TransformError> {
    match operands {
        Lua54Operands::AsBx { a, sbx } => Ok((*a, *sbx)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "AsBx",
        }),
    }
}

fn expect_asj(
    raw_pc: u32,
    opcode: Lua54Opcode,
    operands: &Lua54Operands,
) -> Result<i32, TransformError> {
    match operands {
        Lua54Operands::AsJ { sj } => Ok(*sj),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "AsJ",
        }),
    }
}

fn expect_absck(
    raw_pc: u32,
    opcode: Lua54Opcode,
    operands: &Lua54Operands,
) -> Result<(u8, u8, i16, bool), TransformError> {
    match operands {
        Lua54Operands::ABsCk { a, b, sc, k } => Ok((*a, *b, *sc, *k)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "ABsCk",
        }),
    }
}

fn expect_asbck(
    raw_pc: u32,
    opcode: Lua54Opcode,
    operands: &Lua54Operands,
) -> Result<(u8, i16, u8, bool), TransformError> {
    match operands {
        Lua54Operands::AsBCk { a, sb, c, k } => Ok((*a, *sb, *c, *k)),
        _ => Err(TransformError::UnexpectedOperands {
            raw_pc,
            opcode: opcode_label(opcode),
            expected: "AsBCk",
        }),
    }
}
