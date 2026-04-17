//! 这个文件实现 LuaJIT bytecode 到统一 low-IR 的 lowering。
//!
//! 第一阶段目标是把 LuaJIT 2.1 编出来的常见 opcode 子集稳定映射成现有 low-IR：
//! - calls/returns/vararg 用 LuaJIT 自己的 B/C 约定解释；
//! - compare/test + helper JMP 直接压成结构化 branch；
//! - LOOP/ILOOP/JLOOP 只当 targetable marker，不伪造成额外语义；
//! - TDUP 在这里展开成 `NewTable + SetTable*`，不把模板表细节泄漏到后层。

use crate::parser::{
    LuaJitKgcEntry, LuaJitNumberConstEntry, LuaJitOpcode, LuaJitOperands, LuaJitTableConst,
    LuaJitTableLiteral, RawChunk, RawLiteralConst, RawProto,
};
use crate::transformer::dialect::lowering::{
    PendingLowInstr, PendingLoweringState, TargetPlaceholder, instr_pc, resolve_pending_instr_with,
};
use crate::transformer::operands::define_operand_expecters;
use crate::transformer::{
    AccessBase, AccessKey, BinaryOpInstr, BinaryOpKind, BranchCond, BranchOperands,
    BranchPredicate, CallInstr, CallKind, Capture, CaptureSource, CloseInstr, ClosureInstr,
    ConcatInstr, CondOperand, ConstRef, DialectCaptureExtra, GenericForCallInstr, GetTableInstr,
    GetUpvalueInstr, InstrRef, LoadBoolInstr, LoadConstInstr, LoadIntegerInstr, LoadNilInstr,
    LowInstr, LoweredChunk, LoweredProto, LoweringMap, MoveInstr, NewTableInstr, ProtoRef, Reg,
    RegRange, ResultPack, ReturnInstr, SetListInstr, SetTableInstr, SetUpvalueInstr, TailCallInstr,
    TransformError, UnaryOpInstr, UnaryOpKind, UpvalueRef, ValueOperand, ValuePack, VarArgInstr,
};

const NO_REG: u8 = 0xff;
const BCBIAS_J_RAW: i64 = 0x7fff;
const BCDUMP_KPRI_NIL: u16 = 0;
const BCDUMP_KPRI_FALSE: u16 = 1;
const BCDUMP_KPRI_TRUE: u16 = 2;
const TWO_POW_52: f64 = 4_503_599_627_370_496.0;

pub(crate) fn lower_chunk(chunk: &RawChunk) -> Result<LoweredChunk, TransformError> {
    let fr2 = chunk
        .header
        .luajit_fr2()
        .expect("luajit lowerer should only receive luajit headers");

    Ok(LoweredChunk {
        header: chunk.header.clone(),
        main: lower_proto(&chunk.main, fr2)?,
        origin: chunk.origin,
    })
}

fn lower_proto(raw: &RawProto, fr2: bool) -> Result<LoweredProto, TransformError> {
    let children = raw
        .common
        .children
        .iter()
        .map(|child| lower_proto(child, fr2))
        .collect::<Result<Vec<_>, _>>()?;
    let mut lowerer = ProtoLowerer::new(raw, fr2);
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
    lowering: PendingLoweringState,
    fr2: usize,
}

impl<'a> ProtoLowerer<'a> {
    fn new(raw: &'a RawProto, fr2: bool) -> Self {
        let raw_instr_count = raw.common.instructions.len();
        Self {
            raw,
            lowering: PendingLoweringState::new(raw_instr_count),
            fr2: usize::from(fr2),
        }
    }

    fn lower(&mut self) -> Result<(Vec<LowInstr>, LoweringMap), TransformError> {
        let mut raw_index = 0_usize;

        while raw_index < self.raw.common.instructions.len() {
            let raw_instr = &self.raw.common.instructions[raw_index];
            let (opcode, operands, extra) = raw_instr
                .luajit()
                .expect("luajit lowerer should only decode luajit instructions");
            let raw_pc = extra.pc;

            match opcode {
                LuaJitOpcode::Mov => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
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
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetUpvalue(GetUpvalueInstr {
                            dst: reg_from_u8(a),
                            src: self.upvalue_ref(raw_pc, usize::from(d))?,
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
                            dst: self.upvalue_ref(raw_pc, usize::from(a))?,
                            src: reg_from_u16(d),
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::FNew => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
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
                            dst: reg_from_u8(a),
                            proto,
                            captures,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::TNew => {
                    let (a, _) = expect_ad(raw_pc, opcode, operands)?;
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
                            })),
                        );
                    }
                    raw_index += 1;
                }
                LuaJitOpcode::GGet => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst: reg_from_u8(a),
                            base: AccessBase::Env,
                            key: AccessKey::Const(
                                self.kgc_string_const_ref(raw_pc, usize::from(d))?,
                            ),
                            method_load: false,
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
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::TGetV | LuaJitOpcode::TGetR => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst: reg_from_u8(a),
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Reg(reg_from_u8(c)),
                            method_load: false,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::TGetS => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst: reg_from_u8(a),
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Const(
                                self.kgc_string_const_ref(raw_pc, usize::from(c))?,
                            ),
                            method_load: false,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::TGetB => {
                    let (a, b, c) = expect_abc(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GetTable(GetTableInstr {
                            dst: reg_from_u8(a),
                            base: AccessBase::Reg(reg_from_u8(b)),
                            key: AccessKey::Integer(i64::from(c)),
                            method_load: false,
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
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Call(CallInstr {
                            callee: reg_from_u8(a),
                            args: self.call_args_pack(a, c),
                            results: call_results_pack(a, b),
                            kind: CallKind::Normal,
                            method_name: None,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::CallM => {
                    let (a, b, _c) = expect_abc(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::Call(CallInstr {
                            callee: reg_from_u8(a),
                            args: ValuePack::Open(self.call_arg_start(a)),
                            results: call_results_pack(a, b),
                            kind: CallKind::Normal,
                            method_name: None,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::CallT => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::TailCall(TailCallInstr {
                            callee: reg_from_u8(a),
                            args: self.tail_call_args_pack(a, d),
                            kind: CallKind::Normal,
                            method_name: None,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::CallMT => {
                    let (a, _d) = expect_ad(raw_pc, opcode, operands)?;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::TailCall(TailCallInstr {
                            callee: reg_from_u8(a),
                            args: ValuePack::Open(self.call_arg_start(a)),
                            kind: CallKind::Normal,
                            method_name: None,
                        })),
                    );
                    raw_index += 1;
                }
                LuaJitOpcode::VArg => {
                    let (a, b, _) = expect_abc(raw_pc, opcode, operands)?;
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
                LuaJitOpcode::ForL | LuaJitOpcode::IForL | LuaJitOpcode::JForL => {
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
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
                    self.emit(
                        Some(raw_index),
                        vec![raw_index],
                        PendingLowInstr::Ready(LowInstr::GenericForCall(GenericForCallInstr {
                            state: RegRange::new(Reg(usize::from(a).saturating_sub(3)), 3),
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
                            control: Reg(usize::from(a).saturating_sub(1)),
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
                LuaJitOpcode::Jmp => {
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
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    let _ = a;
                    self.emit(
                        Some(raw_index),
                        vec![raw_index, helper.helper_index],
                        PendingLowInstr::Branch {
                            cond: BranchCond {
                                predicate: BranchPredicate::Truthy,
                                operands: BranchOperands::Unary(CondOperand::Reg(reg_from_u16(d))),
                                negated: matches!(opcode, LuaJitOpcode::IsF),
                            },
                            then_target: TargetPlaceholder::Raw(helper.jump_target),
                            else_target: TargetPlaceholder::Raw(helper.fallthrough_target),
                        },
                    );
                    raw_index += 2;
                }
                LuaJitOpcode::IsTC | LuaJitOpcode::IsFC => {
                    let helper = self.helper_jump(raw_index, opcode)?;
                    let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                    if a == NO_REG || a == (d as u8) {
                        self.emit(
                            Some(raw_index),
                            vec![raw_index, helper.helper_index],
                            PendingLowInstr::Branch {
                                cond: BranchCond {
                                    predicate: BranchPredicate::Truthy,
                                    operands: BranchOperands::Unary(CondOperand::Reg(
                                        reg_from_u16(d),
                                    )),
                                    negated: matches!(opcode, LuaJitOpcode::IsFC),
                                },
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
                                cond: BranchCond {
                                    predicate: BranchPredicate::Truthy,
                                    operands: BranchOperands::Unary(CondOperand::Reg(
                                        reg_from_u16(d),
                                    )),
                                    negated: matches!(opcode, LuaJitOpcode::IsFC),
                                },
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
                LuaJitOpcode::Loop | LuaJitOpcode::ILoop | LuaJitOpcode::JLoop => {
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
        self.lowering
            .resolve_target(owner_pc, target, |raw_index| raw_index)
    }

    fn emit(
        &mut self,
        owner_raw: Option<usize>,
        raw_indices: Vec<usize>,
        instr: PendingLowInstr,
    ) -> usize {
        self.lowering.emit(owner_raw, raw_indices, instr)
    }

    fn mark_raw_target(&mut self, raw_index: usize) {
        self.lowering.mark_raw_target(raw_index);
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

    fn kgc_entries(&self) -> &[LuaJitKgcEntry] {
        self.raw
            .common
            .constants
            .luajit_kgc_entries()
            .expect("luajit lowerer should only receive luajit constant pools")
    }

    fn knum_entries(&self) -> &[LuaJitNumberConstEntry] {
        self.raw
            .common
            .constants
            .luajit_knum_entries()
            .expect("luajit lowerer should only receive luajit constant pools")
    }

    fn kgc_entry(&self, raw_pc: u32, index: usize) -> Result<&LuaJitKgcEntry, TransformError> {
        self.kgc_entries()
            .get(index)
            .ok_or(TransformError::InvalidConstRef {
                raw_pc,
                const_index: index,
                const_count: self.kgc_entries().len(),
            })
    }

    fn knum_entry(
        &self,
        raw_pc: u32,
        index: usize,
    ) -> Result<&LuaJitNumberConstEntry, TransformError> {
        self.knum_entries()
            .get(index)
            .ok_or(TransformError::InvalidConstRef {
                raw_pc,
                const_index: index,
                const_count: self.knum_entries().len(),
            })
    }

    fn kgc_literal_const_ref(&self, raw_pc: u32, index: usize) -> Result<ConstRef, TransformError> {
        match self.kgc_entry(raw_pc, index)? {
            LuaJitKgcEntry::Literal { literal_index, .. } => self.const_ref(raw_pc, *literal_index),
            _ => Err(TransformError::InvalidConstRef {
                raw_pc,
                const_index: index,
                const_count: self.kgc_entries().len(),
            }),
        }
    }

    fn kgc_string_const_ref(&self, raw_pc: u32, index: usize) -> Result<ConstRef, TransformError> {
        let const_ref = self.kgc_literal_const_ref(raw_pc, index)?;
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
                const_count: self.kgc_entries().len(),
            }),
        }
    }

    fn knum_const_ref(&self, raw_pc: u32, index: usize) -> Result<ConstRef, TransformError> {
        match self.knum_entry(raw_pc, index)? {
            LuaJitNumberConstEntry::Integer { literal_index, .. }
            | LuaJitNumberConstEntry::Number { literal_index, .. } => {
                self.const_ref(raw_pc, *literal_index)
            }
        }
    }

    fn table_const(&self, raw_pc: u32, index: usize) -> Result<&LuaJitTableConst, TransformError> {
        match self.kgc_entry(raw_pc, index)? {
            LuaJitKgcEntry::Table(table) => Ok(table),
            _ => Err(TransformError::InvalidConstRef {
                raw_pc,
                const_index: index,
                const_count: self.kgc_entries().len(),
            }),
        }
    }

    fn proto_ref_from_kgc_child(
        &self,
        raw_pc: u32,
        index: usize,
    ) -> Result<ProtoRef, TransformError> {
        match self.kgc_entry(raw_pc, index)? {
            LuaJitKgcEntry::Child { child_proto_index } => {
                self.proto_ref(raw_pc, *child_proto_index)
            }
            _ => Err(TransformError::InvalidConstRef {
                raw_pc,
                const_index: index,
                const_count: self.kgc_entries().len(),
            }),
        }
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

    fn compare_cond(
        &self,
        raw_pc: u32,
        opcode: LuaJitOpcode,
        operands: &LuaJitOperands,
    ) -> Result<BranchCond, TransformError> {
        match opcode {
            LuaJitOpcode::IsLt | LuaJitOpcode::IsGe | LuaJitOpcode::IsLe | LuaJitOpcode::IsGt => {
                let (a, _b, c) = expect_abc(raw_pc, opcode, operands)?;
                let lhs = CondOperand::Reg(reg_from_u8(a));
                let rhs = CondOperand::Reg(reg_from_u8(c));
                let (predicate, left, right) = match opcode {
                    LuaJitOpcode::IsLt => (BranchPredicate::Lt, lhs, rhs),
                    LuaJitOpcode::IsLe => (BranchPredicate::Le, lhs, rhs),
                    LuaJitOpcode::IsGe => (BranchPredicate::Le, rhs, lhs),
                    LuaJitOpcode::IsGt => (BranchPredicate::Lt, rhs, lhs),
                    _ => unreachable!(),
                };
                Ok(BranchCond {
                    predicate,
                    operands: BranchOperands::Binary(left, right),
                    negated: false,
                })
            }
            LuaJitOpcode::IsEqV | LuaJitOpcode::IsNeV => {
                let (a, _b, c) = expect_abc(raw_pc, opcode, operands)?;
                Ok(BranchCond {
                    predicate: BranchPredicate::Eq,
                    operands: BranchOperands::Binary(
                        CondOperand::Reg(reg_from_u8(a)),
                        CondOperand::Reg(reg_from_u8(c)),
                    ),
                    negated: matches!(opcode, LuaJitOpcode::IsNeV),
                })
            }
            LuaJitOpcode::IsEqS | LuaJitOpcode::IsNeS => {
                let (a, _b, c) = expect_abc(raw_pc, opcode, operands)?;
                Ok(BranchCond {
                    predicate: BranchPredicate::Eq,
                    operands: BranchOperands::Binary(
                        CondOperand::Reg(reg_from_u8(a)),
                        CondOperand::Const(self.kgc_string_const_ref(raw_pc, usize::from(c))?),
                    ),
                    negated: matches!(opcode, LuaJitOpcode::IsNeS),
                })
            }
            LuaJitOpcode::IsEqN | LuaJitOpcode::IsNeN => {
                let (a, _b, c) = expect_abc(raw_pc, opcode, operands)?;
                Ok(BranchCond {
                    predicate: BranchPredicate::Eq,
                    operands: BranchOperands::Binary(
                        CondOperand::Reg(reg_from_u8(a)),
                        self.knum_cond_operand(raw_pc, usize::from(c))?,
                    ),
                    negated: matches!(opcode, LuaJitOpcode::IsNeN),
                })
            }
            LuaJitOpcode::IsEqP | LuaJitOpcode::IsNeP => {
                let (a, _b, c) = expect_abc(raw_pc, opcode, operands)?;
                Ok(BranchCond {
                    predicate: BranchPredicate::Eq,
                    operands: BranchOperands::Binary(
                        CondOperand::Reg(reg_from_u8(a)),
                        pri_cond_operand(raw_pc, u16::from(c))?,
                    ),
                    negated: matches!(opcode, LuaJitOpcode::IsNeP),
                })
            }
            _ => unreachable!("only compare opcodes should reach compare_cond"),
        }
    }

    fn knum_cond_operand(&self, raw_pc: u32, index: usize) -> Result<CondOperand, TransformError> {
        match self.knum_entry(raw_pc, index)? {
            LuaJitNumberConstEntry::Integer { value, .. } => Ok(CondOperand::Integer(*value)),
            LuaJitNumberConstEntry::Number { value, .. } => Ok(CondOperand::Number(
                crate::transformer::NumberLiteral::from_f64(*value),
            )),
        }
    }

    fn jump_target(&self, raw_pc: u32, raw_index: usize, d: u16) -> Result<usize, TransformError> {
        let target = raw_index as i64 + i64::from(d) - BCBIAS_J_RAW;
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
        opcode: LuaJitOpcode,
    ) -> Result<HelperJump, TransformError> {
        let raw_pc = raw_pc_at(self.raw, raw_index);
        let helper_index = raw_index + 1;
        let Some(helper_instr) = self.raw.common.instructions.get(helper_index) else {
            return Err(TransformError::MissingHelperJump {
                raw_pc,
                opcode: opcode.label(),
            });
        };
        let (helper_opcode, helper_operands, helper_extra) = helper_instr
            .luajit()
            .expect("luajit lowerer should only decode luajit instructions");
        if helper_opcode != LuaJitOpcode::Jmp {
            return Err(TransformError::InvalidHelperJump {
                raw_pc,
                helper_pc: helper_extra.pc,
                found: helper_opcode.label(),
            });
        }
        let (_, d) = expect_ad(helper_extra.pc, helper_opcode, helper_operands)?;
        Ok(HelperJump {
            helper_index,
            jump_target: self.jump_target(helper_extra.pc, helper_index, d)?,
            fallthrough_target: self.ensure_targetable_raw(raw_pc, raw_index + 2)?,
        })
    }

    fn iter_loop(
        &self,
        raw_index: usize,
        _bindings_plus_one: usize,
    ) -> Result<IterLoopHelper, TransformError> {
        let raw_pc = raw_pc_at(self.raw, raw_index);
        let helper_index = raw_index + 1;
        let Some(helper_instr) = self.raw.common.instructions.get(helper_index) else {
            return Err(TransformError::MissingGenericForLoop { raw_pc });
        };
        let (helper_opcode, helper_operands, helper_extra) = helper_instr
            .luajit()
            .expect("luajit lowerer should only decode luajit instructions");
        if !matches!(
            helper_opcode,
            LuaJitOpcode::IterL | LuaJitOpcode::IIterL | LuaJitOpcode::JIterL
        ) {
            return Err(TransformError::InvalidGenericForLoop {
                raw_pc,
                helper_pc: helper_extra.pc,
                found: helper_opcode.label(),
            });
        }
        let (_a, d) = expect_ad(helper_extra.pc, helper_opcode, helper_operands)?;
        let body_target = self.jump_target(helper_extra.pc, helper_index, d)?;
        let exit_target = self.ensure_targetable_raw(raw_pc, raw_index + 2)?;
        Ok(IterLoopHelper {
            helper_index,
            body_target,
            exit_target,
        })
    }

    fn call_arg_start(&self, a: u8) -> Reg {
        Reg(usize::from(a) + 1 + self.fr2)
    }

    fn call_args_pack(&self, a: u8, c: u8) -> ValuePack {
        let start = self.call_arg_start(a);
        if c == 0 {
            ValuePack::Open(start)
        } else {
            ValuePack::Fixed(RegRange::new(start, usize::from(c.saturating_sub(1))))
        }
    }

    fn tail_call_args_pack(&self, a: u8, d: u16) -> ValuePack {
        let start = self.call_arg_start(a);
        if d == 0 {
            ValuePack::Open(start)
        } else {
            ValuePack::Fixed(RegRange::new(start, usize::from(d.saturating_sub(1))))
        }
    }

    fn table_literal_key(&self, literal: &LuaJitTableLiteral) -> AccessKey {
        match literal.value {
            RawLiteralConst::Integer(value) => AccessKey::Integer(value),
            _ => AccessKey::Const(ConstRef(literal.literal_index)),
        }
    }

    fn table_literal_value(&self, literal: &LuaJitTableLiteral) -> ValueOperand {
        ValueOperand::Const(ConstRef(literal.literal_index))
    }

    fn tsetm_start_index(&self, raw_pc: u32, knum_index: usize) -> Result<u32, TransformError> {
        let LuaJitNumberConstEntry::Number { value, .. } = self.knum_entry(raw_pc, knum_index)?
        else {
            return Err(TransformError::InvalidConstRef {
                raw_pc,
                const_index: knum_index,
                const_count: self.knum_entries().len(),
            });
        };
        let start = (*value - TWO_POW_52).round();
        if !(0.0..=(u32::MAX as f64)).contains(&start) {
            return Err(TransformError::InvalidConstRef {
                raw_pc,
                const_index: knum_index,
                const_count: self.knum_entries().len(),
            });
        }
        Ok(start as u32)
    }
}

#[derive(Debug, Clone, Copy)]
struct HelperJump {
    helper_index: usize,
    jump_target: usize,
    fallthrough_target: usize,
}

#[derive(Debug, Clone, Copy)]
struct IterLoopHelper {
    helper_index: usize,
    body_target: usize,
    exit_target: usize,
}

fn raw_pc_at(raw: &RawProto, index: usize) -> u32 {
    raw.common.instructions[index].pc()
}

fn opcode_at(raw: &RawProto, index: usize) -> LuaJitOpcode {
    raw.common.instructions[index]
        .luajit()
        .expect("luajit lowerer should only decode luajit instructions")
        .0
}

fn reg_from_u8(index: u8) -> Reg {
    Reg(index as usize)
}

fn reg_from_u16(index: u16) -> Reg {
    Reg(index as usize)
}

fn range_len_inclusive(start: usize, end: usize) -> usize {
    end.saturating_sub(start) + 1
}

fn call_results_pack(a: u8, b: u8) -> ResultPack {
    match b {
        0 => ResultPack::Open(reg_from_u8(a)),
        1 => ResultPack::Ignore,
        _ => ResultPack::Fixed(RegRange::new(reg_from_u8(a), usize::from(b - 1))),
    }
}

fn return_pack(a: u8, d: u16) -> ValuePack {
    if d == 0 {
        ValuePack::Open(reg_from_u8(a))
    } else {
        ValuePack::Fixed(RegRange::new(
            reg_from_u8(a),
            usize::from(d.saturating_sub(1)),
        ))
    }
}

fn pri_cond_operand(raw_pc: u32, d: u16) -> Result<CondOperand, TransformError> {
    match d {
        BCDUMP_KPRI_NIL => Ok(CondOperand::Nil),
        BCDUMP_KPRI_FALSE => Ok(CondOperand::Boolean(false)),
        BCDUMP_KPRI_TRUE => Ok(CondOperand::Boolean(true)),
        _ => Err(TransformError::UnsupportedOpcode {
            raw_pc,
            opcode: "KPRI",
        }),
    }
}

fn unary_op_kind(opcode: LuaJitOpcode) -> UnaryOpKind {
    match opcode {
        LuaJitOpcode::Not => UnaryOpKind::Not,
        LuaJitOpcode::Unm => UnaryOpKind::Neg,
        LuaJitOpcode::Len => UnaryOpKind::Length,
        _ => unreachable!("only unary luajit opcodes should reach unary_op_kind"),
    }
}

fn binary_op_kind(opcode: LuaJitOpcode) -> BinaryOpKind {
    match opcode {
        LuaJitOpcode::AddVN | LuaJitOpcode::AddNV | LuaJitOpcode::AddVV => BinaryOpKind::Add,
        LuaJitOpcode::SubVN | LuaJitOpcode::SubNV | LuaJitOpcode::SubVV => BinaryOpKind::Sub,
        LuaJitOpcode::MulVN | LuaJitOpcode::MulNV | LuaJitOpcode::MulVV => BinaryOpKind::Mul,
        LuaJitOpcode::DivVN | LuaJitOpcode::DivNV | LuaJitOpcode::DivVV => BinaryOpKind::Div,
        LuaJitOpcode::ModVN | LuaJitOpcode::ModNV | LuaJitOpcode::ModVV => BinaryOpKind::Mod,
        LuaJitOpcode::Pow => BinaryOpKind::Pow,
        _ => unreachable!("only binary luajit opcodes should reach binary_op_kind"),
    }
}

define_operand_expecters! {
    opcode = LuaJitOpcode,
    operands = LuaJitOperands,
    label = LuaJitOpcode::label,
    fn expect_ad("AD") -> (u8, u16) {
        LuaJitOperands::AD { a, d } => (*a, *d)
    }
    fn expect_abc("ABC") -> (u8, u8, u8) {
        LuaJitOperands::ABC { a, b, c } => (*a, *b, *c)
    }
}
