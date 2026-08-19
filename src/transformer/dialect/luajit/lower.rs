//! 这个文件实现 LuaJIT bytecode 到统一 low-IR 的 lowering。
//!
//! 第一阶段目标是把 LuaJIT 2.1 编出来的常见 opcode 子集稳定映射成现有 low-IR：
//! - calls/returns/vararg 用 LuaJIT 自己的 B/C 约定解释；
//! - compare/test + helper JMP 直接压成结构化 branch；
//! - LOOP/ILOOP 只当 targetable marker，JLOOP 这类 runtime patch opcode 直接拒绝；
//! - ISTYPE/ISNUM 保留内建 guard 与可能的原槽规范化，不猜普通 Lua helper；
//! - method setup 由 split `MOV + TGETS/TGETV` 协议还原，并在这里冻结 receiver snapshot；
//! - 写入和绕过 setup 的外部入边会使 method hint 失效，后层不再猜冒号调用；
//! - TDUP 在这里展开成 `NewTable + SetTable*`，不把模板表细节泄漏到后层。

use crate::parser::{
    LuaJitKgcEntry, LuaJitNumberConstEntry, LuaJitOpcode, LuaJitOperands, LuaJitTableConst,
    LuaJitTableLiteral, RawChunk, RawLiteralConst, RawProto,
};
use crate::transformer::dialect::lowering::{
    JumpSourceEnvelope, PendingLowInstr, PendingLoweringState, PendingMethodHints,
    TargetPlaceholder, instr_pc, resolve_pending_instr_with,
};
use crate::transformer::operands::define_operand_expecters;
use crate::transformer::{
    AccessBase, AccessKey, BinaryOpInstr, BinaryOpKind, BranchCond, BranchPredicate, CallInstr,
    Capture, CaptureSource, CloseInstr, ClosureInstr, ConcatInstr, CondOperand, ConstRef,
    GenericForCallInstr, GetTableInstr, GetTableKind, GetUpvalueInstr, InstrRef, LoadBoolInstr,
    LoadConstInstr, LoadIntegerInstr, LoadNilInstr, LowInstr, LoweredChunk, LoweredProto,
    LoweringMap, MoveInstr, NewTableInstr, ProtoRef, Reg, RegRange, ResultPack, ReturnInstr,
    SetListInstr, SetTableInstr, SetTableKind, SetUpvalueInstr, TailCallInstr, TransformError,
    TypeGuardInstr, TypeGuardKind, UnaryOpInstr, UnaryOpKind, UpvalueRef, ValueOperand, ValuePack,
    VarArgInstr, instantiate_closure_children,
};

mod opcode;

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
    let (mut instrs, lowering_map) = lowerer.lower()?;
    let children = instantiate_closure_children(&mut instrs, children);

    Ok(LoweredProto {
        source: raw.common.source.clone(),
        debug_name: None,
        line_range: raw.common.line_range,
        signature: raw.common.signature,
        frame: raw.common.frame,
        constants: raw.common.constants.clone(),
        upvalues: raw.common.upvalues.clone(),
        debug_info: raw.common.debug_info.clone(),
        debug_locals: crate::transformer::common::normalize_debug_locals(raw),
        children,
        instrs,
        lowering_map,
        origin: raw.origin,
    })
}

struct ProtoLowerer<'a> {
    raw: &'a RawProto,
    lowering: PendingLoweringState,
    pending_methods: PendingMethodHints,
    incoming_jump_sources: Vec<JumpSourceEnvelope>,
    fr2: usize,
}

impl<'a> ProtoLowerer<'a> {
    fn new(raw: &'a RawProto, fr2: bool) -> Self {
        let raw_instr_count = raw.common.instructions.len();
        let method_slots = usize::from(raw.common.frame.max_stack_size).saturating_add(2);
        Self {
            raw,
            lowering: PendingLoweringState::new(raw_instr_count),
            pending_methods: PendingMethodHints::new(method_slots),
            incoming_jump_sources: incoming_jump_sources(raw),
            fr2: usize::from(fr2),
        }
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
                let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                let lhs = CondOperand::Reg(reg_from_u8(a));
                let rhs = CondOperand::Reg(reg_from_u16(d));
                let (predicate, negated) = match opcode {
                    LuaJitOpcode::IsLt => (BranchPredicate::Lt, false),
                    LuaJitOpcode::IsGe => (BranchPredicate::Lt, true),
                    LuaJitOpcode::IsLe => (BranchPredicate::Le, false),
                    LuaJitOpcode::IsGt => (BranchPredicate::Le, true),
                    _ => unreachable!(),
                };
                Ok(BranchCond::compare(predicate, lhs, rhs, negated))
            }
            LuaJitOpcode::IsEqV | LuaJitOpcode::IsNeV => {
                let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                Ok(BranchCond::compare(
                    BranchPredicate::Eq,
                    CondOperand::Reg(reg_from_u8(a)),
                    CondOperand::Reg(reg_from_u16(d)),
                    matches!(opcode, LuaJitOpcode::IsNeV),
                ))
            }
            LuaJitOpcode::IsEqS | LuaJitOpcode::IsNeS => {
                let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                Ok(BranchCond::compare(
                    BranchPredicate::Eq,
                    CondOperand::Reg(reg_from_u8(a)),
                    CondOperand::Const(self.kgc_string_const_ref(raw_pc, usize::from(d))?),
                    matches!(opcode, LuaJitOpcode::IsNeS),
                ))
            }
            LuaJitOpcode::IsEqN | LuaJitOpcode::IsNeN => {
                let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                Ok(BranchCond::compare(
                    BranchPredicate::Eq,
                    CondOperand::Reg(reg_from_u8(a)),
                    self.knum_cond_operand(raw_pc, usize::from(d))?,
                    matches!(opcode, LuaJitOpcode::IsNeN),
                ))
            }
            LuaJitOpcode::IsEqP | LuaJitOpcode::IsNeP => {
                let (a, d) = expect_ad(raw_pc, opcode, operands)?;
                Ok(BranchCond::compare(
                    BranchPredicate::Eq,
                    CondOperand::Reg(reg_from_u8(a)),
                    pri_cond_operand(raw_pc, d)?,
                    matches!(opcode, LuaJitOpcode::IsNeP),
                ))
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
        if helper_opcode == LuaJitOpcode::JIterL {
            return Err(TransformError::UnsupportedOpcode {
                raw_pc: helper_extra.pc,
                opcode: helper_opcode.label(),
            });
        }
        if !matches!(helper_opcode, LuaJitOpcode::IterL | LuaJitOpcode::IIterL) {
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

    fn short_method_setup(
        &self,
        raw_index: usize,
        callee: u8,
        object: u8,
        method_name: ConstRef,
    ) -> Result<Option<MethodSetup>, TransformError> {
        let Some(move_index) = raw_index.checked_sub(1) else {
            return Ok(None);
        };
        let self_arg = self.call_arg_start(callee);
        if !self.raw_move_matches(move_index, self_arg, reg_from_u8(object))?
            || !self.setup_has_no_external_entry(move_index, raw_index)
        {
            return Ok(None);
        }
        Ok(Some(MethodSetup {
            self_arg,
            method_name,
        }))
    }

    fn large_method_setup(
        &self,
        raw_index: usize,
        callee: u8,
        object: u8,
        key: u8,
    ) -> Result<Option<MethodSetup>, TransformError> {
        let Some(move_index) = raw_index.checked_sub(2) else {
            return Ok(None);
        };
        let key_index = move_index + 1;
        let self_arg = self.call_arg_start(callee);
        let expected_key = Reg(usize::from(callee) + 2 + self.fr2);
        if reg_from_u8(key) != expected_key
            || reg_from_u8(object) == expected_key
            || !self.raw_move_matches(move_index, self_arg, reg_from_u8(object))?
            || !self.setup_has_no_external_entry(move_index, raw_index)
        {
            return Ok(None);
        }
        let (opcode, operands, extra) = self.raw.common.instructions[key_index]
            .luajit()
            .expect("luajit lowerer should only decode luajit instructions");
        if opcode != LuaJitOpcode::KStr {
            return Ok(None);
        }
        let (dst, constant) = expect_ad(extra.pc, opcode, operands)?;
        if reg_from_u8(dst) != expected_key {
            return Ok(None);
        }
        Ok(Some(MethodSetup {
            self_arg,
            method_name: self.kgc_string_const_ref(extra.pc, usize::from(constant))?,
        }))
    }

    fn raw_move_matches(
        &self,
        raw_index: usize,
        dst: Reg,
        src: Reg,
    ) -> Result<bool, TransformError> {
        let (opcode, operands, extra) = self.raw.common.instructions[raw_index]
            .luajit()
            .expect("luajit lowerer should only decode luajit instructions");
        if opcode != LuaJitOpcode::Mov {
            return Ok(false);
        }
        let (a, d) = expect_ad(extra.pc, opcode, operands)?;
        Ok(reg_from_u8(a) == dst && reg_from_u16(d) == src)
    }

    fn setup_has_no_external_entry(&self, setup_start: usize, end: usize) -> bool {
        (setup_start + 1..=end).all(|raw_index| self.incoming_jump_sources[raw_index].is_empty())
    }

    fn invalidate_written_reg(&mut self, reg: Reg) {
        self.pending_methods.invalidate_reg(reg);
    }

    fn invalidate_written_range(&mut self, range: RegRange) {
        self.pending_methods.invalidate_range(range);
    }

    fn invalidate_result_pack(&mut self, results: ResultPack) {
        self.pending_methods.invalidate_result_pack(results);
    }

    fn invalidate_bypassed_at(&mut self, raw_index: usize) {
        self.pending_methods
            .invalidate_bypassed_setups(raw_index, self.incoming_jump_sources[raw_index]);
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
struct MethodSetup {
    self_arg: Reg,
    method_name: ConstRef,
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

fn incoming_jump_sources(raw: &RawProto) -> Vec<JumpSourceEnvelope> {
    let mut incoming = vec![JumpSourceEnvelope::EMPTY; raw.common.instructions.len()];
    for (raw_index, instr) in raw.common.instructions.iter().enumerate() {
        let (opcode, operands, _) = instr
            .luajit()
            .expect("luajit lowerer should only decode luajit instructions");
        if !matches!(
            opcode,
            LuaJitOpcode::UClose
                | LuaJitOpcode::IsNext
                | LuaJitOpcode::ForI
                | LuaJitOpcode::JForI
                | LuaJitOpcode::ForL
                | LuaJitOpcode::IForL
                | LuaJitOpcode::IterL
                | LuaJitOpcode::IIterL
                | LuaJitOpcode::Jmp
        ) {
            continue;
        }
        let LuaJitOperands::AD { d, .. } = operands else {
            continue;
        };
        let target = raw_index as i64 + i64::from(*d) - BCBIAS_J_RAW;
        if (0..incoming.len() as i64).contains(&target) {
            incoming[target as usize].include(raw_index);
        }
    }
    incoming
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

fn lua_jit_type_guard_kind(
    raw_pc: u32,
    opcode: LuaJitOpcode,
    type_id: u16,
) -> Result<TypeGuardKind, TransformError> {
    let kind = match (opcode, type_id) {
        (LuaJitOpcode::IsType, 5) => TypeGuardKind::String,
        (LuaJitOpcode::IsType, 9) => TypeGuardKind::Function,
        (LuaJitOpcode::IsType, 12) => TypeGuardKind::Table,
        (LuaJitOpcode::IsType, 14) => TypeGuardKind::Integer,
        (LuaJitOpcode::IsNum, 15) => TypeGuardKind::Number,
        _ => return Err(TransformError::InvalidTypeGuard { raw_pc, type_id }),
    };
    Ok(kind)
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
