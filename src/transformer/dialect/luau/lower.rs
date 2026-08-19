//! 这个文件实现 Luau bytecode 到统一 low-IR 的 lowering。
//!
//! Luau 的 parser 已经把“多字指令 / AUX / capture helper / 平铺 proto”这些字节级细节
//! 折进 raw 层了；这里专注做语义恢复，把它翻成项目里既有的 CFG/HIR/AST 管线能理解
//! 的稳定 low-IR 契约。

use crate::parser::{
    LuauCaptureKind, LuauConstEntry, LuauInstrExtra, LuauOpcode, LuauOperands, RawChunk,
    RawLiteralConst, RawProto,
};
use crate::transformer::dialect::lowering::{
    PendingLowInstr, PendingLoweringState, PendingMethodHints, TargetPlaceholder, WordCodeIndex,
    instr_pc, instr_word_len, resolve_pending_instr_with,
};
use crate::transformer::dialect::puc_lua::{
    call_args_pack, call_result_pack, finish_lowered_proto, range_len_inclusive, reg_from_u8,
    return_pack,
};
use crate::transformer::operands::define_operand_expecters;
use crate::transformer::{
    AccessBase, AccessKey, BinaryOpInstr, BinaryOpKind, BranchCond, BranchPredicate, CallInstr,
    CallKind, Capture, CaptureSource, CloseInstr, ClosureCreation, ClosureInstr, ConcatInstr,
    CondOperand, ConstRef, FastCallArgs, GenericForCallInstr, GetTableInstr, GetTableKind,
    GetUpvalueInstr, InstrRef, LoadBoolInstr, LoadConstInstr, LoadIntegerInstr, LoadNilInstr,
    LowInstr, LoweredChunk, LoweredProto, LoweringMap, MoveInstr, NewTableInstr, ProtoRef, Reg,
    RegRange, ResultPack, ReturnInstr, SetListInstr, SetTableInstr, SetTableKind, SetUpvalueInstr,
    SharedClosureRef, TransformError, UnaryOpInstr, UnaryOpKind, UpvalueRef, ValueOperand,
    ValuePack, VarArgInstr, instantiate_closure_children,
};

mod fastcall;
mod opcode;

pub(crate) fn lower_chunk(chunk: &RawChunk) -> Result<LoweredChunk, TransformError> {
    Ok(LoweredChunk {
        header: chunk.header.clone(),
        main: lower_proto(&chunk.main)?,
        origin: chunk.origin,
    })
}

fn lower_proto(raw: &RawProto) -> Result<LoweredProto, TransformError> {
    let child_templates = raw
        .common
        .children
        .iter()
        .map(lower_proto)
        .collect::<Result<Vec<_>, _>>()?;
    let mut lowerer = ProtoLowerer::new(raw);
    let (mut instrs, lowering_map) = lowerer.lower()?;
    let children = instantiate_closure_children(&mut instrs, child_templates);

    Ok(finish_lowered_proto(raw, children, instrs, lowering_map))
}

struct ProtoLowerer<'a> {
    raw: &'a RawProto,
    lowering: PendingLoweringState,
    pending_methods: PendingMethodHints,
    pending_fastcall_calls: Vec<Option<PendingFastCall>>,
    word_code_index: WordCodeIndex,
}

#[derive(Debug, Clone, Copy)]
enum LogicalSelectValue {
    Reg(Reg),
    Const(ConstRef),
}

#[derive(Debug, Clone, Copy)]
enum PendingFastCall {
    All,
    Fixed { sources: [Option<Reg>; 3], len: u8 },
}

impl PendingFastCall {
    fn freeze(self, callee: Reg, args: ValuePack) -> Option<FastCallArgs> {
        match self {
            Self::All => Some(FastCallArgs::All),
            Self::Fixed { sources, len } => {
                let (start, direct_tail) = match args {
                    ValuePack::Fixed(range) if range.len == usize::from(len) => {
                        (range.start, false)
                    }
                    // `select(k, ...)` 等 fixed FASTCALL 保留已编码前缀，开放尾由 fast path 直接读取、fallback 才在 CALL 前物化。
                    ValuePack::Open(start) => (start, true),
                    ValuePack::Fixed(_) => return None,
                };
                if start != Reg(callee.index() + 1) {
                    return None;
                }
                let mut direct_fixed = 0_u8;
                for (index, source) in sources[..usize::from(len)].iter().enumerate() {
                    let target = Reg(start.index() + index);
                    if source.is_none_or(|source| source == target) {
                        direct_fixed |= 1 << index;
                    }
                }
                Some(FastCallArgs::Mask {
                    direct_fixed,
                    direct_tail,
                })
            }
        }
    }
}

impl<'a> ProtoLowerer<'a> {
    fn new(raw: &'a RawProto) -> Self {
        let raw_instr_count = raw.common.instructions.len();
        let method_slots = usize::from(raw.common.frame.max_stack_size).saturating_add(2);

        Self {
            raw,
            lowering: PendingLoweringState::new(raw_instr_count),
            pending_methods: PendingMethodHints::new(method_slots),
            pending_fastcall_calls: vec![None; raw_instr_count],
            word_code_index: WordCodeIndex::from_raw(raw, instr_pc, instr_word_len),
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
        self.lowering.resolve_target(owner_pc, target, |raw_index| {
            raw_pc_at(self.raw, raw_index) as usize
        })
    }

    fn emit(
        &mut self,
        owner_raw: Option<usize>,
        raw_indices: Vec<usize>,
        instr: PendingLowInstr,
    ) -> usize {
        self.lowering.emit(owner_raw, raw_indices, instr)
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
        self.raw
            .common
            .constants
            .luau_entries()
            .expect("luau lowerer should only receive luau constant pools")
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
        let LuauConstEntry::Closure {
            child_proto_index, ..
        } = self.const_entry(raw_pc, const_index)?
        else {
            return Err(TransformError::InvalidConstRef {
                raw_pc,
                const_index,
                const_count: self.const_entries().len(),
            });
        };
        self.proto_ref(raw_pc, *child_proto_index)
    }

    fn import_path(
        &self,
        raw_pc: u32,
        extra: LuauInstrExtra,
    ) -> Result<Vec<ConstRef>, TransformError> {
        let aux = required_aux(raw_pc, LuauOpcode::GetImport, extra)?;
        let count = (aux >> 30) as usize;
        if count == 0 {
            return Err(TransformError::UnexpectedOperands {
                raw_pc,
                opcode: LuauOpcode::GetImport.label(),
                expected: "AUX import path length in 1..=3",
            });
        }
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
            let (capture_opcode, capture_operands, capture_extra) = raw_capture_instr
                .luau()
                .expect("luau lowerer should only decode luau instructions");
            raw_indices.push(capture_raw);
            if capture_opcode != LuauOpcode::Capture {
                return Err(TransformError::InvalidClosureCapture {
                    raw_pc,
                    capture_pc: capture_extra.pc,
                    found: capture_opcode.label(),
                });
            }

            let (kind_raw, source_raw) =
                expect_ab(capture_extra.pc, capture_opcode, capture_operands)?;
            let kind = LuauCaptureKind::try_from(kind_raw).map_err(|_| {
                TransformError::InvalidClosureCapture {
                    raw_pc,
                    capture_pc: capture_extra.pc,
                    found: capture_opcode.label(),
                }
            })?;
            let source = match kind {
                LuauCaptureKind::Val => CaptureSource::ByValue(reg_from_u8(source_raw)),
                LuauCaptureKind::Ref => CaptureSource::ByReference(reg_from_u8(source_raw)),
                LuauCaptureKind::Upvalue => {
                    CaptureSource::Upvalue(self.upvalue_ref(capture_extra.pc, source_raw as usize)?)
                }
            };
            captures.push(Capture { source });
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
        self.word_code_index.ensure_valid_jump_pc(raw_pc, target_pc)
    }

    fn record_fastcall_target(
        &mut self,
        raw_pc: u32,
        opcode: LuauOpcode,
        skip: u8,
        fastcall: PendingFastCall,
    ) -> Result<(), TransformError> {
        // C 指向 fallback CALL（pc + 1 + C）；fast path 成功后跳到下一条，但协议 owner 仍是该 CALL。
        let call_raw = self.jump_target(raw_pc, i32::from(skip))?;
        let (target_opcode, _, _) = self.raw.common.instructions[call_raw]
            .luau()
            .expect("luau lowerer should only decode luau instructions");
        if target_opcode != LuauOpcode::Call || self.pending_fastcall_calls[call_raw].is_some() {
            return Err(TransformError::UnexpectedOperands {
                raw_pc,
                opcode: opcode.label(),
                expected: "C must uniquely target CALL",
            });
        }
        self.pending_fastcall_calls[call_raw] = Some(fastcall);
        Ok(())
    }

    fn ensure_targetable_pc(&self, raw_pc: u32, target_pc: u32) -> Result<usize, TransformError> {
        self.word_code_index.ensure_targetable_pc(raw_pc, target_pc)
    }

    fn next_raw_pc(&self, raw_index: usize) -> u32 {
        let instr = &self.raw.common.instructions[raw_index];
        instr.pc() + u32::from(instr_word_len(instr))
    }

    fn set_pending_method(
        &mut self,
        callee: Reg,
        self_arg: Reg,
        method_name: Option<crate::transformer::ConstRef>,
    ) {
        self.pending_methods
            .set(callee, self_arg, method_name, None);
    }

    fn take_call_info(
        &mut self,
        callee: Reg,
        raw_b: u16,
        results: ResultPack,
    ) -> (CallKind, Option<crate::transformer::MethodNameHint>) {
        self.pending_methods
            .consume_call_info(callee, Reg(callee.index() + 1), raw_b != 1, results)
    }

    fn invalidate_written_reg(&mut self, reg: Reg) {
        self.pending_methods.invalidate_reg(reg);
    }

    fn invalidate_written_range(&mut self, range: RegRange) {
        self.pending_methods.invalidate_range(range);
    }

    fn invalidate_vararg_results(&mut self, a: u8, b: u8) {
        match call_result_pack(a, u16::from(b)) {
            ResultPack::Fixed(range) => self.invalidate_written_range(range),
            ResultPack::Open(reg) => self.invalidate_written_reg(reg),
            ResultPack::Ignore => {}
        }
    }

    fn clear_all_method_hints(&mut self) {
        self.pending_methods.clear();
    }

    fn emit_logical_select(
        &mut self,
        raw_index: usize,
        condition: Reg,
        dst: Reg,
        truthy_value: LogicalSelectValue,
        falsy_value: LogicalSelectValue,
    ) {
        let branch_low = self.lowering.next_low_index() - 1;
        let truthy_low = branch_low + 1;
        let jump_low = branch_low + 2;
        let falsy_low = branch_low + 3;
        let after_low = branch_low + 4;

        self.emit(
            Some(raw_index),
            vec![raw_index],
            PendingLowInstr::Branch {
                cond: BranchCond::truthy(CondOperand::Reg(condition), false),
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
                            kind: SetTableKind::Normal,
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

fn raw_pc_at(raw: &RawProto, index: usize) -> u32 {
    raw.common.instructions[index].pc()
}

fn required_aux(
    raw_pc: u32,
    opcode: LuauOpcode,
    extra: LuauInstrExtra,
) -> Result<u32, TransformError> {
    extra.aux.ok_or(TransformError::MissingExtraArg {
        raw_pc,
        opcode: opcode.label(),
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
        opcode: opcode.label(),
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

define_operand_expecters! {
    opcode = LuauOpcode,
    operands = LuauOperands,
    label = LuauOpcode::label,
    fn expect_a("A") -> u8 {
        LuauOperands::A { a } => *a
    }
    fn expect_ab("AB") -> (u8, u8) {
        LuauOperands::AB { a, b } => (*a, *b)
    }
    fn expect_abc("ABC") -> (u8, u8, u8) {
        LuauOperands::ABC { a, b, c } => (*a, *b, *c)
    }
    fn expect_ac("AC") -> (u8, u8) {
        LuauOperands::AC { a, c } => (*a, *c)
    }
    fn expect_ad("AD") -> (u8, i16) {
        LuauOperands::AD { a, d } => (*a, *d)
    }
    fn expect_e("E") -> i32 {
        LuauOperands::E { e } => *e
    }
}
