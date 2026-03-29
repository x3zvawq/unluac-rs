//! 这个模块承载各个 dialect lowerer 之间共享的 lowering 状态机。
//!
//! 这些类型只描述“raw 指令如何收集成 low-IR、如何回填 target、如何维护 method
//! hint / raw pc 索引”这类与具体 opcode 语义无关的稳定事实，不应该继续挂在某个
//! family 名下。

use crate::parser::{RawInstr, RawProto};
use crate::transformer::{
    BranchCond, BranchInstr, CallKind, ConstRef, GenericForLoopInstr, InstrRef, JumpInstr,
    LowInstr, LoweringMap, MethodNameHint, NumericForInitInstr, NumericForLoopInstr, RawInstrRef,
    Reg, RegRange, TransformError,
};

#[derive(Debug, Clone)]
pub(crate) struct EmittedInstr {
    pub(crate) raw_indices: Vec<usize>,
    pub(crate) instr: PendingLowInstr,
}

#[derive(Debug, Clone)]
pub(crate) enum PendingLowInstr {
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
pub(crate) enum TargetPlaceholder {
    Raw(usize),
    Low(usize),
}

pub(crate) fn instr_pc(raw: &RawInstr) -> u32 {
    raw.pc()
}

pub(crate) fn instr_word_len(raw: &RawInstr) -> u8 {
    raw.word_len()
        .expect("shared lowering word_len should only be used for word-len-bearing dialects")
}

#[derive(Debug, Clone)]
pub(crate) struct PendingLoweringState {
    emitted: Vec<EmittedInstr>,
    raw_target_low: Vec<Option<usize>>,
    raw_to_low: Vec<Vec<InstrRef>>,
}

impl PendingLoweringState {
    pub(crate) fn new(raw_instr_count: usize) -> Self {
        Self {
            emitted: Vec::new(),
            raw_target_low: vec![None; raw_instr_count],
            raw_to_low: vec![Vec::new(); raw_instr_count],
        }
    }

    pub(crate) fn next_low_index(&self) -> usize {
        self.emitted.len() + 1
    }

    pub(crate) fn finish<ResolvePending, RawPcAt, LineHintAtRaw>(
        &self,
        raw: &RawProto,
        mut resolve_pending: ResolvePending,
        raw_pc_at: RawPcAt,
        line_hint_at_raw: LineHintAtRaw,
    ) -> Result<(Vec<LowInstr>, LoweringMap), TransformError>
    where
        ResolvePending: FnMut(usize, &PendingLowInstr) -> Result<LowInstr, TransformError>,
        RawPcAt: Fn(&RawInstr) -> u32,
        LineHintAtRaw: Fn(usize) -> Option<u32>,
    {
        let instrs = self
            .emitted
            .iter()
            .map(|emitted| {
                let owner_raw = emitted.raw_indices.first().copied().unwrap_or(0);
                resolve_pending(owner_raw, &emitted.instr)
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
                    .map(|index| raw_pc_at(&raw.common.instructions[index]))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let line_hints = self
            .emitted
            .iter()
            .map(|emitted| {
                emitted
                    .raw_indices
                    .iter()
                    .find_map(|raw_index| line_hint_at_raw(*raw_index))
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

    pub(crate) fn resolve_target<F>(
        &self,
        owner_pc: u32,
        target: TargetPlaceholder,
        raw_index_to_target_raw: F,
    ) -> Result<InstrRef, TransformError>
    where
        F: FnOnce(usize) -> usize,
    {
        resolve_target_placeholder(
            owner_pc,
            target,
            &self.raw_target_low,
            raw_index_to_target_raw,
        )
    }

    pub(crate) fn emit(
        &mut self,
        owner_raw: Option<usize>,
        raw_indices: Vec<usize>,
        instr: PendingLowInstr,
    ) -> usize {
        emit_pending_instr(
            &mut self.emitted,
            &mut self.raw_target_low,
            &mut self.raw_to_low,
            owner_raw,
            raw_indices,
            instr,
        )
    }

    pub(crate) fn mark_raw_target(&mut self, raw_index: usize) {
        if self.raw_target_low[raw_index].is_none() {
            self.raw_target_low[raw_index] = Some(self.emitted.len());
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct PendingMethodHints {
    slots: Vec<Option<PendingMethodHint>>,
}

impl PendingMethodHints {
    pub(crate) fn new(slot_count: usize) -> Self {
        Self {
            slots: vec![None; slot_count],
        }
    }

    pub(crate) fn set(&mut self, callee: Reg, self_arg: Reg, method_name: Option<ConstRef>) {
        set_pending_method_hint(&mut self.slots, callee, self_arg, method_name);
    }

    pub(crate) fn call_info(&self, callee: Reg, raw_b: u16) -> (CallKind, Option<MethodNameHint>) {
        self.call_info_if(callee, raw_b != 1)
    }

    pub(crate) fn call_info_if(
        &self,
        callee: Reg,
        hint_allowed: bool,
    ) -> (CallKind, Option<MethodNameHint>) {
        pending_call_info(&self.slots, callee, hint_allowed)
    }

    pub(crate) fn invalidate_reg(&mut self, reg: Reg) {
        invalidate_pending_method_reg(&mut self.slots, reg);
    }

    pub(crate) fn invalidate_range(&mut self, range: RegRange) {
        invalidate_pending_method_range(&mut self.slots, range);
    }

    pub(crate) fn clear(&mut self) {
        clear_pending_method_hints(&mut self.slots);
    }
}

#[derive(Debug, Clone, Copy)]
struct PendingMethodHint {
    self_arg: Reg,
    method_name: Option<ConstRef>,
}

#[derive(Debug, Clone)]
pub(crate) struct WordCodeIndex {
    raw_pc_to_index: Vec<Option<usize>>,
    raw_word_count: usize,
}

impl WordCodeIndex {
    pub(crate) fn from_raw<RawPcAt, WordLen>(
        raw: &RawProto,
        raw_pc_at: RawPcAt,
        word_len: WordLen,
    ) -> Self
    where
        RawPcAt: Fn(&RawInstr) -> u32,
        WordLen: Fn(&RawInstr) -> u8,
    {
        let mut raw_word_count = 0_usize;

        let raw_pcs = raw
            .common
            .instructions
            .iter()
            .enumerate()
            .map(|(index, instr)| {
                let pc = raw_pc_at(instr);
                raw_word_count = raw_word_count.max((pc + u32::from(word_len(instr))) as usize);
                (pc, index)
            })
            .collect::<Vec<_>>();

        let mut raw_pc_to_index = vec![None; raw_word_count];
        for (pc, index) in raw_pcs {
            raw_pc_to_index[pc as usize] = Some(index);
        }

        Self {
            raw_pc_to_index,
            raw_word_count,
        }
    }

    pub(crate) fn raw_index_at_pc(&self, target_pc: u32) -> Option<usize> {
        self.raw_pc_to_index
            .get(target_pc as usize)
            .copied()
            .flatten()
    }

    pub(crate) fn ensure_targetable_pc(
        &self,
        raw_pc: u32,
        target_pc: u32,
    ) -> Result<usize, TransformError> {
        ensure_targetable_pc(
            raw_pc,
            target_pc,
            self.raw_word_count,
            &self.raw_pc_to_index,
        )
    }

    pub(crate) fn ensure_valid_jump_pc(
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
}

pub(crate) fn resolve_pending_instr_with<F>(
    pending: &PendingLowInstr,
    mut resolve_target: F,
) -> Result<LowInstr, TransformError>
where
    F: FnMut(TargetPlaceholder) -> Result<InstrRef, TransformError>,
{
    match pending {
        PendingLowInstr::Ready(instr) => Ok(instr.clone()),
        PendingLowInstr::Jump { target } => Ok(LowInstr::Jump(JumpInstr {
            target: resolve_target(*target)?,
        })),
        PendingLowInstr::Branch {
            cond,
            then_target,
            else_target,
        } => Ok(LowInstr::Branch(BranchInstr {
            cond: *cond,
            then_target: resolve_target(*then_target)?,
            else_target: resolve_target(*else_target)?,
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
            body_target: resolve_target(*body_target)?,
            exit_target: resolve_target(*exit_target)?,
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
            body_target: resolve_target(*body_target)?,
            exit_target: resolve_target(*exit_target)?,
        })),
        PendingLowInstr::GenericForLoop {
            control,
            bindings,
            body_target,
            exit_target,
        } => Ok(LowInstr::GenericForLoop(GenericForLoopInstr {
            control: *control,
            bindings: *bindings,
            body_target: resolve_target(*body_target)?,
            exit_target: resolve_target(*exit_target)?,
        })),
    }
}

pub(crate) fn resolve_target_placeholder<F>(
    owner_pc: u32,
    target: TargetPlaceholder,
    raw_target_low: &[Option<usize>],
    raw_index_to_target_raw: F,
) -> Result<InstrRef, TransformError>
where
    F: FnOnce(usize) -> usize,
{
    match target {
        TargetPlaceholder::Low(index) => Ok(InstrRef(index)),
        TargetPlaceholder::Raw(raw_index) => {
            let Some(low_index) = raw_target_low[raw_index] else {
                return Err(TransformError::UntargetableRawInstruction {
                    raw_pc: owner_pc,
                    target_raw: raw_index_to_target_raw(raw_index),
                });
            };
            Ok(InstrRef(low_index))
        }
    }
}

pub(crate) fn emit_pending_instr(
    emitted: &mut Vec<EmittedInstr>,
    raw_target_low: &mut [Option<usize>],
    raw_to_low: &mut [Vec<InstrRef>],
    owner_raw: Option<usize>,
    raw_indices: Vec<usize>,
    instr: PendingLowInstr,
) -> usize {
    let low_index = emitted.len();

    if let Some(owner_raw) = owner_raw
        && raw_target_low[owner_raw].is_none()
    {
        raw_target_low[owner_raw] = Some(low_index);
    }

    for raw_index in &raw_indices {
        raw_to_low[*raw_index].push(InstrRef(low_index));
    }

    emitted.push(EmittedInstr { raw_indices, instr });
    low_index
}

pub(crate) fn ensure_targetable_pc(
    raw_pc: u32,
    target_pc: u32,
    raw_word_count: usize,
    raw_pc_to_index: &[Option<usize>],
) -> Result<usize, TransformError> {
    if target_pc as usize >= raw_word_count {
        return Err(TransformError::InvalidJumpTarget {
            raw_pc,
            target_raw: target_pc as usize,
            instr_count: raw_word_count,
        });
    }

    raw_pc_to_index
        .get(target_pc as usize)
        .copied()
        .flatten()
        .ok_or(TransformError::UntargetableRawInstruction {
            raw_pc,
            target_raw: target_pc as usize,
        })
}

fn set_pending_method_hint(
    pending_methods: &mut [Option<PendingMethodHint>],
    callee: Reg,
    self_arg: Reg,
    method_name: Option<ConstRef>,
) {
    if callee.index() < pending_methods.len() {
        pending_methods[callee.index()] = Some(PendingMethodHint {
            self_arg,
            method_name,
        });
    }
}

fn pending_call_info(
    pending_methods: &[Option<PendingMethodHint>],
    callee: Reg,
    hint_allowed: bool,
) -> (CallKind, Option<MethodNameHint>) {
    if !hint_allowed {
        return (CallKind::Normal, None);
    }

    match pending_methods.get(callee.index()).and_then(|value| *value) {
        Some(hint) if hint.self_arg == Reg(callee.index() + 1) => (
            CallKind::Method,
            hint.method_name
                .map(|const_ref| MethodNameHint { const_ref }),
        ),
        _ => (CallKind::Normal, None),
    }
}

fn invalidate_pending_method_reg(pending_methods: &mut [Option<PendingMethodHint>], reg: Reg) {
    for (callee, pending) in pending_methods.iter_mut().enumerate() {
        let Some(hint) = *pending else {
            continue;
        };
        if callee == reg.index() || hint.self_arg.index() == reg.index() {
            *pending = None;
        }
    }
}

fn invalidate_pending_method_range(
    pending_methods: &mut [Option<PendingMethodHint>],
    range: RegRange,
) {
    for offset in 0..range.len {
        invalidate_pending_method_reg(pending_methods, Reg(range.start.index() + offset));
    }
}

fn clear_pending_method_hints(pending_methods: &mut [Option<PendingMethodHint>]) {
    pending_methods.fill(None);
}
