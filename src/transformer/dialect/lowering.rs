//! 这个模块承载各个 dialect lowerer 之间共享的 lowering 状态机。
//!
//! 这些类型只描述“raw 指令如何收集成 low-IR、如何回填 target、如何维护 method
//! hint / raw pc 索引”这类与具体 opcode 语义无关的稳定事实，不应该继续挂在某个
//! family 名下。收尾消费 pending 指令与来源映射，一次完成目标回填和公共投影；
//! 方言只提供诊断目标坐标与行号索引规则。

use crate::parser::{RawInstr, RawProto};
use crate::transformer::{
    BranchCond, BranchInstr, CallKind, ConstRef, GenericForLoopInstr, InstrRef, JumpInstr,
    LowInstr, LoweringMap, MethodNameHint, NumericForInitInstr, NumericForLoopInstr, RawInstrRef,
    Reg, RegRange, ResultPack, TransformError,
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
        control_target: Reg,
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

pub(crate) fn raw_pc_at(raw: &RawProto, index: usize) -> u32 {
    instr_pc(&raw.common.instructions[index])
}

pub(crate) fn next_raw_pc(raw: &RawProto, index: usize) -> u32 {
    let instr = &raw.common.instructions[index];
    instr_pc(instr) + u32::from(instr_word_len(instr))
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

    pub(crate) fn finish<RawIndexToTargetRaw, LineHintAtRaw>(
        self,
        raw: &RawProto,
        raw_index_to_target_raw: RawIndexToTargetRaw,
        line_hint_at_raw: LineHintAtRaw,
    ) -> Result<(Vec<LowInstr>, LoweringMap), TransformError>
    where
        RawIndexToTargetRaw: Fn(usize) -> usize,
        LineHintAtRaw: Fn(usize) -> Option<u32>,
    {
        let count = self.emitted.len();
        let mut instrs = Vec::with_capacity(count);
        let mut low_to_raw = Vec::with_capacity(count);
        let mut pc_map = Vec::with_capacity(count);
        let mut line_hints = Vec::with_capacity(count);
        for EmittedInstr { raw_indices, instr } in self.emitted {
            // 合并指令仍由首个原始来源承担诊断位置，与可选的跳转 owner 无关。
            let owner_raw = *raw_indices
                .first()
                .expect("emitted instruction has a raw origin");
            let owner_pc = raw.common.instructions[owner_raw].pc();
            instrs.push(resolve_pending_instr_with(instr, |target| {
                resolve_target_placeholder(
                    owner_pc,
                    target,
                    &self.raw_target_low,
                    &raw_index_to_target_raw,
                )
            })?);
            pc_map.push(
                raw_indices
                    .iter()
                    .map(|&index| raw.common.instructions[index].pc())
                    .collect(),
            );
            line_hints.push(
                raw_indices
                    .iter()
                    .find_map(|&index| line_hint_at_raw(index)),
            );
            low_to_raw.push(raw_indices.into_iter().map(RawInstrRef).collect());
        }

        Ok((
            instrs,
            LoweringMap::new(low_to_raw, self.raw_to_low, pc_map, line_hints),
        ))
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

    pub(crate) fn set(
        &mut self,
        callee: Reg,
        self_arg: Reg,
        method_name: Option<ConstRef>,
        live_from: Option<usize>,
    ) {
        set_pending_method_hint(&mut self.slots, callee, self_arg, method_name, live_from);
    }

    pub(crate) fn consume_call_info(
        &mut self,
        callee: Reg,
        first_arg: Reg,
        hint_allowed: bool,
        results: ResultPack,
    ) -> (CallKind, Option<MethodNameHint>) {
        let info = pending_call_info(&self.slots, callee, first_arg, hint_allowed);
        self.invalidate_reg(callee);
        self.invalidate_result_pack(results);
        info
    }

    pub(crate) fn invalidate_reg(&mut self, reg: Reg) {
        invalidate_pending_method_reg(&mut self.slots, reg);
    }

    pub(crate) fn invalidate_range(&mut self, range: RegRange) {
        invalidate_pending_method_range(&mut self.slots, range);
    }

    pub(crate) fn invalidate_result_pack(&mut self, results: ResultPack) {
        match results {
            ResultPack::Fixed(range) => self.invalidate_range(range),
            ResultPack::Open(start) => {
                for index in start.index()..self.slots.len() {
                    self.invalidate_reg(Reg(index));
                }
            }
            ResultPack::Ignore => {}
        }
    }

    pub(crate) fn clear(&mut self) {
        clear_pending_method_hints(&mut self.slots);
    }

    pub(crate) fn invalidate_bypassed_setups(
        &mut self,
        raw_index: usize,
        incoming_sources: JumpSourceEnvelope,
    ) {
        for pending in &mut self.slots {
            let Some(hint) = *pending else {
                continue;
            };
            if hint
                .live_from
                .is_some_and(|live_from| !incoming_sources.all_within(live_from, raw_index))
            {
                *pending = None;
            }
        }
    }
}

/// 入边查询只问“全部 source 是否落在某个连续区间”，因此保留两端即可精确回答，
/// 同时避免为每个 target 分配小 `Vec`。
#[derive(Debug, Clone, Copy)]
pub(crate) struct JumpSourceEnvelope {
    min: usize,
    max: usize,
}

impl JumpSourceEnvelope {
    pub(crate) const EMPTY: Self = Self {
        min: usize::MAX,
        max: 0,
    };

    pub(crate) fn include(&mut self, source: usize) {
        self.min = self.min.min(source);
        self.max = self.max.max(source);
    }

    pub(crate) fn all_within(self, start: usize, end: usize) -> bool {
        self.min == usize::MAX || (self.min >= start && self.max < end)
    }

    pub(crate) fn is_empty(self) -> bool {
        self.min == usize::MAX
    }
}

#[derive(Debug, Clone, Copy)]
struct PendingMethodHint {
    self_arg: Reg,
    method_name: Option<ConstRef>,
    live_from: Option<usize>,
}

#[derive(Debug, Clone)]
pub(crate) struct WordCodeIndex {
    raw_pc_to_index: Vec<Option<usize>>,
}

impl WordCodeIndex {
    pub(crate) fn from_raw(raw: &RawProto) -> Self {
        let raw_word_count = raw
            .common
            .instructions
            .iter()
            .map(|instr| (instr_pc(instr) + u32::from(instr_word_len(instr))) as usize)
            .max()
            .unwrap_or(0);

        let mut raw_pc_to_index = vec![None; raw_word_count];
        for (index, instr) in raw.common.instructions.iter().enumerate() {
            raw_pc_to_index[instr_pc(instr) as usize] = Some(index);
        }

        Self { raw_pc_to_index }
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
        if target_pc as usize >= self.raw_pc_to_index.len() {
            return Err(TransformError::InvalidJumpTarget {
                raw_pc,
                target_raw: target_pc as usize,
                instr_count: self.raw_pc_to_index.len(),
            });
        }

        self.raw_index_at_pc(target_pc)
            .ok_or(TransformError::UntargetableRawInstruction {
                raw_pc,
                target_raw: target_pc as usize,
            })
    }

    pub(crate) fn ensure_valid_jump_pc(
        &self,
        raw_pc: u32,
        target_pc: i64,
    ) -> Result<usize, TransformError> {
        if target_pc < 0 || target_pc >= self.raw_pc_to_index.len() as i64 {
            return Err(TransformError::InvalidJumpTarget {
                raw_pc,
                target_raw: target_pc.max(0) as usize,
                instr_count: self.raw_pc_to_index.len(),
            });
        }

        self.ensure_targetable_pc(raw_pc, target_pc as u32)
    }
}

fn resolve_pending_instr_with<F>(
    pending: PendingLowInstr,
    mut resolve_target: F,
) -> Result<LowInstr, TransformError>
where
    F: FnMut(TargetPlaceholder) -> Result<InstrRef, TransformError>,
{
    match pending {
        PendingLowInstr::Ready(instr) => Ok(instr),
        PendingLowInstr::Jump { target } => Ok(LowInstr::Jump(JumpInstr {
            target: resolve_target(target)?,
        })),
        PendingLowInstr::Branch {
            cond,
            then_target,
            else_target,
        } => Ok(LowInstr::Branch(BranchInstr {
            cond,
            then_target: resolve_target(then_target)?,
            else_target: resolve_target(else_target)?,
        })),
        PendingLowInstr::NumericForInit {
            index,
            limit,
            step,
            binding,
            body_target,
            exit_target,
        } => Ok(LowInstr::NumericForInit(NumericForInitInstr {
            index,
            limit,
            step,
            binding,
            body_target: resolve_target(body_target)?,
            exit_target: resolve_target(exit_target)?,
        })),
        PendingLowInstr::NumericForLoop {
            index,
            limit,
            step,
            binding,
            body_target,
            exit_target,
        } => Ok(LowInstr::NumericForLoop(NumericForLoopInstr {
            index,
            limit,
            step,
            binding,
            body_target: resolve_target(body_target)?,
            exit_target: resolve_target(exit_target)?,
        })),
        PendingLowInstr::GenericForLoop {
            control_target,
            bindings,
            body_target,
            exit_target,
        } => Ok(LowInstr::GenericForLoop(GenericForLoopInstr {
            control_target,
            bindings,
            body_target: resolve_target(body_target)?,
            exit_target: resolve_target(exit_target)?,
        })),
    }
}

fn resolve_target_placeholder<F>(
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
fn set_pending_method_hint(
    pending_methods: &mut [Option<PendingMethodHint>],
    callee: Reg,
    self_arg: Reg,
    method_name: Option<ConstRef>,
    live_from: Option<usize>,
) {
    if callee.index() < pending_methods.len() {
        pending_methods[callee.index()] = Some(PendingMethodHint {
            self_arg,
            method_name,
            live_from,
        });
    }
}

fn pending_call_info(
    pending_methods: &[Option<PendingMethodHint>],
    callee: Reg,
    first_arg: Reg,
    hint_allowed: bool,
) -> (CallKind, Option<MethodNameHint>) {
    if !hint_allowed {
        return (CallKind::Normal, None);
    }

    match pending_methods.get(callee.index()).and_then(|value| *value) {
        Some(hint) if hint.self_arg == first_arg => (
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
