//! 按 Luau 的冲突寄存器协议证明单次调用与普通 local RHS 的并行赋值。
//! 先模拟冲突槽分配、逐项求值及末尾写回，再与原 MOVE/CALL 顺序精确对照。

use super::*;

pub(super) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed: &[TempId],
    phis: &[TempId],
    index: usize,
) -> Option<ParallelFrame> {
    let LowInstr::Call(call) = proto.instrs[index] else {
        return None;
    };
    if !matches!(call.args, crate::transformer::ValuePack::Fixed(args) if args.len == 0) {
        return None;
    }
    let block = cfg.instr_to_block[index];
    let mut start = index;
    while start > 0
        && cfg.instr_to_block[start - 1] == block
        && matches!(proto.instrs[start - 1], LowInstr::Move(_))
    {
        start -= 1;
    }
    let mut end = index + 1;
    while matches!(proto.instrs.get(end), Some(LowInstr::Move(_)))
        && cfg.instr_to_block[end] == block
    {
        end += 1;
    }
    let LowInstr::Move(callee) = *proto.instrs.get(index.checked_sub(1)?)? else {
        return None;
    };
    let LowInstr::Move(result_copy) = *proto.instrs.get(index + 1)? else {
        return None;
    };
    if start == index || callee.dst != call.callee || result_copy.src != call.callee {
        return None;
    }
    let result = dataflow.instr_def_for_reg(InstrRef(index), call.callee)?;
    let copied = dataflow.instr_def_for_reg(InstrRef(index + 1), result_copy.dst)?;
    let forwarded = dataflow.def_uses[copied.index()]
        .iter()
        .any(|use_| use_.instr.index() < end);
    let base = if forwarded {
        result_copy.dst.index()
    } else {
        call.callee.index()
    };
    if callee.src.index() >= base || base > call.callee.index() {
        return None;
    }
    let canonical = |value| canonical_value_temp(value, dataflow.defs.len(), fixed, phis);
    let mut leading = Vec::new();
    let mut tail = Vec::new();
    let mut targets = BTreeMap::new();
    let mut originals = Vec::new();
    for position in start..end {
        if position == index {
            originals.push(None);
            continue;
        }
        let LowInstr::Move(copy) = proto.instrs[position] else {
            return None;
        };
        let at = InstrRef(position);
        let def = dataflow.instr_def_for_reg(at, copy.dst)?;
        if [copy.src, copy.dst].iter().any(|&reg| {
            epochs.reference_capture_may_be_open(reg, at)
                || epochs.epoch_at(reg, at) != epochs.epoch_at(reg, InstrRef(start))
        }) {
            return None;
        }
        let write = ParallelWrite {
            target: fixed[def.index()],
            source: canonical(dataflow.use_value(at, copy.src))?,
            home: HomeSlotKey::new(copy.dst.index(), epochs.epoch_at(copy.dst, at)),
        };
        originals.push(Some((copy.dst.index(), copy.src.index())));
        if copy.dst.index() < base && targets.insert(copy.dst.index(), (write, def)).is_some() {
            return None;
        }
        if position < index {
            leading.push(write);
        } else {
            tail.push(write);
        }
    }
    if targets.len() < 2 || targets.contains_key(&callee.src.index()) {
        return None;
    }
    let mut inputs = Vec::new();
    let mut source_regs = Vec::new();
    let mut previous = Vec::new();
    let mut calls = 0;
    for &(write, def) in targets.values() {
        previous.push(canonical(dataflow.def_overwritten_value(def)?)?);
        let mut value = dataflow.use_value(
            dataflow.def_instr(def),
            match proto.instrs[dataflow.def_instr(def).index()] {
                LowInstr::Move(copy) => copy.src,
                _ => return None,
            },
        );
        let mut through_copy = false;
        loop {
            let SsaValue::Def(input) = value else {
                return None;
            };
            if input == result {
                inputs.push(None);
                source_regs.push(None);
                calls += 1;
                break;
            }
            let reg = dataflow.def_reg(input);
            if reg.index() < base {
                inputs.push(Some(canonical(value)?));
                source_regs.push(Some(reg.index()));
                break;
            }
            // 每项 RHS 至多经一个冲突/结果 MOVE 到达低槽；更长链不是本协议。
            if through_copy {
                return None;
            }
            through_copy = true;
            let site = dataflow.def_instr(input);
            let LowInstr::Move(copy) = proto.instrs[site.index()] else {
                return None;
            };
            if site.index() < start || site.index() >= end {
                return None;
            }
            value = dataflow.use_value(site, copy.src);
        }
        if write.home.slot() >= base {
            return None;
        }
    }
    if calls != 1 {
        return None;
    }
    let mut assigned = BTreeSet::new();
    let mut conflicts = BTreeSet::new();
    for (&target, source) in targets.keys().zip(&source_regs) {
        if let Some(source) = source
            && assigned.contains(source)
        {
            conflicts.insert(*source);
        }
        assigned.insert(target);
    }
    let scratch = conflicts
        .iter()
        .enumerate()
        .map(|(offset, &target)| (target, base + offset))
        .collect::<BTreeMap<_, _>>();
    let call_slot = base + scratch.len();
    if call_slot != call.callee.index() {
        return None;
    }
    let mut expected = Vec::new();
    let emit_move = |steps: &mut Vec<_>, target, source| {
        if target != source {
            steps.push(Some((target, source)));
        }
    };
    for (&target, source) in targets.keys().zip(source_regs) {
        let destination = scratch.get(&target).copied().unwrap_or(target);
        if let Some(source) = source {
            emit_move(&mut expected, destination, source);
        } else {
            emit_move(&mut expected, call_slot, callee.src.index());
            expected.push(None);
            emit_move(&mut expected, destination, call_slot);
        }
    }
    for (&target, &source) in &scratch {
        emit_move(&mut expected, target, source);
    }
    if expected != originals {
        return None;
    }
    Some(ParallelFrame {
        base: HomeSlotKey::new(base, epochs.epoch_at(Reg(base), InstrRef(start))),
        preparation_count: index - start,
        tail,
        writes: targets.values().rev().map(|(write, _)| *write).collect(),
        previous,
        luau: Some(LuauParallel { leading, inputs }),
    })
}
