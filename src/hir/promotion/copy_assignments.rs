//! 保存并行赋值的原快照、目标版本和写回顺序。
//! 只提供同一基本块的原指令事实；源码声明前缀和后继槽复用由 simplify 核对。

use super::*;

pub(super) mod lookups;
mod luau;
pub(super) mod nil;
pub(super) mod varargs;

/// Luau 参数在整个 proto 中保持原值时，透明 MOVE 链可提供稳定的值身份。
/// 每一跳都排除引用捕获；仅检查链首参数会漏掉中间 cell 被回调改写的情况。
pub(super) fn collect_readonly_parameter_copies(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
) -> BTreeMap<TempId, ParamId> {
    // 开放结果只覆盖其起始槽及以上；高槽尾调用不会改写低槽形参。
    // MOVE 链仍逐 Def 查询，遇到开放值或 phi 时不发布只读身份。
    let open_floor = dataflow
        .open_defs
        .iter()
        .map(|def| def.start_reg.index())
        .min();
    let mut resolved = vec![None; dataflow.defs.len()];
    let mut path = Vec::new();
    for start in 0..dataflow.defs.len() {
        if resolved[start].is_some() {
            continue;
        }
        let mut value = SsaValue::Def(dataflow.defs[start].id);
        let param = loop {
            match value {
                SsaValue::Entry(reg) => {
                    break (reg.index() < usize::from(proto.signature.num_params)
                        && open_floor.is_none_or(|floor| reg.index() < floor)
                        && !dataflow.reg_is_reference_captured(reg)
                        && dataflow
                            .fixed_defs_by_reg
                            .get(reg.index())
                            .is_none_or(Vec::is_empty))
                    .then_some(ParamId(reg.index()));
                }
                SsaValue::Def(def) => {
                    if let Some(param) = resolved[def.index()] {
                        break param;
                    }
                    // 先标记未证明，遇到循环 MOVE 或无法归一的输入时保留拒绝。
                    resolved[def.index()] = Some(None);
                    path.push(def.index());
                    let site = dataflow.def_instr(def);
                    let LowInstr::Move(copy) = proto.instrs[site.index()] else {
                        break None;
                    };
                    if dataflow.reg_is_reference_captured(copy.src)
                        || dataflow.reg_is_reference_captured(copy.dst)
                    {
                        break None;
                    }
                    value = dataflow.use_value(site, copy.src);
                }
                _ => break None,
            }
        };
        for index in path.drain(..) {
            resolved[index] = Some(param);
        }
    }
    resolved
        .into_iter()
        .enumerate()
        .filter_map(|(index, param)| {
            let param = param.flatten()?;
            (param.index() < dataflow.defs[index].reg.index()).then_some((TempId(index), param))
        })
        .collect()
}

/// 首项在高槽准备字面量或旧值快照，再按原逆序写回两项目标。
#[derive(Debug, Clone)]
pub(in crate::hir) struct ScalarPairFrame {
    pub(in crate::hir) temps: [TempId; 3],
    pub(in crate::hir) homes: [HomeSlotKey; 3],
    pub(super) copied_input: Option<(TempId, HomeSlotKey)>,
    pub(in crate::hir) literal_input: Option<HirExpr>,
    pub(in crate::hir) tail: HirExpr,
    pub(super) copied_tail: Option<(TempId, HomeSlotKey)>,
}

/// 相邻 RHS 准备包含末项分配，完成后才逆序写回低槽；捕获 cell 的发布时点属于整个事务。
#[derive(Debug, Clone)]
pub(in crate::hir) struct AllocationPairFrame {
    pub(in crate::hir) sites: [InstrRef; 2],
    pub(in crate::hir) values: [TempId; 2],
    pub(in crate::hir) writes: [ParallelWrite; 2],
    pub(in crate::hir) homes: [HomeSlotKey; 2],
    pub(in crate::hir) literal_input: Option<HirExpr>,
    pub(in crate::hir) copied_input: Option<(TempId, HomeSlotKey)>,
}

pub(super) fn collect_allocation_pairs(
    proto: &LoweredProto,
    dialect: crate::decompile::DecompileDialect,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
) -> BTreeMap<InstrRef, AllocationPairFrame> {
    proto.instrs.windows(3).enumerate().filter_map(|(index, window)| {
        let [first, LowInstr::NewTable(second), third] = window else {
            return None;
        };
        let first_site = InstrRef(index);
        let (first_reg, literal_input, copied_input) = match first {
            LowInstr::NewTable(first) => (first.dst, None, None),
            LowInstr::Move(first) if first.src < first.dst
                && !epochs.reference_capture_may_be_open(first.src, first_site) => {
                let input = canonical_value_temp(dataflow.use_value(first_site, first.src),
                    dataflow.defs.len(), fixed_temps, phi_temps)?;
                (first.dst, None, Some((input,
                    HomeSlotKey::new(first.src.index(), epochs.epoch_at(first.src, first_site)))))
            }
            _ => {
                let (reg, value) = scalar_literal(proto, first)?;
                (reg, Some(value), None)
            }
        };
        let (left, right, end) = match (third, proto.instrs.get(index + 3)) {
            (LowInstr::Move(left), _) if dialect == crate::decompile::DecompileDialect::Luajit
                && second.dst.index() < first_reg.index() => (left, None, index + 2),
            (LowInstr::Move(right), Some(LowInstr::Move(left)))
                if second.dst.index() == first_reg.index() + 1 && right.src == second.dst =>
                (left, Some(right), index + 3),
            _ => return None,
        };
        let right_dst = right.map_or(second.dst, |copy| copy.dst);
        if left.src != first_reg || left.dst.index() >= first_reg.index()
            || right_dst.index() >= first_reg.index() || left.dst == right_dst
            || cfg.instr_to_block[index] != cfg.instr_to_block[end]
        {
            return None;
        }
        let sites = [InstrRef(index), InstrRef(index + 1)];
        let mut values = [TempId(0); 2];
        let mut homes = [HomeSlotKey::new(0, 0); 2];
        let mut writes = Vec::with_capacity(2);
        for (offset, (reg, copy)) in [(first_reg, Some(left)), (second.dst, right)].into_iter().enumerate() {
            let site = sites[offset];
            let def = dataflow.instr_def_for_reg(site, reg)?;
            values[offset] = TempId(def.index());
            homes[offset] = HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, site));
            let (target, home) = if let Some(copy) = copy {
                let write_site = InstrRef(end - offset);
                if epochs.reference_capture_may_be_open(reg, site)
                    || epochs.epoch_at(reg, site) != epochs.epoch_at(reg, write_site)
                    || dataflow.use_value(write_site, reg) != SsaValue::Def(def)
                    || !dataflow.def_phi_uses[def.index()].is_empty()
                    || !matches!(dataflow.def_uses[def.index()].as_slice(), [use_] if use_.instr == write_site)
                {
                    return None;
                }
                (TempId(dataflow.instr_def_for_reg(write_site, copy.dst)?.index()),
                    HomeSlotKey::new(copy.dst.index(), epochs.epoch_at(copy.dst, write_site)))
            } else {
                // JIT 末项直接分配到已有低槽；没有提前发布任何前项，也没有额外 COPY。
                (values[offset], homes[offset])
            };
            writes.push(ParallelWrite { target, source: values[offset], home });
        }
        Some((sites[1], AllocationPairFrame { sites, values, writes: writes.try_into().ok()?, homes, literal_input, copied_input }))
    }).collect()
}

pub(super) fn collect_scalar_pairs(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
) -> Vec<ScalarPairFrame> {
    proto.instrs.windows(3).enumerate().filter_map(|(index, window)| {
        let [first, second, LowInstr::Move(last)] = window else {
            return None;
        };
        let second_site = InstrRef(index + 1);
        let (mut second_reg, tail, copied_tail) = if let LowInstr::Move(copy) = second {
            if copy.src == last.src || epochs.reference_capture_may_be_open(copy.src, second_site) {
                return None;
            }
            let input = canonical_value_temp(dataflow.use_value(second_site, copy.src),
                dataflow.defs.len(), fixed_temps, phi_temps)?;
            (copy.dst, HirExpr::TempRef(input), Some((input,
                HomeSlotKey::new(copy.src.index(), epochs.epoch_at(copy.src, second_site)))))
        } else {
            let (reg, value) = scalar_literal(proto, second)?;
            (reg, value, None)
        };
        let first_site = InstrRef(index);
        let (snapshot_reg, copied_input, literal_input) = match first {
            LowInstr::Move(first) if first.src < first.dst
                && !epochs.reference_capture_may_be_open(first.src, first_site) => {
                let input = canonical_value_temp(dataflow.use_value(first_site, first.src),
                    dataflow.defs.len(), fixed_temps, phi_temps)?;
                (first.dst, Some((input, HomeSlotKey::new(first.src.index(), epochs.epoch_at(first.src, first_site)))), None)
            }
            _ => {
                let (reg, value) = scalar_literal(proto, first)?;
                (reg, None, Some(value))
            },
        };
        let mut last = last;
        let mut second_write = second_site;
        let mut last_site = InstrRef(index + 2);
        if second_reg.index() >= snapshot_reg.index() {
            let Some(LowInstr::Move(final_write)) = proto.instrs.get(index + 3) else { return None; };
            let literal = dataflow.instr_def_for_reg(second_site, second_reg)?;
            if copied_tail.is_some() || second_reg.index() != snapshot_reg.index() + 1
                || last.src != second_reg || last.dst.index() >= snapshot_reg.index()
                || dataflow.use_value(last_site, last.src) != SsaValue::Def(literal)
                || fixed_temps[literal.index()] != TempId(literal.index())
                || !dataflow.def_phi_uses[literal.index()].is_empty()
                || !matches!(dataflow.def_uses[literal.index()].as_slice(), [use_] if use_.instr == last_site)
                || epochs.reference_capture_may_be_open(second_reg, second_site)
                || epochs.epoch_at(second_reg, second_site) != epochs.epoch_at(second_reg, last_site)
            {
                // 候选拒绝[ProofIncomplete]：末项高槽必须是仅供当前低槽 COPY 消费的
                // 原字面量准备；额外读取、合流或捕获需要另一份完整写回证明。
                return None;
            }
            // 重复目标的末项先在高槽准备，再 COPY 回低槽；中间常量写不能因
            // 最终被快照覆盖而消失。HIR 可已把字面量收进这次 COPY，仍保留三个原写的身份。
            second_reg = last.dst;
            second_write = last_site;
            last_site = InstrRef(index + 3);
            last = final_write;
        }
        if last.src != snapshot_reg
            || last.dst.index() >= last.src.index()
            || second_reg.index() >= last.src.index()
            || cfg.instr_to_block[index] != cfg.instr_to_block[last_site.index()]
        {
            return None;
        }
        let regs = [snapshot_reg, second_reg, last.dst];
        let mut temps = [TempId(0); 3];
        let mut homes = [HomeSlotKey::new(0, 0); 3];
        for (offset, (reg, site)) in regs.into_iter().zip([first_site, second_write, last_site]).enumerate() {
            let def = dataflow.instr_def_for_reg(site, reg)?;
            // 只退休高槽快照；两个低槽仍按原逆序写回，捕获 cell 的发布时点不变。
            // 输入 COPY 已在各自读取处排除开放捕获，不能把该限制再套到写目标上。
            if fixed_temps[def.index()] != TempId(def.index())
                || offset == 0 && epochs.reference_capture_may_be_open(reg, site)
            {
                return None;
            }
            temps[offset] = TempId(def.index());
            homes[offset] = HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, site));
        }
        let first_def = dataflow.instr_def_for_reg(InstrRef(index), regs[0])?;
        if dataflow.use_value(last_site, last.src) != SsaValue::Def(first_def)
            || !dataflow.def_phi_uses[first_def.index()].is_empty()
            || !matches!(dataflow.def_uses[first_def.index()].as_slice(), [use_] if use_.instr == last_site)
            || epochs.epoch_at(last.src, last_site) != epochs.epoch_at(last.src, InstrRef(index))
        {
            return None;
        }
        Some(ScalarPairFrame { temps, homes, copied_input, literal_input, tail, copied_tail })
    }).collect()
}

fn scalar_literal(proto: &LoweredProto, instr: &LowInstr) -> Option<(Reg, HirExpr)> {
    match instr {
        LowInstr::LoadNil(load) if load.dst.len == 1 => Some((load.dst.start, HirExpr::Nil)),
        LowInstr::LoadBool(load) => Some((load.dst, HirExpr::Boolean(load.value))),
        LowInstr::LoadInteger(load) => Some((load.dst, HirExpr::Integer(load.value))),
        LowInstr::LoadNumber(load) => Some((load.dst, HirExpr::Number(load.value))),
        LowInstr::LoadConst(load) => {
            use crate::parser::RawLiteralConst;
            let value = match &proto.constants[load.value.index()] {
                RawLiteralConst::Integer(value) => HirExpr::Integer(*value),
                RawLiteralConst::Number(value) => HirExpr::Number(*value),
                RawLiteralConst::String(value) => {
                    HirExpr::String(crate::LuaString::from_raw(value))
                }
                _ => return None,
            };
            Some((load.dst, value))
        }
        _ => None,
    }
}

#[derive(Debug, Clone, Copy)]
pub(in crate::hir) struct ParallelWrite {
    pub(in crate::hir) target: TempId,
    pub(in crate::hir) source: TempId,
    pub(in crate::hir) home: HomeSlotKey,
}

/// 单次调用两侧的寄存器快照与连续低槽写回；不授权拆开提交其中某个结果。
#[derive(Debug, Clone)]
pub(in crate::hir) struct ParallelFrame {
    pub(in crate::hir) base: HomeSlotKey,
    pub(in crate::hir) preparation_count: usize,
    pub(in crate::hir) tail: Vec<ParallelWrite>,
    pub(in crate::hir) writes: Vec<ParallelWrite>,
    pub(in crate::hir) previous: Vec<TempId>,
    pub(in crate::hir) luau: Option<LuauParallel>,
}

impl ParallelFrame {
    pub(in crate::hir) fn moves(&self) -> impl Iterator<Item = &ParallelWrite> {
        self.luau
            .iter()
            .flat_map(|layout| layout.leading.iter())
            .chain(self.tail.iter())
    }
}

#[derive(Debug, Clone)]
pub(in crate::hir) struct LuauParallel {
    pub(in crate::hir) leading: Vec<ParallelWrite>,
    /// RHS 的原低槽输入；None 是本事务唯一的 CALL。
    pub(in crate::hir) inputs: Vec<Option<TempId>>,
}

pub(super) fn collect_parallel(
    proto: &LoweredProto,
    dialect: crate::decompile::DecompileDialect,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
) -> BTreeMap<InstrRef, ParallelFrame> {
    let mut frames = BTreeMap::new();
    for (index, instr) in proto.instrs.iter().enumerate() {
        let LowInstr::Call(call) = instr else {
            continue;
        };
        if !matches!(call.kind, crate::transformer::CallKind::Normal)
            || !matches!(call.results, ResultPack::Fixed(pack) if pack.start == call.callee && pack.len == 1)
        {
            continue;
        }
        if dialect == crate::decompile::DecompileDialect::Luau {
            if let Some(frame) =
                luau::collect(proto, cfg, dataflow, epochs, fixed_temps, phi_temps, index)
            {
                frames.insert(InstrRef(index), frame);
            }
            continue;
        }
        let site = InstrRef(index);
        let block = cfg.instr_to_block[index];
        // MOVE 区被 CALL/其它操作分隔，每段最多从相邻的两个 CALL 各访问一次。
        let mut end = index + 1;
        while matches!(proto.instrs.get(end), Some(LowInstr::Move(_)))
            && cfg.instr_to_block[end] == block
        {
            end += 1;
        }
        let mut write_start = end;
        let mut next_target = None;
        while write_start > index + 1 {
            let LowInstr::Move(copy) = proto.instrs[write_start - 1] else {
                unreachable!()
            };
            if copy.dst.index() >= call.callee.index()
                || next_target.is_some_and(|next| copy.dst.index() != next)
            {
                break;
            }
            next_target = Some(copy.dst.index() + 1);
            write_start -= 1;
        }
        if end - write_start < 2 {
            continue;
        }
        let Some(result) = dataflow.instr_def_for_reg(site, call.callee) else {
            continue;
        };
        let Some(call_offset) = (write_start..end).rev().position(|position| {
            let LowInstr::Move(copy) = proto.instrs[position] else {
                unreachable!()
            };
            dataflow.use_value(InstrRef(position), copy.src) == SsaValue::Def(result)
        }) else {
            continue;
        };
        // 被赋值变量可以位于任意低槽；scratch 从原 CALL 的 RHS 序号反推，
        // 不能把最高目标槽之后误认为空闲区，中间还可能有其它存活声明。
        let Some(base) = call
            .callee
            .index()
            .checked_sub(call_offset)
            .filter(|base| *base >= next_target.unwrap())
        else {
            continue;
        };
        let mut start = index;
        while start > 0
            && cfg.instr_to_block[start - 1] == block
            && matches!(proto.instrs[start - 1], LowInstr::Move(copy) if copy.dst.index() >= base)
        {
            start -= 1;
        }
        let frame = (|| {
            let temp =
                |value| canonical_value_temp(value, dataflow.defs.len(), fixed_temps, phi_temps);
            let mut tail = Vec::new();
            let mut previous = Vec::new();
            for position in index + 1..end {
                let LowInstr::Move(copy) = proto.instrs[position] else {
                    return None;
                };
                let at = InstrRef(position);
                let def = dataflow.instr_def_for_reg(at, copy.dst)?;
                if fixed_temps[def.index()] != TempId(def.index())
                    || [copy.dst, copy.src].iter().any(|&reg| {
                        epochs.epoch_at(reg, at) != epochs.epoch_at(reg, InstrRef(start))
                    })
                    || epochs.reference_capture_may_be_open(copy.src, at)
                    || (position < write_start
                        && epochs.reference_capture_may_be_open(copy.dst, at))
                {
                    return None;
                }
                // 最后的低槽写回已在全部 RHS 之后，完整赋值按同一逆序重发这些写。
                // 目标 cell 可以被捕获；中间准备写和读取已激活 cell 的来源仍不在此授权。
                tail.push(ParallelWrite {
                    target: TempId(def.index()),
                    source: temp(dataflow.use_value(at, copy.src))?,
                    home: HomeSlotKey::new(copy.dst.index(), epochs.epoch_at(copy.dst, at)),
                });
                if position >= write_start {
                    previous.push(temp(dataflow.def_overwritten_value(def)?)?);
                } else if copy.dst.index() < base {
                    return None;
                }
            }
            let writes = tail[write_start - index - 1..].to_vec();
            let mut calls = 0;
            for (offset, write) in writes.iter().rev().enumerate() {
                let def = dataflow.defs.get(write.source.index())?;
                let source = dataflow.def_instr(def.id);
                if source == site {
                    calls += 1;
                    if call.callee.index() != base + offset {
                        return None;
                    }
                } else if def.reg.index() >= base {
                    let LowInstr::Move(copy) = proto.instrs[source.index()] else {
                        return None;
                    };
                    if source.index() < start
                        || source.index() >= write_start
                        || copy.dst.index() != base + offset
                        || copy.src.index() >= base
                    {
                        return None;
                    }
                } else if offset + 1 != writes.len() {
                    // 末项裸 local 可直接写最终目标；前项必须有原高槽快照。
                    return None;
                }
            }
            (calls == 1).then_some(ParallelFrame {
                base: HomeSlotKey::new(base, epochs.epoch_at(Reg(base), InstrRef(start))),
                luau: None,
                preparation_count: index - start,
                tail,
                writes,
                previous,
            })
        })();
        if let Some(frame) = frame {
            frames.insert(site, frame);
        }
    }
    frames
}

#[derive(Debug, Clone, Copy)]
pub(super) struct SwapFrame {
    pub(super) snapshot: TempId,
    pub(super) writes: [TempId; 2],
    pub(super) left: HirBinding,
    pub(super) right: HirBinding,
    pub(super) left_home: HomeSlotKey,
    pub(super) right_home: HomeSlotKey,
    pub(super) home: HomeSlotKey,
}

pub(super) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
) -> BTreeMap<TempId, SwapFrame> {
    proto.instrs.windows(3).enumerate().filter_map(|(index, window)| {
        let [LowInstr::Move(save), LowInstr::Move(second), LowInstr::Move(last)] = window else {
            return None;
        };
        let first_site = InstrRef(index);
        let second_site = InstrRef(index + 1);
        let last_site = InstrRef(index + 2);
        if second.dst != save.src || last.dst != second.src || last.src != save.dst
            || save.src == second.src || save.dst.index() <= save.src.index()
            || save.dst.index() <= second.src.index()
            || cfg.instr_to_block[index] != cfg.instr_to_block[index + 2]
            || [save.dst, save.src, second.src].iter().any(|&reg| {
                epochs.reference_capture_may_be_open(reg, first_site)
                    || epochs.reference_capture_may_be_open(reg, last_site)
                    || epochs.epoch_at(reg, first_site) != epochs.epoch_at(reg, last_site)
            })
        {
            return None;
        }
        let snapshot = dataflow.instr_def_for_reg(first_site, save.dst)?;
        if fixed_temps[snapshot.index()] != TempId(snapshot.index())
            || dataflow.use_value(last_site, last.src) != SsaValue::Def(snapshot)
            || !dataflow.def_phi_uses[snapshot.index()].is_empty()
            || !matches!(dataflow.def_uses[snapshot.index()].as_slice(), [use_] if use_.instr == last_site)
        {
            return None;
        }
        let value = |site, reg| canonical_value_temp(
            dataflow.use_value(site, reg), dataflow.defs.len(), fixed_temps, phi_temps,
        );
        let frame = SwapFrame {
            snapshot: TempId(snapshot.index()),
            writes: [
                TempId(dataflow.instr_def_for_reg(second_site, second.dst)?.index()),
                TempId(dataflow.instr_def_for_reg(last_site, last.dst)?.index()),
            ],
            left: HirBinding::Temp(value(second_site, second.src)?),
            right: HirBinding::Temp(value(first_site, save.src)?),
            left_home: HomeSlotKey::new(second.src.index(), epochs.epoch_at(second.src, first_site)),
            right_home: HomeSlotKey::new(save.src.index(), epochs.epoch_at(save.src, first_site)),
            home: HomeSlotKey::new(save.dst.index(), epochs.epoch_at(save.dst, first_site)),
        };
        Some((frame.snapshot, frame))
    }).collect()
}
