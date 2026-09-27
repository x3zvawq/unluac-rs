//! 保存并行赋值的原快照、目标版本和写回顺序。
//! 只提供同一基本块的原指令事实；源码声明前缀和后继槽复用由 simplify 核对。

use super::*;

pub(super) mod lookups;
mod luau;

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

/// 首项在高槽准备字面量或旧值快照，再写第二项字面量和第一项 COPY。
#[derive(Debug, Clone)]
pub(in crate::hir) struct ScalarPairFrame {
    pub(in crate::hir) temps: [TempId; 3],
    pub(in crate::hir) homes: [HomeSlotKey; 3],
    pub(super) copied_input: Option<(TempId, HomeSlotKey)>,
    pub(in crate::hir) literal_input: Option<HirExpr>,
    pub(in crate::hir) tail: HirExpr,
    pub(super) copied_tail: Option<(TempId, HomeSlotKey)>,
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
        let (second_reg, tail, copied_tail) = if let LowInstr::Move(copy) = second {
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
        if last.src != snapshot_reg || last.dst == second_reg
            || last.dst.index() >= last.src.index()
            || second_reg.index() >= last.src.index()
            || cfg.instr_to_block[index] != cfg.instr_to_block[index + 2]
        {
            return None;
        }
        let regs = [snapshot_reg, second_reg, last.dst];
        let mut temps = [TempId(0); 3];
        let mut homes = [HomeSlotKey::new(0, 0); 3];
        for (offset, reg) in regs.into_iter().enumerate() {
            let site = InstrRef(index + offset);
            let def = dataflow.instr_def_for_reg(site, reg)?;
            if fixed_temps[def.index()] != TempId(def.index())
                || epochs.reference_capture_may_be_open(reg, site)
            {
                return None;
            }
            temps[offset] = TempId(def.index());
            homes[offset] = HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, site));
        }
        let first_def = dataflow.instr_def_for_reg(InstrRef(index), regs[0])?;
        let last_site = InstrRef(index + 2);
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
        let base = next_target.unwrap();
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
                        epochs.reference_capture_may_be_open(reg, at)
                            || epochs.epoch_at(reg, at) != epochs.epoch_at(reg, InstrRef(start))
                    })
                {
                    return None;
                }
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
) -> Vec<SwapFrame> {
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
        Some(SwapFrame {
            snapshot: TempId(snapshot.index()),
            left: HirBinding::Temp(value(second_site, second.src)?),
            right: HirBinding::Temp(value(first_site, save.src)?),
            left_home: HomeSlotKey::new(second.src.index(), epochs.epoch_at(second.src, first_site)),
            right_home: HomeSlotKey::new(save.src.index(), epochs.epoch_at(save.src, first_site)),
            home: HomeSlotKey::new(save.dst.index(), epochs.epoch_at(save.dst, first_site)),
        })
    }).collect()
}
