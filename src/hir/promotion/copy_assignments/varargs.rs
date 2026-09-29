//! 保存固定变参包的初始定义与完整 COPY 重赋值事实。
//! 同块原指令和 SSA 证明值包对应关系；源码作用域及声明前缀由消费者验证。

use super::*;

#[derive(Debug, Clone)]
pub(in crate::hir) struct VarargFrame {
    pub(in crate::hir) initial: Vec<TempId>,
    pub(in crate::hir) results: Vec<TempId>,
    pub(in crate::hir) result_homes: Vec<HomeSlotKey>,
    pub(in crate::hir) writes: Vec<ParallelWrite>,
    pub(in crate::hir) scratch: HomeSlotKey,
}

pub(in crate::hir::promotion) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
) -> BTreeMap<TempId, VarargFrame> {
    let mut frames = BTreeMap::new();
    for (index, pair) in proto.instrs.windows(2).enumerate() {
        let [LowInstr::VarArg(first), LowInstr::VarArg(second)] = pair else {
            continue;
        };
        let (ResultPack::Fixed(initial), ResultPack::Fixed(results)) =
            (first.results, second.results)
        else {
            continue;
        };
        if initial.len == 0
            || initial.len != results.len
            || initial.start.index() + initial.len != results.start.index()
        {
            continue;
        }
        let frame = (|| {
            let first_site = InstrRef(index);
            let result_site = InstrRef(index + 1);
            let mut seeds = Vec::with_capacity(initial.len);
            let mut values = Vec::with_capacity(initial.len);
            for offset in 0..initial.len {
                let seed =
                    dataflow.instr_def_for_reg(first_site, Reg(initial.start.index() + offset))?;
                let value =
                    dataflow.instr_def_for_reg(result_site, Reg(results.start.index() + offset))?;
                if [seed, value]
                    .iter()
                    .any(|def| fixed_temps[def.index()] != TempId(def.index()))
                    || !dataflow.def_uses[seed.index()].is_empty()
                    || !dataflow.def_phi_uses[seed.index()].is_empty()
                {
                    return None;
                }
                seeds.push(TempId(seed.index()));
                values.push(TempId(value.index()));
            }
            let mut writes = vec![None; initial.len];
            for position in index + 2..index + 2 + initial.len {
                let LowInstr::Move(copy) = *proto.instrs.get(position)? else {
                    return None;
                };
                let offset = copy.dst.index().checked_sub(initial.start.index())?;
                if offset >= initial.len
                    || writes[offset].is_some()
                    || copy.src.index() != results.start.index() + offset
                    || cfg.instr_to_block[position] != cfg.instr_to_block[index]
                {
                    return None;
                }
                let site = InstrRef(position);
                let def = dataflow.instr_def_for_reg(site, copy.dst)?;
                let value = dataflow.instr_def_for_reg(result_site, copy.src)?;
                if fixed_temps[def.index()] != TempId(def.index())
                    || dataflow.use_value(site, copy.src) != SsaValue::Def(value)
                    || dataflow.def_overwritten_value(def)
                        != Some(SsaValue::Def(
                            dataflow.instr_def_for_reg(first_site, copy.dst)?,
                        ))
                    || !dataflow.def_phi_uses[value.index()].is_empty()
                    || !matches!(dataflow.def_uses[value.index()].as_slice(), [use_] if use_.instr == site)
                    || [copy.src, copy.dst].iter().any(|&reg| {
                        epochs.reference_capture_may_be_open(reg, first_site)
                            || epochs.reference_capture_may_be_open(reg, site)
                            || epochs.epoch_at(reg, first_site) != epochs.epoch_at(reg, site)
                    })
                {
                    return None;
                }
                writes[offset] = Some(ParallelWrite {
                    target: TempId(def.index()),
                    source: values[offset],
                    home: HomeSlotKey::new(copy.dst.index(), epochs.epoch_at(copy.dst, site)),
                });
            }
            Some(VarargFrame {
                initial: seeds,
                results: values,
                result_homes: (0..results.len)
                    .map(|offset| {
                        let reg = Reg(results.start.index() + offset);
                        HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, result_site))
                    })
                    .collect(),
                writes: writes.into_iter().collect::<Option<Vec<_>>>()?,
                scratch: HomeSlotKey::new(
                    results.start.index(),
                    epochs.epoch_at(results.start, result_site),
                ),
            })
        })();
        if let Some(frame) = frame {
            frames.insert(frame.results[0], frame);
        }
    }
    frames
}
