//! 保存批量 nil 准备、末项低槽直写和逆序 COPY 的并列赋值协议。
//! 原指令与 SSA 固定输入证明写回顺序；源码前缀及当前绑定由 native owner 验证。

use super::*;

#[derive(Debug, Clone)]
pub(in crate::hir) struct NilAssignmentFrame {
    pub(in crate::hir) base: HomeSlotKey,
    /// 按 RHS 顺序保存高槽输入及其低槽 COPY 目标。
    pub(in crate::hir) writes: Vec<ParallelWrite>,
    pub(in crate::hir) last: TempId,
    pub(in crate::hir) last_home: HomeSlotKey,
}

pub(in crate::hir::promotion) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
) -> Vec<NilAssignmentFrame> {
    let mut frames = Vec::new();
    for (index, instr) in proto.instrs.iter().enumerate() {
        let LowInstr::LoadNil(batch) = instr else {
            continue;
        };
        let Some(LowInstr::LoadNil(last)) = proto.instrs.get(index + 1) else {
            continue;
        };
        if batch.dst.len < 2 || last.dst.len != 1
            // PUC 会合并相邻的 LOADNIL；重发两个独立批次必须保留中间未写槽。
            || last.dst.start.index() + 1 >= batch.dst.start.index()
        {
            continue;
        }
        let width = batch.dst.len;
        let Some(copies) = proto.instrs.get(index + 2..index + 2 + width) else {
            continue;
        };
        // 先按执行顺序拒绝非 COPY；失败窗口止于下一种指令，不反复扫描共享长后缀。
        if !copies
            .iter()
            .all(|instr| matches!(instr, LowInstr::Move(_)))
        {
            continue;
        }
        let defs = &dataflow.instr_defs[index];
        if defs.len() != width {
            continue;
        }
        let frame = (|| {
            let last_site = InstrRef(index + 1);
            let last_def = dataflow.instr_def_for_reg(last_site, last.dst.start)?;
            if fixed_temps[last_def.index()] != TempId(last_def.index())
                || cfg.instr_to_block[index + 1] != cfg.instr_to_block[index]
            {
                return None;
            }
            let base = HomeSlotKey::new(
                batch.dst.start.index(),
                epochs.epoch_at(batch.dst.start, InstrRef(index)),
            );
            let mut targets = BTreeSet::from([last.dst.start]);
            let mut writes = Vec::with_capacity(width);
            for (offset, (instr, &source)) in copies.iter().rev().zip(defs).enumerate() {
                let LowInstr::Move(copy) = instr else {
                    return None;
                };
                let site = InstrRef(index + 1 + width - offset);
                let target = dataflow.instr_def_for_reg(site, copy.dst)?;
                if cfg.instr_to_block[site.index()] != cfg.instr_to_block[index]
                    || copy.src.index() != base.slot() + offset
                    || dataflow.def_reg(source) != copy.src
                    || dataflow.use_value(site, copy.src) != SsaValue::Def(source)
                    || fixed_temps[source.index()] != TempId(source.index())
                    || fixed_temps[target.index()] != TempId(target.index())
                    || !matches!(dataflow.def_uses[source.index()].as_slice(), [use_] if use_.instr == site)
                    || !dataflow.def_phi_uses[source.index()].is_empty()
                    || copy.dst.index() >= base.slot()
                    || !targets.insert(copy.dst)
                    || epochs.epoch_at(copy.src, site) != base.epoch
                    || epochs.reference_capture_may_be_open(copy.src, site)
                {
                    // ProofIncomplete：每个原批次成员只能由这次 COPY 消费，不能删部分组。
                    return None;
                }
                writes.push(ParallelWrite {
                    source: TempId(source.index()),
                    target: TempId(target.index()),
                    home: HomeSlotKey::new(copy.dst.index(), epochs.epoch_at(copy.dst, site)),
                });
            }
            Some(NilAssignmentFrame {
                base,
                writes,
                last: TempId(last_def.index()),
                last_home: HomeSlotKey::new(
                    last.dst.start.index(),
                    epochs.epoch_at(last.dst.start, last_site),
                ),
            })
        })();
        if let Some(frame) = frame {
            frames.push(frame);
        }
    }
    frames
}
