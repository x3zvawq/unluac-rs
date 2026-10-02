//! 保存 PUC/LuaJIT 并行赋值中查表与标量准备、末项直接写低槽及逆序写回的原 Def。
//! 这里只识别无额外左值准备的固定键读取；源码声明和后继 scratch 复用由完整帧验证。

use super::*;
use crate::transformer::{AccessBase, AccessKey, GetTableKind, SetTableKind, ValueOperand};

#[derive(Debug, Clone)]
pub(in crate::hir) struct LookupRead {
    pub(in crate::hir) site: InstrRef,
    pub(in crate::hir) value: TempId,
    pub(in crate::hir) home: HomeSlotKey,
    pub(in crate::hir) literal: Option<HirExpr>,
}

#[derive(Debug, Clone)]
pub(in crate::hir) struct LookupWrite {
    pub(in crate::hir) site: InstrRef,
    pub(in crate::hir) target: Option<(TempId, HomeSlotKey)>,
}

#[derive(Debug, Clone)]
pub(in crate::hir) struct LookupFrame {
    pub(in crate::hir) reads: Vec<LookupRead>,
    /// 与前面的 scratch 读取同序；原指令按逆序执行这些写。
    pub(in crate::hir) writes: Vec<LookupWrite>,
}

pub(in crate::hir::promotion) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
) -> BTreeMap<InstrRef, LookupFrame> {
    let mut frames = BTreeMap::new();
    let mut index = 0;
    while index < proto.instrs.len() {
        let start = index;
        index += 1;
        let LowInstr::GetTable(first) = proto.instrs[start] else {
            continue;
        };
        let base = first.dst.index();
        let block = cfg.instr_to_block[start];
        let mut reads = Vec::new();
        let mut inputs = BTreeSet::new();
        let frame = (|| {
            let mut at = start;
            loop {
                let (dst, literal) = match proto.instrs.get(at)? {
                    LowInstr::GetTable(read) => {
                        let AccessBase::Reg(table) = read.base else {
                            return None;
                        };
                        if read.kind != GetTableKind::Normal
                            || !matches!(read.key, AccessKey::Const(_) | AccessKey::Integer(_))
                            || table.index() >= base
                        {
                            return None;
                        }
                        inputs.insert(table);
                        (read.dst, None)
                    }
                    instr => {
                        let (dst, value) = scalar_literal(proto, instr)?;
                        (dst, Some(value))
                    }
                };
                if cfg.instr_to_block[at] != block
                    || (dst.index() >= base && dst.index() != base + reads.len())
                {
                    return None;
                }
                let site = InstrRef(at);
                let def = dataflow.instr_def_for_reg(site, dst)?;
                reads.push(LookupRead {
                    site,
                    value: TempId(def.index()),
                    home: HomeSlotKey::new(dst.index(), epochs.epoch_at(dst, site)),
                    literal,
                });
                at += 1;
                index = at;
                if dst.index() < base {
                    break;
                }
            }
            let count = reads.len().checked_sub(1)?;
            if count == 0 {
                return None;
            }
            let mut targets = BTreeSet::from([Reg(reads.last()?.home.slot())]);
            let mut writes = Vec::with_capacity(count);
            for read in reads[..count].iter().rev() {
                let site = InstrRef(at);
                let instr = proto.instrs.get(at)?;
                if cfg.instr_to_block[at] != block {
                    return None;
                }
                let source = Reg(read.home.slot());
                if dataflow.use_value(site, source)
                    != SsaValue::Def(crate::structure::DefId(read.value.index()))
                {
                    return None;
                }
                if read.literal.is_some()
                    && (!matches!(dataflow.def_uses[read.value.index()].as_slice(), [use_] if use_.instr == site)
                        || !dataflow.def_phi_uses[read.value.index()].is_empty()
                        || epochs.reference_capture_may_be_open(source, read.site)
                        || epochs.epoch_at(source, site) != read.home.epoch)
                {
                    // 标量准备须只供这次原 COPY 使用，才能保留到整组赋值提交时退休。
                    return None;
                }
                let target = match instr {
                    LowInstr::Move(copy) if copy.src == source && copy.dst.index() < base => {
                        if !targets.insert(copy.dst) {
                            return None;
                        }
                        let def = dataflow.instr_def_for_reg(site, copy.dst)?;
                        Some((
                            TempId(def.index()),
                            HomeSlotKey::new(copy.dst.index(), epochs.epoch_at(copy.dst, site)),
                        ))
                    }
                    LowInstr::SetTable(write)
                        if write.kind == SetTableKind::Normal
                            && write.value == ValueOperand::Reg(source)
                            && matches!(write.key, AccessKey::Const(_) | AccessKey::Integer(_)) =>
                    {
                        let AccessBase::Reg(table) = write.base else {
                            return None;
                        };
                        if table.index() >= base {
                            return None;
                        }
                        inputs.insert(table);
                        None
                    }
                    _ => return None,
                };
                writes.push(LookupWrite { site, target });
                at += 1;
            }
            // 低槽表/key 没有左值快照；目标更新不能同时改写后续要读取的表身份。
            if !inputs.is_disjoint(&targets) {
                return None;
            }
            writes.reverse();
            index = at;
            Some(LookupFrame {
                reads: std::mem::take(&mut reads),
                writes,
            })
        })();
        if let Some(frame) = frame {
            frames.insert(InstrRef(start), frame);
        }
    }
    frames
}
