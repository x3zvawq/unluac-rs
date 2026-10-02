//! 保存以空表或标量常量结尾的并列赋值准备、原 Def 与逆序低槽写回。
//! 写回指令确定完整批次；当前构造器、声明前缀和根生命周期由 HIR 完整帧验证。

use super::*;

#[derive(Debug, Clone)]
pub(in crate::hir) struct PreparedInput {
    pub(in crate::hir) site: InstrRef,
    pub(in crate::hir) value: TempId,
    pub(in crate::hir) home: HomeSlotKey,
    pub(in crate::hir) literal: Option<HirExpr>,
    pub(in crate::hir) copied: Option<(TempId, HomeSlotKey)>,
}

/// inputs 与 writes 同序；末项常量及 JIT 空表可直接写入低槽，其余目标按原 COPY 逆序提交。
#[derive(Debug, Clone)]
pub(in crate::hir) struct PreparedFrame {
    pub(in crate::hir) inputs: Vec<PreparedInput>,
    pub(in crate::hir) writes: Vec<ParallelWrite>,
}

pub(in crate::hir::promotion) fn collect(
    proto: &LoweredProto,
    dialect: crate::decompile::DecompileDialect,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
) -> BTreeMap<InstrRef, PreparedFrame> {
    let mut frames = BTreeMap::new();
    for (index, instr) in proto.instrs.iter().enumerate() {
        let (last_reg, literal_tail) = match instr {
            LowInstr::NewTable(allocation) => (allocation.dst, false),
            instr => {
                let Some((reg, _)) = scalar_literal(proto, instr) else {
                    continue;
                };
                (reg, true)
            }
        };
        let Some(LowInstr::Move(first_copy)) = proto.instrs.get(index + 1) else {
            continue;
        };
        let direct = (literal_tail || dialect == crate::decompile::DecompileDialect::Luajit)
            && last_reg < first_copy.src;
        if !direct && first_copy.src != last_reg {
            continue;
        }
        let input = |at: usize, reg: Reg| -> Option<PreparedInput> {
            let site = InstrRef(at);
            if cfg.instr_to_block[at] != cfg.instr_to_block[index] {
                return None;
            }
            let (dst, literal, copied) = match &proto.instrs[at] {
                LowInstr::NewTable(table) => (table.dst, None, None),
                LowInstr::Move(copy)
                    if copy.src < copy.dst
                        && !epochs.reference_capture_may_be_open(copy.src, site) =>
                {
                    let source = canonical_value_temp(
                        dataflow.use_value(site, copy.src),
                        dataflow.defs.len(),
                        fixed_temps,
                        phi_temps,
                    )?;
                    (
                        copy.dst,
                        None,
                        Some((
                            source,
                            HomeSlotKey::new(copy.src.index(), epochs.epoch_at(copy.src, site)),
                        )),
                    )
                }
                instr => {
                    let (dst, literal) = scalar_literal(proto, instr)?;
                    (dst, Some(literal), None)
                }
            };
            if dst != reg {
                return None;
            }
            let def = dataflow.instr_def_for_reg(site, reg)?;
            Some(PreparedInput {
                site,
                value: TempId(def.index()),
                home: HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, site)),
                literal,
                copied,
            })
        };
        let mut inputs = Vec::new();
        let mut writes = Vec::new();
        if direct {
            let Some(last) = input(index, last_reg) else {
                continue;
            };
            writes.push(ParallelWrite {
                target: last.value,
                source: last.value,
                home: last.home,
            });
            inputs.push(last);
        }
        // 每段 COPY 只跟随一个末项操作；按对应准备位置逐项扩展，不对每个常量重扫前缀。
        while let Some(at) = index.checked_sub(inputs.len()) {
            let write_site = InstrRef(index + 1 + writes.len() - usize::from(direct));
            let Some(LowInstr::Move(copy)) = proto.instrs.get(write_site.index()) else {
                break;
            };
            let Some(prepared) = input(at, copy.src) else {
                break;
            };
            let def = crate::structure::DefId(prepared.value.index());
            if copy.dst >= copy.src
                || cfg.instr_to_block[write_site.index()] != cfg.instr_to_block[index]
                || epochs.reference_capture_may_be_open(copy.src, prepared.site)
                || epochs.epoch_at(copy.src, write_site) != prepared.home.epoch
                || dataflow.use_value(write_site, copy.src) != SsaValue::Def(def)
                || !dataflow.def_phi_uses[def.index()].is_empty()
                || !matches!(dataflow.def_uses[def.index()].as_slice(), [use_] if use_.instr == write_site)
            {
                break;
            }
            let Some(target) = dataflow.instr_def_for_reg(write_site, copy.dst) else {
                break;
            };
            writes.push(ParallelWrite {
                target: TempId(target.index()),
                source: prepared.value,
                home: HomeSlotKey::new(copy.dst.index(), epochs.epoch_at(copy.dst, write_site)),
            });
            inputs.push(prepared);
        }
        if inputs.len() < 2 {
            continue;
        }
        // 候选拒绝[TargetConstraint]：PUC 的并列 nil 可合并原 LOADNIL 区间，
        // 逐项常量/COPY 证书不足以验证该范围；沿用 nil owner 的独立合同。
        if literal_tail
            && dialect != crate::decompile::DecompileDialect::Luajit
            && inputs
                .iter()
                .any(|input| input.literal == Some(HirExpr::Nil))
        {
            continue;
        }
        inputs.reverse();
        writes.reverse();
        let base = inputs[0].home.slot();
        let mut targets = BTreeSet::new();
        if inputs.iter().enumerate().any(|(offset, input)| {
            !(direct && offset + 1 == inputs.len()) && input.home.slot() != base + offset
        }) || writes
            .iter()
            .any(|write| write.home.slot() >= base || !targets.insert(write.home.slot()))
        {
            continue;
        }
        frames.insert(InstrRef(index), PreparedFrame { inputs, writes });
    }
    frames
}
