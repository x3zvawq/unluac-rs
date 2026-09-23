//! 短路查表与调用值的原分支、准备及合流身份。
//!
//! Structure 的单 predicate phi 和 SSA Def 确定输入、备用值及结果的原身份与极性。
//! 这里不恢复表达式或签发根退休；完整帧消费者仍须核对当前操作、分支和准备位置。

use super::*;

#[derive(Debug, Clone, Copy)]
pub(super) struct ShortCircuitCallFrame {
    pub(super) input: TempId,
    pub(super) kept: TempId,
    pub(super) alternative: TempId,
    pub(super) result: TempId,
    pub(super) logical_and: bool,
    pub(super) value: ShortCircuitCallValue,
}

#[derive(Debug, Clone, Copy)]
pub(super) enum ShortCircuitCallValue {
    Scalar(CopyRootScalarValue),
    CopyTemp(TempId),
    CopyParam(ParamId),
}

/// CALL 的单结果直接保留或经单次 MOVE 写入 phi，另一臂写常量或读取已有低槽 binding。
/// 原两臂及 merge 必须由同一 predicate 拥有，不从最终表达式外形猜 COPY。
pub(super) fn collect_calls(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    fixed: &[TempId],
    phis: &[TempId],
    predicates: &BTreeMap<PhiId, InstrRef>,
) -> BTreeMap<InstrRef, Option<ShortCircuitCallFrame>> {
    let mut frames = BTreeMap::new();
    for phi in plan.phis() {
        let candidate = || {
            let predicate = *predicates.get(&phi.phi)?;
            let LowInstr::Branch(branch) = proto.instrs[predicate.index()] else {
                return None;
            };
            let crate::transformer::BranchSubject::Truthy(crate::transformer::CondOperand::Reg(
                reg,
            )) = branch.cond.subject
            else {
                return None;
            };
            let SsaValue::Def(input) = dataflow.use_value(predicate, reg) else {
                return None;
            };
            let source = dataflow.def_instr(input);
            if source.index() + 1 != predicate.index()
                || dataflow.defs[input.index()].block != cfg.instr_to_block[predicate.index()]
                || !matches!(&proto.instrs[source.index()], LowInstr::Call(call)
                    if call.results == ResultPack::Fixed(crate::transformer::RegRange { start: reg, len: 1 }))
            {
                return None;
            }
            let merge = cfg.blocks[phi.block.index()].instrs.start;
            let (truthy, falsy) = if branch.cond.negated {
                (branch.else_target, branch.then_target)
            } else {
                (branch.then_target, branch.else_target)
            };
            let mut kept = None;
            let mut alternative = None;
            for incoming in &phi.incomings {
                let SsaValue::Def(def) = incoming.value else {
                    return None;
                };
                let site = dataflow.def_instr(def);
                let temp = canonical_value_temp(incoming.value, dataflow.defs.len(), fixed, phis)?;
                if def == input {
                    if phi.reg != reg || kept.replace((temp, merge)).is_some() {
                        return None;
                    }
                    continue;
                }
                let block = &cfg.blocks[dataflow.defs[def.index()].block.index()];
                if block.instrs.start != site
                    || !match block.instrs.len {
                        1 => site.index() + 1 == merge.index(),
                        2 => {
                            matches!(proto.instrs[site.index() + 1], LowInstr::Jump(jump) if jump.target == merge)
                        }
                        _ => false,
                    }
                {
                    return None;
                }
                if matches!(&proto.instrs[site.index()], LowInstr::Move(movement)
                    if movement.dst == phi.reg && movement.src == reg
                        && dataflow.use_value(site, reg) == SsaValue::Def(input))
                {
                    if kept.replace((temp, site)).is_some() {
                        return None;
                    }
                } else {
                    let value = if let LowInstr::Move(movement) = &proto.instrs[site.index()] {
                        if movement.dst != phi.reg || movement.src.index() >= phi.reg.index() {
                            return None;
                        }
                        // 记录选中备用臂时读取的原 binding，而不是 CALL 前的值快照。
                        match dataflow.use_value(site, movement.src) {
                            SsaValue::Entry(reg)
                                if reg.index() < usize::from(proto.signature.num_params) =>
                            {
                                ShortCircuitCallValue::CopyParam(ParamId(reg.index()))
                            }
                            value => ShortCircuitCallValue::CopyTemp(canonical_value_temp(
                                value,
                                dataflow.defs.len(),
                                fixed,
                                phis,
                            )?),
                        }
                    } else {
                        ShortCircuitCallValue::Scalar(
                            direct_scalar_overwrite_value(&proto.instrs[site.index()], phi.reg)
                                .or_else(|| {
                                    let LowInstr::LoadConst(load) = &proto.instrs[site.index()]
                                    else {
                                        return None;
                                    };
                                    if load.dst != phi.reg {
                                        return None;
                                    }
                                    match proto.constants.get(load.value.index())? {
                                        crate::parser::RawLiteralConst::Integer(value) => {
                                            Some(CopyRootScalarValue::Integer(*value))
                                        }
                                        crate::parser::RawLiteralConst::Number(value) => {
                                            Some(CopyRootScalarValue::Number(*value))
                                        }
                                        _ => None,
                                    }
                                })?,
                        )
                    };
                    if alternative.replace((temp, site, value)).is_some() {
                        return None;
                    }
                }
            }
            let (kept, kept_site) = kept?;
            let (alternative, alternative_site, value) = alternative?;
            let logical_and = if kept_site == falsy && alternative_site == truthy {
                true
            } else if kept_site == truthy && alternative_site == falsy {
                false
            } else {
                return None;
            };
            Some((
                source,
                ShortCircuitCallFrame {
                    input: canonical_value_temp(
                        SsaValue::Def(input),
                        dataflow.defs.len(),
                        fixed,
                        phis,
                    )?,
                    kept,
                    alternative,
                    result: canonical_value_temp(
                        SsaValue::Phi(phi.phi),
                        dataflow.defs.len(),
                        fixed,
                        phis,
                    )?,
                    logical_and,
                    value,
                },
            ))
        };
        if let Some((source, frame)) = candidate() {
            frames
                .entry(source)
                .and_modify(|entry| *entry = None)
                .or_insert(Some(frame));
        }
    }
    frames
}

#[derive(Debug, Clone, Copy)]
pub(super) struct ShortCircuitTableFrame {
    pub(super) input: TempId,
    pub(super) alternative: TempId,
    pub(super) result: TempId,
}

pub(super) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    fixed: &[TempId],
    phis: &[TempId],
    predicates: &BTreeMap<PhiId, InstrRef>,
) -> BTreeMap<(InstrRef, InstrRef), Option<ShortCircuitTableFrame>> {
    let mut frames = BTreeMap::new();
    for phi in plan.phis() {
        let candidate = || {
            let predicate = *predicates.get(&phi.phi)?;
            let LowInstr::Branch(branch) = proto.instrs[predicate.index()] else {
                return None;
            };
            let crate::transformer::BranchSubject::Truthy(crate::transformer::CondOperand::Reg(
                reg,
            )) = branch.cond.subject
            else {
                return None;
            };
            let SsaValue::Def(input) = dataflow.use_value(predicate, reg) else {
                return None;
            };
            let input_site = dataflow.def_instr(input);
            if input_site.index() + 1 != predicate.index()
                || dataflow.defs[input.index()].block != cfg.instr_to_block[predicate.index()]
                || !matches!(proto.instrs[input_site.index()], LowInstr::GetTable(_))
                || phi.reg != reg
                || phi.incomings.len() != 2
            {
                return None;
            }
            let merge = cfg.blocks[phi.block.index()].instrs.start;
            let (truthy, falsy) = if branch.cond.negated {
                (branch.else_target, branch.then_target)
            } else {
                (branch.then_target, branch.else_target)
            };
            if truthy != merge {
                return None;
            }
            let mut kept = false;
            let mut alternative = None;
            for incoming in &phi.incomings {
                let SsaValue::Def(def) = incoming.value else {
                    return None;
                };
                if def == input {
                    kept = true;
                    continue;
                }
                let site = dataflow.def_instr(def);
                let block = &cfg.blocks[dataflow.defs[def.index()].block.index()];
                if alternative.is_some()
                    || site != falsy
                    || site != block.instrs.start
                    || !matches!(proto.instrs[site.index()], LowInstr::NewTable(_))
                    || !match block.instrs.len {
                        1 => site.index() + 1 == merge.index(),
                        2 => {
                            matches!(proto.instrs[site.index()+1], LowInstr::Jump(jump) if jump.target == merge)
                        }
                        _ => false,
                    }
                {
                    return None;
                }
                alternative = Some((
                    site,
                    canonical_value_temp(incoming.value, dataflow.defs.len(), fixed, phis)?,
                ));
            }
            let (alternative_site, alternative) = alternative?;
            kept.then_some((
                (input_site, alternative_site),
                ShortCircuitTableFrame {
                    input: canonical_value_temp(
                        SsaValue::Def(input),
                        dataflow.defs.len(),
                        fixed,
                        phis,
                    )?,
                    alternative,
                    result: canonical_value_temp(
                        SsaValue::Phi(phi.phi),
                        dataflow.defs.len(),
                        fixed,
                        phis,
                    )?,
                },
            ))
        };
        if let Some((sites, frame)) = candidate() {
            frames
                .entry(sites)
                .and_modify(|entry| *entry = None)
                .or_insert(Some(frame));
        }
    }
    frames
}
