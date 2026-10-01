//! 短路查表与调用值的原分支、准备及合流身份。
//!
//! Structure 的冻结条件、值决策和 SSA Def 确定输入、备用值及结果的原身份与极性。
//! 这里不恢复表达式或签发根退休；完整帧消费者仍须核对当前操作、分支和准备位置。

use super::*;

/// 原高槽谓词选择字面量后写回低槽；保留两臂直写或经过 COPY 的独立定义关系。
#[derive(Debug, Clone)]
pub(super) struct SelectionWriteback {
    pub(super) input: operand_preparations::OperandPreparation,
    pub(super) result: TempId,
    pub(super) previous: TempId,
    pub(super) home: HomeSlotKey,
    /// 真值臂经高槽字面量 COPY 时记录该准备；两臂直写时没有这一项。
    pub(super) literal_preparation: Option<TempId>,
    pub(super) writes: [TempId; 2],
    pub(super) truthy: HirExpr,
    pub(super) falsy: HirExpr,
}

pub(super) fn collect_selections(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    epochs: &SlotEpochFacts,
    fixed: &[TempId],
    phis: &[TempId],
) -> BTreeMap<TempId, SelectionWriteback> {
    use crate::structure::ValueDecisionTarget;
    use crate::transformer::{BranchSubject, CondOperand};
    let mut frames = BTreeMap::new();
    for (_, decision) in plan.value_decisions() {
        let candidate = (|| {
            if decision.nodes.len() != 2
                || decision.leaves.len() != 2
                || decision.blocks.len() != 4
                || !decision.operands.is_empty()
                || !decision.absorbed_phis.is_empty()
                || decision.loop_entry.is_some()
            {
                return None;
            }
            let entry = &decision.nodes[decision.entry.index()];
            let (ValueDecisionTarget::Node(next), ValueDecisionTarget::Leaf(falsy)) =
                (entry.truthy.target, entry.falsy.target)
            else {
                return None;
            };
            let next = &decision.nodes[next.index()];
            let (ValueDecisionTarget::CurrentValue(kept), ValueDecisionTarget::Leaf(other)) =
                (next.truthy.target, next.falsy.target)
            else {
                return None;
            };
            if other != falsy || kept == falsy {
                return None;
            }
            let LowInstr::Branch(test) = proto.instrs[entry.predicate.index()] else {
                return None;
            };
            let BranchSubject::Truthy(CondOperand::Reg(reg)) = test.cond.subject else {
                return None;
            };
            let input = operand_preparations::collect(
                proto,
                cfg,
                dataflow,
                epochs,
                fixed,
                entry.predicate,
                reg,
            )?;
            let home = HomeSlotKey::new(
                decision.result_reg.index(),
                epochs.epoch_at(decision.result_reg, entry.predicate),
            );
            if input.home.slot() <= home.slot() {
                return None;
            }
            let kept = &decision.leaves[kept.index()];
            let falsy = &decision.leaves[falsy.index()];
            let SsaValue::Def(kept_def) = kept.value else {
                return None;
            };
            let SsaValue::Def(falsy_def) = falsy.value else {
                return None;
            };
            let copy_site = dataflow.def_instr(kept_def);
            let false_site = dataflow.def_instr(falsy_def);
            let LowInstr::Move(copy) = proto.instrs[copy_site.index()] else {
                return None;
            };
            if copy.src != reg || copy.dst != decision.result_reg {
                return None;
            }
            let SsaValue::Def(literal_def) = dataflow.use_value(copy_site, reg) else {
                return None;
            };
            let literal_site = dataflow.def_instr(literal_def);
            let (literal_reg, truthy) =
                copy_assignments::scalar_literal(proto, &proto.instrs[literal_site.index()])?;
            let (false_reg, falsy_value) =
                copy_assignments::scalar_literal(proto, &proto.instrs[false_site.index()])?;
            let LowInstr::Branch(test) = proto.instrs[next.predicate.index()] else {
                return None;
            };
            if literal_reg != reg
                || false_reg != decision.result_reg
                || test.cond.subject != BranchSubject::Truthy(CondOperand::Reg(reg))
                || dataflow.use_value(next.predicate, reg) != SsaValue::Def(literal_def)
                || crate::hir::value_facts::value_facts(&truthy).truthiness() != Some(true)
            {
                return None;
            }
            // 冻结图提供极性和合流；原块内容还须仅有这三次写，不能把其它事件收入字面量臂。
            let literal_block = &cfg.blocks[next.block.index()];
            if literal_block.instrs.start != literal_site
                || literal_block.instrs.len != 2
                || next.predicate.index() != literal_site.index() + 1
            {
                return None;
            }
            for (block, site) in [(kept.block, copy_site), (falsy.block, false_site)] {
                let range = cfg.blocks[block.index()].instrs;
                if range.start != site
                    || !match range.len {
                        1 => {
                            site.index() + 1
                                == cfg.blocks[decision.merge.index()].instrs.start.index()
                        }
                        2 => matches!(proto.instrs[site.index() + 1], LowInstr::Jump(jump)
                        if jump.target == cfg.blocks[decision.merge.index()].instrs.start),
                        _ => false,
                    }
                {
                    return None;
                }
            }
            let incoming = &dataflow.phi_candidates[decision.result_phi.index()].incoming;
            if incoming.len() != 2
                || !incoming
                    .iter()
                    .all(|edge| edge.value == kept.value || edge.value == falsy.value)
            {
                return None;
            }
            let writes = [literal_def, kept_def, falsy_def].map(|def| fixed[def.index()]);
            if writes
                .iter()
                .zip([literal_def, kept_def, falsy_def])
                .any(|(&temp, def)| temp != TempId(def.index()))
            {
                return None;
            }
            for (reg, site, expected) in [
                (reg, literal_site, input.home),
                (reg, copy_site, input.home),
                (decision.result_reg, copy_site, home),
                (decision.result_reg, false_site, home),
            ] {
                if epochs.epoch_at(reg, site) != expected.epoch
                    || epochs.reference_capture_may_be_open(reg, site)
                {
                    return None;
                }
            }
            let result = canonical_value_temp(
                SsaValue::Phi(decision.result_phi),
                dataflow.defs.len(),
                fixed,
                phis,
            )?;
            let previous = dataflow.def_overwritten_value(kept_def)?;
            if dataflow.def_overwritten_value(falsy_def) != Some(previous) {
                return None;
            }
            let previous = canonical_value_temp(previous, dataflow.defs.len(), fixed, phis)?;
            Some(SelectionWriteback {
                input,
                result,
                previous,
                home,
                literal_preparation: Some(writes[0]),
                writes: [writes[1], writes[2]],
                truthy,
                falsy: falsy_value,
            })
        })();
        if let Some(frame) = candidate {
            frames
                .entry(frame.result)
                .and_modify(|entry| *entry = None)
                .or_insert(Some(frame));
        }
    }
    for (owner, _) in plan.regions() {
        let candidate = (|| {
            let initializer = plan.branch_initializer(owner, cfg, dataflow)?;
            let condition = plan.condition(initializer.condition)?;
            let [node] = condition.nodes.as_slice() else {
                return None;
            };
            if node.materialized_value.is_some() {
                return None;
            }
            let LowInstr::Branch(branch) = proto.instrs[node.predicate.index()] else {
                return None;
            };
            let BranchSubject::Truthy(CondOperand::Reg(reg)) = branch.cond.subject else {
                return None;
            };
            let input = operand_preparations::collect(
                proto,
                cfg,
                dataflow,
                epochs,
                fixed,
                node.predicate,
                reg,
            )?;
            let home = HomeSlotKey::new(
                initializer.reg.index(),
                epochs.epoch_at(initializer.reg, node.predicate),
            );
            if input.home.slot() <= home.slot() {
                return None;
            }
            let mut defs = initializer.defs;
            if initializer.condition_inverted {
                defs.swap(0, 1);
            }
            let [truthy_site, falsy_site] = defs.map(|def| dataflow.def_instr(def));
            let (_, truthy) =
                copy_assignments::scalar_literal(proto, &proto.instrs[truthy_site.index()])?;
            let (_, falsy) =
                copy_assignments::scalar_literal(proto, &proto.instrs[falsy_site.index()])?;
            if crate::hir::value_facts::value_facts(&truthy).truthiness() != Some(true) {
                return None;
            }
            let value = dataflow.block_entry_value(initializer.continuation, initializer.reg);
            let SsaValue::Phi(phi) = value else {
                return None;
            };
            let [left, right] = dataflow.phi_candidates[phi.index()].incoming.as_slice() else {
                return None;
            };
            let values = defs.map(SsaValue::Def);
            if [left.value, right.value] != values && [right.value, left.value] != values {
                return None;
            }
            let previous = dataflow.def_overwritten_value(defs[0])?;
            if dataflow.def_overwritten_value(defs[1]) != Some(previous) {
                return None;
            }
            let previous = canonical_value_temp(previous, dataflow.defs.len(), fixed, phis)?;
            let writes = defs.map(|def| fixed[def.index()]);
            for (temp, def) in writes.into_iter().zip(defs) {
                let site = dataflow.def_instr(def);
                if temp != TempId(def.index())
                    || epochs.epoch_at(initializer.reg, site) != home.epoch
                    || epochs.reference_capture_may_be_open(initializer.reg, site)
                {
                    return None;
                }
            }
            let result = canonical_value_temp(value, dataflow.defs.len(), fixed, phis)?;
            Some(SelectionWriteback {
                input,
                result,
                previous,
                home,
                literal_preparation: None,
                writes,
                truthy,
                falsy,
            })
        })();
        if let Some(frame) = candidate {
            frames
                .entry(frame.result)
                .and_modify(|entry| *entry = None)
                .or_insert(Some(frame));
        }
    }
    frames
        .into_iter()
        .filter_map(|(result, frame)| Some((result, frame?)))
        .collect()
}

#[derive(Debug, Clone, Copy)]
pub(super) struct ShortCircuitScalarFrame {
    pub(super) input: TempId,
    pub(super) kept: TempId,
    pub(super) alternative: TempId,
    pub(super) result: TempId,
    pub(super) logical_and: bool,
    pub(super) value: ShortCircuitScalarValue,
}

#[derive(Debug, Clone, Copy)]
pub(super) enum ShortCircuitScalarValue {
    Scalar(CopyRootScalarValue),
    CopyTemp(TempId),
    CopyParam(ParamId),
}

/// CALL 或 GETTABLE 的单结果直接保留或经单次 MOVE 写入 phi，另一臂写常量或读取已有低槽 binding。
/// 原两臂及 merge 必须由同一 predicate 拥有，不从最终表达式外形猜 COPY。
pub(super) fn collect_scalars(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    fixed: &[TempId],
    phis: &[TempId],
    predicates: &BTreeMap<PhiId, InstrRef>,
) -> BTreeMap<InstrRef, Option<ShortCircuitScalarFrame>> {
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
                || !match &proto.instrs[source.index()] {
                    LowInstr::Call(call) => {
                        call.results
                            == ResultPack::Fixed(crate::transformer::RegRange {
                                start: reg,
                                len: 1,
                            })
                    }
                    LowInstr::GetTable(read) => read.dst == reg,
                    _ => false,
                }
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
                        // 记录选中备用臂时读取的原 binding，而不是求左值前的快照。
                        match dataflow.use_value(site, movement.src) {
                            SsaValue::Entry(reg)
                                if reg.index() < usize::from(proto.signature.num_params) =>
                            {
                                ShortCircuitScalarValue::CopyParam(ParamId(reg.index()))
                            }
                            value => ShortCircuitScalarValue::CopyTemp(canonical_value_temp(
                                value,
                                dataflow.defs.len(),
                                fixed,
                                phis,
                            )?),
                        }
                    } else {
                        ShortCircuitScalarValue::Scalar(
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
                ShortCircuitScalarFrame {
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
