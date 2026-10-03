//! 保存冻结布尔测试和比较内取值叶中的上值读取身份与准备槽。
//! 消费 Structure 的互斥写回、条件图与 SSA 输入；后层仍核对整棵值树和声明前缀。

use super::*;
use crate::transformer::{BranchSubject, CondOperand, UpvalueOperand};

#[derive(Debug, Clone)]
pub(super) struct BooleanConditionFrame {
    pub(super) home: HomeSlotKey,
    pub(super) upvalues: BTreeMap<UpvalueId, operand_preparations::OperandPreparation>,
}

#[derive(Debug, Clone)]
pub(super) struct ValueUpvalueFrame {
    pub(super) home: HomeSlotKey,
    pub(super) upvalues: BTreeMap<UpvalueId, ValueUpvalueLeaf>,
}

#[derive(Debug, Clone)]
pub(in crate::hir) struct ValueUpvalueLeaf {
    pub(super) read: TempId,
    pub(in crate::hir) home: HomeSlotKey,
    pub(super) write: TempId,
    /// ANDK/ORK 的高槽读取经选择 COPY 到结果槽；直接 GETUPVAL 没有这一项。
    pub(in crate::hir) copy_and: Option<bool>,
}

/// 比较内的取值 phi 已由 Structure 冻结；保存 GETUPVAL 叶及选择 COPY 的原 Def。
/// 同一 cell 的多次读取没有 occurrence 身份时不签证，不能按上值名合并读取。
pub(super) fn collect_value_leaves(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    epochs: &SlotEpochFacts,
    fixed: &[TempId],
    phis: &[TempId],
) -> BTreeMap<TempId, ValueUpvalueFrame> {
    let mut frames = BTreeMap::new();
    for (_, decision) in plan.value_decisions() {
        for operand in &decision.operands {
            let candidate = (|| {
                let result = canonical_value_temp(
                    SsaValue::Phi(operand.phi),
                    dataflow.defs.len(),
                    fixed,
                    phis,
                )?;
                let reg = dataflow.phi_candidates[operand.phi.index()].reg;
                let mut seen = BTreeSet::new();
                let mut home = None;
                let mut upvalues = BTreeMap::new();
                for &leaf in operand.leaves.values() {
                    let SsaValue::Def(def) = leaf else {
                        return None;
                    };
                    if !seen.insert(def) {
                        continue;
                    }
                    let write_site = dataflow.def_instr(def);
                    let (read_def, copy_and) = if let LowInstr::Move(copy) =
                        proto.instrs[write_site.index()]
                    {
                        let SsaValue::Def(read_def) = dataflow.use_value(write_site, copy.src)
                        else {
                            return None;
                        };
                        let read_site = dataflow.def_instr(read_def);
                        let predicate = InstrRef(read_site.index() + 1);
                        let LowInstr::Branch(branch) = proto.instrs.get(predicate.index())? else {
                            return None;
                        };
                        if copy.dst != reg
                            || copy.src.index() != reg.index() + 1
                            || branch.cond.subject
                                != BranchSubject::Truthy(CondOperand::Reg(copy.src))
                            || dataflow.use_value(predicate, copy.src) != SsaValue::Def(read_def)
                        {
                            return None;
                        }
                        let (truthy, falsy) = if branch.cond.negated {
                            (branch.else_target, branch.then_target)
                        } else {
                            (branch.then_target, branch.else_target)
                        };
                        let and = if truthy == write_site {
                            false
                        } else if falsy == write_site {
                            true
                        } else {
                            return None;
                        };
                        (read_def, Some(and))
                    } else {
                        (def, None)
                    };
                    let site = dataflow.def_instr(read_def);
                    let LowInstr::GetUpvalue(read) = proto.instrs[site.index()] else {
                        continue;
                    };
                    let input_home =
                        HomeSlotKey::new(read.dst.index(), epochs.epoch_at(read.dst, site));
                    let output_home =
                        HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, write_site));
                    let temp = TempId(read_def.index());
                    let (UpvalueOperand::Env(upvalue) | UpvalueOperand::Upvalue(upvalue)) =
                        read.src;
                    if read.dst.index() != reg.index() + usize::from(copy_and.is_some())
                        || fixed[read_def.index()] != temp
                        || epochs.reference_capture_may_be_open(read.dst, site)
                        || epochs.reference_capture_may_be_open(reg, write_site)
                        || epochs.epoch_at(read.dst, write_site) != input_home.epoch
                        || home.is_some_and(|home| home != output_home)
                        || upvalues
                            .insert(
                                UpvalueId(upvalue.index()),
                                ValueUpvalueLeaf {
                                    read: temp,
                                    home: input_home,
                                    write: TempId(def.index()),
                                    copy_and,
                                },
                            )
                            .is_some()
                    {
                        return None;
                    }
                    home = Some(output_home);
                }
                Some((
                    result,
                    ValueUpvalueFrame {
                        home: home?,
                        upvalues,
                    },
                ))
            })();
            if let Some((result, frame)) = candidate {
                frames
                    .entry(result)
                    .and_modify(|entry| *entry = None)
                    .or_insert(Some(frame));
            }
        }
    }
    frames
        .into_iter()
        .filter_map(|(result, frame)| frame.map(|frame| (result, frame)))
        .collect()
}

pub(super) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
) -> BTreeMap<TempId, BooleanConditionFrame> {
    let mut frames = BTreeMap::new();
    for (owner, _) in plan.regions() {
        let candidate = (|| {
            let initializer = plan.boolean_initializer(owner, proto, cfg, dataflow)?;
            let value = dataflow.block_entry_value(initializer.continuation, initializer.reg);
            let SsaValue::Phi(phi) = value else {
                return None;
            };
            let [left, right] = dataflow.phi_candidates[phi.index()].incoming.as_slice() else {
                return None;
            };
            let defs = initializer.defs.map(SsaValue::Def);
            if [left.value, right.value] != defs && [right.value, left.value] != defs {
                // FactGap：当前条件必须拥有完整结果，不接受还含其它入口写入的合流。
                return None;
            }
            let result = canonical_value_temp(value, dataflow.defs.len(), fixed_temps, phi_temps)?;
            let first = dataflow.def_instr(initializer.defs[0]);
            let home = HomeSlotKey::new(
                initializer.reg.index(),
                epochs.epoch_at(initializer.reg, first),
            );
            if initializer.defs.iter().any(|&def| {
                let site = dataflow.def_instr(def);
                epochs.epoch_at(initializer.reg, site) != home.epoch
                    || epochs.reference_capture_may_be_open(initializer.reg, site)
            }) {
                return None;
            }
            let mut upvalues = BTreeMap::new();
            for node in &plan.condition(initializer.condition)?.nodes {
                let LowInstr::Branch(branch) = &proto.instrs[node.predicate.index()] else {
                    return None;
                };
                let BranchSubject::Truthy(CondOperand::Reg(reg)) = branch.cond.subject else {
                    // FactGap：比较操作数已有独立准备协议，不借本证书推断复合比较的槽。
                    return None;
                };
                if node.materialized_value.is_some() {
                    return None;
                }
                let input = operand_preparations::collect(
                    proto,
                    cfg,
                    dataflow,
                    epochs,
                    fixed_temps,
                    node.predicate,
                    reg,
                )?;
                if input.home != home {
                    // 只签发所有原谓词都在同一结果槽准备的帧；不移动高槽残根。
                    return None;
                }
                match &proto.instrs[input.read.index()] {
                    LowInstr::GetUpvalue(get) => {
                        let (UpvalueOperand::Env(upvalue) | UpvalueOperand::Upvalue(upvalue)) =
                            get.src;
                        if upvalues.insert(UpvalueId(upvalue.index()), input).is_some() {
                            // FactGap：同一 cell 的多次读取需要逐测试来源，不能按名字合并。
                            return None;
                        }
                    }
                    LowInstr::Call(_) => {}
                    _ => return None,
                }
            }
            (!upvalues.is_empty()).then_some((result, BooleanConditionFrame { home, upvalues }))
        })();
        if let Some((result, frame)) = candidate {
            frames
                .entry(result)
                .and_modify(|entry| *entry = None)
                .or_insert(Some(frame));
        }
    }
    frames
        .into_iter()
        .filter_map(|(result, frame)| frame.map(|frame| (result, frame)))
        .collect()
}
