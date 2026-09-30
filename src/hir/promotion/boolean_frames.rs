//! 保存冻结布尔结果中上值测试的原读取身份与准备槽。
//! 消费 Structure 的互斥写回、条件图与 SSA 输入；后层仍核对整棵值树和声明前缀。

use super::*;
use crate::transformer::{BranchSubject, CondOperand, UpvalueOperand};

#[derive(Debug, Clone)]
pub(super) struct BooleanConditionFrame {
    pub(super) home: HomeSlotKey,
    pub(super) upvalues: BTreeMap<UpvalueId, operand_preparations::OperandPreparation>,
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
