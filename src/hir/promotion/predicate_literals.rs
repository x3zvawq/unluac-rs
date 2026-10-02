//! 保存原布尔字面量定义与唯一 TEST 使用之间的 SSA 关系。
//!
//! 事实绑定原指令，不授权移动当前 HIR 条件；消费者另证当前绑定、效果顺序和声明前缀。

use super::*;

#[derive(Clone, Copy, Debug)]
pub(in crate::hir) struct LiteralPredicate {
    pub definition: InstrRef,
    pub input: TempId,
    pub home: HomeSlotKey,
    pub value: bool,
}

pub(super) fn collect(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed: &[TempId],
) -> BTreeMap<InstrRef, LiteralPredicate> {
    use crate::transformer::{BranchSubject, CondOperand};
    proto
        .instrs
        .iter()
        .enumerate()
        .filter_map(|(index, instruction)| {
            let LowInstr::Branch(branch) = instruction else {
                return None;
            };
            let BranchSubject::Truthy(CondOperand::Reg(reg)) = branch.cond.subject else {
                return None;
            };
            let predicate = InstrRef(index);
            let SsaValue::Def(def) = dataflow.use_value(predicate, reg) else {
                return None;
            };
            let definition = dataflow.def_instr(def);
            let LowInstr::LoadBool(load) = &proto.instrs[definition.index()] else {
                return None;
            };
            let uses = &dataflow.def_uses[def.index()];
            if fixed[def.index()] != TempId(def.index())
                || uses.len() != 1
                || uses[0].instr != predicate
                || !dataflow.def_phi_uses[def.index()].is_empty()
                || load.dst != reg
            {
                return None;
            }
            Some((
                predicate,
                LiteralPredicate {
                    definition,
                    input: fixed[def.index()],
                    home: HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, definition)),
                    value: load.value,
                },
            ))
        })
        .collect()
}
