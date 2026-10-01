//! 冻结按输入真值选择常量的原决策帧，供展开调用恢复消费。
//!
//! 输入沿 SSA 版本连接，叶写和结果 phi 保持各自身份；仅发布没有额外事件的完整决策域。

use super::*;

#[derive(Debug, Clone)]
pub(in crate::hir) struct LiteralChoice {
    pub(in crate::hir) source: InstrRef,
    pub(in crate::hir) result: TempId,
    pub(in crate::hir) inputs: Vec<TempId>,
    pub(in crate::hir) values: Vec<HirExpr>,
    writes: Vec<TempId>,
}

impl LiteralChoice {
    pub(super) fn valid(&self, facts: &ProtoPromotionFacts) -> bool {
        let Some(home) = facts.trusted_temp_home_slot(self.result) else {
            return false;
        };
        self.inputs
            .iter()
            .all(|&input| facts.trusted_temp_home_slot(input).is_some())
            && self
                .writes
                .iter()
                .all(|&write| facts.trusted_temp_home_slot(write) == Some(home))
    }
}

pub(super) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    fixed: &[TempId],
    phis: &[TempId],
) -> Vec<LiteralChoice> {
    use crate::structure::ValueDecisionTarget;
    use crate::transformer::{BranchSubject, CondOperand};
    let mut choices = Vec::new();
    for (_, decision) in plan.value_decisions() {
        let candidate = (|| {
            if !decision.operands.is_empty()
                || !decision.absorbed_phis.is_empty()
                || decision.loop_entry.is_some()
                || decision.leaves.len() != decision.nodes.len() + 1
            {
                return None;
            }
            let mut inputs = Vec::new();
            let mut leaves = Vec::new();
            let mut id = decision.entry;
            let mut nodes = BTreeSet::new();
            loop {
                let node = decision.nodes.get(id.index())?;
                let LowInstr::Branch(branch) = &proto.instrs[node.predicate.index()] else {
                    return None;
                };
                let BranchSubject::Truthy(CondOperand::Reg(reg)) = branch.cond.subject else {
                    return None;
                };
                let range = cfg.blocks[node.block.index()].instrs;
                if !nodes.insert(id)
                    || node.predicate_negated != branch.cond.negated
                    || range.start != node.predicate
                    || range.len != 1
                {
                    return None;
                }
                inputs.push(canonical_value_temp(
                    dataflow.use_value(node.predicate, reg),
                    dataflow.defs.len(),
                    fixed,
                    phis,
                )?);
                let ValueDecisionTarget::Leaf(truthy) = node.truthy.target else {
                    return None;
                };
                leaves.push(truthy);
                match node.falsy.target {
                    ValueDecisionTarget::Node(next) => id = next,
                    ValueDecisionTarget::Leaf(falsy) => {
                        leaves.push(falsy);
                        break;
                    }
                    _ => return None,
                }
            }
            if nodes.len() != decision.nodes.len()
                || leaves.iter().copied().collect::<BTreeSet<_>>().len() != decision.leaves.len()
                || decision.blocks.len() != nodes.len() + leaves.len()
            {
                return None;
            }
            let mut values = Vec::new();
            let mut writes = Vec::new();
            let merge = cfg.blocks[decision.merge.index()].instrs.start;
            for leaf in leaves {
                let leaf = &decision.leaves[leaf.index()];
                let SsaValue::Def(def) = leaf.value else {
                    return None;
                };
                let source = dataflow.def_instr(def);
                let instr = &proto.instrs[source.index()];
                let (reg, value) = match instr {
                    LowInstr::LoadConst(load)
                        if matches!(
                            proto.constants[load.value.index()],
                            crate::parser::RawLiteralConst::Vector(_)
                        ) =>
                    {
                        let crate::parser::RawLiteralConst::Vector(value) =
                            proto.constants[load.value.index()]
                        else {
                            unreachable!();
                        };
                        (load.dst, HirExpr::Vector(value))
                    }
                    _ => copy_assignments::scalar_literal(proto, instr)?,
                };
                let range = cfg.blocks[leaf.block.index()].instrs;
                if reg != decision.result_reg
                    || range.start != source
                    || !match range.len {
                        1 => source.index() + 1 == merge.index(),
                        2 => {
                            matches!(proto.instrs[source.index()+1], LowInstr::Jump(jump) if jump.target == merge)
                        }
                        _ => false,
                    }
                {
                    return None;
                }
                writes.push(canonical_value_temp(
                    SsaValue::Def(def),
                    dataflow.defs.len(),
                    fixed,
                    phis,
                )?);
                values.push(value);
            }
            Some(LiteralChoice {
                source: decision.nodes[decision.entry.index()].predicate,
                result: canonical_value_temp(
                    SsaValue::Phi(decision.result_phi),
                    dataflow.defs.len(),
                    fixed,
                    phis,
                )?,
                inputs,
                values,
                writes,
            })
        })();
        choices.extend(candidate);
    }
    choices
}
