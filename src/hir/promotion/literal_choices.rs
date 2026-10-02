//! 冻结按输入真值或标量比较选择常量的原决策帧，供展开调用恢复消费。
//!
//! 输入沿 SSA 版本连接，叶写和结果 phi 保持各自身份；仅发布没有额外事件的完整决策域。

use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::hir) enum LiteralChoiceTest {
    Truthy,
    EqualNil,
    EqualBoolean(bool),
}

#[derive(Debug, Clone)]
pub(in crate::hir) struct LiteralChoice {
    pub(in crate::hir) source: InstrRef,
    /// 所有常量叶汇合后的 exclusive 边界，不包含消费该结果的指令。
    pub(in crate::hir) end: InstrRef,
    pub(in crate::hir) result: TempId,
    pub(in crate::hir) inputs: Vec<TempId>,
    pub(in crate::hir) tests: Vec<LiteralChoiceTest>,
    pub(in crate::hir) predicates: Vec<InstrRef>,
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
) -> BTreeMap<TempId, LiteralChoice> {
    use crate::structure::ValueDecisionTarget;
    use crate::transformer::{BranchSubject, CondOperand};
    let mut choices = BTreeMap::new();
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
            let mut tests = Vec::new();
            let mut predicates = Vec::new();
            let mut leaves = Vec::new();
            let mut id = decision.entry;
            let mut nodes = BTreeSet::new();
            loop {
                let node = decision.nodes.get(id.index())?;
                let LowInstr::Branch(branch) = &proto.instrs[node.predicate.index()] else {
                    return None;
                };
                let (reg, test) = match branch.cond.subject {
                    BranchSubject::Truthy(CondOperand::Reg(reg)) => {
                        (reg, LiteralChoiceTest::Truthy)
                    }
                    BranchSubject::Compare {
                        predicate: crate::transformer::BranchPredicate::Eq,
                        lhs: CondOperand::Reg(reg),
                        rhs: CondOperand::Nil,
                    } => (reg, LiteralChoiceTest::EqualNil),
                    BranchSubject::Compare {
                        predicate: crate::transformer::BranchPredicate::Eq,
                        lhs: CondOperand::Reg(reg),
                        rhs: CondOperand::Boolean(value),
                    } => (reg, LiteralChoiceTest::EqualBoolean(value)),
                    _ => return None,
                };
                let range = cfg.blocks[node.block.index()].instrs;
                if !nodes.insert(id)
                    || node.predicate_negated != branch.cond.negated
                    || range.end() != node.predicate.index() + 1
                    || id != decision.entry && range.start != node.predicate
                {
                    return None;
                }
                inputs.push(canonical_value_temp(
                    dataflow.use_value(node.predicate, reg),
                    dataflow.defs.len(),
                    fixed,
                    phis,
                )?);
                tests.push(test);
                predicates.push(node.predicate);
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
                end: merge,
                result: canonical_value_temp(
                    SsaValue::Phi(decision.result_phi),
                    dataflow.defs.len(),
                    fixed,
                    phis,
                )?,
                inputs,
                tests,
                predicates,
                values,
                writes,
            })
        })();
        if let Some(choice) = candidate {
            choices.insert(choice.result, choice);
        }
        for operand in &decision.operands {
            if let Some(choice) =
                comparison_operand(proto, cfg, dataflow, decision, operand, fixed, phis)
            {
                choices.insert(choice.result, choice);
            }
        }
    }

    choices
}

/// 内嵌 phi 的叶值已由 Structure 投影到每条原弧；不重新展开其它操作数或猜合流输入。
fn comparison_operand(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    decision: &crate::structure::ValueDecisionPlan,
    operand: &crate::structure::ValueDecisionOperandPlan,
    fixed: &[TempId],
    phis: &[TempId],
) -> Option<LiteralChoice> {
    use crate::structure::ValueDecisionTarget;
    use crate::transformer::{BranchPredicate, BranchSubject, CondOperand};
    if !operand.current_values.is_empty() || decision.loop_entry.is_some() {
        return None;
    }
    let mut nodes = BTreeSet::new();

    let mut id = operand.entry;
    let mut inputs = Vec::new();
    let mut tests = Vec::new();
    let mut predicates = Vec::new();
    let mut leaves = Vec::new();
    loop {
        let node = decision.nodes.get(id.index())?;
        let LowInstr::Branch(branch) = &proto.instrs[node.predicate.index()] else {
            return None;
        };
        let (reg, test) = match branch.cond.subject {
            BranchSubject::Compare {
                predicate: BranchPredicate::Eq,
                lhs: CondOperand::Reg(reg),
                rhs: CondOperand::Nil,
            } => (reg, LiteralChoiceTest::EqualNil),
            BranchSubject::Compare {
                predicate: BranchPredicate::Eq,
                lhs: CondOperand::Reg(reg),
                rhs: CondOperand::Boolean(value),
            } => (reg, LiteralChoiceTest::EqualBoolean(value)),
            _ => return None,
        };
        let range = cfg.blocks[node.block.index()].instrs;
        // Plan lowering 在决策前单独发射入口前缀；其准备仍须由 FrameBuilder 完整消费。
        // 其它条件块不能夹带操作，否则这份纯选值证书会遗漏路径内的事件。
        if !nodes.insert(id)
            || range.end() != node.predicate.index() + 1
            || id != decision.entry && range.start != node.predicate
            || node.predicate_negated != branch.cond.negated
            || node.truthy.target != ValueDecisionTarget::Node(operand.continuation)
        {
            return None;
        }
        inputs.push(canonical_value_temp(
            dataflow.use_value(node.predicate, reg),
            dataflow.defs.len(),
            fixed,
            phis,
        )?);

        tests.push(test);
        predicates.push(node.predicate);
        leaves.push(
            *operand
                .route_values
                .get(&(id, *node.truthy.route.first()?))?,
        );
        match node.falsy.target {
            ValueDecisionTarget::Node(next) if next != operand.continuation => id = next,
            ValueDecisionTarget::Node(_) => {
                leaves.push(
                    *operand
                        .route_values
                        .get(&(id, *node.falsy.route.first()?))?,
                );
                break;
            }
            _ => return None,
        }
    }
    if nodes.len() != operand.nodes.len()
        || operand.nodes.iter().any(|node| !nodes.contains(node))
        || leaves.len() != operand.leaves.len()
    {
        return None;
    }
    let merge = decision.nodes.get(operand.continuation.index())?.predicate;
    let result_reg = dataflow.phi_candidate(operand.phi)?.reg;
    let mut values = Vec::new();
    let mut writes = Vec::new();

    for value in leaves {
        let SsaValue::Def(def) = value else {
            return None;
        };
        let source = dataflow.def_instr(def);

        let (reg, value) = copy_assignments::scalar_literal(proto, &proto.instrs[source.index()])?;
        let range = cfg.blocks[cfg.instr_to_block[source.index()].index()].instrs;
        if reg != result_reg
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
        source: decision.nodes[operand.entry.index()].predicate,
        end: merge,
        result: canonical_value_temp(SsaValue::Phi(operand.phi), dataflow.defs.len(), fixed, phis)?,
        inputs,
        tests,
        predicates,
        values,
        writes,
    })
}
