//! 短路查表值的原分支、分配与合流身份。
//!
//! Structure 的单 predicate phi 和 SSA Def 证明 `input.key or {}` 只在假值臂
//! 分配备用表，三次值写都属于同一物理结果槽。这里不恢复表达式或签发根退休；
//! 完整帧消费者仍须核对当前查表输入、备用表及源码准备位置。

use super::*;

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
) -> BTreeMap<(InstrRef, InstrRef), Option<ShortCircuitTableFrame>> {
    let mut frames = BTreeMap::new();
    for phi in plan.phis() {
        let candidate = || {
            let predicate = single_phi_predicate(plan, phi)?;
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
