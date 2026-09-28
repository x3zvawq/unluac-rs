//! 冻结原 CFG 中由字面量定义证明不可执行的边。
//!
//! 消费 SSA 与观察事实，供物理状态分析查询；保留原控制结构身份。

use super::super::common::{EdgeKind, InstrUseValues};
use super::*;
use crate::parser::RawLiteralConst;

pub(super) struct ExecutionFacts {
    pub(super) blocks: Vec<bool>,
    pub(super) edges: Vec<bool>,
}

pub(super) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    defs: &[Def],
    uses: &[InstrUseValues],
    captures: &[RegCaptures],
    roots: &super::super::common::RootIntervalIndex,
) -> ExecutionFacts {
    let mut edges = vec![true; cfg.edges.len()];
    for &block in &cfg.block_order {
        let Some(last) = cfg.blocks[block.index()].instrs.last() else {
            continue;
        };
        let LowInstr::Branch(branch) = &proto.instrs[last.index()] else {
            continue;
        };
        let BranchSubject::Truthy(operand) = branch.cond.subject else {
            continue;
        };
        let truthy = match operand {
            CondOperand::Nil => Some(false),
            CondOperand::Boolean(value) => Some(value),
            CondOperand::Integer(_) | CondOperand::Number(_) => Some(true),
            CondOperand::Const(value) => proto.constants.get(value.index()).map(literal_truthy),
            CondOperand::Reg(reg) if !captures[reg.index()].by_reference => {
                match uses[last.index()].fixed.get(reg) {
                    Some(SsaValue::Def(def))
                        if defs[def.index()].block == block
                            && !roots.has_observation(
                                defs[def.index()].instr.index() + 1..last.index(),
                            ) =>
                    {
                        match &proto.instrs[defs[def.index()].instr.index()] {
                            LowInstr::LoadNil(_) => Some(false),
                            LowInstr::LoadBool(value) => Some(value.value),
                            LowInstr::LoadInteger(_) | LowInstr::LoadNumber(_) => Some(true),
                            LowInstr::LoadConst(value) => {
                                proto.constants.get(value.value.index()).map(literal_truthy)
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        let Some(taken) = truthy.map(|value| value != branch.cond.negated) else {
            continue;
        };
        for &edge in &cfg.succs[block.index()] {
            edges[edge.index()] = match cfg.edges[edge.index()].kind {
                EdgeKind::BranchTrue => taken,
                EdgeKind::BranchFalse => !taken,
                _ => true,
            };
        }
    }
    let mut blocks = vec![false; cfg.blocks.len()];
    blocks[cfg.entry_block.index()] = true;
    let mut pending = vec![cfg.entry_block];
    while let Some(block) = pending.pop() {
        for &edge in &cfg.succs[block.index()] {
            let next = cfg.edges[edge.index()].to;
            if edges[edge.index()] && !blocks[next.index()] {
                blocks[next.index()] = true;
                pending.push(next);
            }
        }
    }
    ExecutionFacts { blocks, edges }
}

fn literal_truthy(value: &RawLiteralConst) -> bool {
    !matches!(
        value,
        RawLiteralConst::Nil | RawLiteralConst::Boolean(false)
    )
}
