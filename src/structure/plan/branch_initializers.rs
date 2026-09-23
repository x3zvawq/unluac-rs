//! 查询冻结分支中未进入 SSA 合流的比较初始化，供 debug 身份及 HIR 绑定共同消费。
//! 这里只证明原比较、互斥写入和汇合关系；物理槽 epoch 与源码绑定仍由 HIR 校验。

use super::*;
use crate::structure::DefId;
use crate::transformer::{BranchSubject, InstrRef, LowInstr, Reg};

pub(crate) struct UnusedComparisonInitializer {
    pub defs: [DefId; 2],
    pub predicate: InstrRef,
    pub reg: Reg,
    pub entry: BlockRef,
    pub continuation: BlockRef,
}

impl StructurePlan {
    pub(crate) fn unused_comparison_initializer(
        &self,
        owner: RegionId,
        proto: &LoweredProto,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
    ) -> Option<UnusedComparisonInitializer> {
        let RegionPlan::Branch {
            plan: branch,
            entry,
            then_arm,
            else_arm: Some(else_arm),
            continuation: Some(continuation),
            ..
        } = self.region(owner)?
        else {
            return None;
        };
        let condition = self.condition(self.branch(*branch)?.condition)?;
        let [node] = condition.nodes.as_slice() else {
            return None;
        };
        if node.materialized_value.is_some()
            || !matches!(proto.instrs[node.predicate.index()], LowInstr::Branch(ref branch)
                if matches!(branch.cond.subject, BranchSubject::Compare { .. }))
        {
            // FactGap：普通 truth test 或多节点条件不证明一次比较结果的初始化。
            return None;
        }
        let arm_value = |arm| {
            let &[block] = self.region_blocks(arm) else {
                return None;
            };
            let terminator = self.block_terminator(block)?;
            let edge = match terminator.kind {
                BlockTerminatorKind::Linear { edge: Some(edge) }
                | BlockTerminatorKind::Jump { edge, .. } => edge,
                _ => return None,
            };
            let range = terminator.instrs;
            if cfg.edges[edge.index()].to != *continuation
                || range.len != 1 + usize::from(terminator.kind.instr().is_some())
            {
                // SemanticBarrier:ControlFlow：两臂必须只初始化结果并直接汇合。
                return None;
            }
            let LowInstr::LoadBool(value) = proto.instrs[range.start.index()] else {
                return None;
            };
            let def = dataflow.instr_def_for_reg(range.start, value.dst)?;
            if value.dst.index() < usize::from(proto.signature.num_params)
                || (proto.signature.has_vararg_param_reg
                    && value.dst.index() == usize::from(proto.signature.num_params))
                || dataflow.reg_is_captured(value.dst)
                || !dataflow.def_uses[def.index()].is_empty()
                || !dataflow.def_phi_uses[def.index()].is_empty()
                || dataflow.def_overwritten_value(def) != Some(SsaValue::Entry(value.dst))
            {
                // SemanticBarrier:Binding：已占用的源码槽和有读者的结果沿用现有 owner。
                // 比较留下的 VM scratch 仍由同槽写入覆盖，这不证明可提前清根。
                return None;
            }
            Some((def, value))
        };
        let (then_def, then_value) = arm_value(*then_arm)?;
        let (else_def, else_value) = arm_value(*else_arm)?;
        (then_value.dst == else_value.dst && then_value.value != else_value.value).then_some(
            UnusedComparisonInitializer {
                defs: [then_def, else_def],
                predicate: node.predicate,
                reg: then_value.dst,
                entry: *entry,
                continuation: *continuation,
            },
        )
    }
}
