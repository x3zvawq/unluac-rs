//! 查询冻结条件的互斥单值写回，供 HIR 来源、debug 身份和初始化绑定共同消费。
//! 这里只证明原条件、互斥写入和汇合关系；物理槽 epoch 与源码绑定仍由 HIR 校验。

use super::*;
use crate::structure::DefId;
use crate::transformer::{BranchSubject, InstrRef, LowInstr, Reg};

pub(crate) struct BranchInitializer {
    pub defs: [DefId; 2],
    pub condition: ConditionPlanId,
    pub condition_inverted: bool,
    pub reg: Reg,
    pub entry: BlockRef,
    pub continuation: BlockRef,
}

pub(crate) struct ComparisonInitializer {
    pub defs: [DefId; 2],
    pub predicate: InstrRef,
    pub reg: Reg,
    pub entry: BlockRef,
    pub continuation: BlockRef,
}

impl StructurePlan {
    /// 外层值决策可吸收一次比较；两条弧仍须各自只写 Boolean 并直接汇入同一结果。
    pub(crate) fn decision_comparison_initializers<'a>(
        &'a self,
        proto: &'a LoweredProto,
        cfg: &'a Cfg,
        dataflow: &'a DataflowFacts,
    ) -> impl Iterator<Item = ComparisonInitializer> + 'a {
        self.value_decisions().flat_map(move |(_, decision)| {
            decision.nodes.iter().filter_map(move |node| {
                if !matches!(&proto.instrs[node.predicate.index()], LowInstr::Branch(branch)
                    if matches!(branch.cond.subject, BranchSubject::Compare { .. }))
                {
                    return None;
                }
                let arm = |arc: &ValueDecisionArcPlan| {
                    let ValueDecisionTarget::Leaf(id) = arc.target else {
                        return None;
                    };
                    let [entry, terminal] = arc.route.as_slice() else {
                        return None;
                    };
                    let leaf = &decision.leaves[id.index()];
                    if cfg.edges[entry.index()].from != node.block
                        || cfg.edges[entry.index()].to != leaf.block
                        || *terminal != leaf.terminal_edge
                        || leaf.physical_pred != leaf.block
                        || leaf.physical_value != leaf.value
                    {
                        return None;
                    }
                    let def = self.direct_arm_write(leaf.block, decision.merge, cfg, dataflow)?;
                    (leaf.value == SsaValue::Def(def)
                        && leaf.latest_local_def == Some(def)
                        && dataflow.def_reg(def) == decision.result_reg)
                        .then_some(def)
                };
                let defs = [arm(&node.truthy)?, arm(&node.falsy)?];
                let [left, right] = defs.map(|def| &proto.instrs[dataflow.def_instr(def).index()]);
                if !matches!((left, right), (LowInstr::LoadBool(left), LowInstr::LoadBool(right))
                    if left.value != right.value)
                {
                    return None;
                }
                Some(ComparisonInitializer {
                    defs,
                    predicate: node.predicate,
                    reg: decision.result_reg,
                    entry: node.block,
                    continuation: decision.merge,
                })
            })
        })
    }

    fn direct_arm_write(
        &self,
        block: BlockRef,
        continuation: BlockRef,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
    ) -> Option<DefId> {
        let terminator = self.block_terminator(block)?;
        let edge = match terminator.kind {
            BlockTerminatorKind::Linear { edge: Some(edge) }
            | BlockTerminatorKind::Jump { edge, .. } => edge,
            _ => return None,
        };
        let range = terminator.instrs;
        if cfg.edges[edge.index()].to != continuation
            || range.len != 1 + usize::from(terminator.kind.instr().is_some())
        {
            // SemanticBarrier:ControlFlow：臂内只允许一次结果写入及直接汇合。
            return None;
        }
        let [def] = dataflow.instr_defs[range.start.index()].as_slice() else {
            return None;
        };
        Some(*def)
    }

    /// 未使用的新槽初始化仍保留原限制；一般比较写回事实不能授权建立新的源码身份。
    pub(crate) fn unused_comparison_initializer(
        &self,
        owner: RegionId,
        proto: &LoweredProto,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
    ) -> Option<ComparisonInitializer> {
        let initializer = self.comparison_initializer(owner, proto, cfg, dataflow)?;
        let reg = initializer.reg;
        if reg.index() < usize::from(proto.signature.num_params)
            || proto.signature.has_vararg_param_reg
                && reg.index() == usize::from(proto.signature.num_params)
            || dataflow.reg_is_captured(reg)
            || initializer.defs.iter().any(|def| {
                !dataflow.def_uses[def.index()].is_empty()
                    || !dataflow.def_phi_uses[def.index()].is_empty()
                    || dataflow.def_overwritten_value(*def) != Some(SsaValue::Entry(reg))
            })
        {
            // 候选拒绝[SemanticBarrier:Binding]：已占用的源码槽和有读者的结果沿用现有 owner。
            return None;
        }
        Some(initializer)
    }

    pub(crate) fn comparison_initializer(
        &self,
        owner: RegionId,
        proto: &LoweredProto,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
    ) -> Option<ComparisonInitializer> {
        let initializer = self.boolean_initializer(owner, proto, cfg, dataflow)?;
        let condition = self.condition(initializer.condition)?;
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
        Some(ComparisonInitializer {
            defs: initializer.defs,
            predicate: node.predicate,
            reg: initializer.reg,
            entry: initializer.entry,
            continuation: initializer.continuation,
        })
    }

    /// 冻结条件可以含多个测试；两臂仅写互斥 Boolean 后汇合，不签发输入求值或槽位许可。
    pub(crate) fn boolean_initializer(
        &self,
        owner: RegionId,
        proto: &LoweredProto,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
    ) -> Option<BranchInitializer> {
        let initializer = self.branch_initializer(owner, cfg, dataflow)?;
        let [left, right] = initializer
            .defs
            .map(|def| &proto.instrs[dataflow.def_instr(def).index()]);
        (matches!((left, right), (LowInstr::LoadBool(left), LowInstr::LoadBool(right))
            if left.value != right.value))
        .then_some(initializer)
    }

    /// 两臂各有一个固定写入并直接汇合；不证明值类别、求值效果或声明身份。
    pub(crate) fn branch_initializer(
        &self,
        owner: RegionId,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
    ) -> Option<BranchInitializer> {
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
        let branch = self.branch(*branch)?;
        let arm_value = |arm| {
            let &[block] = self.region_blocks(arm) else {
                return None;
            };
            let def = self.direct_arm_write(block, *continuation, cfg, dataflow)?;
            Some((def, dataflow.def_reg(def)))
        };
        let (then_def, then_value) = arm_value(*then_arm)?;
        let (else_def, else_value) = arm_value(*else_arm)?;
        (then_value == else_value).then_some(BranchInitializer {
            defs: [then_def, else_def],
            condition: branch.condition,
            condition_inverted: branch.condition_inverted,
            reg: then_value,
            entry: *entry,
            continuation: *continuation,
        })
    }
}
