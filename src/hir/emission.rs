//! 查询冻结 Structure plan 中仍由 HIR 单独发射的指令域与词法 owner。
//!
//! region 父子关系、条件和值判定的 header、循环协议均由 Structure 发布；这里仅投影
//! HIR lowering 的消费边界，不重新分析 CFG，也不把已吸收的表达式节点当作独立语句。
//! 例如 `a and b()` 的后续条件块进入 decision expression，只有 header 前缀逐指令
//! 发射；需要在精确 low 位置恢复作用域或 root 退休时，必须先排除这些非 header 位置。
//! 本查询不包含 HIR global declaration 等后续批量发射协议，它们仍需保护内部边界。

use std::collections::BTreeSet;
use std::ops::Range;

use crate::structure::{
    BlockEmissionPlan, BlockRef, LoopVmProtocol, RegionId, RegionPlan, StructurePlan,
};
use crate::transformer::InstrRef;

pub(super) struct HirEmissionFacts<'a> {
    plan: &'a StructurePlan,
    regions: Vec<RegionEmission>,
    for_instrs: BTreeSet<InstrRef>,
}

#[derive(Clone, Copy)]
struct RegionEmission {
    ordinary: bool,
    prefix_allowed: bool,
    prefix_header: Option<BlockRef>,
    scope_owner: RegionId,
}

impl RegionEmission {
    fn restrict_header(&mut self, header: Option<BlockRef>) {
        self.prefix_allowed &=
            header.is_some_and(|header| self.prefix_header.is_none_or(|prior| prior == header));
        self.prefix_header = header;
    }
}

impl<'a> HirEmissionFacts<'a> {
    pub(super) fn new(plan: &'a StructurePlan) -> Self {
        let unrestricted = RegionEmission {
            ordinary: true,
            prefix_allowed: true,
            prefix_header: None,
            scope_owner: plan.root(),
        };
        let mut regions = vec![unrestricted; plan.regions().len()];
        let mut for_instrs = BTreeSet::new();
        for (id, _) in plan.loops() {
            match plan.loop_protocol(id) {
                Some(LoopVmProtocol::NumericFor(protocol)) => {
                    for_instrs.insert(protocol.init_instr);
                    for_instrs.extend(protocol.loop_instr);
                }
                Some(LoopVmProtocol::GenericFor(protocol)) => {
                    for_instrs.extend(protocol.prep_instr);
                    for_instrs.extend([protocol.call_instr, protocol.loop_instr]);
                }
                _ => {}
            }
        }
        for &region in plan.region_postorder().iter().rev() {
            let node = plan
                .region(region)
                .expect("ready region order retains every node");
            let mut state = node
                .parent()
                .map_or(unrestricted, |parent| regions[parent.index()]);
            if let Some(parent) = node.parent().and_then(|parent| plan.region(parent)) {
                // 条件前缀与循环外前缀仍属于外围语法块；arm/body 是独立词法 owner。
                match parent {
                    RegionPlan::Branch {
                        then_arm, else_arm, ..
                    } if *then_arm == region || *else_arm == Some(region) => {
                        state.scope_owner = region
                    }
                    RegionPlan::Loop {
                        body,
                        control,
                        normal_tail,
                        ..
                    } => {
                        if *body == region || *control == region {
                            state.scope_owner = *body;
                        } else if *normal_tail == Some(region) {
                            state.scope_owner = region;
                        }
                    }
                    _ => {}
                }
                match parent {
                    RegionPlan::Branch {
                        plan: branch,
                        condition,
                        ..
                    } if *condition == region => {
                        state.restrict_header(
                            plan.branch(*branch)
                                .and_then(|branch| plan.condition(branch.condition))
                                .and_then(|condition| condition.header()),
                        );
                    }
                    RegionPlan::Loop {
                        plan: loop_id,
                        control,
                        ..
                    } if *control == region => {
                        // while/repeat 的首条件块经 lower_condition_prefix 单独发射；
                        // 只有后续条件节点被吸收进 decision expression。
                        state.restrict_header(
                            plan.loop_(*loop_id)
                                .and_then(|payload| payload.condition)
                                .and_then(|condition| plan.condition(condition))
                                .and_then(|condition| condition.header()),
                        );
                    }
                    _ => {}
                }
            }
            if let RegionPlan::ValueDecision { plan: decision, .. } = node {
                state.restrict_header(
                    plan.value_decision(*decision)
                        .and_then(|value| value.header()),
                );
            }
            state.ordinary &= !matches!(
                node,
                RegionPlan::Unstructured { .. } | RegionPlan::ValueDecision { .. }
            ) && plan.single_pass_for_region(region).is_none();
            regions[region.index()] = state;
        }
        Self {
            plan,
            regions,
            for_instrs,
        }
    }

    pub(super) fn scope_owner(&self, block: BlockRef) -> Option<RegionId> {
        let owner = self.plan.region_for_block(block)?;
        Some(self.regions[owner.index()].scope_owner)
    }

    /// 两端必须由 regular/header prefix 发射，不能切入被吸收的表达式或 loop 绑定。
    pub(super) fn regular_prefix(&self, block: BlockRef) -> Option<Range<usize>> {
        let plan = self.plan;
        if plan.block_emission(block) != Some(BlockEmissionPlan::Emit) {
            return None;
        }
        let owner = plan.region_for_block(block)?;
        let state = self.regions[owner.index()];
        if !state.prefix_allowed || state.prefix_header.is_some_and(|header| header != block) {
            return None;
        }
        let terminator = plan.block_terminator(block)?;
        Some(
            terminator.instrs.start.index()
                ..terminator
                    .kind
                    .instr()
                    .map_or(terminator.instrs.end(), InstrRef::index),
        )
    }

    pub(super) fn ordinary_block(&self, block: BlockRef) -> bool {
        self.plan
            .region_for_block(block)
            .is_some_and(|owner| self.regions[owner.index()].ordinary)
    }

    pub(super) fn for_instr(&self, instr: InstrRef) -> bool {
        self.for_instrs.contains(&instr)
    }
}
