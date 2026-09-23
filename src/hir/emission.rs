//! 查询冻结 Structure plan 中仍由 HIR 单独发射的指令域与词法 owner。
//!
//! region 父子关系、条件和值判定的 header、循环协议均由 Structure 发布；这里仅投影
//! HIR lowering 的消费边界，不重新分析 CFG，也不把已吸收的表达式节点当作独立语句。
//! 例如 `a and b()` 的后续条件块进入 decision expression，只有 header 前缀逐指令
//! 发射；需要在精确 low 位置恢复作用域或 root 退休时，必须先排除这些非 header 位置。
//! 本查询不包含 HIR global declaration 等后续批量发射协议，它们仍需保护内部边界。
//! 源码 scope 的原始结束 PC 与可发射交接点分别保留：CFG 排除不可达尾部，冻结的
//! 无求值 Jump 允许在普通前缀末端交接；有求值的终结器不能据此提前结束来源身份。
//! 每个 proto 的 lowering 在绑定分配前建立一次投影，词法窗口、copy-root 退休和
//! 来源身份交接共同借用；这些消费者不改变 plan，最后一次查询后释放索引。

use std::collections::BTreeSet;
use std::ops::Range;

use crate::decompile::DecompileDialect;
use crate::structure::{
    BlockEmissionPlan, BlockRef, BlockTerminatorKind, Cfg, LoopVmProtocol, RegionId, RegionPlan,
    StructurePlan,
};
use crate::transformer::{InstrRef, LowInstr, LoweredProto, ValuePack};

pub(super) struct HirEmissionFacts<'a> {
    plan: &'a StructurePlan,
    regions: Vec<RegionEmission>,
    for_instrs: BTreeSet<InstrRef>,
    hoisted_prefixes: BTreeSet<BlockRef>,
    island_entry_prefixes: BTreeSet<BlockRef>,
    target: DecompileDialect,
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
    pub(super) fn new(plan: &'a StructurePlan, cfg: &Cfg, target: DecompileDialect) -> Self {
        let unrestricted = RegionEmission {
            ordinary: true,
            prefix_allowed: true,
            prefix_header: None,
            scope_owner: plan.root(),
        };
        let mut regions = vec![unrestricted; plan.regions().len()];
        let mut for_instrs = BTreeSet::new();
        let mut hoisted_prefixes = BTreeSet::new();
        let mut island_entry_prefixes = BTreeSet::new();
        for (id, payload) in plan.loops() {
            match plan.loop_protocol(id) {
                Some(LoopVmProtocol::Repeat(protocol))
                    if protocol.prefix_placement
                        == crate::structure::LoopConditionPrefixPlacement::BeforeBody =>
                {
                    if let Some(header) = plan
                        .condition(protocol.condition.condition)
                        .and_then(crate::structure::ConditionPlan::header)
                        && header != payload.header
                    {
                        hoisted_prefixes.insert(header);
                    }
                }
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
            if let RegionPlan::Unstructured {
                entry,
                entries,
                layout,
                ..
            } = node
                && matches!(layout.first(), Some(crate::structure::UnstructuredLayoutItem::Block(first)) if first == entry)
                && entries
                    .iter()
                    .all(|edge| cfg.edges[edge.index()].to == *entry)
            {
                // 每个区域只检查一次入口，避免同块的多个 debug 声明重复扫描全部边。
                island_entry_prefixes.insert(*entry);
            }
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
            if plan.single_pass_for_region(region).is_some() {
                // 单次 repeat 包装同样形成词法块；其中的声明不能冒充函数入口声明。
                state.scope_owner = region;
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
            hoisted_prefixes,
            island_entry_prefixes,
            target,
        }
    }

    pub(super) fn scope_owner(&self, block: BlockRef) -> Option<RegionId> {
        let owner = self.plan.region_for_block(block)?;
        Some(self.regions[owner.index()].scope_owner)
    }

    /// 声明可以供其词法子域写入，但 CFG 支配本身不授权逃出源码作用域。
    pub(super) fn scope_contains(&self, declaration: BlockRef, write: BlockRef) -> bool {
        self.scope_owner(declaration)
            .zip(self.scope_owner(write))
            .is_some_and(|(outer, inner)| self.plan.region_contains(outer, inner))
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

    /// island 的所有外部入口落在同一个首块时，其前缀仍可拥有原位置的声明。
    /// 是否会由内部回边再次进入，由调用方的 CFG 循环事实另证。
    pub(super) fn island_entry_prefix(&self, block: BlockRef) -> bool {
        self.island_entry_prefixes.contains(&block)
    }

    /// 词法窗口可包住完整值决策，但不能从表达式内部开始或结束。
    /// CFG/SSA 与生命周期闭包由调用方另证，这里只核对 lowering 的原子发射边界。
    pub(super) fn window_emission_is_local(&self, cfg: &Cfg, window: &Range<usize>) -> bool {
        let mut seen = BTreeSet::new();
        for run in cfg.instr_to_block[window.clone()].chunk_by(|a, b| a == b) {
            let block = run[0];
            if self.ordinary_block(block) {
                continue;
            }
            let Some(owner) = self.plan.region_for_block(block) else {
                return false;
            };
            if !seen.insert(owner) {
                continue;
            }
            let Some(RegionPlan::ValueDecision { plan, parent, .. }) = self.plan.region(owner)
            else {
                return false;
            };
            if !self.regions[parent.index()].ordinary {
                return false;
            }
            let Some(decision) = self.plan.value_decision(*plan) else {
                return false;
            };
            if decision.blocks().any(|block| {
                let range = cfg.blocks[block.index()].instrs;
                range.start.index() < window.start || range.end() > window.end
            }) {
                return false;
            }
        }
        true
    }

    /// Lua 5.1 的函数根块在隐式空 RETURN 前结束 debug local，已提供该词法终点。
    pub(super) fn function_body_ends_at(
        &self,
        proto: &LoweredProto,
        block: BlockRef,
        end: usize,
    ) -> bool {
        self.target == DecompileDialect::Lua51
            && self.scope_owner(block) == Some(self.plan.root())
            && end + 1 == proto.instrs.len()
            && matches!(self.plan.block_terminator(block).map(|term| term.kind),
                Some(BlockTerminatorKind::Return { instr, .. }) if instr.index() == end)
            && matches!(proto.instrs.get(end), Some(LowInstr::Return(ret))
                if matches!(ret.values, ValuePack::Fixed(values) if values.len == 0))
    }

    /// 无附加动作的 while 回边已结束 body 的词法域，不再为同一末端增加 do。
    pub(super) fn loop_body_ends_at(&self, block: BlockRef, end: usize) -> bool {
        let Some(terminator) = self.plan.block_terminator(block) else {
            return false;
        };
        let BlockTerminatorKind::Jump { instr, edge } = terminator.kind else {
            return false;
        };
        let Some(edge) = self.plan.edge_plan(edge) else {
            return false;
        };
        let crate::structure::EdgeTransfer::LoopBack(region) = edge.transfer else {
            return false;
        };
        let Some(RegionPlan::Loop { plan, body, .. }) = self.plan.region(region) else {
            return false;
        };
        // repeat 条件仍处于 body 作用域，不能借回边把条件前的 debug 终点延后。
        instr.index() == end
            && self.scope_owner(block) == Some(*body)
            && matches!(
                self.plan.loop_protocol(*plan),
                Some(LoopVmProtocol::While(_) | LoopVmProtocol::WhileTrue)
            )
            && edge.phi_copies.is_empty()
            && edge.cleanup.is_empty()
            && edge.iteration.is_empty()
            && edge.forward_route.is_none()
    }

    /// 将源码 exclusive 末端投影到仍能发射交接语句的 prefix 边界。
    /// 例如 `copy=owner; use(); goto again; unreachable CLOSE` 在 goto 前结束词法域。
    /// 仅无求值的 Jump 可移到前缀末尾；Branch/Return 等操作数不能被这项投影越过。
    /// 窗口的单入口/出口、身份与 cleanup 时序仍由消费者另行证明。
    pub(super) fn source_scope_prefix_end(&self, cfg: &Cfg, end: usize) -> Option<usize> {
        let last = cfg.last_reachable_instr_before(end)?;
        let block = cfg.instr_to_block[last.index()];
        let prefix = self.regular_prefix(block)?;
        if prefix.contains(&last.index()) {
            return Some(last.index() + 1);
        }
        matches!(self.plan.block_terminator(block)?.kind,
            BlockTerminatorKind::Jump { instr, .. } if instr == last)
        .then_some(prefix.end)
    }

    pub(super) fn for_instr(&self, instr: InstrRef) -> bool {
        self.for_instrs.contains(&instr)
    }

    /// repeat/continue 协议把惰性条件前缀移到 body 前，只承诺独立 SSA 值的求值。
    /// 该处若改成原可写 binding，会提前覆盖 body 仍要读取的旧值。
    pub(super) fn prefix_is_hoisted(&self, block: BlockRef) -> bool {
        self.hoisted_prefixes.contains(&block)
    }
}
