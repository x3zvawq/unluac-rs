//! 把已证明的词法生命周期统一为 exclusive low 区间，供 plan body 原子物化。
//!
//! Close 区间来自捕获 cell 的真实 cleanup；debug 窗口来自共同结束的源码 binding：
//! `local object = {}; local function use(x) end; use(object); debug-end` 恢复为一个 `do`。
//! 窗口的新对象必须属于这些 binding，或有末端前必定覆盖/被调用排除的 scratch home；捕获 cell、
//! open 值和跨窗口 SSA 使用仍拒绝。debug end 恢复槽复用边界，不表示 VM 已清空旧槽。
//! 这里消费 Structure 的 debug 边界与 SSA/root 事实，不从 HIR 语句或 AST 形状猜作用域。
//! 普通 if/else 与完整循环可处于窗口内部；共享图区间查询证明唯一入口、出口，
//! 冻结 plan 则保证两端仍在实际发射的指令前缀，不能切入已被表达式或循环语法吸收的位置。

use std::ops::Range;

use super::*;
use crate::structure::{
    BlockEmissionPlan, CleanupDisposition, DebugBindingFact, GraphFacts, LoopVmProtocol,
    RegionPlan, RootObservation,
};
use crate::transformer::ResultPack;

pub(super) fn collect_lexical_scopes(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    graph: &GraphFacts,
    structure: &ReadyStructureFacts,
    mut scopes: Vec<Range<usize>>,
) -> Vec<Range<usize>> {
    let debug_bindings = structure.debug_bindings();
    // 同一结束点的 local 共同拥有窗口；producer 可以分属 if 前缀和合流后的基本块。
    let mut cohorts = BTreeMap::<_, Vec<&DebugBindingFact>>::new();
    for fact in debug_bindings.accepted() {
        if let (SsaValue::Def(def), Some(end)) = (fact.value, fact.end_instr)
            && proto.debug_locals[fact.scope].is_source()
        {
            let origin = dataflow.def_instr(def).index();
            if origin < end.index() {
                cohorts.entry(end.index()).or_default().push(fact);
            }
        }
    }
    if cohorts.is_empty() {
        return retain_non_crossing(scopes);
    }
    let emission = DebugEmissionIndex::new(structure);
    scopes.extend(cohorts.into_iter().filter_map(|(end, facts)| {
        debug_binding_window(proto, cfg, dataflow, graph, &emission, end, &facts)
    }));
    retain_non_crossing(scopes)
}

fn debug_binding_window(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    graph: &GraphFacts,
    emission: &DebugEmissionIndex<'_>,
    end: usize,
    facts: &[&DebugBindingFact],
) -> Option<Range<usize>> {
    let debug_bindings = emission.structure.debug_bindings();
    let LowInstr::Call(call) = proto.instrs.get(end - 1)? else {
        // 候选拒绝[ProofIncomplete]：debug end 前缺少当前分析能证明的 callee 观察边界。
        return None;
    };
    let mut owners = BTreeMap::new();
    let mut origin = end;
    for fact in facts {
        let SsaValue::Def(def) = fact.value else {
            unreachable!("cohort contains only definition bindings");
        };
        // 候选拒绝[ProofIncomplete]：canonical 身份若来自其他槽，或同槽存在多个 owner，
        // 不能把 source scope 直接当作该固定定义的生命周期。
        if dataflow.def_reg(def) != fact.reg || owners.insert(fact.reg, def).is_some() {
            return None;
        }
        origin = origin.min(dataflow.def_instr(def).index());
    }
    let (&floor, _) = owners.first_key_value()?;
    let (&ceiling, _) = owners.last_key_value()?;
    // 候选拒绝[ProofIncomplete]：非空结果或更宽 caller 前缀仍需额外结果根、外来 binding 证明。
    let final_observation = dataflow.effect_summaries.get(end - 1)?.root_observation;
    if !matches!(call.results, ResultPack::Ignore)
        || !matches!(final_observation,
            RootObservation::Call { caller_end } if caller_end.index() == ceiling.index() + 1)
    {
        return None;
    }
    let entry = cfg.instr_to_block[origin];
    let exit = cfg.instr_to_block[end - 1];
    let start = lexical_scope_evaluation_start(dataflow, cfg, entry, floor, origin)?;
    let window = start..end;

    if !emission.regular_prefix(entry)?.contains(&start)
        || !emission.regular_prefix(exit)?.contains(&(end - 1))
        || emission.scope_owner(entry) != emission.scope_owner(exit)
    {
        return None;
    }
    if entry != exit
        && (!graph.closed_instruction_window(cfg, window.clone())
            || !window_emission_is_local(cfg, emission, &window)
            || owners
                .values()
                .any(|&def| !graph.dominates(dataflow.def_block(def), exit)))
    {
        return None;
    }
    // 调用排除上界与必经覆盖写共同证明末端退休；高槽不需要再重建 for 的动态值类型。
    let home_retires = |reg: Reg, at: usize, block: BlockRef| {
        final_observation.excludes_home_from_caller(reg)
            || owners.get(&reg).is_some_and(|owner| {
                dataflow.def_instr(*owner).index() > at
                    && graph.post_dominates(dataflow.def_block(*owner), block)
            })
    };
    let local_phis = dataflow.closed_phis_in_instruction_window(cfg, window.clone(), floor)?;
    for &id in &local_phis {
        let phi = dataflow.phi_candidate(id)?;
        if dataflow.reg_is_reference_captured(phi.reg)
            || !home_retires(
                phi.reg,
                cfg.blocks[phi.block.index()].instrs.start.index(),
                phi.block,
            )
        {
            return None;
        }
    }
    let mut values = BTreeMap::<DefId, WindowValue>::new();
    for index in window.clone() {
        let instr = &proto.instrs[index];
        let effect = &dataflow.instr_effects[index];
        // for 控制只消费冻结协议的指令身份；其隐式 closing 仍由原生语法在原位置执行。
        // 额外 Close 只接纳不涉及捕获 cell/显式 TBC 的已归属词法边界。
        if (instr.is_control_terminator()
            && !matches!(instr, LowInstr::Branch(_) | LowInstr::Jump(_))
            && !emission.for_instrs.contains(&InstrRef(index)))
            || matches!(instr, LowInstr::Tbc(_))
            || matches!(instr, LowInstr::Close(close) if close.from < floor
                || dataflow.reference_captured_regs().any(|reg| reg >= close.from)
                || emission.structure.plan().cleanup_tbc_origins(InstrRef(index)).is_some_and(|origins| !origins.is_empty())
                || !matches!(emission.structure.plan().cleanup_disposition(InstrRef(index)),
                    Some(CleanupDisposition::LexicalScope(_))))
            || effect.open_use.is_some()
            || effect.open_must_def.is_some()
            || effect.fixed_uses_from(floor).iter().any(|&reg| {
                match dataflow.use_value(InstrRef(index), reg) {
                    SsaValue::Def(def) => !window.contains(&dataflow.def_instr(def).index()),
                    SsaValue::Phi(phi) => !local_phis.contains(&phi),
                    SsaValue::Entry(_) => true,
                }
            })
        {
            return None;
        }
        for &def in &dataflow.instr_defs[index] {
            let reg = dataflow.def_reg(def);
            let owner = owners.get(&reg);
            let is_owner = owner == Some(&def);
            // 候选拒绝[ProofIncomplete]：禁止外层写、声明后的 owner 槽复写、未结束的异期 binding、
            // 捕获 cell 和逃逸 def/phi；窗口不能吞掉其他生命周期或延续其值身份。
            if reg < floor
                || (owner.is_some_and(|owner| dataflow.def_instr(*owner).index() <= index)
                    && !is_owner)
                || dataflow.reg_is_reference_captured(reg)
                || (!is_owner
                    && debug_bindings
                        .for_value(SsaValue::Def(def))
                        .is_some_and(|binding| {
                            binding.reg != reg
                                || binding.end_instr.is_none_or(|binding_end| {
                                    binding_end.index() > end
                                        || (!final_observation.excludes_home_from_caller(reg)
                                            && owner.is_none_or(|owner| {
                                                binding_end.index()
                                                    > dataflow.def_instr(*owner).index()
                                            }))
                                })
                        }))
                || dataflow.def_uses[def.index()]
                    .iter()
                    .any(|site| !window.contains(&site.instr.index()))
                || dataflow.def_phi_uses[def.index()]
                    .iter()
                    .any(|&phi| !dataflow.phi_is_truly_dead(phi) && !local_phis.contains(&phi))
            {
                return None;
            }
            let value = if is_owner {
                WindowValue::Cohort
            } else {
                match instr {
                    LowInstr::LoadNil(_)
                    | LowInstr::LoadBool(_)
                    | LowInstr::LoadConst(_)
                    | LowInstr::LoadInteger(_)
                    | LowInstr::LoadNumber(_) => WindowValue::Anchored,
                    LowInstr::Move(mov) if mov.src < floor => {
                        // 引用捕获的外层槽可能被调用回写；其副本仍按独立 scratch 证明退休。
                        if dataflow.reg_is_reference_captured(mov.src) {
                            WindowValue::Scratch
                        } else {
                            WindowValue::Anchored
                        }
                    }
                    LowInstr::Move(mov) => match dataflow.use_value(InstrRef(index), mov.src) {
                        SsaValue::Def(source) => {
                            values.get(&source).copied().unwrap_or(WindowValue::Scratch)
                        }
                        SsaValue::Phi(_) => WindowValue::Scratch,
                        SsaValue::Entry(_) => return None,
                    },
                    _ => WindowValue::Scratch,
                }
            };
            // 该证书只授权 END，不授权在内部提前删根或移动求值。
            if value == WindowValue::Scratch && !home_retires(reg, index, dataflow.def_block(def)) {
                return None;
            }
            values.insert(def, value);
        }
    }
    let SsaValue::Def(callee) = dataflow.use_value(InstrRef(end - 1), call.callee) else {
        return None;
    };
    // 候选拒绝[ProofIncomplete]：末尾 callee 必须与窗口内某一 owner 的真实别名配对。
    (values.get(&callee) == Some(&WindowValue::Cohort)).then_some(window)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum WindowValue {
    Cohort,
    Anchored,
    Scratch,
}

/// 仅对有 debug cohort 的快照投影一次 plan 发射域；逆后序保证父状态先于子节点。
struct DebugEmissionIndex<'a> {
    structure: &'a ReadyStructureFacts,
    regions: Vec<DebugRegionEmission>,
    for_instrs: BTreeSet<InstrRef>,
}

#[derive(Clone, Copy)]
struct DebugRegionEmission {
    ordinary: bool,
    prefix_allowed: bool,
    prefix_header: Option<BlockRef>,
    scope_owner: RegionId,
}

impl DebugRegionEmission {
    fn restrict_header(&mut self, header: Option<BlockRef>) {
        self.prefix_allowed &=
            header.is_some_and(|header| self.prefix_header.is_none_or(|prior| prior == header));
        self.prefix_header = header;
    }
}

impl<'a> DebugEmissionIndex<'a> {
    fn new(structure: &'a ReadyStructureFacts) -> Self {
        let plan = structure.plan();
        let unrestricted = DebugRegionEmission {
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
                    RegionPlan::Loop { control, .. } if *control == region => {
                        state.prefix_allowed = false;
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
            structure,
            regions,
            for_instrs,
        }
    }

    fn scope_owner(&self, block: BlockRef) -> Option<RegionId> {
        let owner = self.structure.plan().region_for_block(block)?;
        Some(self.regions[owner.index()].scope_owner)
    }

    /// 两端必须由 regular/header prefix 发射，不能切入被吸收的表达式或 loop 绑定。
    fn regular_prefix(&self, block: BlockRef) -> Option<Range<usize>> {
        let plan = self.structure.plan();
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
}
/// 图边界已经证明；这里只限制窗口内的发射域和会被新词法块截断的值。
fn window_emission_is_local(
    cfg: &Cfg,
    emission: &DebugEmissionIndex<'_>,
    window: &Range<usize>,
) -> bool {
    for run in cfg.instr_to_block[window.clone()].chunk_by(|a, b| a == b) {
        let block = run[0];
        let Some(owner) = emission.structure.plan().region_for_block(block) else {
            return false;
        };
        if !emission.regions[owner.index()].ordinary {
            return false;
        }
    }
    true
}

fn retain_non_crossing(mut scopes: Vec<Range<usize>>) -> Vec<Range<usize>> {
    scopes.sort_unstable_by(|a, b| a.start.cmp(&b.start).then_with(|| b.end.cmp(&a.end)));
    scopes.dedup();
    let mut retained = vec![true; scopes.len()];
    let mut all_ends = BTreeSet::new();
    let mut pending = BTreeMap::<usize, Vec<usize>>::new();
    let mut group_start = 0;
    while group_start < scopes.len() {
        let start = scopes[group_start].start;
        let group_end =
            group_start + scopes[group_start..].partition_point(|scope| scope.start == start);
        for index in group_start..group_end {
            let end = scopes[index].end;
            // 同起点区间彼此嵌套；先完成整组查询再插入。已拒绝的区间仍能证明
            // 后续 crossing，但每个待拒绝区间只从 pending 移除一次，合计 O(C log C)。
            // 候选拒绝[ProofIncomplete]：交叉的恢复边界尚无统一词法 owner，不能任意延长或缩短任一窗口。
            if all_ends.range(start + 1..end).next().is_some() {
                retained[index] = false;
            }
            // 候选拒绝[ProofIncomplete]：同一 crossing 的较早区间也没有可独立提交的嵌套边界。
            while let Some((&crossed_end, _)) = pending.range(start + 1..end).next() {
                for crossed in pending
                    .remove(&crossed_end)
                    .expect("queried scope end exists")
                {
                    retained[crossed] = false;
                }
            }
        }
        for index in group_start..group_end {
            let end = scopes[index].end;
            all_ends.insert(end);
            if retained[index] {
                pending.entry(end).or_default().push(index);
            }
        }
        group_start = group_end;
    }
    scopes
        .into_iter()
        .zip(retained)
        .filter_map(|(scope, retained)| retained.then_some(scope))
        .collect()
}
