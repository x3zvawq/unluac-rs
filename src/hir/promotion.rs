//! 这个文件承载 HIR 内部给 simplify 使用的 promotion facts。
//!
//! `locals` pass 只看 HIR 语法本身时，能判断“哪些 temp 正在沿别名链流动”，却不知道
//! “这个 temp 最早来自哪个词法槽位”。一旦某个 local 已经被 closure reference capture，
//! 后续同一词法槽位的新 def 就不该再长成新的 local，而应继续写回原绑定；按值 capture
//! 只保存当前快照，不激活这条 sticky 身份。`close` 之后复用同一个寄存器号已经是新的
//! 词法槽位，不能继续沿用旧 upvalue 的 local。
//!
//! 这里专门把那份“temp -> home slot”事实从 analyze 阶段带给 simplify：
//! - 它依赖 Dataflow 已经给出的 fixed def/reg 与 phi incoming 身份，以及
//!   Transformer 保留下来的 `close from rX` 词法边界
//! - 它不会重新做结构恢复，也不会把事实暴露成公开 HIR API
//! - 例子：`t0(slot 0, epoch 0)` 被闭包 capture 之后，后续同 epoch 的
//!   `t7(slot 0, epoch 0)` 与同槽 phi 会被 locals 认成同一个源码 local 的写回；
//!   若中间经过 `close from r0`，后续 `t8(slot 0, epoch 1)` 会被视为新的词法槽位
//! - carried-local 后续若把不同 home 的 binding 并入同一目标，会失效单一 home
//!   的正向 provenance，但保留完整有限的可能 home 并集；未知来源则传播未知。原始
//!   物理槽事实仍保留给 capture/TBC 等负向保护
//! - 由 `NewTable` canonical def 直接产生的 temp 单独保留 constructor origin；MOVE、
//!   phi 或后续 local 物化不能冒充分配本身

use crate::hir::common::{
    HirBlock, HirExpr, HirLValue, HirStmt, HirTableField, HirTableKey, LocalId, ParamId, TempId,
};
use crate::structure::{
    BlockRef, CanonicalMoveIndex, Cfg, DataflowFacts, DefId, EffectTag, GraphFacts, InstrEffect,
    LoopConditionPrefixPlacement, LoopVmProtocol, PhiId, PhiIncomingDisposition, SideEffectSummary,
    SsaValue, StructurePlan,
};
use crate::transformer::{CaptureSource, InstrRef, LowInstr, LoweredProto, Reg, UpvalueOperand};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

/// temp promotion 使用的词法槽位身份。
///
/// Lua VM 会在 `close from rX` 之后复用同一个寄存器号。单独用 `slot` 作为 local 身份
/// 会把已关闭 upvalue 和后续普通临时值混成同一个绑定，因此这里额外带上 close epoch。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(super) struct HomeSlotKey {
    slot: usize,
    epoch: usize,
}

/// capture / TBC / promotion 共用的物理槽词法 epoch。
///
/// `Close` 只结束经过该 CFG 路径的 upvalue。这里把 close 当作槽位身份的 SSA 定义，
/// 在 dominance frontier 建 merge epoch，再沿支配树给指令标注进入点身份；不能按线性
/// PC 给所有后缀指令累加边界，否则 break/continue cleanup 会污染 sibling 路径。
pub(super) struct SlotEpochFacts {
    epochs_by_reg: Vec<Option<SlotEpochFlow>>,
    reference_captured_regs: Vec<bool>,
}

struct SlotEpochFlow {
    at_instr: Vec<usize>,
    spans_entry: bool,
}

impl SlotEpochFacts {
    pub(super) fn analyze(
        proto: &LoweredProto,
        cfg: &Cfg,
        graph: &GraphFacts,
        dataflow: &DataflowFacts,
    ) -> Self {
        let reference_captured_regs = proto
            .instrs
            .iter()
            .filter_map(|instr| match instr {
                LowInstr::Closure(closure) => Some(&closure.captures),
                _ => None,
            })
            .flatten()
            .filter_map(|capture| match capture.source {
                CaptureSource::ByReference(reg) => Some(reg),
                CaptureSource::ByValue(_) | CaptureSource::Upvalue(_) => None,
            })
            .collect::<BTreeSet<_>>();
        let mut tracked_regs = reference_captured_regs.clone();
        tracked_regs.extend(proto.instrs.iter().filter_map(|instr| match instr {
            LowInstr::Tbc(tbc) => Some(tbc.reg),
            _ => None,
        }));
        let reg_count = tracked_regs
            .iter()
            .map(|reg| reg.index() + 1)
            .max()
            .unwrap_or_default()
            .max(usize::from(proto.frame.max_stack_size));
        let mut epochs_by_reg = (0..reg_count).map(|_| None).collect::<Vec<_>>();
        for reg in tracked_regs {
            epochs_by_reg[reg.index()] = Some(analyze_slot_epoch(proto, cfg, graph, dataflow, reg));
        }
        let mut reference_captured_by_reg = vec![false; reg_count];
        for reg in reference_captured_regs {
            reference_captured_by_reg[reg.index()] = true;
        }
        Self {
            epochs_by_reg,
            reference_captured_regs: reference_captured_by_reg,
        }
    }

    fn all_home_slots(&self, max_stack_size: usize) -> BTreeSet<HomeSlotKey> {
        let mut homes = BTreeSet::new();
        for slot in 0..max_stack_size {
            homes.insert(HomeSlotKey::new(slot, 0));
            if let Some(flow) = self.epochs_by_reg.get(slot).and_then(Option::as_ref) {
                homes.extend(
                    flow.at_instr
                        .iter()
                        .copied()
                        .map(|epoch| HomeSlotKey::new(slot, epoch)),
                );
            }
        }
        homes
    }

    pub(super) fn epoch_at(&self, reg: Reg, instr: InstrRef) -> usize {
        self.epochs_by_reg
            .get(reg.index())
            .and_then(Option::as_ref)
            .and_then(|flow| flow.at_instr.get(instr.index()))
            .copied()
            .unwrap_or_default()
    }

    pub(super) fn spans_entry(&self, reg: Reg) -> bool {
        self.epochs_by_reg
            .get(reg.index())
            .and_then(Option::as_ref)
            .is_none_or(|flow| flow.spans_entry)
    }

    pub(super) fn tracks_reference_capture(&self, reg: Reg) -> bool {
        self.reference_captured_regs
            .get(reg.index())
            .copied()
            .unwrap_or(false)
    }
}

fn analyze_slot_epoch(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph: &GraphFacts,
    dataflow: &DataflowFacts,
    reg: Reg,
) -> SlotEpochFlow {
    let close_blocks = proto
        .instrs
        .iter()
        .enumerate()
        .filter_map(|(instr_index, instr)| {
            let LowInstr::Close(close) = instr else {
                return None;
            };
            let block = cfg.instr_to_block[instr_index];
            (close.from.index() <= reg.index() && cfg.reachable_blocks.contains(&block))
                .then_some(block)
        })
        .collect::<BTreeSet<_>>();
    let merge_blocks = place_epoch_merges(cfg, graph, &close_blocks);
    let mut at_instr = vec![0; proto.instrs.len()];
    let mut stack = vec![0];
    let mut events = vec![EpochRenameEvent::Enter(cfg.entry_block)];

    while let Some(event) = events.pop() {
        match event {
            EpochRenameEvent::Exit(count) => stack.truncate(stack.len() - count),
            EpochRenameEvent::Enter(block) => {
                let mut pushed = 0;
                if merge_blocks.contains(&block) {
                    stack.push(1 + proto.instrs.len() + block.index());
                    pushed += 1;
                }
                let range = cfg.blocks[block.index()].instrs;
                for (instr_index, epoch) in at_instr
                    .iter_mut()
                    .enumerate()
                    .take(range.end())
                    .skip(range.start.index())
                {
                    *epoch = *stack.last().expect("epoch stack has entry identity");
                    if matches!(
                        proto.instrs[instr_index],
                        LowInstr::Close(close) if close.from.index() <= reg.index()
                    ) {
                        stack.push(1 + instr_index);
                        pushed += 1;
                    }
                }

                events.push(EpochRenameEvent::Exit(pushed));
                for child in graph.dominator_tree.children[block.index()].iter().rev() {
                    events.push(EpochRenameEvent::Enter(*child));
                }
            }
        }
    }

    let defs_span_entry = dataflow
        .defs
        .iter()
        .filter(|def| def.reg == reg)
        .all(|def| at_instr[def.instr.index()] == 0);
    let captures_span_entry = proto.instrs.iter().enumerate().all(|(instr_index, instr)| {
        let LowInstr::Closure(closure) = instr else {
            return true;
        };
        !closure
            .captures
            .iter()
            .any(|capture| capture.source == CaptureSource::ByReference(reg))
            || at_instr[instr_index] == 0
    });

    SlotEpochFlow {
        at_instr,
        spans_entry: defs_span_entry && captures_span_entry,
    }
}

fn place_epoch_merges(
    cfg: &Cfg,
    graph: &GraphFacts,
    close_blocks: &BTreeSet<BlockRef>,
) -> BTreeSet<BlockRef> {
    // loop 内的 Close 会先在 header 的 dominance frontier 合成 epoch，但 header
    // 可能同时支配下一轮 body 和循环外 continuation。循环外物理槽已经越过 cleanup，
    // 因此真实 exit target 也必须显式开始一个 merge epoch，不能继续继承 header 身份。
    let mut placed = graph
        .natural_loops
        .iter()
        .filter(|natural_loop| !natural_loop.blocks.is_disjoint(close_blocks))
        .flat_map(|natural_loop| {
            natural_loop.blocks.iter().flat_map(|block| {
                cfg.succs[block.index()].iter().filter_map(|edge_ref| {
                    let target = cfg.edges[edge_ref.index()].to;
                    (!natural_loop.blocks.contains(&target)
                        && cfg.reachable_blocks.contains(&target))
                    .then_some(target)
                })
            })
        })
        .collect::<BTreeSet<_>>();
    let mut pending = close_blocks.iter().copied().collect::<VecDeque<_>>();
    pending.extend(placed.iter().copied());
    while let Some(block) = pending.pop_front() {
        for frontier in graph.dominance_frontier_blocks(block) {
            if placed.insert(frontier) && !close_blocks.contains(&frontier) {
                pending.push_back(frontier);
            }
        }
    }

    if graph.natural_loops.iter().any(|natural_loop| {
        natural_loop.header == cfg.entry_block
            && natural_loop
                .blocks
                .iter()
                .any(|block| close_blocks.contains(block))
    }) {
        placed.insert(cfg.entry_block);
    }
    placed
}

enum EpochRenameEvent {
    Enter(BlockRef),
    Exit(usize),
}

impl HomeSlotKey {
    pub(super) const fn new(slot: usize, epoch: usize) -> Self {
        Self { slot, epoch }
    }

    pub(super) const fn slot(self) -> usize {
        self.slot
    }
}

#[derive(Debug, Clone, Default, Eq, PartialEq)]
enum HomeSlotResolution {
    #[default]
    Pending,
    Known(BTreeSet<HomeSlotKey>),
    Unknown,
}

impl HomeSlotResolution {
    fn from_home(home: HomeSlotKey) -> Self {
        Self::Known(BTreeSet::from([home]))
    }

    fn exact_home(&self) -> Option<HomeSlotKey> {
        let Self::Known(homes) = self else {
            return None;
        };
        let mut homes = homes.iter().copied();
        let home = homes.next()?;
        homes.next().is_none().then_some(home)
    }

    fn complete_homes(&self) -> Option<BTreeSet<HomeSlotKey>> {
        match self {
            Self::Known(homes) => Some(homes.clone()),
            Self::Pending | Self::Unknown => None,
        }
    }
}

/// 单个 proto 的 temp promotion 与后续 binding provenance 辅助事实。
#[derive(Debug, Clone, Default)]
pub(super) struct ProtoPromotionFacts {
    temp_home_slots: Vec<HomeSlotResolution>,
    immediate_move_write_homes: Vec<BTreeSet<HomeSlotKey>>,
    entry_nil_overwrite_temps: BTreeSet<TempId>,
    entry_nil_phi_temps: BTreeSet<TempId>,
    entry_nil_phi_locals: BTreeSet<LocalId>,
    entry_nil_pruned_locals: BTreeSet<LocalId>,
    repeat_condition_prefix_temps: BTreeSet<TempId>,
    direct_table_seed_temps: BTreeSet<TempId>,
    direct_table_seed_locals: BTreeSet<LocalId>,
    loop_carrier_temps: BTreeSet<TempId>,
    scope_end_copy_root_temps: BTreeSet<TempId>,
    copy_root_overwrites: BTreeMap<TempId, Vec<CopyRootOverwrite>>,
    local_home_slots: Vec<HomeSlotResolution>,
    invalidated_param_homes: BTreeSet<ParamId>,
    invalidated_local_homes: BTreeSet<LocalId>,
    invalidated_temp_homes: BTreeSet<TempId>,
    home_free_locals: BTreeSet<LocalId>,
    possible_param_homes: BTreeMap<ParamId, Option<BTreeSet<HomeSlotKey>>>,
    possible_local_homes: BTreeMap<LocalId, Option<BTreeSet<HomeSlotKey>>>,
    possible_temp_homes: BTreeMap<TempId, Option<BTreeSet<HomeSlotKey>>>,
    physical_home_universe: BTreeSet<HomeSlotKey>,
    compact_home_slots: bool,
}

impl ProtoPromotionFacts {
    /// 从 canonical def 与最终 value plan 提取当前 proto 的 temp -> home slot 对照表。
    pub(super) fn from_plan(
        proto: &LoweredProto,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
        plan: &StructurePlan,
        slot_epochs: &SlotEpochFacts,
        fixed_temps: &[TempId],
        phi_temps: &[TempId],
    ) -> Self {
        let total_temps = dataflow.defs.len() + plan.phis().len();
        let mut temp_home_slots = vec![HomeSlotResolution::Pending; total_temps];
        let physical_home_universe =
            slot_epochs.all_home_slots(usize::from(proto.frame.max_stack_size));

        fill_fixed_def_home_slots(dataflow, slot_epochs, &mut temp_home_slots);
        fill_phi_home_slots(dataflow, plan, &mut temp_home_slots);
        let immediate_move_write_homes = collect_immediate_move_write_homes(
            proto,
            dataflow,
            slot_epochs,
            fixed_temps,
            phi_temps,
            total_temps,
        );
        let copy_roots = collect_copy_root_facts(proto, cfg, dataflow, fixed_temps);

        Self {
            temp_home_slots,
            immediate_move_write_homes,
            entry_nil_overwrite_temps: collect_entry_nil_overwrite_temps(
                proto,
                dataflow,
                fixed_temps,
            ),
            entry_nil_phi_temps: collect_entry_nil_phi_temps(proto, dataflow, plan, phi_temps),
            entry_nil_phi_locals: BTreeSet::new(),
            entry_nil_pruned_locals: BTreeSet::new(),
            repeat_condition_prefix_temps: collect_repeat_condition_prefix_temps(
                dataflow,
                plan,
                fixed_temps,
            ),
            direct_table_seed_temps: collect_direct_table_seed_temps(proto, dataflow, fixed_temps),
            direct_table_seed_locals: BTreeSet::new(),
            loop_carrier_temps: collect_loop_carrier_temps(plan, phi_temps),
            scope_end_copy_root_temps: copy_roots.scope_end,
            copy_root_overwrites: copy_roots.overwrites,
            local_home_slots: Vec::new(),
            invalidated_param_homes: BTreeSet::new(),
            invalidated_local_homes: BTreeSet::new(),
            invalidated_temp_homes: BTreeSet::new(),
            home_free_locals: BTreeSet::new(),
            possible_param_homes: BTreeMap::new(),
            possible_local_homes: BTreeMap::new(),
            possible_temp_homes: BTreeMap::new(),
            physical_home_universe,
            compact_home_slots: false,
        }
    }

    pub(super) fn is_direct_table_seed_temp(&self, temp: TempId) -> bool {
        self.direct_table_seed_temps.contains(&temp)
    }

    /// 该 temp 是非参数槽的首个 canonical fixed def；槽在函数入口因此必为 nil。
    ///
    /// 这不证明 def 只执行一次。消费方仍须把候选限制在 proto 根级单次执行区间，
    /// 不能把同一静态 def 在循环下一轮面对的旧值误当成入口 nil。
    pub(super) fn overwrites_entry_nil(&self, temp: TempId) -> bool {
        self.entry_nil_overwrite_temps.contains(&temp)
    }

    /// 该 local 来自仍含同槽 `Entry(nil)` incoming 的 direct region-result phi。
    pub(super) fn is_entry_nil_phi_local(&self, local: LocalId) -> bool {
        self.entry_nil_phi_locals.contains(&local)
    }

    pub(super) fn record_entry_nil_phi_promotion(&mut self, temp: TempId, local: LocalId) {
        if self.entry_nil_phi_temps.contains(&temp) {
            self.entry_nil_phi_locals.insert(local);
        }
    }

    pub(super) fn mark_entry_nil_writes_pruned(&mut self, local: LocalId) {
        self.entry_nil_pruned_locals.insert(local);
    }

    pub(super) fn entry_nil_writes_were_pruned(&self, local: LocalId) -> bool {
        self.entry_nil_pruned_locals.contains(&local)
    }

    /// Structure 已冻结为 repeat condition prefix、但为 continue 语义移到 body 前的 temp。
    pub(super) fn is_repeat_condition_prefix_temp(&self, temp: TempId) -> bool {
        self.repeat_condition_prefix_temps.contains(&temp)
    }

    pub(super) fn is_direct_table_seed_local(&self, local: LocalId) -> bool {
        self.direct_table_seed_locals.contains(&local)
    }

    pub(super) fn record_direct_table_seed_promotion(&mut self, temp: TempId, local: LocalId) {
        if self.is_direct_table_seed_temp(temp) {
            self.direct_table_seed_locals.insert(local);
        }
    }

    /// HIR lowering 为 loop carried protocol 合成的 carrier temp。
    ///
    /// 包括两类来源：
    /// - `LoopValueSource::Binding` 在 body/latch phase 上给 carried owner 补的协议写回
    /// - loop region synthetic input 为 header phi materialize 的一次性 carrier copy
    ///
    /// 这些 temp 不是源码作者声明的 root alias。后续 pass 只有在 temp 也已证明无读者、
    /// 且未被 debug/source identity 占用时，才可继续消去对应 mirror。
    pub(super) fn is_loop_carrier_temp(&self, temp: TempId) -> bool {
        self.loop_carrier_temps.contains(&temp)
    }

    /// 该 temp 的 direct copy home 在已证前向 CFG 的每条路径一直活跃到 scope end。
    ///
    /// 这份事实只服务于“源码读取已经结束、物理栈槽仍作为 GC root”的负向保护；若
    /// 后续 binding 合并使 home provenance 失效，就不能再消费原始证明。
    pub(super) fn is_scope_end_copy_root_temp(&self, temp: TempId) -> bool {
        !self.temp_home_was_invalidated(temp) && self.scope_end_copy_root_temps.contains(&temp)
    }

    /// 返回结束该 direct copy root transaction 每条路径的精确 GC-inert overwrite。
    pub(super) fn copy_root_overwrites(&self, temp: TempId) -> Option<&[CopyRootOverwrite]> {
        if self.temp_home_was_invalidated(temp) {
            return None;
        }
        let overwrites = self.copy_root_overwrites.get(&temp)?;
        (!overwrites.is_empty()
            && overwrites.iter().all(|overwrite| {
                !self.temp_home_was_invalidated(overwrite.temp)
                    && self.trusted_temp_home_slot(temp)
                        == self.trusted_temp_home_slot(overwrite.temp)
            }))
        .then_some(overwrites)
    }

    #[cfg(test)]
    pub(super) fn record_copy_root_overwrites_for_test(
        &mut self,
        producer: TempId,
        overwrites: Vec<(TempId, HirExpr)>,
    ) {
        let overwrites = overwrites
            .into_iter()
            .map(|(temp, value)| CopyRootOverwrite {
                temp,
                value: CopyRootScalarValue::from_hir_expr(&value)
                    .expect("test overwrite must be a direct GC-inert scalar"),
            })
            .collect();
        self.copy_root_overwrites.insert(producer, overwrites);
    }

    /// 返回某个 temp 对应的原始寄存器槽位。
    pub(super) fn home_slot(&self, temp: TempId) -> Option<HomeSlotKey> {
        self.temp_home_slots.get(temp.index())?.exact_home()
    }

    pub(super) fn home_slot_definition_count(&self) -> usize {
        self.temp_home_slots
            .iter()
            .filter(|resolution| resolution.exact_home().is_some())
            .count()
    }

    #[cfg(test)]
    pub(super) fn record_temp_home_slot_for_test(&mut self, temp: TempId, home_slot: HomeSlotKey) {
        if self.temp_home_slots.len() <= temp.index() {
            self.temp_home_slots
                .resize(temp.index() + 1, HomeSlotResolution::Pending);
        }
        self.temp_home_slots[temp.index()] = HomeSlotResolution::from_home(home_slot);
        self.physical_home_universe.insert(home_slot);
    }

    #[cfg(test)]
    pub(super) fn record_direct_table_seed_for_test(&mut self, temp: TempId) {
        self.direct_table_seed_temps.insert(temp);
    }

    #[cfg(test)]
    pub(super) fn record_loop_carrier_temp_for_test(&mut self, temp: TempId) {
        self.loop_carrier_temps.insert(temp);
    }

    /// 返回 temp 提升后 local 仍对应的原始词法槽位。
    ///
    /// 同一 local 若吸收过不同槽位，不再具有单一 home；后续 pass 不能再把它
    /// 作为跨 region 合并的单一物理身份依据。
    pub(super) fn local_home_slot(
        &self,
        local: crate::hir::common::LocalId,
    ) -> Option<HomeSlotKey> {
        self.local_home_slots.get(local.index())?.exact_home()
    }

    pub(super) fn record_local_home_slot(
        &mut self,
        local: crate::hir::common::LocalId,
        home_slot: HomeSlotKey,
    ) {
        self.home_free_locals.remove(&local);
        if self.local_home_slots.len() <= local.index() {
            self.local_home_slots
                .resize(local.index() + 1, HomeSlotResolution::Pending);
        }
        let resolution = &mut self.local_home_slots[local.index()];
        *resolution = merge_home_slot_resolutions(
            resolution.clone(),
            HomeSlotResolution::from_home(home_slot),
        );
        self.physical_home_universe.insert(home_slot);
        if let Some(possible) = self.possible_local_homes.get_mut(&local)
            && let Some(homes) = possible
        {
            homes.insert(home_slot);
        }
    }

    /// 记录由 HIR pass 新建、并不对应任何原始 VM 槽位的 local。
    ///
    /// 这与 `HomeSlotResolution::Unknown` 不同：后者仍可能来自 provenance 缺失的
    /// 物理 binding，不能据此排除 raw-home alias。
    pub(super) fn record_home_free_local(&mut self, local: LocalId) {
        self.home_free_locals.insert(local);
        self.possible_local_homes
            .insert(local, Some(BTreeSet::new()));
    }

    /// 记录由 HIR lowering owner 新建、并不对应任何原始 VM 槽位的 temp。
    ///
    /// 调用方必须在分配该 synthetic temp 的位置显式登记；未知或越界的普通 temp
    /// 仍保留为 `None`，不能仅凭编号推断为 home-free。
    pub(super) fn record_home_free_temp(&mut self, temp: TempId) {
        debug_assert!(
            self.temp_home_slots.get(temp.index()).is_none(),
            "canonical VM temp cannot be marked home-free"
        );
        self.possible_temp_homes.insert(temp, Some(BTreeSet::new()));
    }

    pub(super) fn local_has_no_physical_home(&self, local: LocalId) -> bool {
        self.home_free_locals.contains(&local)
    }

    /// 返回 binding 在当前 HIR 改写后可能对应的完整物理 home 集合。
    ///
    /// `Some(empty)` 表示由 HIR 合成且明确 home-free；`None` 表示某次
    /// merge 的来源本身就缺 provenance，不得用 raw home 冒充完整集合。
    pub(super) fn possible_param_home_slots(
        &self,
        param: ParamId,
    ) -> Option<BTreeSet<HomeSlotKey>> {
        match self.possible_param_homes.get(&param) {
            Some(homes) => homes.clone(),
            None => Some(BTreeSet::from([HomeSlotKey::new(param.index(), 0)])),
        }
    }

    pub(super) fn possible_local_home_slots(
        &self,
        local: LocalId,
    ) -> Option<BTreeSet<HomeSlotKey>> {
        match self.possible_local_homes.get(&local) {
            Some(homes) => homes.clone(),
            None if self.local_has_no_physical_home(local) => Some(BTreeSet::new()),
            None => self
                .local_home_slots
                .get(local.index())
                .and_then(HomeSlotResolution::complete_homes),
        }
    }

    pub(super) fn possible_temp_home_slots(&self, temp: TempId) -> Option<BTreeSet<HomeSlotKey>> {
        match self.possible_temp_homes.get(&temp) {
            Some(homes) => homes.clone(),
            None => self
                .temp_home_slots
                .get(temp.index())
                .and_then(HomeSlotResolution::complete_homes),
        }
    }

    /// 当前 proto 中任一物理 binding 可能占用的完整 `(slot, close epoch)` 全集。
    ///
    /// 某个 binding 的 provenance 若已退化为 Unknown，consumer 可以用该全集继续做
    /// 保守 may-alias：它不会证明两个物理 binding 异槽，但能在单 home proto 中保留
    /// 精确结论，也能把多 home 情况归入已有 alias/lifetime barrier。
    pub(super) fn physical_home_universe(&self) -> &BTreeSet<HomeSlotKey> {
        &self.physical_home_universe
    }

    pub(super) fn record_param_home_merge(
        &mut self,
        param: ParamId,
        source_homes: Option<BTreeSet<HomeSlotKey>>,
    ) {
        let merged = merge_possible_home_slots(self.possible_param_home_slots(param), source_homes);
        self.possible_param_homes.insert(param, merged);
        self.invalidated_param_homes.insert(param);
    }

    pub(super) fn record_local_home_merge(
        &mut self,
        local: LocalId,
        source_homes: Option<BTreeSet<HomeSlotKey>>,
    ) {
        let merged = merge_possible_home_slots(self.possible_local_home_slots(local), source_homes);
        if merged.as_ref().is_some_and(BTreeSet::is_empty) {
            self.home_free_locals.insert(local);
        } else {
            self.home_free_locals.remove(&local);
        }
        self.possible_local_homes.insert(local, merged);
        self.invalidated_local_homes.insert(local);
        self.direct_table_seed_locals.remove(&local);
        self.entry_nil_phi_locals.remove(&local);
    }

    pub(super) fn record_temp_home_merge(
        &mut self,
        temp: TempId,
        source_homes: Option<BTreeSet<HomeSlotKey>>,
    ) {
        let merged = merge_possible_home_slots(self.possible_temp_home_slots(temp), source_homes);
        self.possible_temp_homes.insert(temp, merged);
        self.invalidated_temp_homes.insert(temp);
    }

    pub(super) fn enable_home_slot_compaction(&mut self) {
        self.compact_home_slots = true;
    }

    pub(super) const fn compacts_home_slots(&self) -> bool {
        self.compact_home_slots
    }

    pub(super) fn trusted_param_home_slot(&self, param: ParamId) -> Option<HomeSlotKey> {
        (!self.param_home_was_invalidated(param)).then_some(HomeSlotKey::new(param.index(), 0))
    }

    pub(super) fn trusted_local_home_slot(&self, local: LocalId) -> Option<HomeSlotKey> {
        (!self.local_home_was_invalidated(local))
            .then(|| self.local_home_slot(local))
            .flatten()
    }

    pub(super) fn trusted_temp_home_slot(&self, temp: TempId) -> Option<HomeSlotKey> {
        (!self.temp_home_was_invalidated(temp))
            .then(|| self.home_slot(temp))
            .flatten()
    }

    /// 证明一个 dead temp 赋值只是把同一个可见 binding 的当前值写回它自己的物理槽。
    ///
    /// 这里故意只相信 RHS 的 visible binding provenance：目标 temp 自己可以已经失去
    /// trusted home，但 raw `home_slot` 仍足以说明“它写向哪个物理 cell”。只有当
    /// `ParamRef/LocalRef` 这边仍保有同一 trusted home 时，删除写入才不会缩短 GC root
    /// 生命周期，也不会把别的 cell 误当成同值 no-op。
    pub(super) fn copies_same_visible_home_value(&self, temp: TempId, value: &HirExpr) -> bool {
        let Some(target_home) = self.home_slot(temp) else {
            return false;
        };
        match value {
            HirExpr::ParamRef(param) => self.trusted_param_home_slot(*param) == Some(target_home),
            HirExpr::LocalRef(local) => self.trusted_local_home_slot(*local) == Some(target_home),
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Vector(_)
            | HirExpr::Complex { .. }
            | HirExpr::UpvalueRef(_)
            | HirExpr::TempRef(_)
            | HirExpr::GlobalRef(_)
            | HirExpr::TableAccess(_)
            | HirExpr::Unary(_)
            | HirExpr::Binary(_)
            | HirExpr::LogicalAnd(_)
            | HirExpr::LogicalOr(_)
            | HirExpr::Decision(_)
            | HirExpr::Call(_)
            | HirExpr::VarArg
            | HirExpr::TableConstructor(_)
            | HirExpr::Closure(_)
            | HirExpr::Unresolved(_) => false,
        }
    }

    /// Returns physical homes written by an immediately following transparent MOVE chain.
    ///
    /// This is intentionally separate from `home_slot`: a compiler MOVE can be elided from HIR
    /// while its adjacent destination write remains observable through GC root lifetime. A MOVE
    /// separated from its producer is excluded because HIR no longer retains its exact timing.
    pub(super) fn trusted_immediate_move_write_homes(
        &self,
        temp: TempId,
    ) -> Option<&BTreeSet<HomeSlotKey>> {
        (!self.temp_home_was_invalidated(temp))
            .then(|| self.immediate_move_write_homes.get(temp.index()))
            .flatten()
    }

    pub(super) fn param_home_was_invalidated(&self, param: ParamId) -> bool {
        self.invalidated_param_homes.contains(&param)
    }

    pub(super) fn local_home_was_invalidated(&self, local: LocalId) -> bool {
        self.invalidated_local_homes.contains(&local)
    }

    pub(super) fn temp_home_was_invalidated(&self, temp: TempId) -> bool {
        self.invalidated_temp_homes.contains(&temp)
    }

    #[cfg(test)]
    pub(super) fn invalidate_temp_home(&mut self, temp: TempId) {
        self.invalidated_temp_homes.insert(temp);
        self.possible_temp_homes.insert(temp, None);
    }

    pub(super) fn record_temp_to_local_merge(&mut self, temp: TempId, local: LocalId) {
        let source_home = self.trusted_temp_home_slot(temp);
        let target_home = self.trusted_local_home_slot(local);
        if source_home.is_none() || source_home != target_home {
            self.record_local_home_merge(local, self.possible_temp_home_slots(temp));
        }
    }

    pub(super) fn record_local_to_param_merge(&mut self, local: LocalId, param: ParamId) {
        let source_home = self.trusted_local_home_slot(local);
        let target_home = self.trusted_param_home_slot(param);
        if source_home.is_none() || source_home != target_home {
            self.record_param_home_merge(param, self.possible_local_home_slots(local));
        }
    }

    /// 把当前语句里所有 closure capture 观察到的 home slot 收集进集合。
    pub(super) fn collect_captured_home_slots_in_stmt(
        &self,
        stmt: &HirStmt,
        slots: &mut BTreeSet<HomeSlotKey>,
    ) {
        match stmt {
            HirStmt::LocalDecl(local_decl) => {
                for value in &local_decl.values {
                    self.collect_captured_home_slots_in_expr(value, slots);
                }
            }
            HirStmt::GlobalDecl(global_decl) => {
                for value in &global_decl.values {
                    self.collect_captured_home_slots_in_expr(value, slots);
                }
            }
            HirStmt::Assign(assign) => {
                for target in &assign.targets {
                    if let HirLValue::TableAccess(access) = target {
                        self.collect_captured_home_slots_in_expr(&access.base, slots);
                        self.collect_captured_home_slots_in_expr(&access.key, slots);
                    }
                }
                for value in &assign.values {
                    self.collect_captured_home_slots_in_expr(value, slots);
                }
            }
            HirStmt::TableSetList(set_list) => {
                self.collect_captured_home_slots_in_expr(&set_list.base, slots);
                for value in &set_list.values {
                    self.collect_captured_home_slots_in_expr(value, slots);
                }
            }
            HirStmt::ErrNil(err_nil) => {
                self.collect_captured_home_slots_in_expr(&err_nil.value, slots);
            }
            HirStmt::ToBeClosed(to_be_closed) => {
                self.collect_captured_home_slots_in_expr(&to_be_closed.value, slots);
            }
            HirStmt::CallStmt(call_stmt) => {
                self.collect_captured_home_slots_in_expr(&call_stmt.call.callee, slots);
                for arg in &call_stmt.call.args {
                    self.collect_captured_home_slots_in_expr(arg, slots);
                }
            }
            HirStmt::Return(ret) => {
                for value in &ret.values {
                    self.collect_captured_home_slots_in_expr(value, slots);
                }
            }
            HirStmt::If(if_stmt) => {
                self.collect_captured_home_slots_in_expr(&if_stmt.cond, slots);
                self.collect_captured_home_slots_in_block(&if_stmt.then_block, slots);
                if let Some(else_block) = &if_stmt.else_block {
                    self.collect_captured_home_slots_in_block(else_block, slots);
                }
            }
            HirStmt::While(while_stmt) => {
                self.collect_captured_home_slots_in_expr(&while_stmt.cond, slots);
                self.collect_captured_home_slots_in_block(&while_stmt.body, slots);
            }
            HirStmt::Repeat(repeat_stmt) => {
                self.collect_captured_home_slots_in_block(&repeat_stmt.body, slots);
                self.collect_captured_home_slots_in_expr(&repeat_stmt.cond, slots);
            }
            HirStmt::NumericFor(numeric_for) => {
                self.collect_captured_home_slots_in_expr(&numeric_for.start, slots);
                self.collect_captured_home_slots_in_expr(&numeric_for.limit, slots);
                self.collect_captured_home_slots_in_expr(&numeric_for.step, slots);
                self.collect_captured_home_slots_in_block(&numeric_for.body, slots);
            }
            HirStmt::GenericFor(generic_for) => {
                for iterator in &generic_for.iterator {
                    self.collect_captured_home_slots_in_expr(iterator, slots);
                }
                self.collect_captured_home_slots_in_block(&generic_for.body, slots);
            }
            HirStmt::Block(block) => self.collect_captured_home_slots_in_block(block, slots),
            HirStmt::Break
            | HirStmt::Close(_)
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => {}
        }
    }

    /// 只收集在进入嵌套 block 之前就会执行到的 capture。
    pub(super) fn collect_prefix_captured_home_slots_in_stmt(
        &self,
        stmt: &HirStmt,
        slots: &mut BTreeSet<HomeSlotKey>,
    ) {
        match stmt {
            HirStmt::If(if_stmt) => self.collect_captured_home_slots_in_expr(&if_stmt.cond, slots),
            HirStmt::While(while_stmt) => {
                self.collect_captured_home_slots_in_expr(&while_stmt.cond, slots);
            }
            HirStmt::NumericFor(numeric_for) => {
                self.collect_captured_home_slots_in_expr(&numeric_for.start, slots);
                self.collect_captured_home_slots_in_expr(&numeric_for.limit, slots);
                self.collect_captured_home_slots_in_expr(&numeric_for.step, slots);
            }
            HirStmt::GenericFor(generic_for) => {
                for iterator in &generic_for.iterator {
                    self.collect_captured_home_slots_in_expr(iterator, slots);
                }
            }
            HirStmt::LocalDecl(_)
            | HirStmt::GlobalDecl(_)
            | HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Return(_)
            | HirStmt::Repeat(_)
            | HirStmt::Block(_)
            | HirStmt::Break
            | HirStmt::Close(_)
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => {}
        }
    }

    fn collect_captured_home_slots_in_block(
        &self,
        block: &HirBlock,
        slots: &mut BTreeSet<HomeSlotKey>,
    ) {
        for stmt in &block.stmts {
            self.collect_captured_home_slots_in_stmt(stmt, slots);
        }
    }

    fn collect_captured_home_slots_in_expr(
        &self,
        expr: &HirExpr,
        slots: &mut BTreeSet<HomeSlotKey>,
    ) {
        match expr {
            HirExpr::TableAccess(access) => {
                self.collect_captured_home_slots_in_expr(&access.base, slots);
                self.collect_captured_home_slots_in_expr(&access.key, slots);
            }
            HirExpr::Unary(unary) => self.collect_captured_home_slots_in_expr(&unary.expr, slots),
            HirExpr::Binary(binary) => {
                self.collect_captured_home_slots_in_expr(&binary.lhs, slots);
                self.collect_captured_home_slots_in_expr(&binary.rhs, slots);
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                self.collect_captured_home_slots_in_expr(&logical.lhs, slots);
                self.collect_captured_home_slots_in_expr(&logical.rhs, slots);
            }
            HirExpr::Decision(decision) => {
                for node in &decision.nodes {
                    self.collect_captured_home_slots_in_expr(&node.test, slots);
                    self.collect_captured_home_slots_in_decision_target(&node.truthy, slots);
                    self.collect_captured_home_slots_in_decision_target(&node.falsy, slots);
                }
            }
            HirExpr::Call(call) => {
                self.collect_captured_home_slots_in_expr(&call.callee, slots);
                for arg in &call.args {
                    self.collect_captured_home_slots_in_expr(arg, slots);
                }
            }
            HirExpr::TableConstructor(table) => {
                for field in &table.fields {
                    match field {
                        HirTableField::Array(value) => {
                            self.collect_captured_home_slots_in_expr(value, slots);
                        }
                        HirTableField::Record(field) => {
                            if let HirTableKey::Expr(key) = &field.key {
                                self.collect_captured_home_slots_in_expr(key, slots);
                            }
                            self.collect_captured_home_slots_in_expr(&field.value, slots);
                        }
                    }
                }
                if let Some(trailing) = &table.trailing_multivalue {
                    self.collect_captured_home_slots_in_expr(trailing.as_expr(), slots);
                }
            }
            HirExpr::Closure(closure) => {
                for capture in &closure.captures {
                    if capture.mode == crate::hir::common::HirCaptureMode::ByReference {
                        self.collect_temp_home_slots_in_expr(&capture.value, slots);
                    }
                    self.collect_captured_home_slots_in_expr(&capture.value, slots);
                }
            }
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Vector(_)
            | HirExpr::Complex { .. }
            | HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::TempRef(_)
            | HirExpr::GlobalRef(_)
            | HirExpr::VarArg
            | HirExpr::Unresolved(_) => {}
        }
    }

    fn collect_captured_home_slots_in_decision_target(
        &self,
        target: &crate::hir::common::HirDecisionTarget,
        slots: &mut BTreeSet<HomeSlotKey>,
    ) {
        if let crate::hir::common::HirDecisionTarget::Expr(expr) = target {
            self.collect_captured_home_slots_in_expr(expr, slots);
        }
    }

    fn collect_temp_home_slots_in_expr(&self, expr: &HirExpr, slots: &mut BTreeSet<HomeSlotKey>) {
        match expr {
            HirExpr::TempRef(temp) => {
                if let Some(slot) = self.home_slot(*temp) {
                    slots.insert(slot);
                }
            }
            HirExpr::TableAccess(access) => {
                self.collect_temp_home_slots_in_expr(&access.base, slots);
                self.collect_temp_home_slots_in_expr(&access.key, slots);
            }
            HirExpr::Unary(unary) => self.collect_temp_home_slots_in_expr(&unary.expr, slots),
            HirExpr::Binary(binary) => {
                self.collect_temp_home_slots_in_expr(&binary.lhs, slots);
                self.collect_temp_home_slots_in_expr(&binary.rhs, slots);
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                self.collect_temp_home_slots_in_expr(&logical.lhs, slots);
                self.collect_temp_home_slots_in_expr(&logical.rhs, slots);
            }
            HirExpr::Decision(decision) => {
                for node in &decision.nodes {
                    self.collect_temp_home_slots_in_expr(&node.test, slots);
                    self.collect_temp_home_slots_in_decision_target(&node.truthy, slots);
                    self.collect_temp_home_slots_in_decision_target(&node.falsy, slots);
                }
            }
            HirExpr::Call(call) => {
                self.collect_temp_home_slots_in_expr(&call.callee, slots);
                for arg in &call.args {
                    self.collect_temp_home_slots_in_expr(arg, slots);
                }
            }
            HirExpr::TableConstructor(table) => {
                for field in &table.fields {
                    match field {
                        HirTableField::Array(value) => {
                            self.collect_temp_home_slots_in_expr(value, slots);
                        }
                        HirTableField::Record(field) => {
                            if let HirTableKey::Expr(key) = &field.key {
                                self.collect_temp_home_slots_in_expr(key, slots);
                            }
                            self.collect_temp_home_slots_in_expr(&field.value, slots);
                        }
                    }
                }
                if let Some(trailing) = &table.trailing_multivalue {
                    self.collect_temp_home_slots_in_expr(trailing.as_expr(), slots);
                }
            }
            HirExpr::Closure(closure) => {
                for capture in &closure.captures {
                    self.collect_temp_home_slots_in_expr(&capture.value, slots);
                }
            }
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Vector(_)
            | HirExpr::Complex { .. }
            | HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::GlobalRef(_)
            | HirExpr::VarArg
            | HirExpr::Unresolved(_) => {}
        }
    }

    fn collect_temp_home_slots_in_decision_target(
        &self,
        target: &crate::hir::common::HirDecisionTarget,
        slots: &mut BTreeSet<HomeSlotKey>,
    ) {
        if let crate::hir::common::HirDecisionTarget::Expr(expr) = target {
            self.collect_temp_home_slots_in_expr(expr, slots);
        }
    }
}

fn fill_fixed_def_home_slots(
    dataflow: &DataflowFacts,
    slot_epochs: &SlotEpochFacts,
    temp_home_slots: &mut [HomeSlotResolution],
) {
    for def in &dataflow.defs {
        let epoch = slot_epochs.epoch_at(def.reg, def.instr);
        temp_home_slots[def.id.index()] =
            HomeSlotResolution::from_home(HomeSlotKey::new(def.reg.index(), epoch));
    }
}

fn collect_immediate_move_write_homes(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    slot_epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
    total_temps: usize,
) -> Vec<BTreeSet<HomeSlotKey>> {
    let mut homes = vec![BTreeSet::new(); total_temps];
    let mut canonical_moves = CanonicalMoveIndex::new(proto, dataflow);
    let mut last_instr_by_root = std::collections::BTreeMap::<SsaValue, (usize, BlockRef)>::new();

    for (instr_index, def_ids) in dataflow.instr_defs.iter().enumerate() {
        for def_id in def_ids {
            let Some(def) = dataflow.defs.get(def_id.index()) else {
                continue;
            };
            let value = SsaValue::Def(*def_id);
            let Ok(root) = canonical_moves.resolve(value) else {
                continue;
            };

            if root == value {
                // Start a chain only at a real definition. A later MOVE is accepted only when
                // it is the next low instruction in the same basic block.
                last_instr_by_root.insert(root, (instr_index, def.block));
                continue;
            }

            let Some(crate::transformer::LowInstr::Move(move_)) = proto.instrs.get(instr_index)
            else {
                continue;
            };
            if move_.dst != def.reg {
                continue;
            }
            let Some((last_instr, last_block)) = last_instr_by_root.get(&root).copied() else {
                continue;
            };
            if last_block != def.block || last_instr.checked_add(1) != Some(instr_index) {
                continue;
            }

            let Some(temp) = (match root {
                SsaValue::Def(source) => fixed_temps.get(source.index()).copied(),
                SsaValue::Phi(source) => phi_temps.get(source.index()).copied(),
                SsaValue::Entry(_) => None,
            }) else {
                continue;
            };
            let epoch = slot_epochs.epoch_at(def.reg, def.instr);
            if let Some(temp_homes) = homes.get_mut(temp.index()) {
                temp_homes.insert(HomeSlotKey::new(def.reg.index(), epoch));
            }
            last_instr_by_root.insert(root, (instr_index, def.block));
        }
    }
    homes
}

fn collect_entry_nil_overwrite_temps(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
) -> BTreeSet<TempId> {
    let param_count = usize::from(proto.signature.num_params);
    let vararg_param_reg = proto.signature.has_vararg_param_reg.then_some(param_count);
    let mut first_defs = vec![None::<DefId>; usize::from(proto.frame.max_stack_size)];

    for def in &dataflow.defs {
        let slot = def.reg.index();
        if slot < param_count || Some(slot) == vararg_param_reg {
            continue;
        }
        let Some(first) = first_defs.get_mut(slot) else {
            continue;
        };
        if first.is_none_or(|current| dataflow.def_instr(current).index() > def.instr.index()) {
            *first = Some(def.id);
        }
    }

    first_defs
        .into_iter()
        .flatten()
        .filter_map(|def| {
            let direct = TempId(def.index());
            (fixed_temps.get(def.index()) == Some(&direct)).then_some(direct)
        })
        .collect()
}

fn collect_entry_nil_phi_temps(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    phi_temps: &[TempId],
) -> BTreeSet<TempId> {
    let param_count = usize::from(proto.signature.num_params);
    let vararg_param_reg = proto.signature.has_vararg_param_reg.then_some(param_count);
    let direct_offset = dataflow.defs.len();

    plan.phis()
        .filter_map(|phi| {
            let slot = phi.reg.index();
            if slot < param_count || Some(slot) == vararg_param_reg {
                return None;
            }
            let direct = TempId(direct_offset + phi.phi.index());
            (phi_temps.get(phi.phi.index()) == Some(&direct)
                && phi.incomings.iter().any(|incoming| {
                    incoming.value == SsaValue::Entry(phi.reg)
                        && matches!(
                            incoming.disposition,
                            PhiIncomingDisposition::RegionResult(_)
                        )
                }))
            .then_some(direct)
        })
        .collect()
}

fn collect_repeat_condition_prefix_temps(
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    fixed_temps: &[TempId],
) -> BTreeSet<TempId> {
    let condition_headers = plan
        .loops()
        .filter_map(|(loop_id, _)| match plan.loop_protocol(loop_id) {
            Some(LoopVmProtocol::Repeat(protocol))
                if protocol.prefix_placement == LoopConditionPrefixPlacement::BeforeBody =>
            {
                plan.condition(protocol.condition.condition)
                    .and_then(|condition| condition.header())
            }
            Some(
                LoopVmProtocol::While(_)
                | LoopVmProtocol::Repeat(_)
                | LoopVmProtocol::WhileTrue
                | LoopVmProtocol::NumericFor(_)
                | LoopVmProtocol::GenericFor(_),
            )
            | None => None,
        })
        .collect::<BTreeSet<_>>();

    dataflow
        .defs
        .iter()
        .filter(|def| condition_headers.contains(&def.block))
        .filter_map(|def| {
            let direct = TempId(def.id.index());
            (fixed_temps.get(def.id.index()) == Some(&direct)).then_some(direct)
        })
        .collect()
}

fn collect_direct_table_seed_temps(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
) -> BTreeSet<TempId> {
    proto
        .instrs
        .iter()
        .enumerate()
        .filter_map(|(instr_index, instr)| {
            let LowInstr::NewTable(new_table) = instr else {
                return None;
            };
            dataflow.instr_defs[instr_index]
                .iter()
                .find(|def| dataflow.defs[def.index()].reg == new_table.dst)
                .and_then(|def| {
                    let canonical = fixed_temps.get(def.index()).copied()?;
                    // loop-state coalescing 可把多个 fixed def 映射到同一个 phi temp；
                    // 这时 temp 也代表分配前的旧状态，不能再作为 fresh owner 证据。
                    (canonical == TempId(def.index())).then_some(canonical)
                })
        })
        .collect()
}

fn collect_loop_carrier_temps(plan: &StructurePlan, phi_temps: &[TempId]) -> BTreeSet<TempId> {
    let mut temps = plan
        .loops()
        .filter_map(|(loop_id, _)| plan.loop_value_actions(loop_id))
        .flat_map(|actions| actions.batches.iter())
        .flat_map(|batch| batch.writes.iter())
        .filter(|write| matches!(write.source, crate::structure::LoopValueSource::Binding(_)))
        .filter_map(|write| phi_temps.get(write.target.index()).copied())
        .collect::<BTreeSet<_>>();
    temps.extend(plan.phis().filter_map(|phi| {
        phi.incomings.iter().any(|incoming| {
            matches!(incoming.disposition, PhiIncomingDisposition::RegionInput(region) if matches!(plan.region(region), Some(crate::structure::RegionPlan::Loop { .. })))
        })
        .then(|| phi_temps.get(phi.phi.index()).copied())
        .flatten()
    }));
    temps
}

/// 从 low-IR 正证一个 direct `GETUPVAL`/跨槽 `MOVE` copy 的物理槽在后续所有潜在
/// 用户代码/GC 观察点都仍位于 VM active stack top 以下，并沿同一 basic block、线性
/// single-entry fast path，或 predecessor-closed 的严格前向 CFG DAG 活到每条路径的
/// Return/TailCall 或精确的 direct nil/boolean/integer/number overwrite。
///
/// HIR 会丢失 block 结束时的隐式 stack-top 收缩；只看“后缀没有同槽写”会把已经到期
/// 的高槽误提升成函数级 local。这里保留 raw 指令层的最小充分事实；分支 successor 与
/// join 用 entry-driven must-state 合流，只有 producer 支配的前向闭合子图才能发布
/// all-successor 终点。overwrite 的 raw DefId/TempId 与值类会一同发布，HIR consumer
/// 必须重新定位唯一赋值 owner 并原子重放；回边、外部 join 入口、collectable/effectful
/// overwrite 与无法计算活动栈下界的事件仍拒绝。TBC 与专用调用协议只消费各自的固定
/// 输入 root prefix；`Close` 本身不覆盖槽位，因此可以继续到原始终点。
#[derive(Default)]
struct CopyRootFacts {
    scope_end: BTreeSet<TempId>,
    overwrites: BTreeMap<TempId, Vec<CopyRootOverwrite>>,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(super) enum CopyRootScalarValue {
    Nil,
    Boolean(bool),
    Integer(i64),
    Number(f64),
}

impl CopyRootScalarValue {
    #[cfg(test)]
    fn from_hir_expr(value: &HirExpr) -> Option<Self> {
        match value {
            HirExpr::Nil => Some(Self::Nil),
            HirExpr::Boolean(value) => Some(Self::Boolean(*value)),
            HirExpr::Integer(value) => Some(Self::Integer(*value)),
            HirExpr::Number(value) => Some(Self::Number(*value)),
            _ => None,
        }
    }

    pub(super) fn matches_hir_expr(self, value: &HirExpr) -> bool {
        match (self, value) {
            (Self::Nil, HirExpr::Nil) => true,
            (Self::Boolean(expected), HirExpr::Boolean(actual)) => expected == *actual,
            (Self::Integer(expected), HirExpr::Integer(actual)) => expected == *actual,
            (Self::Number(expected), HirExpr::Number(actual)) => {
                expected.to_bits() == actual.to_bits()
            }
            _ => false,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(super) struct CopyRootOverwrite {
    temp: TempId,
    value: CopyRootScalarValue,
}

impl CopyRootOverwrite {
    pub(super) const fn temp(self) -> TempId {
        self.temp
    }

    pub(super) fn matches_hir_expr(self, value: &HirExpr) -> bool {
        self.value.matches_hir_expr(value)
    }
}

#[derive(Default)]
struct CopyRootEnd {
    scope_end: bool,
    overwrites: BTreeMap<TempId, CopyRootOverwrite>,
}

impl CopyRootEnd {
    fn scope_end() -> Self {
        Self {
            scope_end: true,
            overwrites: BTreeMap::new(),
        }
    }

    fn overwrite(overwrite: CopyRootOverwrite) -> Self {
        Self {
            scope_end: false,
            overwrites: BTreeMap::from([(overwrite.temp, overwrite)]),
        }
    }

    fn is_complete(&self) -> bool {
        self.scope_end || !self.overwrites.is_empty()
    }
}

fn collect_copy_root_facts(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
) -> CopyRootFacts {
    let mut facts = CopyRootFacts::default();
    for def in &dataflow.defs {
        let is_direct_copy = match proto.instrs.get(def.instr.index()) {
            Some(LowInstr::GetUpvalue(get_upvalue)) => {
                get_upvalue.dst == def.reg && matches!(get_upvalue.src, UpvalueOperand::Upvalue(_))
            }
            Some(LowInstr::Move(move_)) => move_.dst == def.reg && move_.src != move_.dst,
            _ => false,
        };
        if !is_direct_copy {
            continue;
        }

        let direct = TempId(def.id.index());
        if fixed_temps.get(def.id.index()) != Some(&direct) {
            continue;
        }
        if let Some(root_end) = copy_root_end(proto, cfg, dataflow, fixed_temps, def.instr, def.reg)
        {
            if root_end.scope_end {
                facts.scope_end.insert(direct);
            }
            if !root_end.overwrites.is_empty() {
                facts
                    .overwrites
                    .insert(direct, root_end.overwrites.into_values().collect());
            }
        }
    }
    facts
}

fn copy_root_end(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
    producer: InstrRef,
    home: Reg,
) -> Option<CopyRootEnd> {
    let mut observed = false;
    let mut current_block = *cfg.instr_to_block.get(producer.index())?;
    let mut index = producer.index() + 1;

    while index < proto.instrs.len() {
        let instr_block = *cfg.instr_to_block.get(index)?;
        if instr_block != current_block {
            if copy_root_forward_block_successor(cfg, current_block) != Some(instr_block)
                || cfg.blocks.get(instr_block.index())?.instrs.start != InstrRef(index)
            {
                return copy_root_cfg_end(
                    proto,
                    cfg,
                    dataflow,
                    fixed_temps,
                    current_block,
                    observed,
                    home,
                );
            }
            current_block = instr_block;
        }
        let instr = proto.instrs.get(index)?;
        let effect = dataflow.instr_effects.get(index)?;

        // 当前值若被覆盖，同一 root transaction 要么在精确 direct GC-inert 写处终止，
        // 要么因新值可能建立独立生命周期而失去证明。
        if effect.must_define(home) {
            return observed
                .then(|| direct_scalar_overwrite(proto, dataflow, fixed_temps, index, home))
                .flatten()
                .map(CopyRootEnd::overwrite);
        }

        match copy_root_instr_progress(
            instr,
            effect,
            low_instr_may_observe_gc_roots(&dataflow.effect_summaries, index),
            home,
            &mut observed,
        )? {
            CopyRootInstrProgress::Continue => {}
            CopyRootInstrProgress::ScopeEnd => return Some(CopyRootEnd::scope_end()),
        }

        match instr {
            LowInstr::Jump(_) => {
                return copy_root_cfg_end(
                    proto,
                    cfg,
                    dataflow,
                    fixed_temps,
                    current_block,
                    observed,
                    home,
                );
            }
            _ if instr.is_control_terminator() => {
                return copy_root_cfg_end(
                    proto,
                    cfg,
                    dataflow,
                    fixed_temps,
                    current_block,
                    observed,
                    home,
                );
            }
            _ => {}
        }
        index += 1;
    }

    None
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum CopyRootInstrProgress {
    Continue,
    ScopeEnd,
}

fn copy_root_instr_progress(
    instr: &LowInstr,
    effect: &InstrEffect,
    may_observe_gc_roots: bool,
    home: Reg,
    observed: &mut bool,
) -> Option<CopyRootInstrProgress> {
    match instr {
        LowInstr::Return(_) => observed.then_some(CopyRootInstrProgress::ScopeEnd),
        LowInstr::Call(call) => {
            // 只消费跨方言共同成立的 caller-prefix：callee base 以下的槽在被调
            // 函数执行期间仍属于 caller frame。LuaJIT 的 FR1/FR2 frame link 会让
            // args.start 与真实 TValue root 区间不同，不能用参数 range 推 active top。
            if call.callee.index() <= home.index() {
                // 候选拒绝[SemanticBarrier:Lifetime]：callee base 不高于 copy home
                // 时，该槽不属于被调函数执行期间的 caller root 前缀。
                return None;
            }
            *observed = true;
            Some(CopyRootInstrProgress::Continue)
        }
        LowInstr::Close(_) => {
            // CLOSE 结束 open-upvalue / TBC 事务，但不覆盖当前槽；前序观察点已经
            // 证明 home 位于活动 caller prefix，保留同一物理 local 穿过 CLOSE
            // 只复现 VM 原有 root。继续扫描到原始 Return 才冻结作用域终点。
            Some(CopyRootInstrProgress::Continue)
        }
        LowInstr::Tbc(tbc) => {
            let active_top = fixed_input_root_prefix_top([tbc.reg]);
            if active_top <= home.index() {
                // 候选拒绝[SemanticBarrier:Lifetime]：TBC 的异常/cleanup 路径只保证
                // 标记槽以下仍属于活动 caller prefix；更高 copy home 已过期。
                return None;
            }
            *observed = true;
            Some(CopyRootInstrProgress::Continue)
        }
        LowInstr::GenericForCall(call) => {
            // 迭代器调用执行期间只把 iterator/state/control 作为 caller roots；result
            // targets 尚未产生，不能用通用 InstrEffect 的 must-def 抬高 active top。
            let active_top = fixed_input_root_prefix_top([call.iterator, call.state, call.control]);
            if active_top <= home.index() {
                // 候选拒绝[SemanticBarrier:Lifetime]：copy 位于 TFORCALL 的三个活动
                // 输入以上时，迭代器中的 GC 可观察其已经失活（同 regress_416 的
                // block-end 高槽到期边界）。
                return None;
            }
            *observed = true;
            Some(CopyRootInstrProgress::Continue)
        }
        LowInstr::TailCall(_) => {
            // tail callee 执行前 caller frame 已结束，不能把它当成新的 root 观察点；
            // 但此前已被普通调用观察过的 transaction 可精确在此结束作用域。
            observed.then_some(CopyRootInstrProgress::ScopeEnd)
        }
        _ if instr.is_control_terminator() => Some(CopyRootInstrProgress::Continue),
        _ if may_observe_gc_roots => {
            if !effect_keeps_copy_home_rooted(effect, home) {
                // 候选拒绝[SemanticBarrier:Lifetime]：当前观察点不能正证 copy home
                // 位于活动栈下界内；block-end 高槽到期反例会在这里被排除。
                return None;
            }
            *observed = true;
            Some(CopyRootInstrProgress::Continue)
        }
        _ => Some(CopyRootInstrProgress::Continue),
    }
}

enum CopyRootCfgBlockEnd {
    Continue { observed: bool },
    End(CopyRootEnd),
}

/// 从一个已执行的 control terminator 出发，只接受严格前向、无环且每条动态路径都在
/// scope end 或 direct GC-inert overwrite 前观察过同一 active home 的 CFG。incoming
/// observation 在 join 取交集；状态只会由 true 变为 false，有限 DAG 上的 worklist
/// 因而必然收敛。
fn copy_root_cfg_end(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
    source: BlockRef,
    observed: bool,
    home: Reg,
) -> Option<CopyRootEnd> {
    copy_root_cfg_end_with(
        CopyRootCfgInputs {
            instrs: &proto.instrs,
            cfg,
            instr_effects: &dataflow.instr_effects,
            effect_summaries: &dataflow.effect_summaries,
            home,
        },
        source,
        observed,
        |index, home| direct_scalar_overwrite(proto, dataflow, fixed_temps, index, home),
    )
}

#[derive(Clone, Copy)]
struct CopyRootCfgInputs<'a> {
    instrs: &'a [LowInstr],
    cfg: &'a Cfg,
    instr_effects: &'a [InstrEffect],
    effect_summaries: &'a [SideEffectSummary],
    home: Reg,
}

fn copy_root_cfg_end_with(
    inputs: CopyRootCfgInputs<'_>,
    source: BlockRef,
    observed: bool,
    mut overwrite_at: impl FnMut(usize, Reg) -> Option<CopyRootOverwrite>,
) -> Option<CopyRootEnd> {
    let region = copy_root_forward_cfg_region(
        inputs.instrs,
        inputs.cfg,
        inputs.instr_effects,
        source,
        inputs.home,
    )?;
    if region.iter().any(|block| {
        inputs
            .cfg
            .reachable_predecessors(*block)
            .into_iter()
            .any(|predecessor| predecessor != source && !region.contains(&predecessor))
    }) {
        // 候选拒绝[SemanticBarrier:ControlFlow]：子图外 predecessor 会在未执行 producer
        // 的情况下进入 join；把该 raw def 提升为 join 后仍活跃的 root 会伪造支配关系。
        return None;
    }

    let mut incoming = BTreeMap::<BlockRef, bool>::new();
    let mut pending = VecDeque::new();
    for successor in copy_root_forward_cfg_successors(inputs.cfg, source)? {
        merge_copy_root_cfg_incoming(&mut incoming, &mut pending, successor, observed);
    }

    let mut ends = CopyRootEnd::default();
    while let Some(block) = pending.pop_front() {
        let observed = incoming.get(&block).copied()?;
        match scan_copy_root_cfg_block(inputs, block, observed, &mut overwrite_at)? {
            CopyRootCfgBlockEnd::End(block_ends) => {
                ends.scope_end |= block_ends.scope_end;
                ends.overwrites.extend(block_ends.overwrites);
            }
            CopyRootCfgBlockEnd::Continue { observed } => {
                for successor in copy_root_forward_cfg_successors(inputs.cfg, block)? {
                    merge_copy_root_cfg_incoming(&mut incoming, &mut pending, successor, observed);
                }
            }
        }
    }

    ends.is_complete().then_some(ends)
}

#[cfg(test)]
fn copy_root_cfg_scope_end(
    instrs: &[LowInstr],
    cfg: &Cfg,
    instr_effects: &[InstrEffect],
    effect_summaries: &[SideEffectSummary],
    source: BlockRef,
    observed: bool,
    home: Reg,
) -> Option<()> {
    let ends = copy_root_cfg_end_with(
        CopyRootCfgInputs {
            instrs,
            cfg,
            instr_effects,
            effect_summaries,
            home,
        },
        source,
        observed,
        |_index, _home| None,
    )?;
    (ends.scope_end && ends.overwrites.is_empty()).then_some(())
}

fn copy_root_forward_cfg_region(
    instrs: &[LowInstr],
    cfg: &Cfg,
    instr_effects: &[InstrEffect],
    source: BlockRef,
    home: Reg,
) -> Option<BTreeSet<BlockRef>> {
    let mut region = BTreeSet::new();
    let mut pending = VecDeque::from(copy_root_forward_cfg_successors(cfg, source)?);
    while let Some(block) = pending.pop_front() {
        if !region.insert(block) {
            continue;
        }
        let range = cfg.blocks.get(block.index())?.instrs;
        if matches!(
            cfg.terminator(instrs, block),
            Some(LowInstr::Return(_) | LowInstr::TailCall(_))
        ) || (range.start.index()..range.end()).any(|index| {
            instr_effects
                .get(index)
                .is_some_and(|effect| effect.must_define(home))
        }) {
            continue;
        }
        pending.extend(copy_root_forward_cfg_successors(cfg, block)?);
    }
    Some(region)
}

fn merge_copy_root_cfg_incoming(
    incoming: &mut BTreeMap<BlockRef, bool>,
    pending: &mut VecDeque<BlockRef>,
    block: BlockRef,
    observed: bool,
) {
    match incoming.get_mut(&block) {
        None => {
            incoming.insert(block, observed);
            pending.push_back(block);
        }
        Some(previous) => {
            let merged = *previous && observed;
            if merged != *previous {
                *previous = merged;
                pending.push_back(block);
            }
        }
    }
}

fn scan_copy_root_cfg_block(
    inputs: CopyRootCfgInputs<'_>,
    block: BlockRef,
    mut observed: bool,
    overwrite_at: &mut impl FnMut(usize, Reg) -> Option<CopyRootOverwrite>,
) -> Option<CopyRootCfgBlockEnd> {
    let range = inputs.cfg.blocks.get(block.index())?.instrs;
    if range.is_empty() {
        return None;
    }
    for index in range.start.index()..range.end() {
        let instr = inputs.instrs.get(index)?;
        let effect = inputs.instr_effects.get(index)?;
        if effect.must_define(inputs.home) {
            let overwrite = observed
                .then(|| overwrite_at(index, inputs.home))
                .flatten()?;
            return Some(CopyRootCfgBlockEnd::End(CopyRootEnd::overwrite(overwrite)));
        }
        match copy_root_instr_progress(
            instr,
            effect,
            low_instr_may_observe_gc_roots(inputs.effect_summaries, index),
            inputs.home,
            &mut observed,
        )? {
            CopyRootInstrProgress::Continue => {}
            CopyRootInstrProgress::ScopeEnd => {
                return Some(CopyRootCfgBlockEnd::End(CopyRootEnd::scope_end()));
            }
        }
        if instr.is_control_terminator() {
            if range.last() != Some(InstrRef(index)) {
                return None;
            }
            return Some(CopyRootCfgBlockEnd::Continue { observed });
        }
    }
    Some(CopyRootCfgBlockEnd::Continue { observed })
}

fn copy_root_forward_cfg_successors(cfg: &Cfg, block: BlockRef) -> Option<Vec<BlockRef>> {
    let block_end = cfg.blocks.get(block.index())?.instrs.end();
    let successors = cfg.reachable_successors(block);
    if successors.is_empty()
        || successors.iter().any(|successor| {
            let Some(range) = cfg.blocks.get(successor.index()).map(|block| block.instrs) else {
                return true;
            };
            range.is_empty() || range.start.index() < block_end
        })
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：回边会重用同一静态 copy def，空/synthetic
        // successor 也没有可扫描的 scope-end transaction，均不能冻结成本轮 root。
        return None;
    }
    Some(successors)
}

fn copy_root_forward_block_successor(cfg: &Cfg, block: BlockRef) -> Option<BlockRef> {
    let successor = cfg.unique_reachable_successor(block)?;
    if cfg.unique_reachable_predecessor_matching(successor, |_| true) != Some(block) {
        // 候选拒绝[SemanticBarrier:ControlFlow]：线性 Jump/fallthrough 进入多前驱 join
        // 时，另一入口可能没有执行 producer；只有 copy_root_cfg_scope_end 证明整个
        // 前向子图 predecessor-closed 的 branch join 才能合流。
        return None;
    }
    let successor_range = cfg.blocks.get(successor.index())?.instrs;
    let block_end = cfg.blocks.get(block.index())?.instrs.end();
    if successor_range.is_empty() || successor_range.start.index() < block_end {
        // 候选拒绝[SemanticBarrier:Lifetime]：回边会再次执行同一静态 copy def；把首轮
        // reaching root 冻结到函数作用域会混同迭代 transaction，并越过真实覆盖/失活点。
        return None;
    }
    Some(successor)
}

fn direct_scalar_overwrite(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
    index: usize,
    home: Reg,
) -> Option<CopyRootOverwrite> {
    let value = direct_scalar_overwrite_value(proto.instrs.get(index)?, home)?;
    let def = dataflow.instr_def_for_reg(InstrRef(index), home)?;
    let direct = TempId(def.index());
    (fixed_temps.get(def.index()) == Some(&direct)).then_some(CopyRootOverwrite {
        temp: direct,
        value,
    })
}

fn direct_scalar_overwrite_value(instr: &LowInstr, home: Reg) -> Option<CopyRootScalarValue> {
    match instr {
        LowInstr::LoadNil(load_nil) if load_nil.dst.start == home && load_nil.dst.len == 1 => {
            Some(CopyRootScalarValue::Nil)
        }
        LowInstr::LoadBool(load_bool) if load_bool.dst == home => {
            Some(CopyRootScalarValue::Boolean(load_bool.value))
        }
        LowInstr::LoadInteger(load_integer) if load_integer.dst == home => {
            Some(CopyRootScalarValue::Integer(load_integer.value))
        }
        LowInstr::LoadNumber(load_number) if load_number.dst == home => {
            Some(CopyRootScalarValue::Number(load_number.value))
        }
        // 候选拒绝[SemanticBarrier:Lifetime]：collectable/effectful overwrite 若改写为
        // PhysicalRoot local，会把新 RHS 的生命周期延长到 raw home 失活点之后。
        _ => None,
    }
}

fn effect_active_top_lower_bound(effect: &crate::structure::InstrEffect) -> usize {
    effect
        .fixed_uses
        .iter()
        .chain(&effect.fixed_must_defs)
        .map(|reg| reg.index().saturating_add(1))
        .chain(effect.open_use.map(Reg::index))
        .chain(effect.open_must_def.map(Reg::index))
        .max()
        .unwrap_or_default()
}

fn effect_keeps_copy_home_rooted(effect: &crate::structure::InstrEffect, home: Reg) -> bool {
    effect_active_top_lower_bound(effect) > home.index()
}

fn fixed_input_root_prefix_top<const N: usize>(regs: [Reg; N]) -> usize {
    regs.into_iter()
        .map(|reg| reg.index().saturating_add(1))
        .max()
        .unwrap_or_default()
}

fn low_instr_may_observe_gc_roots(effect_summaries: &[SideEffectSummary], index: usize) -> bool {
    const OBSERVATION_TAGS: &[EffectTag] = &[
        EffectTag::Alloc,
        EffectTag::ReadTable,
        EffectTag::WriteTable,
        EffectTag::ReadEnv,
        EffectTag::WriteEnv,
        EffectTag::Call,
        EffectTag::Metamethod,
    ];

    effect_summaries.get(index).is_some_and(|summary| {
        OBSERVATION_TAGS
            .iter()
            .any(|tag| summary.tags.contains(tag))
    })
}

fn fill_phi_home_slots(
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    temp_home_slots: &mut [HomeSlotResolution],
) {
    let phi_count = plan.phis().len();
    let mut resolutions = vec![HomeSlotResolution::Pending; phi_count];
    let mut consumers = vec![Vec::<PhiId>::new(); phi_count];
    let mut pending = VecDeque::<(PhiId, HomeSlotResolution)>::new();

    for phi in plan.phis() {
        let mut resolution = HomeSlotResolution::Pending;
        for incoming in &phi.incomings {
            match incoming.disposition {
                PhiIncomingDisposition::Dead => continue,
                PhiIncomingDisposition::DiagnosticUnresolved => {
                    resolution = HomeSlotResolution::Unknown;
                    continue;
                }
                PhiIncomingDisposition::RegionInput(_)
                | PhiIncomingDisposition::RegionResult(_)
                | PhiIncomingDisposition::LoopCarried(_)
                | PhiIncomingDisposition::EdgeCopy => {}
            }
            if let SsaValue::Phi(source) = incoming.value {
                if let Some(source_consumers) = consumers.get_mut(source.index()) {
                    source_consumers.push(phi.phi);
                }
                continue;
            }
            resolution = merge_home_slot_resolutions(
                resolution,
                home_slot_resolution_for_leaf(incoming.value, temp_home_slots),
            );
        }
        let Some(slot) = resolutions.get_mut(phi.phi.index()) else {
            continue;
        };
        *slot = resolution.clone();
        if !matches!(resolution, HomeSlotResolution::Pending) {
            pending.push_back((phi.phi, resolution));
        }
    }

    // resolution 只会由 Pending 增长为有限集，或传播为 Unknown；集合有限，因此必然收敛。
    while let Some((phi_id, source_resolution)) = pending.pop_front() {
        let Some(phi_consumers) = consumers.get(phi_id.index()) else {
            continue;
        };
        for consumer in phi_consumers {
            let Some(resolution) = resolutions.get_mut(consumer.index()) else {
                continue;
            };
            let merged = merge_home_slot_resolutions(resolution.clone(), source_resolution.clone());
            if merged != *resolution {
                *resolution = merged.clone();
                pending.push_back((*consumer, merged));
            }
        }
    }

    // 纯 phi 环没有已知 leaf；依赖该环的后续 phi 也不能只凭其它 incoming
    // 继承 home slot。在反向索引上做一次闭包，避免重新扫描 incoming。
    let mut unresolved = VecDeque::new();
    let mut invalid = vec![false; phi_count];
    for (index, resolution) in resolutions.iter().enumerate() {
        if matches!(resolution, HomeSlotResolution::Pending) {
            invalid[index] = true;
            unresolved.push_back(PhiId(index));
        }
    }
    while let Some(phi_id) = unresolved.pop_front() {
        let Some(phi_consumers) = consumers.get(phi_id.index()) else {
            continue;
        };
        for consumer in phi_consumers {
            let Some(is_invalid) = invalid.get_mut(consumer.index()) else {
                continue;
            };
            if *is_invalid {
                continue;
            }
            *is_invalid = true;
            if let Some(resolution) = resolutions.get_mut(consumer.index()) {
                *resolution = HomeSlotResolution::Unknown;
            }
            unresolved.push_back(*consumer);
        }
    }

    let phi_temp_offset = dataflow.defs.len();
    for (phi_index, resolution) in resolutions.into_iter().enumerate() {
        if let Some(home_slot) = temp_home_slots.get_mut(phi_temp_offset + phi_index) {
            *home_slot = resolution;
        }
    }
}

fn home_slot_resolution_for_leaf(
    value: SsaValue,
    temp_home_slots: &[HomeSlotResolution],
) -> HomeSlotResolution {
    match value {
        SsaValue::Entry(reg) => HomeSlotResolution::from_home(HomeSlotKey::new(reg.index(), 0)),
        SsaValue::Def(def) => temp_home_slots
            .get(def.index())
            .cloned()
            .unwrap_or(HomeSlotResolution::Unknown),
        SsaValue::Phi(_) => HomeSlotResolution::Pending,
    }
}

fn merge_home_slot_resolutions(
    left: HomeSlotResolution,
    right: HomeSlotResolution,
) -> HomeSlotResolution {
    match (left, right) {
        (HomeSlotResolution::Unknown, _) | (_, HomeSlotResolution::Unknown) => {
            HomeSlotResolution::Unknown
        }
        (HomeSlotResolution::Pending, known) | (known, HomeSlotResolution::Pending) => known,
        (HomeSlotResolution::Known(mut left), HomeSlotResolution::Known(right)) => {
            left.extend(right);
            HomeSlotResolution::Known(left)
        }
    }
}

fn merge_possible_home_slots(
    left: Option<BTreeSet<HomeSlotKey>>,
    right: Option<BTreeSet<HomeSlotKey>>,
) -> Option<BTreeSet<HomeSlotKey>> {
    let (Some(mut left), Some(right)) = (left, right) else {
        return None;
    };
    left.extend(right);
    Some(left)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::structure::{
        BasicBlock, BlockKind, CfgEdge, EdgeKind, EdgeRef, InstrEffect, InstrRange,
    };
    use crate::transformer::{
        BranchCond, BranchInstr, CallInstr, CallKind, CondOperand, JumpInstr, LoadBoolInstr,
        LoadIntegerInstr, LoadNilInstr, LoadNumberInstr, MoveInstr, NewTableInstr, RegRange,
        ResultPack, ReturnInstr, ValuePack,
    };

    #[test]
    fn physical_home_universe_covers_entry_and_close_epochs() {
        let facts = SlotEpochFacts {
            epochs_by_reg: vec![
                None,
                Some(SlotEpochFlow {
                    at_instr: vec![0, 1, 1, 2],
                    spans_entry: true,
                }),
            ],
            reference_captured_regs: vec![false, true],
        };

        assert_eq!(
            facts.all_home_slots(3),
            BTreeSet::from([
                HomeSlotKey::new(0, 0),
                HomeSlotKey::new(1, 0),
                HomeSlotKey::new(1, 1),
                HomeSlotKey::new(1, 2),
                HomeSlotKey::new(2, 0),
            ])
        );
    }

    #[test]
    fn home_resolution_retains_finite_multi_home_union() {
        let first = HomeSlotKey::new(0, 0);
        let second = HomeSlotKey::new(1, 0);
        let merged = merge_home_slot_resolutions(
            HomeSlotResolution::from_home(first),
            HomeSlotResolution::from_home(second),
        );

        assert_eq!(merged.exact_home(), None);
        assert_eq!(
            merged.complete_homes(),
            Some(BTreeSet::from([first, second]))
        );
        assert_eq!(
            merge_home_slot_resolutions(merged, HomeSlotResolution::Unknown),
            HomeSlotResolution::Unknown
        );
    }

    #[test]
    fn binding_merge_retains_complete_home_union_but_invalidates_exact_home() {
        let source = TempId(0);
        let target = LocalId(0);
        let source_home = HomeSlotKey::new(1, 0);
        let target_home = HomeSlotKey::new(0, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(source, source_home);
        facts.record_local_home_slot(target, target_home);

        facts.record_temp_to_local_merge(source, target);

        assert_eq!(facts.trusted_local_home_slot(target), None);
        assert_eq!(
            facts.possible_local_home_slots(target),
            Some(BTreeSet::from([target_home, source_home]))
        );
    }

    #[test]
    fn dedicated_protocol_root_prefix_excludes_future_result_slots() {
        assert_eq!(fixed_input_root_prefix_top([Reg(4)]), 5);
        assert_eq!(fixed_input_root_prefix_top([Reg(4), Reg(5), Reg(6)]), 7);
        assert!(Reg(6).index() < fixed_input_root_prefix_top([Reg(4), Reg(5), Reg(6)]));
        assert!(Reg(7).index() >= fixed_input_root_prefix_top([Reg(4), Reg(5), Reg(6)]));
    }

    #[test]
    fn copy_root_linear_fast_path_crosses_only_a_forward_single_entry_block() {
        let forward = Cfg {
            blocks: vec![
                BasicBlock {
                    kind: BlockKind::Normal,
                    instrs: InstrRange::new(InstrRef(0), 2),
                },
                BasicBlock {
                    kind: BlockKind::Normal,
                    instrs: InstrRange::new(InstrRef(2), 1),
                },
                BasicBlock {
                    kind: BlockKind::SyntheticExit,
                    instrs: InstrRange::new(InstrRef(3), 0),
                },
            ],
            edges: vec![
                CfgEdge {
                    from: BlockRef(0),
                    to: BlockRef(1),
                    kind: EdgeKind::Jump,
                },
                CfgEdge {
                    from: BlockRef(1),
                    to: BlockRef(2),
                    kind: EdgeKind::Return,
                },
            ],
            entry_block: BlockRef(0),
            exit_block: BlockRef(2),
            block_order: vec![BlockRef(0), BlockRef(1)],
            instr_to_block: vec![BlockRef(0), BlockRef(0), BlockRef(1)],
            preds: vec![vec![], vec![EdgeRef(0)], vec![EdgeRef(1)]],
            succs: vec![vec![EdgeRef(0)], vec![EdgeRef(1)], vec![]],
            reachable_blocks: BTreeSet::from([BlockRef(0), BlockRef(1), BlockRef(2)]),
        };
        assert_eq!(
            copy_root_forward_block_successor(&forward, BlockRef(0)),
            Some(BlockRef(1))
        );

        let backedge = Cfg {
            blocks: vec![
                BasicBlock {
                    kind: BlockKind::Normal,
                    instrs: InstrRange::new(InstrRef(0), 1),
                },
                BasicBlock {
                    kind: BlockKind::Normal,
                    instrs: InstrRange::new(InstrRef(1), 1),
                },
                BasicBlock {
                    kind: BlockKind::SyntheticExit,
                    instrs: InstrRange::new(InstrRef(2), 0),
                },
            ],
            edges: vec![
                CfgEdge {
                    from: BlockRef(0),
                    to: BlockRef(1),
                    kind: EdgeKind::Fallthrough,
                },
                CfgEdge {
                    from: BlockRef(1),
                    to: BlockRef(0),
                    kind: EdgeKind::Jump,
                },
            ],
            entry_block: BlockRef(0),
            exit_block: BlockRef(2),
            block_order: vec![BlockRef(0), BlockRef(1)],
            instr_to_block: vec![BlockRef(0), BlockRef(1)],
            preds: vec![vec![EdgeRef(1)], vec![EdgeRef(0)], vec![]],
            succs: vec![vec![EdgeRef(0)], vec![EdgeRef(1)], vec![]],
            reachable_blocks: BTreeSet::from([BlockRef(0), BlockRef(1)]),
        };
        assert_eq!(
            copy_root_forward_block_successor(&backedge, BlockRef(1)),
            None
        );
        assert_eq!(
            copy_root_cfg_scope_end(
                &[
                    LowInstr::Jump(JumpInstr {
                        target: InstrRef(1),
                    }),
                    LowInstr::Jump(JumpInstr {
                        target: InstrRef(0),
                    }),
                ],
                &backedge,
                &[InstrEffect::default(), InstrEffect::default()],
                &[SideEffectSummary::default(), SideEffectSummary::default()],
                BlockRef(0),
                true,
                Reg(1),
            ),
            None
        );
    }

    #[test]
    fn copy_root_cfg_join_meets_observation_from_every_predecessor() {
        let cfg = Cfg {
            blocks: vec![
                BasicBlock {
                    kind: BlockKind::Normal,
                    instrs: InstrRange::new(InstrRef(0), 1),
                },
                BasicBlock {
                    kind: BlockKind::Normal,
                    instrs: InstrRange::new(InstrRef(1), 2),
                },
                BasicBlock {
                    kind: BlockKind::Normal,
                    instrs: InstrRange::new(InstrRef(3), 2),
                },
                BasicBlock {
                    kind: BlockKind::Normal,
                    instrs: InstrRange::new(InstrRef(5), 1),
                },
                BasicBlock {
                    kind: BlockKind::SyntheticExit,
                    instrs: InstrRange::new(InstrRef(6), 0),
                },
            ],
            edges: vec![
                CfgEdge {
                    from: BlockRef(0),
                    to: BlockRef(1),
                    kind: EdgeKind::BranchTrue,
                },
                CfgEdge {
                    from: BlockRef(0),
                    to: BlockRef(2),
                    kind: EdgeKind::BranchFalse,
                },
                CfgEdge {
                    from: BlockRef(1),
                    to: BlockRef(3),
                    kind: EdgeKind::Jump,
                },
                CfgEdge {
                    from: BlockRef(2),
                    to: BlockRef(3),
                    kind: EdgeKind::Jump,
                },
                CfgEdge {
                    from: BlockRef(3),
                    to: BlockRef(4),
                    kind: EdgeKind::Return,
                },
            ],
            entry_block: BlockRef(0),
            exit_block: BlockRef(4),
            block_order: vec![BlockRef(0), BlockRef(1), BlockRef(2), BlockRef(3)],
            instr_to_block: vec![
                BlockRef(0),
                BlockRef(1),
                BlockRef(1),
                BlockRef(2),
                BlockRef(2),
                BlockRef(3),
            ],
            preds: vec![
                vec![],
                vec![EdgeRef(0)],
                vec![EdgeRef(1)],
                vec![EdgeRef(2), EdgeRef(3)],
                vec![EdgeRef(4)],
            ],
            succs: vec![
                vec![EdgeRef(0), EdgeRef(1)],
                vec![EdgeRef(2)],
                vec![EdgeRef(3)],
                vec![EdgeRef(4)],
                vec![],
            ],
            reachable_blocks: BTreeSet::from([
                BlockRef(0),
                BlockRef(1),
                BlockRef(2),
                BlockRef(3),
                BlockRef(4),
            ]),
        };
        let observing_call = || {
            LowInstr::Call(CallInstr {
                callee: Reg(2),
                args: ValuePack::Fixed(RegRange::new(Reg(3), 0)),
                results: ResultPack::Ignore,
                kind: CallKind::Normal,
                method_name: None,
            })
        };
        let mut instrs = vec![
            LowInstr::Branch(BranchInstr {
                cond: BranchCond::truthy(CondOperand::Reg(Reg(0)), false),
                then_target: InstrRef(1),
                else_target: InstrRef(3),
            }),
            observing_call(),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(5),
            }),
            observing_call(),
            LowInstr::Jump(JumpInstr {
                target: InstrRef(5),
            }),
            LowInstr::Return(ReturnInstr {
                values: ValuePack::Fixed(RegRange::new(Reg(0), 0)),
            }),
        ];
        let effects = vec![InstrEffect::default(); instrs.len()];
        let summaries = vec![SideEffectSummary::default(); instrs.len()];

        assert_eq!(
            copy_root_cfg_scope_end(
                &instrs,
                &cfg,
                &effects,
                &summaries,
                BlockRef(0),
                false,
                Reg(1),
            ),
            Some(())
        );

        instrs[3] = LowInstr::Move(MoveInstr {
            dst: Reg(3),
            src: Reg(4),
        });
        assert_eq!(
            copy_root_cfg_scope_end(
                &instrs,
                &cfg,
                &effects,
                &summaries,
                BlockRef(0),
                false,
                Reg(1),
            ),
            None
        );
    }

    #[test]
    fn copy_root_cfg_collects_each_forward_branch_scalar_overwrite() {
        let cfg = Cfg {
            blocks: vec![
                BasicBlock {
                    kind: BlockKind::Normal,
                    instrs: InstrRange::new(InstrRef(0), 1),
                },
                BasicBlock {
                    kind: BlockKind::Normal,
                    instrs: InstrRange::new(InstrRef(1), 2),
                },
                BasicBlock {
                    kind: BlockKind::Normal,
                    instrs: InstrRange::new(InstrRef(3), 2),
                },
                BasicBlock {
                    kind: BlockKind::SyntheticExit,
                    instrs: InstrRange::new(InstrRef(5), 0),
                },
            ],
            edges: vec![
                CfgEdge {
                    from: BlockRef(0),
                    to: BlockRef(1),
                    kind: EdgeKind::BranchTrue,
                },
                CfgEdge {
                    from: BlockRef(0),
                    to: BlockRef(2),
                    kind: EdgeKind::BranchFalse,
                },
            ],
            entry_block: BlockRef(0),
            exit_block: BlockRef(3),
            block_order: vec![BlockRef(0), BlockRef(1), BlockRef(2)],
            instr_to_block: vec![
                BlockRef(0),
                BlockRef(1),
                BlockRef(1),
                BlockRef(2),
                BlockRef(2),
            ],
            preds: vec![vec![], vec![EdgeRef(0)], vec![EdgeRef(1)], vec![]],
            succs: vec![vec![EdgeRef(0), EdgeRef(1)], vec![], vec![], vec![]],
            reachable_blocks: BTreeSet::from([BlockRef(0), BlockRef(1), BlockRef(2)]),
        };
        let observing_call = || {
            LowInstr::Call(CallInstr {
                callee: Reg(2),
                args: ValuePack::Fixed(RegRange::new(Reg(3), 0)),
                results: ResultPack::Ignore,
                kind: CallKind::Normal,
                method_name: None,
            })
        };
        let instrs = vec![
            LowInstr::Branch(BranchInstr {
                cond: BranchCond::truthy(CondOperand::Reg(Reg(0)), false),
                then_target: InstrRef(1),
                else_target: InstrRef(3),
            }),
            observing_call(),
            LowInstr::LoadBool(LoadBoolInstr {
                dst: Reg(1),
                value: false,
            }),
            observing_call(),
            LowInstr::LoadInteger(LoadIntegerInstr {
                dst: Reg(1),
                value: 0,
            }),
        ];
        let mut effects = vec![InstrEffect::default(); instrs.len()];
        effects[2].fixed_must_defs.insert(Reg(1));
        effects[4].fixed_must_defs.insert(Reg(1));
        let summaries = vec![SideEffectSummary::default(); instrs.len()];
        let overwrite = |index, _home| match index {
            2 => Some(CopyRootOverwrite {
                temp: TempId(2),
                value: CopyRootScalarValue::Boolean(false),
            }),
            4 => Some(CopyRootOverwrite {
                temp: TempId(4),
                value: CopyRootScalarValue::Integer(0),
            }),
            _ => None,
        };

        let ends = copy_root_cfg_end_with(
            CopyRootCfgInputs {
                instrs: &instrs,
                cfg: &cfg,
                instr_effects: &effects,
                effect_summaries: &summaries,
                home: Reg(1),
            },
            BlockRef(0),
            false,
            overwrite,
        )
        .expect("both dominated paths observe then overwrite the root home");
        assert!(!ends.scope_end);
        assert_eq!(
            ends.overwrites.keys().copied().collect::<Vec<_>>(),
            vec![TempId(2), TempId(4)]
        );

        assert!(
            copy_root_cfg_end_with(
                CopyRootCfgInputs {
                    instrs: &instrs,
                    cfg: &cfg,
                    instr_effects: &effects,
                    effect_summaries: &summaries,
                    home: Reg(1),
                },
                BlockRef(0),
                false,
                |index, home| (index == 2).then(|| overwrite(index, home)).flatten(),
            )
            .is_none(),
            "a collectable/effectful overwrite on either path must reject the whole transaction"
        );
    }

    #[test]
    fn copy_root_direct_scalar_overwrite_excludes_collectable_and_effectful_values() {
        let home = Reg(1);
        assert_eq!(
            direct_scalar_overwrite_value(
                &LowInstr::LoadNil(LoadNilInstr {
                    dst: RegRange::new(home, 1),
                }),
                home,
            ),
            Some(CopyRootScalarValue::Nil)
        );
        assert_eq!(
            direct_scalar_overwrite_value(
                &LowInstr::LoadBool(LoadBoolInstr {
                    dst: home,
                    value: true,
                }),
                home,
            ),
            Some(CopyRootScalarValue::Boolean(true))
        );
        assert_eq!(
            direct_scalar_overwrite_value(
                &LowInstr::LoadNumber(LoadNumberInstr {
                    dst: home,
                    value: -0.0,
                }),
                home,
            ),
            Some(CopyRootScalarValue::Number(-0.0))
        );
        assert_eq!(
            direct_scalar_overwrite_value(&LowInstr::NewTable(NewTableInstr { dst: home }), home,),
            None
        );
        assert_eq!(
            direct_scalar_overwrite_value(
                &LowInstr::Call(CallInstr {
                    callee: Reg(0),
                    args: ValuePack::Fixed(RegRange::new(Reg(1), 0)),
                    results: ResultPack::Fixed(RegRange::new(home, 1)),
                    kind: CallKind::Normal,
                    method_name: None,
                }),
                home,
            ),
            None
        );
    }

    #[test]
    fn copy_root_successor_observation_requires_active_top_above_home() {
        let home = Reg(1);
        let mut expired = InstrEffect::default();
        expired.fixed_uses.insert(Reg(0));
        assert!(!effect_keeps_copy_home_rooted(&expired, home));

        let mut rooted = InstrEffect::default();
        rooted.fixed_uses.insert(Reg(2));
        assert!(effect_keeps_copy_home_rooted(&rooted, home));
    }
}
