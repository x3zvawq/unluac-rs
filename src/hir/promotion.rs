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
//! - root 观察期间的有效槽位只消费 Dataflow 的 `RootObservation`；这里负责路径闭合和
//!   producer/endpoint 配对，不重建 CALL、TFORCALL、TBC 的 VM 栈协议
//! - 由 `NewTable` canonical def 直接产生的 temp 单独保留 constructor origin；MOVE、
//!   phi 或后续 local 物化不能冒充分配本身
//! - 覆盖前的非资源值按 canonical def 保存为入口 nil 或已定义 scalar；例如 LOADNIL
//!   的 temp 被后续 HIR 内联删除，下一次 MOVE 仍能证明没有旧对象需要释放
//! - ordinary CALL 参数交接沿 Dataflow SSA 固定前缀与 caller 边界发布到具体调用，
//!   例如 `f({})` 的参数 home 不得在后层被重建成调用后继续持有的 caller root
//! - possible/complete home query 借用已有集合；定义写需要补充新 home 时才复制。
//!   跨 provenance 改写保存来源的 owner 显式取得 owned 快照，不让后层缓存整份映射。

mod call_roots;
mod slot_captures;

use crate::hir::common::{HirExpr, HirMethodSetupProtocolId, HirStmt, LocalId, ParamId, TempId};
use crate::structure::{
    BlockRef, Cfg, DataflowFacts, EdgeRef, ForwardRouteKind, GraphFacts, InstrEffect,
    LoopConditionPrefixPlacement, LoopVmProtocol, PhiId, PhiIncomingDisposition, RegionId,
    RegionPlan, RootObservation, SideEffectSummary, SsaValue, StructurePlan,
};
use crate::transformer::{CaptureSource, InstrRef, LowInstr, LoweredProto, Reg, ResultPack};
use std::borrow::Cow;
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
}

struct SlotEpochFlow {
    at_instr: Vec<usize>,
    reference_capture_before: Vec<bool>,
    spans_entry: bool,
}

impl SlotEpochFacts {
    pub(super) fn analyze(
        proto: &LoweredProto,
        cfg: &Cfg,
        graph: &GraphFacts,
        dataflow: &DataflowFacts,
    ) -> Self {
        let mut tracked_regs = dataflow.reference_captured_regs().collect::<BTreeSet<_>>();
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
        Self { epochs_by_reg }
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

    pub(super) fn reference_capture_may_be_open(&self, reg: Reg, instr: InstrRef) -> bool {
        self.epochs_by_reg
            .get(reg.index())
            .and_then(Option::as_ref)
            .is_some_and(|flow| flow.reference_capture_before[instr.index()])
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
        .fixed_defs_for_reg(reg)
        .iter()
        .all(|&def| at_instr[dataflow.def_instr(def).index()] == 0);
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
        reference_capture_before: slot_captures::before_instructions(proto, cfg, reg),
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
    graph.extend_dominance_frontier(close_blocks, &mut placed, |_| true);

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

/// 物理 home 集合视图：已有事实借用，新增写入的并集按需持有独立存储。
pub(super) type HomeSlots<'a> = Cow<'a, BTreeSet<HomeSlotKey>>;

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

    fn complete_homes(&self) -> Option<&BTreeSet<HomeSlotKey>> {
        match self {
            Self::Known(homes) => Some(homes),
            Self::Pending | Self::Unknown => None,
        }
    }
}

/// 单个 proto 的 temp promotion 与后续 binding provenance 辅助事实。
#[derive(Debug, Clone, Default)]
pub(super) struct ProtoPromotionFacts {
    temp_home_slots: Vec<HomeSlotResolution>,
    immediate_move_write_homes: Vec<BTreeSet<HomeSlotKey>>,
    inert_home_overwrites: BTreeMap<TempId, InertHomeOverwrite>,
    entry_nil_phi_temps: BTreeSet<TempId>,
    entry_nil_phi_locals: BTreeSet<LocalId>,
    entry_nil_pruned_locals: BTreeSet<LocalId>,
    repeat_condition_prefix_temps: BTreeSet<TempId>,
    direct_table_seed_temps: BTreeSet<TempId>,
    direct_table_seed_locals: BTreeSet<LocalId>,
    loop_carrier_temps: BTreeSet<TempId>,
    implicit_root_scope_fences: BTreeMap<RegionId, ImplicitRootScopeFence>,
    scope_end_copy_root_temps: BTreeSet<TempId>,
    copy_root_overwrites: BTreeMap<TempId, Vec<CopyRootOverwrite>>,
    copy_root_endpoint_producers: BTreeMap<TempId, BTreeSet<TempId>>,
    promoted_local_by_temp: BTreeMap<TempId, LocalId>,
    local_home_slots: Vec<HomeSlotResolution>,
    invalidated_param_homes: BTreeSet<ParamId>,
    invalidated_local_homes: BTreeSet<LocalId>,
    invalidated_temp_homes: BTreeSet<TempId>,
    home_free_locals: BTreeSet<LocalId>,
    possible_param_homes: BTreeMap<ParamId, Option<BTreeSet<HomeSlotKey>>>,
    possible_local_homes: BTreeMap<LocalId, Option<BTreeSet<HomeSlotKey>>>,
    possible_temp_homes: BTreeMap<TempId, Option<BTreeSet<HomeSlotKey>>>,
    propagated_param_definition_write_homes: BTreeMap<ParamId, BTreeSet<HomeSlotKey>>,
    propagated_local_definition_write_homes: BTreeMap<LocalId, BTreeSet<HomeSlotKey>>,
    propagated_temp_definition_write_homes: BTreeMap<TempId, BTreeSet<HomeSlotKey>>,
    physical_home_universe: BTreeSet<HomeSlotKey>,
    compact_home_slots: bool,
    argument_roots_by_call: BTreeMap<InstrRef, Vec<crate::hir::common::HirCallArgumentRoot>>,
    argument_root_producers: BTreeSet<TempId>,
    unobserved_call_result_ends: BTreeMap<TempId, TempId>,
    frame_result_ends_by_call: BTreeMap<InstrRef, Vec<TempId>>,
    method_setup_protocols: Vec<HirMethodSetupProtocol>,
    method_setup_protocol_by_call: BTreeMap<InstrRef, HirMethodSetupProtocolId>,
    method_setup_protocol_by_get: BTreeMap<InstrRef, HirMethodSetupProtocolId>,
}

/// raw VM active-top 与最终 Structure sequence 共同冻结的隐式 root 作用域。
///
/// `ended_roots` 是 collective 证明的一部分而不是 consumer 的匹配输入；它记录在
/// ordinary call 观察期间已被 caller prefix 排除的全部原始 VM home。真正的 lowering
/// 边界只由两个 direct child identity 决定。无法把所有 by-value holder 一并纳入时
/// producer 不发布该 fence。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ImplicitRootScopeFence {
    pub(super) first_child: RegionId,
    pub(super) end_before_child: RegionId,
    pub(super) ended_roots: BTreeSet<TempId>,
}

/// low method setup 与 canonical callee definition 之间的 HIR 私有桥接事实。
///
/// 它只活到 HIR finalizer；AST 永远不会看到 `TempId` 或 physical home。
#[derive(Debug, Clone)]
pub(super) struct HirMethodSetupProtocol {
    pub(super) callee_temp: TempId,
    pub(super) prior_callee_root_temp: TempId,
    pub(super) method_key: crate::LuaString,
}

impl ProtoPromotionFacts {
    /// 查询原始参数 producer 候选；消费者仍须匹配当前唯一 definition 与具体 call 参数端点。
    pub(super) fn temp_is_transferred_call_argument(&self, temp: TempId) -> bool {
        self.trusted_temp_home_slot(temp).is_some() && self.argument_root_producers.contains(&temp)
    }

    /// 源 call result 在最后值读取后、首个观察前已有精确同 home 覆盖。
    /// 这仅约束物理 root 后缀，当前 producer 单写/单读和移动到消费点的求值顺序仍由 HIR 证明。
    pub(super) fn call_result_root_ends_after_value_use(&self, temp: TempId) -> bool {
        let Some(home) = self.trusted_temp_home_slot(temp) else {
            return false;
        };
        self.unobserved_call_result_ends
            .get(&temp)
            .is_some_and(|end| self.trusted_temp_home_slot(*end) == Some(home))
    }

    /// 精确 dispatch 排除的原始 caller root；当前值流和求值前缀仍由 HIR 消费者核对。
    pub(super) fn call_frame_root_ends(&self, call: InstrRef) -> Vec<TempId> {
        self.frame_result_ends_by_call
            .get(&call)
            .into_iter()
            .flatten()
            .copied()
            .filter(|temp| self.trusted_temp_home_slot(*temp).is_some())
            .collect()
    }

    pub(super) fn call_argument_roots(
        &self,
        call: InstrRef,
    ) -> Vec<crate::hir::common::HirCallArgumentRoot> {
        self.argument_roots_by_call
            .get(&call)
            .cloned()
            .unwrap_or_default()
    }

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
        let implicit_root_scope_fences =
            collect_implicit_root_scope_fences(proto, cfg, dataflow, plan, fixed_temps);
        let copy_root_endpoint_producers = copy_roots
            .overwrites
            .iter()
            .flat_map(|(producer, overwrites)| {
                overwrites
                    .iter()
                    .map(move |overwrite| (overwrite.temp(), *producer))
            })
            .fold(
                BTreeMap::<TempId, BTreeSet<TempId>>::new(),
                |mut index, (endpoint, producer)| {
                    index.entry(endpoint).or_default().insert(producer);
                    index
                },
            );

        let argument_roots_by_call =
            call_roots::collect(proto, cfg, dataflow, slot_epochs, fixed_temps);
        let argument_root_producers = argument_roots_by_call
            .values()
            .flatten()
            .map(|root| root.producer)
            .collect();
        Self {
            argument_roots_by_call,
            argument_root_producers,
            frame_result_ends_by_call: call_roots::collect_frame_result_ends(
                proto,
                cfg,
                dataflow,
                slot_epochs,
                fixed_temps,
            ),
            unobserved_call_result_ends: call_roots::collect_unobserved_result_ends(
                proto,
                cfg,
                dataflow,
                fixed_temps,
            ),
            temp_home_slots,
            immediate_move_write_homes,
            inert_home_overwrites: collect_inert_home_overwrites(proto, dataflow, fixed_temps),
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
            implicit_root_scope_fences,
            scope_end_copy_root_temps: copy_roots.scope_end,
            copy_root_overwrites: copy_roots.overwrites,
            copy_root_endpoint_producers,
            promoted_local_by_temp: BTreeMap::new(),
            local_home_slots: Vec::new(),
            invalidated_param_homes: BTreeSet::new(),
            invalidated_local_homes: BTreeSet::new(),
            invalidated_temp_homes: BTreeSet::new(),
            home_free_locals: BTreeSet::new(),
            possible_param_homes: BTreeMap::new(),
            possible_local_homes: BTreeMap::new(),
            possible_temp_homes: BTreeMap::new(),
            propagated_param_definition_write_homes: BTreeMap::new(),
            propagated_local_definition_write_homes: BTreeMap::new(),
            propagated_temp_definition_write_homes: BTreeMap::new(),
            physical_home_universe,
            compact_home_slots: false,
            method_setup_protocols: Vec::new(),
            method_setup_protocol_by_call: BTreeMap::new(),
            method_setup_protocol_by_get: BTreeMap::new(),
        }
    }

    pub(super) fn is_direct_table_seed_temp(&self, temp: TempId) -> bool {
        self.direct_table_seed_temps.contains(&temp)
    }

    /// 多个静态 definition 合为一个 carrier 后，home 仍精确，但原 producer 的专属
    /// 正向证书不再代表整个 binding。物理根负向事实由合并入口保护，不在此处删除。
    pub(super) fn retire_coalesced_definition_facts(&mut self, temps: &BTreeSet<TempId>) {
        self.inert_home_overwrites
            .retain(|temp, _| !temps.contains(temp));
        self.entry_nil_phi_temps
            .retain(|temp| !temps.contains(temp));
        self.direct_table_seed_temps
            .retain(|temp| !temps.contains(temp));
        self.repeat_condition_prefix_temps
            .retain(|temp| !temps.contains(temp));
        self.loop_carrier_temps.retain(|temp| !temps.contains(temp));
        self.promoted_local_by_temp
            .retain(|temp, _| !temps.contains(temp));
        self.argument_root_producers
            .retain(|temp| !temps.contains(temp));
        self.unobserved_call_result_ends
            .retain(|producer, end| !temps.contains(producer) && !temps.contains(end));
        self.frame_result_ends_by_call.retain(|_, roots| {
            roots.retain(|temp| !temps.contains(temp));
            !roots.is_empty()
        });
    }

    /// 该 canonical fixed def 在所有可达前驱路径上覆盖非参数槽的入口 nil。
    /// 回边携带的前一轮写入不能冒充入口值；当前 HIR 的重入与 home 合并仍由消费者检查。
    pub(super) fn overwrites_entry_nil(&self, temp: TempId) -> bool {
        self.inert_home_overwrites.get(&temp) == Some(&InertHomeOverwrite::EntryNil)
    }

    /// 前层证明当前定义覆盖非资源旧值，后续 RHS 内联删除旧写时仍保留该事实。
    pub(super) fn overwrites_gc_inert(&self, temp: TempId) -> bool {
        !self.temp_home_was_invalidated(temp) && self.inert_home_overwrites.contains_key(&temp)
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

    pub(super) fn implicit_root_scope_fence(
        &self,
        owner: RegionId,
    ) -> Option<&ImplicitRootScopeFence> {
        self.implicit_root_scope_fences.get(&owner)
    }

    /// 该 temp 的潜在对象 home 在 producer 支配的 CFG 中沿每条路径精确走到 frame end
    /// 或已登记 overwrite，且至少一条路径在终点前经过 GC-root 观察事件。
    ///
    /// 这份事实只服务于“源码读取已经结束、物理栈槽仍作为 GC root”的负向保护；若
    /// 后续 binding 合并使 home provenance 失效，就不能再消费原始证明。
    pub(super) fn is_scope_end_copy_root_temp(&self, temp: TempId) -> bool {
        !self.temp_home_was_invalidated(temp) && self.scope_end_copy_root_temps.contains(&temp)
    }

    /// 该 transaction 的所有动态路径都走到 frame end，不含需要在更早位置提交的 overwrite。
    /// 只消费 scope-end provenance、却不会同步改写 overwrite endpoint 的分析必须使用这个查询。
    pub(super) fn is_pure_scope_end_copy_root_temp(&self, temp: TempId) -> bool {
        self.is_scope_end_copy_root_temp(temp) && !self.copy_root_overwrites.contains_key(&temp)
    }

    /// 返回结束该 physical root transaction 各路径的精确 GC-inert overwrite。
    pub(super) fn copy_root_overwrites(&self, temp: TempId) -> Option<&[CopyRootOverwrite]> {
        if self.temp_home_was_invalidated(temp) {
            return None;
        }
        let producer_home = self.trusted_temp_home_slot(temp)?;
        let overwrites = self.copy_root_overwrites.get(&temp)?;
        (!overwrites.is_empty()
            && overwrites.iter().all(|overwrite| {
                let endpoint = overwrite.temp();
                !self.temp_home_was_invalidated(endpoint)
                    && match overwrite {
                        CopyRootOverwrite::Scalar { .. } => {
                            self.trusted_temp_home_slot(endpoint) == Some(producer_home)
                        }
                        CopyRootOverwrite::CallResultMove { .. } => self
                            .trusted_immediate_move_write_homes(endpoint)
                            .is_some_and(|homes| homes.contains(&producer_home)),
                    }
            }))
        .then_some(overwrites)
    }

    /// 返回以单结果 call 的紧邻透明 MOVE 精确结束的 copy-root transaction。
    ///
    /// 该 endpoint temp 自身属于 call result home，`trusted_immediate_move_write_homes`
    /// 证明同一求值事件随后还写入 producer 的旧 home。只接受唯一 endpoint，避免把
    /// CFG 分支上的多个动态终点压成一个线性 HIR handoff。
    pub(super) fn copy_root_call_result_move_overwrite(&self, temp: TempId) -> Option<TempId> {
        let [overwrite] = self.copy_root_overwrites(temp)? else {
            return None;
        };
        match overwrite {
            CopyRootOverwrite::CallResultMove { temp } => Some(*temp),
            CopyRootOverwrite::Scalar { .. } => None,
        }
    }

    /// Whether this temp is an exact scalar endpoint of a still-valid raw CFG physical-root
    /// transaction. This reverse index lets block-local consumers recover cross-child endpoints
    /// without rescanning every producer transaction for every candidate.
    pub(super) fn is_copy_root_endpoint(&self, temp: TempId) -> bool {
        if self.temp_home_was_invalidated(temp) {
            return false;
        }
        self.copy_root_endpoint_producers
            .get(&temp)
            .is_some_and(|producers| {
                producers.iter().any(|producer| {
                    self.copy_root_overwrites(*producer)
                        .is_some_and(|overwrites| {
                            overwrites.iter().any(|overwrite| overwrite.temp() == temp)
                        })
                })
            })
    }

    #[cfg(test)]
    pub(super) fn record_copy_root_overwrites_for_test(
        &mut self,
        producer: TempId,
        overwrites: Vec<(TempId, HirExpr)>,
    ) {
        let overwrites: Vec<CopyRootOverwrite> = overwrites
            .into_iter()
            .map(|(temp, value)| CopyRootOverwrite::Scalar {
                temp,
                value: CopyRootScalarValue::from_hir_expr(&value)
                    .expect("test overwrite must be a direct GC-inert scalar"),
            })
            .collect();
        for overwrite in &overwrites {
            self.copy_root_endpoint_producers
                .entry(overwrite.temp())
                .or_default()
                .insert(producer);
        }
        self.copy_root_overwrites.insert(producer, overwrites);
    }

    #[cfg(test)]
    pub(super) fn record_copy_root_call_result_move_for_test(
        &mut self,
        producer: TempId,
        endpoint: TempId,
    ) {
        let home = self
            .trusted_temp_home_slot(producer)
            .expect("test copy-root producer must retain one trusted home");
        if self.immediate_move_write_homes.len() <= endpoint.index() {
            self.immediate_move_write_homes
                .resize_with(endpoint.index() + 1, BTreeSet::new);
        }
        self.immediate_move_write_homes[endpoint.index()].insert(home);
        self.copy_root_endpoint_producers
            .entry(endpoint)
            .or_default()
            .insert(producer);
        self.copy_root_overwrites.insert(
            producer,
            vec![CopyRootOverwrite::CallResultMove { temp: endpoint }],
        );
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
    /// 已存储集合借用当前 facts；需要跨改写保留来源时显式 `into_owned`。
    pub(super) fn possible_param_home_slots(&self, param: ParamId) -> Option<HomeSlots<'_>> {
        match self.possible_param_homes.get(&param) {
            Some(homes) => homes.as_ref().map(Cow::Borrowed),
            None => Some(Cow::Owned(BTreeSet::from([HomeSlotKey::new(
                param.index(),
                0,
            )]))),
        }
    }

    pub(super) fn possible_local_home_slots(&self, local: LocalId) -> Option<HomeSlots<'_>> {
        match self.possible_local_homes.get(&local) {
            Some(homes) => homes.as_ref().map(Cow::Borrowed),
            None if self.local_has_no_physical_home(local) => Some(Cow::Owned(BTreeSet::new())),
            None => self
                .local_home_slots
                .get(local.index())
                .and_then(HomeSlotResolution::complete_homes)
                .map(Cow::Borrowed),
        }
    }

    pub(super) fn possible_temp_home_slots(&self, temp: TempId) -> Option<HomeSlots<'_>> {
        match self.possible_temp_homes.get(&temp) {
            Some(homes) => homes.as_ref().map(Cow::Borrowed),
            None => self
                .temp_home_slots
                .get(temp.index())
                .and_then(HomeSlotResolution::complete_homes)
                .map(Cow::Borrowed),
        }
    }

    /// 返回 param 在当前 HIR 改写后保守且完整的物理 home 集合。
    ///
    /// provenance 未知仍表示它来自某个物理 binding，因此必须扩大到当前 proto 的
    /// 完整 home universe；只有显式 `Some(empty)` 才表示 HIR 合成且 home-free。
    pub(super) fn complete_param_home_slots(&self, param: ParamId) -> HomeSlots<'_> {
        self.complete_possible_home_slots(self.possible_param_home_slots(param))
    }

    /// 返回 local 在当前 HIR 改写后保守且完整的物理 home 集合。
    pub(super) fn complete_local_home_slots(&self, local: LocalId) -> HomeSlots<'_> {
        self.complete_possible_home_slots(self.possible_local_home_slots(local))
    }

    /// 返回 temp 在当前 HIR 改写后保守且完整的物理 home 集合。
    pub(super) fn complete_temp_home_slots(&self, temp: TempId) -> HomeSlots<'_> {
        self.complete_possible_home_slots(self.possible_temp_home_slots(temp))
    }

    fn complete_possible_home_slots<'a>(
        &'a self,
        possible: Option<HomeSlots<'a>>,
    ) -> HomeSlots<'a> {
        possible.unwrap_or_else(|| {
            assert!(
                !self.physical_home_universe.is_empty(),
                "unknown physical binding requires a non-empty physical-home universe"
            );
            Cow::Borrowed(&self.physical_home_universe)
        })
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
        let merged = merge_possible_home_slots(
            self.possible_param_home_slots(param).map(Cow::into_owned),
            source_homes,
        );
        self.possible_param_homes.insert(param, merged);
        self.invalidated_param_homes.insert(param);
    }

    pub(super) fn record_local_home_merge(
        &mut self,
        local: LocalId,
        source_homes: Option<BTreeSet<HomeSlotKey>>,
    ) {
        let merged = merge_possible_home_slots(
            self.possible_local_home_slots(local).map(Cow::into_owned),
            source_homes,
        );
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
        let merged = merge_possible_home_slots(
            self.possible_temp_home_slots(temp).map(Cow::into_owned),
            source_homes,
        );
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

    /// 返回该 producer 紧邻透明 MOVE 链可能写入的完整物理 home 集合。
    ///
    /// home provenance 已失效时，consumer 仍须按任意物理 home 都可能被写入处理。
    pub(super) fn complete_immediate_move_write_homes(&self, temp: TempId) -> HomeSlots<'_> {
        if self
            .possible_temp_home_slots(temp)
            .is_some_and(|homes| homes.is_empty())
        {
            return Cow::Owned(BTreeSet::new());
        }
        self.complete_possible_home_slots(
            self.trusted_immediate_move_write_homes(temp)
                .map(Cow::Borrowed),
        )
    }

    /// 返回一次最终 temp 定义可能写入的全部物理 home。
    ///
    /// 除 temp 自身 home 外，还包含 low IR 中紧邻而被 HIR 隐藏的透明 MOVE，以及 carried
    /// binding 合并时继承的定义写。consumer 必须在定义 lvalue 处查询，不能在读取 TempRef
    /// 时把这些写副作用补回。
    pub(super) fn complete_temp_definition_write_homes(&self, temp: TempId) -> HomeSlots<'_> {
        Self::with_supplemental_write_homes(
            self.complete_temp_home_slots(temp),
            self.supplemental_temp_definition_write_homes(temp),
        )
    }

    /// 返回一次最终 local 定义可能写入的全部物理 home。
    pub(super) fn complete_local_definition_write_homes(&self, local: LocalId) -> HomeSlots<'_> {
        Self::with_supplemental_write_homes(
            self.complete_local_home_slots(local),
            self.supplemental_local_definition_write_homes(local),
        )
    }

    /// 返回一次最终 param 定义可能写入的全部物理 home。
    pub(super) fn complete_param_definition_write_homes(&self, param: ParamId) -> HomeSlots<'_> {
        Self::with_supplemental_write_homes(
            self.complete_param_home_slots(param),
            self.supplemental_param_definition_write_homes(param),
        )
    }

    fn with_supplemental_write_homes(
        mut homes: HomeSlots<'_>,
        writes: BTreeSet<HomeSlotKey>,
    ) -> HomeSlots<'_> {
        if !writes.is_subset(&homes) {
            homes.to_mut().extend(writes);
        }
        homes
    }

    pub(super) fn supplemental_temp_definition_write_homes(
        &self,
        temp: TempId,
    ) -> BTreeSet<HomeSlotKey> {
        let mut homes = if self
            .possible_temp_home_slots(temp)
            .is_some_and(|homes| homes.is_empty())
        {
            BTreeSet::new()
        } else {
            self.trusted_immediate_move_write_homes(temp)
                .cloned()
                .unwrap_or_default()
        };
        if let Some(propagated) = self.propagated_temp_definition_write_homes.get(&temp) {
            homes.extend(propagated.iter().copied());
        }
        homes
    }

    pub(super) fn supplemental_local_definition_write_homes(
        &self,
        local: LocalId,
    ) -> BTreeSet<HomeSlotKey> {
        self.propagated_local_definition_write_homes
            .get(&local)
            .cloned()
            .unwrap_or_default()
    }

    pub(super) fn supplemental_param_definition_write_homes(
        &self,
        param: ParamId,
    ) -> BTreeSet<HomeSlotKey> {
        self.propagated_param_definition_write_homes
            .get(&param)
            .cloned()
            .unwrap_or_default()
    }

    pub(super) fn merge_param_definition_write_homes(
        &mut self,
        param: ParamId,
        homes: BTreeSet<HomeSlotKey>,
    ) {
        self.propagated_param_definition_write_homes
            .entry(param)
            .or_default()
            .extend(homes);
    }

    pub(super) fn merge_local_definition_write_homes(
        &mut self,
        local: LocalId,
        homes: BTreeSet<HomeSlotKey>,
    ) {
        self.propagated_local_definition_write_homes
            .entry(local)
            .or_default()
            .extend(homes);
    }

    pub(super) fn merge_temp_definition_write_homes(
        &mut self,
        temp: TempId,
        homes: BTreeSet<HomeSlotKey>,
    ) {
        self.propagated_temp_definition_write_homes
            .entry(temp)
            .or_default()
            .extend(homes);
    }

    /// 返回 TBC 原始寄存器在当前 proto 中可能对应的完整物理 home 集合。
    ///
    /// value binding 的 home 可缩小到精确 epoch；若 value 是 home-free 表达式或其 home
    /// 与协议寄存器不一致，TBC 仍由原始 `reg_index` 指定物理 cell，因此退回该寄存器的
    /// 全部 close epoch。原始协议寄存器不在 universe 中属于内部事实错误。
    pub(super) fn complete_tbc_home_slots(
        &self,
        reg_index: usize,
        value_homes: &BTreeSet<HomeSlotKey>,
    ) -> BTreeSet<HomeSlotKey> {
        let matching_value_homes = value_homes
            .iter()
            .copied()
            .filter(|home| home.slot() == reg_index)
            .collect::<BTreeSet<_>>();
        if !matching_value_homes.is_empty() {
            return matching_value_homes;
        }
        let physical_homes = self
            .physical_home_universe
            .iter()
            .copied()
            .filter(|home| home.slot() == reg_index)
            .collect::<BTreeSet<_>>();
        assert!(
            !physical_homes.is_empty(),
            "to-be-closed register requires a physical home in the proto universe"
        );
        physical_homes
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
        let definition_write_homes = self.supplemental_temp_definition_write_homes(temp);
        self.merge_local_definition_write_homes(local, definition_write_homes);
        self.promoted_local_by_temp.insert(temp, local);
        let source_home = self.trusted_temp_home_slot(temp);
        let target_home = self.trusted_local_home_slot(local);
        if source_home.is_none() || source_home != target_home {
            self.record_local_home_merge(
                local,
                self.possible_temp_home_slots(temp).map(Cow::into_owned),
            );
        }
    }

    pub(super) fn promoted_local_for_temp(&self, temp: TempId) -> Option<LocalId> {
        self.promoted_local_by_temp.get(&temp).copied()
    }

    pub(super) fn record_method_setup_protocol(
        &mut self,
        call: InstrRef,
        get: InstrRef,
        callee_temp: TempId,
        prior_callee_root_temp: TempId,
        method_key: crate::LuaString,
    ) {
        let id = HirMethodSetupProtocolId::new(self.method_setup_protocols.len());
        self.method_setup_protocols.push(HirMethodSetupProtocol {
            callee_temp,
            prior_callee_root_temp,
            method_key,
        });
        self.method_setup_protocol_by_call.insert(call, id);
        self.method_setup_protocol_by_get.insert(get, id);
    }

    pub(super) fn method_setup_protocol_for_call(
        &self,
        call: InstrRef,
    ) -> Option<HirMethodSetupProtocolId> {
        self.method_setup_protocol_by_call.get(&call).copied()
    }

    pub(super) fn method_setup_protocol_for_get(
        &self,
        get: InstrRef,
    ) -> Option<HirMethodSetupProtocolId> {
        self.method_setup_protocol_by_get.get(&get).copied()
    }

    pub(super) fn method_setup_protocol(
        &self,
        id: HirMethodSetupProtocolId,
    ) -> Option<&HirMethodSetupProtocol> {
        self.method_setup_protocols.get(id.index())
    }

    pub(super) fn record_local_to_param_merge(&mut self, local: LocalId, param: ParamId) {
        let definition_write_homes = self.supplemental_local_definition_write_homes(local);
        self.merge_param_definition_write_homes(param, definition_write_homes);
        let source_home = self.trusted_local_home_slot(local);
        let target_home = self.trusted_param_home_slot(param);
        if source_home.is_none() || source_home != target_home {
            self.record_param_home_merge(
                param,
                self.possible_local_home_slots(local).map(Cow::into_owned),
            );
        }
    }

    /// 收集当前语句及嵌套 block 中按引用捕获的 temp home；不进入子 proto。
    pub(super) fn collect_captured_home_slots_in_stmt(
        &self,
        stmt: &HirStmt,
        slots: &mut BTreeSet<HomeSlotKey>,
    ) {
        crate::hir::visit::visit_stmts(
            std::slice::from_ref(stmt),
            &mut CapturedHomeSlotCollector { facts: self, slots },
        );
    }

    /// 只收集进入嵌套 block 前执行的 capture；repeat 尾条件不属于入口前缀。
    pub(super) fn collect_prefix_captured_home_slots_in_stmt(
        &self,
        stmt: &HirStmt,
        slots: &mut BTreeSet<HomeSlotKey>,
    ) {
        if matches!(
            stmt,
            HirStmt::If(_) | HirStmt::While(_) | HirStmt::NumericFor(_) | HirStmt::GenericFor(_)
        ) {
            crate::hir::visit::visit_stmt_header(
                stmt,
                &mut CapturedHomeSlotCollector { facts: self, slots },
            );
        }
    }
}

struct CapturedHomeSlotCollector<'a> {
    facts: &'a ProtoPromotionFacts,
    slots: &'a mut BTreeSet<HomeSlotKey>,
}

impl crate::hir::visit::HirVisitor for CapturedHomeSlotCollector<'_> {
    fn visit_capture(&mut self, capture: &crate::hir::HirCapture) {
        // 按值捕获不激活原槽的 sticky 身份；这里只维护尚未物化的 temp home。
        if capture.mode == crate::hir::HirCaptureMode::ByReference
            && let crate::hir::HirBinding::Temp(temp) = capture.binding
            && let Some(slot) = self.facts.home_slot(temp)
        {
            self.slots.insert(slot);
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
    let mut last_instr_by_root = std::collections::BTreeMap::<SsaValue, (usize, BlockRef)>::new();

    for (instr_index, def_ids) in dataflow.instr_defs.iter().enumerate() {
        for def_id in def_ids {
            let Some(def) = dataflow.defs.get(def_id.index()) else {
                continue;
            };
            let value = SsaValue::Def(*def_id);
            let Some(root) = dataflow.canonical_move_value(value) else {
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

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum InertHomeOverwrite {
    EntryNil,
    DefinedScalar,
}

fn collect_inert_home_overwrites(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
) -> BTreeMap<TempId, InertHomeOverwrite> {
    let param_count = usize::from(proto.signature.num_params);
    let vararg_param_reg = proto.signature.has_vararg_param_reg.then_some(param_count);
    let mut overwrites = BTreeMap::new();
    for def in &dataflow.defs {
        let direct = TempId(def.id.index());
        if fixed_temps.get(def.id.index()) != Some(&direct) {
            continue;
        }
        match dataflow.def_overwritten_value(def.id) {
            Some(SsaValue::Def(previous))
                if !ssa_value_may_hold_gc_root(proto, dataflow, SsaValue::Def(previous)) =>
            {
                overwrites.insert(direct, InertHomeOverwrite::DefinedScalar);
            }
            Some(SsaValue::Entry(reg))
                if reg.index() >= param_count && Some(reg.index()) != vararg_param_reg =>
            {
                overwrites.insert(direct, InertHomeOverwrite::EntryNil);
            }
            _ => {}
        }
    }
    overwrites
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
            dataflow
                .instr_def_for_reg(InstrRef(instr_index), new_table.dst)
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

/// Luau 等 VM 会通过 call base 收缩 active stack top；这个物理 scope end 不一定有
/// `Close` 指令。这里只为已冻结的 repeat body sequence 发布一种很窄的 collective
/// fence：repeat condition 已通过 continue route 前递到 body 的终端 dispatch child，
/// 且 dispatch 后每条路径的首个 GC/user-code observer 都已排除整个高槽 root 集。
fn collect_implicit_root_scope_fences(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    fixed_temps: &[TempId],
) -> BTreeMap<RegionId, ImplicitRootScopeFence> {
    let mut fences = BTreeMap::new();
    for (loop_id, loop_) in plan.loops() {
        let Some(loop_region) = plan.loop_region(loop_id) else {
            continue;
        };
        if !matches!(plan.loop_protocol(loop_id), Some(LoopVmProtocol::Repeat(_))) {
            continue;
        }
        let Some(RegionPlan::Loop { body, .. }) = plan.region(loop_region) else {
            continue;
        };
        let Some(fence) = implicit_repeat_root_scope_fence(
            proto,
            cfg,
            dataflow,
            plan,
            fixed_temps,
            &loop_.control_edges.continues,
            *body,
        ) else {
            continue;
        };
        fences.insert(*body, fence);
    }
    fences
}

fn implicit_repeat_root_scope_fence(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    fixed_temps: &[TempId],
    continue_edges: &[EdgeRef],
    body: RegionId,
) -> Option<ImplicitRootScopeFence> {
    let RegionPlan::Sequence { children, .. } = plan.region(body)? else {
        return None;
    };
    if children.len() < 2 {
        return None;
    }

    // A forwarded repeat-condition arc is the frozen proof that this direct body child owns
    // the source condition which an early `continue` must evaluate. All such arcs must agree.
    let mut dispatch_positions = BTreeSet::new();
    let mut repeat_condition_arc = None;
    for &edge_ref in continue_edges {
        let edge = plan.edge_plan(edge_ref)?;
        let route = edge
            .forward_route
            .and_then(|route| plan.forward_route(route))?;
        let ForwardRouteKind::RepeatConditionArc(arc) = route.kind else {
            return None;
        };
        if repeat_condition_arc.is_some_and(|expected| expected != arc) {
            return None;
        }
        repeat_condition_arc = Some(arc);
        let source_owner = plan.region_for_block(cfg.edges.get(edge_ref.index())?.from)?;
        let position = children
            .iter()
            .position(|child| plan.region_contains(*child, source_owner))?;
        dispatch_positions.insert(position);
    }
    let dispatch_position = dispatch_positions.iter().copied().next()?;
    if repeat_condition_arc.is_none() || dispatch_positions.len() != 1 || dispatch_position == 0 {
        return None;
    }

    let dispatch_child = children[dispatch_position];
    let RegionPlan::Branch {
        plan: branch_id, ..
    } = plan.region(dispatch_child)?
    else {
        return None;
    };
    let branch = plan.branch(*branch_id)?;
    let condition = plan.condition(branch.condition)?;
    let dispatch_blocks_vec = condition.blocks().collect::<Vec<_>>();
    let [dispatch_header] = dispatch_blocks_vec.as_slice() else {
        return None;
    };
    let prefix_children = &children[..dispatch_position];
    let prefix_blocks = prefix_children
        .iter()
        .flat_map(|region| plan.region_blocks(*region).iter().copied())
        .collect::<BTreeSet<_>>();
    let dispatch_blocks = plan
        .region_blocks(dispatch_child)
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    if prefix_blocks.is_empty() || dispatch_blocks.is_empty() {
        return None;
    }

    let mut entries = BTreeSet::new();
    for edge_ref in dispatch_blocks
        .iter()
        .flat_map(|block| &cfg.preds[block.index()])
    {
        let edge = &cfg.edges[edge_ref.index()];
        if !dispatch_blocks.contains(&edge.from) {
            if !prefix_blocks.contains(&edge.from) {
                return None;
            }
            entries.insert(edge.to);
        }
    }
    if entries.len() != 1 || entries.first().copied() != Some(*dispatch_header) {
        return None;
    }
    let dispatch_terminator = cfg.blocks.get(dispatch_header.index())?.instrs.last()?;
    if dataflow
        .effect_summaries
        .get(dispatch_terminator.index())
        .is_some_and(SideEffectSummary::may_observe_gc_roots)
    {
        return None;
    }
    let observer_starts = cfg
        .reachable_successors(*dispatch_header)
        .into_iter()
        .filter(|successor| dispatch_blocks.contains(successor))
        .collect::<Vec<_>>();
    if observer_starts.is_empty() {
        return None;
    }

    let relevant_blocks = prefix_blocks
        .union(&dispatch_blocks)
        .copied()
        .collect::<BTreeSet<_>>();
    for block in &relevant_blocks {
        if dataflow.block_open_live_in(*block) || dataflow.block_open_live_out(*block) {
            return None;
        }
        let range = cfg.blocks.get(block.index())?.instrs;
        for index in range.start.index()..range.end() {
            let instr = proto.instrs.get(index)?;
            let effect = dataflow.instr_effects.get(index)?;
            if effect.open_use.is_some()
                || effect.open_must_def.is_some()
                || matches!(instr, LowInstr::Close(_) | LowInstr::Tbc(_))
                || matches!(instr, LowInstr::Closure(closure) if closure.captures.iter().any(|capture| matches!(capture.source, CaptureSource::ByReference(_))))
            {
                return None;
            }
        }
    }
    for &edge_ref in relevant_blocks
        .iter()
        .flat_map(|block| &cfg.succs[block.index()])
    {
        if matches!(
            plan.edge_plan(edge_ref)?.transfer,
            crate::structure::EdgeTransfer::Goto(..) | crate::structure::EdgeTransfer::LoopBack(_)
        ) {
            return None;
        }
    }

    // Region-result phi 候选若仍可能持有 collectable，当前 fixed-def collective proof
    // 没有覆盖其 source identity。Loop-carried/region-input phi 由外层 binding 拥有，
    // 不会因这个内层 block 获得新声明。
    for &phi_id in prefix_blocks
        .iter()
        .flat_map(|block| plan.phis_in_block(*block))
    {
        let phi = plan.phi_plan(phi_id)?;
        let outer_owned = phi.incomings.iter().any(|incoming| {
            matches!(
                incoming.disposition,
                PhiIncomingDisposition::LoopCarried(_) | PhiIncomingDisposition::RegionInput(_)
            )
        });
        if !outer_owned
            && phi.incomings.iter().any(|incoming| {
                dataflow
                    .leaf_values(incoming.value)
                    .into_iter()
                    .any(|value| ssa_value_may_hold_gc_root(proto, dataflow, value))
            })
        {
            return None;
        }
    }

    let mut candidate_defs = BTreeSet::new();
    let mut roots = BTreeSet::new();
    let mut homes = BTreeSet::new();
    let prefix_defs = prefix_blocks
        .iter()
        .flat_map(|&block| dataflow.fixed_defs_in_block(cfg, block));
    for def_id in prefix_defs {
        let def = &dataflow.defs[def_id.index()];
        if fixed_temps.get(def.id.index()) != Some(&TempId(def.id.index()))
            || !low_instr_def_may_hold_gc_root(proto.instrs.get(def.instr.index())?, def.reg)
            || dataflow.def_has_use_outside(cfg, def.id, &prefix_blocks)
            || dataflow.live_in_regs(*dispatch_header).contains(&def.reg)
        {
            continue;
        }
        candidate_defs.insert(def.id);
        roots.insert(TempId(def.id.index()));
        homes.insert(def.reg);
    }
    if roots.is_empty() {
        return None;
    }

    // A by-value closure is an independent physical holder. Requiring a complete source+holder
    // pair keeps this first implementation narrow and prevents publishing a one-binding fence
    // for the regress_457 shape.
    let mut collective_holder = false;
    for def in candidate_defs.iter().copied() {
        let instr = dataflow.def_instr(def);
        let Some(LowInstr::Closure(closure)) = proto.instrs.get(instr.index()) else {
            continue;
        };
        if closure.dst != dataflow.def_reg(def) {
            continue;
        }
        if closure.captures.iter().any(|capture| {
            let CaptureSource::ByValue(reg) = capture.source else {
                return false;
            };
            matches!(dataflow.use_value(instr, reg), SsaValue::Def(source) if candidate_defs.contains(&source))
        }) {
            collective_holder = true;
            break;
        }
    }
    if !collective_holder
        || !all_paths_remove_implicit_roots_from_first_observation(
            cfg,
            dataflow,
            &dispatch_blocks,
            &observer_starts,
            &homes,
        )
    {
        return None;
    }

    Some(ImplicitRootScopeFence {
        first_child: prefix_children[0],
        end_before_child: dispatch_child,
        ended_roots: roots,
    })
}

fn ssa_value_may_hold_gc_root(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    value: SsaValue,
) -> bool {
    match value {
        SsaValue::Entry(_) | SsaValue::Phi(_) => true,
        SsaValue::Def(def) => proto
            .instrs
            .get(dataflow.def_instr(def).index())
            .is_none_or(|instr| low_instr_def_may_hold_gc_root(instr, dataflow.def_reg(def))),
    }
}

fn all_paths_remove_implicit_roots_from_first_observation(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    condition_blocks: &BTreeSet<BlockRef>,
    entries: &[BlockRef],
    homes: &BTreeSet<Reg>,
) -> bool {
    let mut pending = entries
        .iter()
        .copied()
        .map(|entry| (entry, homes.clone()))
        .collect::<Vec<_>>();
    let mut seen = BTreeSet::new();
    while let Some((block, mut active)) = pending.pop() {
        if !seen.insert((block, active.clone())) {
            return false;
        }
        let Some(range) = cfg.blocks.get(block.index()).map(|block| block.instrs) else {
            return false;
        };
        let mut resolved = false;
        for index in range.start.index()..range.end() {
            let Some(effect) = dataflow.instr_effects.get(index) else {
                return false;
            };
            if dataflow
                .effect_summaries
                .get(index)
                .is_some_and(SideEffectSummary::may_observe_gc_roots)
            {
                if !dataflow.effect_summaries[index]
                    .root_observation
                    .excludes_homes_from_caller(&active)
                {
                    return false;
                }
                resolved = true;
                break;
            }
            active.retain(|home| !effect.must_define(*home));
            if active.is_empty() {
                resolved = true;
                break;
            }
        }
        if resolved {
            continue;
        }
        let successors = cfg
            .reachable_successors(block)
            .into_iter()
            .filter(|successor| condition_blocks.contains(successor))
            .collect::<Vec<_>>();
        if successors.is_empty() {
            return false;
        }
        pending.extend(
            successors
                .into_iter()
                .map(|successor| (successor, active.clone())),
        );
    }
    true
}

/// 从 low-IR 正证一个可能承载 GC root 的 canonical fixed def 在后续所有潜在用户代码 /
/// GC 观察点都仍位于 VM active stack top 以下，并沿同一 basic block、线性 single-entry
/// fast path，或 predecessor-closed 的严格前向 CFG DAG 活到每条路径的 Return/TailCall、
/// 精确 direct nil/boolean/integer/number overwrite，或无观察 suffix 的其它 overwrite。
///
/// low classifier 只排除已知必为 GC-inert 的 primitive/numeric def；HIR consumer 再用
/// `HirExprSafety::result_is_gc_inert` 复核恢复后的 producer 值，并要求 producer 单写、无读。
/// HIR 会丢失 block 结束时的隐式 stack-top 收缩；只看“后缀没有同槽写”会把已经到期
/// 的高槽误提升成函数级 local。这里保留 raw 指令层的最小充分事实；分支 successor 与
/// join 用 entry-driven must-state 合流，只有 producer 支配的前向闭合子图才能发布
/// all-successor 终点。overwrite 的 raw DefId/TempId 与值类会一同发布，HIR consumer
/// 必须重新定位唯一赋值 owner 并原子重放；非 scalar overwrite 只有在其后到 caller
/// scope end 全路径无 allocation/metamethod/table/env/call/Close 观察时才算安全终点。
/// 回边、外部 join 入口与无法计算活动栈下界的事件仍拒绝。TBC 与专用调用协议只消费
/// 各自的固定输入 root prefix；`Close` 本身不覆盖槽位，因此可以继续到原始终点。
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
pub(super) enum CopyRootOverwrite {
    Scalar {
        temp: TempId,
        value: CopyRootScalarValue,
    },
    /// 单结果 call 先写自己的 result home，下一条透明 MOVE 再覆盖旧 root home。
    /// HIR 会折叠 MOVE，因此 endpoint 绑定 call result temp，而不是一个同 home scalar temp。
    CallResultMove { temp: TempId },
}

impl CopyRootOverwrite {
    pub(super) const fn temp(self) -> TempId {
        match self {
            Self::Scalar { temp, .. } | Self::CallResultMove { temp } => temp,
        }
    }

    pub(super) fn matches_hir_expr(self, value: &HirExpr) -> bool {
        match self {
            Self::Scalar { value: scalar, .. } => scalar.matches_hir_expr(value),
            Self::CallResultMove { .. } => false,
        }
    }
}

#[derive(Default)]
struct CopyRootEnd {
    scope_end: bool,
    overwrites: BTreeMap<TempId, CopyRootOverwrite>,
    observed_any: bool,
}

impl CopyRootEnd {
    fn scope_end() -> Self {
        Self {
            scope_end: true,
            overwrites: BTreeMap::new(),
            observed_any: true,
        }
    }

    fn overwrite(overwrite: CopyRootOverwrite) -> Self {
        Self {
            scope_end: false,
            overwrites: BTreeMap::from([(overwrite.temp(), overwrite)]),
            observed_any: true,
        }
    }

    fn with_observation(mut self, observed: bool) -> Self {
        self.observed_any = observed;
        self
    }

    fn is_complete(&self) -> bool {
        self.observed_any && (self.scope_end || !self.overwrites.is_empty())
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
        let Some(instr) = proto.instrs.get(def.instr.index()) else {
            continue;
        };

        let direct = TempId(def.id.index());
        if fixed_temps.get(def.id.index()) != Some(&direct)
            || !low_instr_def_may_hold_gc_root(instr, def.reg)
        {
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

fn low_instr_def_may_hold_gc_root(instr: &LowInstr, reg: Reg) -> bool {
    match instr {
        LowInstr::LoadNil(load_nil)
            if load_nil.dst.start.index() <= reg.index()
                && reg.index() < load_nil.dst.start.index().saturating_add(load_nil.dst.len) =>
        {
            false
        }
        LowInstr::LoadBool(load_bool) if load_bool.dst == reg => false,
        LowInstr::LoadInteger(load_integer) if load_integer.dst == reg => false,
        LowInstr::LoadNumber(load_number) if load_number.dst == reg => false,
        LowInstr::UnaryOp(unary)
            if unary.dst == reg && matches!(unary.op, crate::transformer::UnaryOpKind::Not) =>
        {
            false
        }
        LowInstr::TypeGuard(guard)
            if guard.subject == reg
                && matches!(
                    guard.kind,
                    crate::transformer::TypeGuardKind::Integer
                        | crate::transformer::TypeGuardKind::Number
                ) =>
        {
            false
        }
        LowInstr::NumericForInit(init) if init.index == reg || init.binding == reg => false,
        LowInstr::NumericForLoop(loop_) if loop_.index == reg || loop_.binding == reg => false,
        _ => true,
    }
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
        let range = cfg.blocks.get(current_block.index())?.instrs;
        let last = range.last()?;
        let control = proto
            .instrs
            .get(last.index())?
            .is_control_terminator()
            .then_some(last.index());
        let overwrite = dataflow.first_must_write_in_range(home, index..range.end());
        let stop = overwrite
            .map_or(range.end(), |instr| instr.index())
            .min(control.unwrap_or(range.end()));
        if let Some(prefix) = dataflow.minimum_rooted_prefix(index..stop) {
            if home.index() >= prefix {
                // 候选拒绝[SemanticBarrier:Lifetime]：观察前缀外的槽不能继续保活（regress_416）。
                return None;
            }
            observed = true;
        }
        if overwrite == Some(InstrRef(stop)) {
            // 覆写指令自身的观察不属于此前 root transaction。
            return observed
                .then(|| root_end_at_overwrite(proto, cfg, dataflow, fixed_temps, stop, home))
                .flatten();
        }
        if control == Some(stop) {
            match copy_root_instr_progress(
                dataflow.effect_summaries.get(stop)?.root_observation,
                home,
                &mut observed,
            )? {
                CopyRootInstrProgress::Continue => {}
                CopyRootInstrProgress::ScopeEnd => return Some(CopyRootEnd::scope_end()),
            }
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
        index = range.end();
    }

    None
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum CopyRootInstrProgress {
    Continue,
    ScopeEnd,
}

/// 只消费 Dataflow 已证明的观察点 root 边界；producer 与终点的路径闭合仍属于 HIR。
fn copy_root_instr_progress(
    observation: RootObservation,
    home: Reg,
    observed: &mut bool,
) -> Option<CopyRootInstrProgress> {
    match observation {
        RootObservation::FrameExit => observed.then_some(CopyRootInstrProgress::ScopeEnd),
        RootObservation::None | RootObservation::Close => Some(CopyRootInstrProgress::Continue),
        RootObservation::Call { .. } | RootObservation::PrefixLowerBound { .. } => {
            if !observation.keeps_home_rooted(home) {
                // 候选拒绝[SemanticBarrier:Lifetime]：前层没有证明该 home 在观察期间存活。
                // 前缀下界之外只代表未知，不能被 consumer 升级成释放 root 的许可。
                return None;
            }
            *observed = true;
            Some(CopyRootInstrProgress::Continue)
        }
    }
}

enum CopyRootCfgBlockEnd {
    Continue { observed: bool },
    End(CopyRootEnd),
}

/// 从一个已执行的 control terminator 出发，只接受 producer 支配且 predecessor-closed 的
/// CFG region；每条动态路径都必须精确走到 frame end 或 direct GC-inert overwrite。任一路径
/// 在终点前观察过同一 active home，就需要保留该 root；没有观察的路径是 neutral，因为延续
/// raw root 到它原本的终点不会新增可观察差异。incoming observation 因此在 join 取并集；
/// 有限 CFG 上的 bool lattice 只会由 false 单调变为 true，worklist 必然收敛。region 可以
/// 包含 cycle，但不能回到 producer（否则会产生新的动态 root epoch）；cycle 内若 must-define
/// home 则在该 overwrite 精确截断，因此所有继续边仍描述同一个 producer value。
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
        |index, home| root_end_at_overwrite(proto, cfg, dataflow, fixed_temps, index, home),
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
    mut end_at: impl FnMut(usize, Reg) -> Option<CopyRootEnd>,
) -> Option<CopyRootEnd> {
    let region = copy_root_cfg_region(
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
    for successor in copy_root_cfg_successors(inputs.cfg, source)? {
        merge_copy_root_cfg_incoming(&mut incoming, &mut pending, successor, observed);
    }

    let mut ends = CopyRootEnd::default();
    while let Some(block) = pending.pop_front() {
        let observed = incoming.get(&block).copied()?;
        match scan_copy_root_cfg_block(inputs, block, observed, &mut end_at)? {
            CopyRootCfgBlockEnd::End(block_ends) => {
                ends.scope_end |= block_ends.scope_end;
                ends.overwrites.extend(block_ends.overwrites);
                ends.observed_any |= block_ends.observed_any;
            }
            CopyRootCfgBlockEnd::Continue { observed } => {
                for successor in copy_root_cfg_successors(inputs.cfg, block)? {
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

fn copy_root_cfg_region(
    instrs: &[LowInstr],
    cfg: &Cfg,
    instr_effects: &[InstrEffect],
    source: BlockRef,
    home: Reg,
) -> Option<BTreeSet<BlockRef>> {
    let mut region = BTreeSet::new();
    let mut pending = VecDeque::from(copy_root_cfg_successors(cfg, source)?);
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
        pending.extend(copy_root_cfg_successors(cfg, block)?);
    }
    if region.contains(&source) {
        // Re-entering the producer block would execute the same static def in a new dynamic
        // iteration, so one root fact could no longer describe a single value epoch.
        return None;
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
            let merged = *previous || observed;
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
    end_at: &mut impl FnMut(usize, Reg) -> Option<CopyRootEnd>,
) -> Option<CopyRootCfgBlockEnd> {
    let range = inputs.cfg.blocks.get(block.index())?.instrs;
    if range.is_empty() {
        return None;
    }
    for index in range.start.index()..range.end() {
        let instr = inputs.instrs.get(index)?;
        let effect = inputs.instr_effects.get(index)?;
        if effect.must_define(inputs.home) {
            // Every dynamic overwrite path contributes its exact endpoint. Even a neutral path
            // must overwrite the promoted local there: otherwise a sibling observed path could
            // publish the root fact and incorrectly keep this path's old value across a later
            // join observation.
            let end = end_at(index, inputs.home)?.with_observation(observed);
            return Some(CopyRootCfgBlockEnd::End(end));
        }
        if matches!(instr, LowInstr::Return(_) | LowInstr::TailCall(_)) {
            // A return/tailcall ends the current frame. An unobserved path is neutral rather than
            // evidence against a sibling path that did execute a root-observing call.
            let end = CopyRootEnd::scope_end().with_observation(observed);
            return Some(CopyRootCfgBlockEnd::End(end));
        }
        match copy_root_instr_progress(
            inputs.effect_summaries.get(index)?.root_observation,
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

fn copy_root_cfg_successors(cfg: &Cfg, block: BlockRef) -> Option<Vec<BlockRef>> {
    let successors = cfg.reachable_successors(block);
    if successors.is_empty()
        || successors.iter().any(|successor| {
            cfg.blocks
                .get(successor.index())
                .is_none_or(|block| block.instrs.is_empty())
        })
    {
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

fn root_end_at_overwrite(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
    index: usize,
    home: Reg,
) -> Option<CopyRootEnd> {
    if let Some(overwrite) = direct_scalar_overwrite(proto, dataflow, fixed_temps, index, home) {
        return Some(CopyRootEnd::overwrite(overwrite));
    }
    if let Some(overwrite) =
        immediate_call_result_move_overwrite(proto, dataflow, fixed_temps, index, home)
    {
        return Some(CopyRootEnd::overwrite(overwrite));
    }
    overwrite_suffix_is_unobservable_until_scope_end(proto, cfg, dataflow, index)
        .then(CopyRootEnd::scope_end)
}

/// 识别 `CALL rX -> rX; MOVE old_home <- rX` 的单次 overwrite endpoint。
///
/// CALL 期间旧 home 是否仍位于 caller root prefix 已由 `copy_root_end` 在前一条指令
/// 处理并证明；这里仅冻结结果宽度、相邻性与 SSA source identity。开放结果、多结果或
/// 非相邻 forwarding 需要额外的 value-pack/事件证明，不能借这条证书。
fn immediate_call_result_move_overwrite(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
    index: usize,
    home: Reg,
) -> Option<CopyRootOverwrite> {
    let LowInstr::Move(move_) = proto.instrs.get(index)? else {
        return None;
    };
    if move_.dst != home {
        return None;
    }
    let SsaValue::Def(source_def) = dataflow.use_value(InstrRef(index), move_.src) else {
        return None;
    };
    let source = dataflow.defs.get(source_def.index())?;
    if source.reg != move_.src || source.instr.index().checked_add(1) != Some(index) {
        return None;
    }
    let LowInstr::Call(call) = proto.instrs.get(source.instr.index())? else {
        return None;
    };
    if !matches!(
        call.results,
        ResultPack::Fixed(results) if results.start == move_.src && results.len == 1
    ) {
        return None;
    }
    let direct = TempId(source_def.index());
    (fixed_temps.get(source_def.index()) == Some(&direct))
        .then_some(CopyRootOverwrite::CallResultMove { temp: direct })
}

/// Marking the old value as a source local may keep it alive past a non-scalar raw overwrite.
/// That extension is safe only when every forward path reaches Return/TailCall without an
/// intervening allocation, metamethod, table/environment access, call, or Close hook.
fn overwrite_suffix_is_unobservable_until_scope_end(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    overwrite: usize,
) -> bool {
    let Some(start_block) = cfg.instr_to_block.get(overwrite).copied() else {
        return false;
    };
    let mut pending = VecDeque::from([(start_block, overwrite.saturating_add(1))]);
    let mut visited = BTreeSet::new();
    while let Some((block, begin)) = pending.pop_front() {
        if !visited.insert(block) {
            return false;
        }
        let Some(range) = cfg.blocks.get(block.index()).map(|block| block.instrs) else {
            return false;
        };
        let mut reached_terminator = false;
        for index in begin.max(range.start.index())..range.end() {
            let Some(instr) = proto.instrs.get(index) else {
                return false;
            };
            if matches!(instr, LowInstr::Return(_) | LowInstr::TailCall(_)) {
                reached_terminator = true;
                break;
            }
            if matches!(instr, LowInstr::Close(_))
                || dataflow
                    .effect_summaries
                    .get(index)
                    .is_some_and(SideEffectSummary::may_observe_gc_roots)
            {
                return false;
            }
            if instr.is_control_terminator() {
                if range.last() != Some(InstrRef(index)) {
                    return false;
                }
                let Some(successors) = copy_root_forward_cfg_successors(cfg, block) else {
                    return false;
                };
                pending.extend(successors.into_iter().filter_map(|successor| {
                    cfg.blocks
                        .get(successor.index())
                        .map(|block| (successor, block.instrs.start.index()))
                }));
                reached_terminator = true;
                break;
            }
        }
        if !reached_terminator {
            let Some(successors) = copy_root_forward_cfg_successors(cfg, block) else {
                return false;
            };
            pending.extend(successors.into_iter().filter_map(|successor| {
                cfg.blocks
                    .get(successor.index())
                    .map(|block| (successor, block.instrs.start.index()))
            }));
        }
    }
    true
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
    (fixed_temps.get(def.index()) == Some(&direct)).then_some(CopyRootOverwrite::Scalar {
        temp: direct,
        value,
    })
}

pub(super) fn direct_scalar_overwrite_value(
    instr: &LowInstr,
    home: Reg,
) -> Option<CopyRootScalarValue> {
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
                    reference_capture_before: vec![false; 4],
                    spans_entry: true,
                }),
            ],
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
            Some(&BTreeSet::from([first, second]))
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
            facts.possible_local_home_slots(target).as_deref(),
            Some(&BTreeSet::from([target_home, source_home]))
        );
    }

    #[test]
    fn dedicated_protocol_root_prefix_excludes_future_result_slots() {
        let observation = RootObservation::PrefixLowerBound { end: 7 };
        assert!(observation.keeps_home_rooted(Reg(6)));
        assert!(!observation.keeps_home_rooted(Reg(7)));
        assert!(!observation.excludes_homes_from_caller(&BTreeSet::from([Reg(7)])));
    }

    #[test]
    fn ordinary_call_excludes_only_the_complete_high_home_collective_from_caller_prefix() {
        let call = RootObservation::Call { caller_end: Reg(6) };
        assert!(call.excludes_homes_from_caller(&BTreeSet::from([Reg(6), Reg(7)])));
        assert!(!call.excludes_homes_from_caller(&BTreeSet::from([Reg(5), Reg(7)])));
        assert!(
            !RootObservation::FrameExit
                .excludes_homes_from_caller(&BTreeSet::from([Reg(6), Reg(7)]))
        );
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
    fn copy_root_cfg_join_keeps_observation_from_any_dominated_path() {
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
        let mut summaries = vec![SideEffectSummary::default(); instrs.len()];
        summaries[1].root_observation = RootObservation::Call { caller_end: Reg(2) };
        summaries[3].root_observation = RootObservation::Call { caller_end: Reg(2) };
        summaries[5].root_observation = RootObservation::FrameExit;

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

        summaries[3].root_observation = RootObservation::None;
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
            Some(())
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
            LowInstr::Move(MoveInstr {
                dst: Reg(3),
                src: Reg(4),
            }),
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
        effects[2] = InstrEffect::new(Vec::new(), vec![Reg(1)], None, None);
        effects[4] = InstrEffect::new(Vec::new(), vec![Reg(1)], None, None);
        let mut summaries = vec![SideEffectSummary::default(); instrs.len()];
        summaries[3].root_observation = RootObservation::Call { caller_end: Reg(2) };
        let overwrite = |index, _home| match index {
            2 => Some(CopyRootEnd::overwrite(CopyRootOverwrite::Scalar {
                temp: TempId(2),
                value: CopyRootScalarValue::Boolean(false),
            })),
            4 => Some(CopyRootEnd::overwrite(CopyRootOverwrite::Scalar {
                temp: TempId(4),
                value: CopyRootScalarValue::Integer(0),
            })),
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
        .expect("one observed path publishes every dominated path's exact overwrite endpoint");
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
            "an overwrite without a scalar or unobservable scope-end proof must reject the transaction"
        );
    }

    #[test]
    fn copy_root_producer_classifier_excludes_primitives_but_accepts_call_results() {
        let home = Reg(1);
        assert!(!low_instr_def_may_hold_gc_root(
            &LowInstr::LoadInteger(LoadIntegerInstr {
                dst: home,
                value: 1,
            }),
            home,
        ));
        assert!(low_instr_def_may_hold_gc_root(
            &LowInstr::Call(CallInstr {
                callee: Reg(0),
                args: ValuePack::Fixed(RegRange::new(Reg(1), 0)),
                results: ResultPack::Fixed(RegRange::new(home, 1)),
                kind: CallKind::Normal,
                method_name: None,
            }),
            home,
        ));
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
            direct_scalar_overwrite_value(
                &LowInstr::NewTable(NewTableInstr {
                    dst: home,
                    allocation: crate::transformer::TableAllocation::PucBatched(
                        crate::value_semantics::table::allocation::TablePreallocation::exact(0, 0)
                            .unwrap()
                    )
                }),
                home,
            ),
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
        let expired = RootObservation::PrefixLowerBound { end: 1 };
        assert!(!expired.keeps_home_rooted(home));

        let rooted = RootObservation::PrefixLowerBound { end: 3 };
        assert!(rooted.keeps_home_rooted(home));
    }
}
