//! 将 analyze 阶段的物理来源与协议事实带给 HIR simplify。
//!
//! 消费 Dataflow 的 Def/phi、root observation 及 Transformer 的 close 边界，
//! 保存 temp 的 home、捕获身份和原操作来源；不重新恢复结构，也不作为公开 HIR API。
//! 例如 t0 与 t7 同属 (slot 0, epoch 0) 时可由 locals 复用绑定，close 后的 epoch 1
//! 必须独立。合并不同 home 后失效单一来源的正向证明，可能 home 集仍服务负向保护。

mod call_roots;
mod comparison_preparations;
mod copy_assignments;
pub(super) use copy_assignments::ParallelFrame as NativeParallelFrame;
mod copy_root_retirement;
mod operand_preparations;
mod short_circuit_frames;

pub(super) use call_roots::NativeCallFrame;

use crate::hir::common::{
    HirBinding, HirExpr, HirMethodSetupProtocolId, HirStmt, LocalId, ParamId, TempId, UpvalueId,
};
use crate::structure::{
    BlockRef, Cfg, DataflowFacts, EdgeRef, ForwardRouteKind, GraphFacts,
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

/// 循环头的源码求值槽与原 SSA 值版本；值身份不替代物理根退休证明。
#[derive(Debug, Clone, Copy)]
pub(super) struct NativeNumericForHeader {
    pub(super) homes: [HomeSlotKey; 3],
    pub(super) values: [Option<TempId>; 3],
}

/// CALL 参数、CONCAT 输入与循环头共用 canonical 值版本投影；合并的 Def 不冒充原槽独立 producer。
fn canonical_value_temp(
    value: SsaValue,
    def_count: usize,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
) -> Option<TempId> {
    match value {
        SsaValue::Def(def) if fixed_temps[def.index()] == TempId(def.index()) => {
            Some(fixed_temps[def.index()])
        }
        SsaValue::Phi(phi) if phi_temps[phi.index()] == TempId(def_count + phi.index()) => {
            Some(phi_temps[phi.index()])
        }
        _ => None,
    }
}

/// 原 GETTABLE 及 GETIMPORT 字段段的 base/key 布局；不把合成字面量当作原 RK 操作数。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(super) struct NativeTableReadLayout {
    pub(super) base: HomeSlotKey,
    pub(super) key: Option<HomeSlotKey>,
}

/// 结果可合流为 phi，但原指令的写槽和输入布局仍然独立存在。
#[derive(Debug, Clone, Copy)]
struct NativeTableReadFacts {
    layout: Option<NativeTableReadLayout>,
    result: TempId,
    result_home: HomeSlotKey,
}

impl NativeTableReadLayout {
    fn for_access(
        base: crate::transformer::AccessBase,
        key: crate::transformer::AccessKey,
        site: InstrRef,
        epochs: &SlotEpochFacts,
    ) -> Option<Self> {
        use crate::transformer::{AccessBase, AccessKey};
        let AccessBase::Reg(base) = base else {
            return None;
        };
        let home = |reg: Reg| HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, site));
        Some(Self {
            base: home(base),
            key: match key {
                AccessKey::Reg(reg) => Some(home(reg)),
                AccessKey::Const(_) | AccessKey::Integer(_) => None,
            },
        })
    }
}

/// 原二元值操作或比较谓词读取的槽；常量 None 与未知来源的外层 None 分离。
#[derive(Debug, Clone, Copy)]
pub(super) struct NativeBinaryLayout {
    pub(super) lhs: Option<HomeSlotKey>,
    pub(super) rhs: Option<HomeSlotKey>,
}

/// CONCAT 的连续槽和各输入原值版本共同属于该次操作；结果的后继 COPY 写域
/// 不应因输入/输出复用 Local 而污染输入准备证明。
#[derive(Debug, Clone)]
struct NativeConcatFrame {
    buffer: crate::transformer::RegRange,
    operands: Vec<Option<TempId>>,
    operand_homes: Vec<HomeSlotKey>,
    /// 低槽原位更新的连续 MOVE/LOADK 准备；buffer 自身仍要求没有开放捕获。
    captured_update: Option<(HomeSlotKey, crate::LuaString)>,
}

/// 普通值操作数与字段值共用原指令时点的寄存器投影，不从内联后的字面量恢复槽。
fn native_operand_home(
    operand: crate::transformer::ValueOperand,
    site: InstrRef,
    epochs: &SlotEpochFacts,
) -> Option<HomeSlotKey> {
    use crate::transformer::ValueOperand;
    match operand {
        ValueOperand::Reg(reg) => Some(HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, site))),
        ValueOperand::Const(_)
        | ValueOperand::Integer(_)
        | ValueOperand::Nil
        | ValueOperand::Boolean(_) => None,
    }
}

/// 原写表协议区分寄存器 base 与 SETTABUP 的上值 cell，不为上值伪造物理 home。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum NativeTableWriteLayout {
    Register(NativeRegisterTableWriteLayout),
    Upvalue(NativeUpvalueTableWriteLayout),
    Environment {
        key: Option<HomeSlotKey>,
        value: Option<HomeSlotKey>,
    },
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(super) struct NativeUpvalueTableWriteLayout {
    pub(super) base: crate::hir::common::UpvalueId,
    pub(super) key: Option<HomeSlotKey>,
    pub(super) value: Option<HomeSlotKey>,
}

/// 原普通 SETTABLE 的读取槽布局；None 仅表示原操作数是常量，并非未知寄存器。
/// 例如大常量池的字段 key 先 LOADK r4 时必须保留 key=Some(r4)，不能从字面量重猜 RK。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(super) struct NativeRegisterTableWriteLayout {
    pub(super) base: HomeSlotKey,
    pub(super) key: Option<HomeSlotKey>,
    pub(super) value: Option<HomeSlotKey>,
    /// 原 base Def 及尚未开始的 debug scope；只由 scope 入口紧邻的末次写发布。
    pub(super) initializer: Option<(TempId, usize)>,
}

/// 原 SETLIST 的表与独立缓冲区；Luau 的缓冲区不能按 PUC 的 table+1 反推。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct NativeTableBatchLayout {
    /// 开放尾直接来自同块紧邻的 VARARG，CALL 与 pack phi 不签发此事实。
    pub(super) vararg_tail_home: Option<HomeSlotKey>,
    pub(super) base: HomeSlotKey,
    pub(super) buffer: HomeSlotKey,
    pub(super) fixed_width: Option<usize>,
    pub(super) start_index: u32,
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
    reference_capture_before: Option<std::sync::Arc<[bool]>>,
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
            .and_then(|flow| flow.reference_capture_before.as_ref())
            .is_some_and(|flow| flow[instr.index()])
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
        reference_capture_before: dataflow.reference_capture_flow(reg),
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

#[derive(Debug, Clone, Copy)]
enum UpvalueWriteInput {
    Temp(TempId),
    EntryNil(HomeSlotKey),
}

/// 单个 proto 的 temp promotion 与后续 binding provenance 辅助事实。
#[derive(Debug, Clone, Default)]
pub(super) struct ProtoPromotionFacts {
    closed_capture_temps: BTreeSet<TempId>,
    copy_root_retirements: copy_root_retirement::CopyRootRetirements,
    copy_scoped_temps: BTreeSet<TempId>,
    copy_scope_handoffs: BTreeMap<InstrRef, Vec<(TempId, TempId)>>,
    temp_home_slots: Vec<HomeSlotResolution>,
    reference_unaliased_temps: BTreeSet<TempId>,
    reference_unaliased_locals: BTreeMap<LocalId, bool>,
    reference_aliased_move_temps: BTreeSet<TempId>,
    immediate_move_writes: Vec<ImmediateMoveWrites>,
    inert_home_overwrites: BTreeMap<TempId, InertHomeOverwrite>,
    copy_predecessors: BTreeMap<TempId, TempId>,
    scratch_overwrite_temps: BTreeSet<TempId>,
    /// 普通 fixed 写清除旧残值的责任；不等同于 COPY 新根的保活/退休协议。
    unknown_scratch_write_temps: BTreeSet<TempId>,
    entry_nil_phi_temps: BTreeSet<TempId>,
    entry_nil_phi_locals: BTreeSet<LocalId>,
    repeat_condition_prefix_temps: BTreeSet<TempId>,
    direct_table_seed_temps: BTreeSet<TempId>,
    direct_table_seed_locals: BTreeSet<LocalId>,
    loop_carrier_temps: BTreeSet<TempId>,
    phi_carrier_temps: BTreeSet<TempId>,
    implicit_root_scope_fences: BTreeMap<RegionId, ImplicitRootScopeFence>,
    /// 原 SSA 的标量 COPY/phi 证明，仅用于排除 Luau 的额外保活身份。
    scalar_copy_temps: BTreeSet<TempId>,
    scope_end_copy_root_temps: BTreeSet<TempId>,
    copy_root_overwrites: BTreeMap<TempId, Vec<CopyRootOverwrite>>,
    copy_root_endpoint_producers: BTreeMap<TempId, BTreeSet<TempId>>,
    /// HIR 已把完整 scalar 退休端点原子接回 producer；只授权原定义处的声明物化。
    retargeted_scalar_roots: BTreeSet<TempId>,
    promoted_local_by_temp: BTreeMap<TempId, LocalId>,
    /// 完整移除的 local 身份在本轮 carried 改写结束时批量归并，避免逐候选扫描 Def 表。
    consumed_local_bindings: BTreeMap<LocalId, HirBinding>,
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
    tbc_homes: BTreeMap<InstrRef, HomeSlotKey>,
    compact_home_slots: bool,
    source_proto: Option<crate::hir::common::HirProtoRef>,
    calls: BTreeMap<InstrRef, call_roots::NativeCallFacts>,
    return_frames: BTreeMap<InstrRef, NativeReturnFrame>,
    return_fixed_inputs: BTreeMap<InstrRef, Vec<Option<TempId>>>,
    parameter_return_scratch: Option<HomeSlotKey>,
    /// 无参数/变参入口调整、原寄存器写入或观察；空调用不会改变返回后残留的槽内容。
    empty_call_preserves_frame: bool,
    return_copy_roots: BTreeSet<TempId>,
    entry_parameter_copy_roots: BTreeSet<TempId>,
    readonly_parameter_copies: BTreeMap<TempId, ParamId>,
    return_frame_sources: BTreeMap<InstrRef, InstrRef>,
    operation_results: BTreeMap<InstrRef, NativeOperationResult>,
    swap_frames: Vec<copy_assignments::SwapFrame>,
    scalar_pair_frames: Vec<copy_assignments::ScalarPairFrame>,
    parallel_frames: BTreeMap<InstrRef, copy_assignments::ParallelFrame>,
    lookup_assignment_frames: BTreeMap<InstrRef, copy_assignments::lookups::LookupFrame>,
    parallel_target_seeds: BTreeSet<TempId>,
    table_write_layouts: BTreeMap<InstrRef, NativeTableWriteLayout>,
    /// 原 SETTABLE 的 base/key 读取 owner；只证明原位读取，不签发 cell 合并许可。
    table_write_local_inputs: BTreeMap<InstrRef, [Option<LocalId>; 2]>,
    table_batch_layouts: BTreeMap<InstrRef, NativeTableBatchLayout>,
    table_batch_values: BTreeMap<InstrRef, Vec<Option<TempId>>>,
    /// 原 allocation 的唯一 SETLIST；多批次保持未知，不能仅用最后一批签完整初始化。
    allocation_batches: BTreeMap<InstrRef, Vec<InstrRef>>,
    table_read_layouts: BTreeMap<InstrRef, NativeTableReadFacts>,
    table_read_bases: BTreeMap<InstrRef, TempId>,
    binary_layouts: BTreeMap<InstrRef, NativeBinaryLayout>,
    /// 原比较读取位置的可见 local owner；循环 cell 可跨 epoch，不能只比较声明处 home。
    binary_local_inputs: BTreeMap<InstrRef, [Option<LocalId>; 2]>,
    /// Structure 已证明单次消费的内部取值 phi，按消费指令和原寄存器索引。
    binary_value_operands: BTreeMap<(InstrRef, Reg), TempId>,
    comparison_preparations: BTreeMap<InstrRef, comparison_preparations::ComparisonPreparation>,
    /// 二元左右输入和 SETTABLE 的 base/value 分别占 0/1；一元、CONCAT 首项只用 0。
    operand_preparations: BTreeMap<InstrRef, [Option<operand_preparations::OperandPreparation>; 2]>,
    upvalue_writes: BTreeMap<InstrRef, (UpvalueId, UpvalueWriteInput)>,
    upvalue_table_reads: BTreeMap<InstrRef, (UpvalueId, HirExpr)>,
    table_preparations: BTreeMap<InstrRef, operand_preparations::TablePreparation>,
    unary_operands: BTreeMap<InstrRef, NativeUnaryOperand>,
    concat_frames: BTreeMap<InstrRef, NativeConcatFrame>,
    argument_root_producers: BTreeSet<TempId>,
    call_frame_temps: BTreeSet<TempId>,
    comparison_result_writes: BTreeMap<TempId, InstrRef>,
    boolean_value_prewrites: BTreeMap<TempId, (TempId, bool)>,
    copy_value_prewrites: BTreeMap<TempId, TempId>,
    value_result_copies: BTreeMap<TempId, ImmediateMoveWrite>,
    comparison_results_by_predicate: BTreeMap<InstrRef, Option<TempId>>,
    conditional_value_results: BTreeMap<InstrRef, Option<NativeConditionalValueResult>>,
    short_circuit_call_frames:
        BTreeMap<InstrRef, Option<short_circuit_frames::ShortCircuitCallFrame>>,
    short_circuit_table_frames:
        BTreeMap<(InstrRef, InstrRef), Option<short_circuit_frames::ShortCircuitTableFrame>>,
    /// 原物理覆盖的 canonical endpoint -> 条件输入根；不从后层槽号猜退休点。
    conditional_root_endpoints: BTreeMap<TempId, TempId>,
    unobserved_call_result_ends: BTreeMap<TempId, Vec<TempId>>,
    frame_root_ends_by_call: BTreeMap<InstrRef, Vec<TempId>>,
    numeric_for_headers: BTreeMap<InstrRef, NativeNumericForHeader>,
    nil_write_temps: BTreeMap<TempId, Vec<TempId>>,
    generic_for_body_frames: BTreeMap<InstrRef, NativeGenericForFrame>,
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

/// 原分配/CALL truthiness 判定后的同值标量写回；保留 phi 或直达结果身份，不禁止值化简。
/// 完整源码帧仍须核对构造事件、当前值版本和声明前缀，不能仅凭常量相等领取许可。
#[derive(Debug, Clone, Copy)]
pub(super) struct NativeConditionalValueResult {
    pub(super) input: TempId,
    pub(super) result: TempId,
    pub(super) value: CopyRootScalarValue,
    pub(super) writes: [Option<TempId>; 2],
}

/// low method setup 与 canonical callee definition 之间的 HIR 私有桥接事实。
///
/// 它只活到 HIR finalizer；AST 永远不会看到 `TempId` 或 physical home。
#[derive(Debug, Clone)]
pub(super) struct HirMethodSetupProtocol {
    pub(super) callee_temp: TempId,
    pub(super) receiver_temp: Option<TempId>,
    pub(super) prior_callee_root_temp: Option<TempId>,
    pub(super) method_key: crate::LuaString,
}

/// 一元输入的物理槽和原 use→Def/Phi 身份一起保留；槽位置不代替值版本。
#[derive(Debug, Clone, Copy)]
struct NativeUnaryOperand {
    home: HomeSlotKey,
    value: Option<TempId>,
}

/// 单值原操作的结果身份与环境读取角色，共用一个 source 索引。
#[derive(Debug, Clone, Copy)]
struct NativeOperationResult {
    temp: TempId,
    direct_global_read: bool,
}

/// 原 RETURN 的连续结果区；不把 frame 退出误当作此前未观察到对象的证明。
#[derive(Debug, Clone, Copy)]
pub(super) struct NativeReturnFrame {
    pub(super) home: HomeSlotKey,
    pub(super) values: crate::transformer::ValuePack,
}

/// 原数值循环控制区中，用户 binding 可占最后控制槽，也可紧随独立控制区。
/// 固定数组只保存已签发的三槽；controls_len 排除与用户 binding 共用的槽。
pub(super) struct NativeNumericForFrame {
    pub(super) controls: [HomeSlotKey; 3],
    pub(super) controls_len: usize,
    /// 每轮被捕获的 binding 可有多个 close epoch，源码声明布局只证明其固定槽号。
    pub(super) binding_slot: usize,
}

/// Structure 的循环协议在 body 入口占据的控制区与用户 binding；不制造隐式 LocalId。
#[derive(Debug, Clone)]
pub(super) struct NativeGenericForFrame {
    /// 初始化接收区独立于 body 的隐式控制区；Lua 5.5 的末槽同时是首个 binding。
    pub(super) initializers: Vec<HomeSlotKey>,
    pub(super) controls: Vec<HomeSlotKey>,
    pub(super) bindings: Vec<HomeSlotKey>,
    /// Luau 单变量遍历仍保留第二个结果槽；这里只表示占槽，不声明或初始化新值。
    pub(super) binding_padding: usize,
}

impl ProtoPromotionFacts {
    #[expect(
        clippy::too_many_arguments,
        reason = "退休、支配、调试身份和发射作用域消费同一 lowering 快照"
    )]
    pub(super) fn record_copy_root_retirements(
        &mut self,
        proto: &LoweredProto,
        cfg: &Cfg,
        graph: &GraphFacts,
        dataflow: &DataflowFacts,
        fixed_temps: &[TempId],
        debug_scopes: &[Option<usize>],
        emission: &crate::hir::emission::HirEmissionFacts<'_>,
        target: crate::decompile::DecompileDialect,
    ) {
        let emitted = |instr: InstrRef| {
            !emission.for_instr(instr)
                && emission
                    .regular_prefix(cfg.instr_to_block[instr.index()])
                    .is_some_and(|range| range.contains(&instr.index()))
        };
        self.copy_root_retirements = copy_root_retirement::CopyRootRetirements::collect(
            proto,
            cfg,
            dataflow,
            fixed_temps,
            debug_scopes,
            emitted,
            |instr| emission.for_instr(instr),
        );
        // 两个退休 owner 消费同一原 SSA 值证明。额外 holder 的 nil 初始化/退休是
        // 我们合成的保活操作，标量没有该需求；原 COPY 与覆盖仍由源码帧保留。
        self.copy_root_retirements
            .producers
            .retain(|temp| !self.scalar_copy_temps.contains(temp));
        for roots in self
            .copy_root_retirements
            .releases
            .values_mut()
            .chain(self.copy_root_retirements.after_releases.values_mut())
        {
            roots.retain(|temp| !self.scalar_copy_temps.contains(temp));
        }
        if target == crate::decompile::DecompileDialect::Luau {
            self.readonly_parameter_copies =
                copy_assignments::collect_readonly_parameter_copies(proto, dataflow);
            // 低槽形参在整个函数中未写、未暴露引用 cell，已保有同一对象。高槽 COPY
            // 不需要再造入口 holder 和清零；原 COPY 的槽覆盖仍由原帧/root owner 验证。
            // Luau 没有 debug.setlocal，不能把此证明套到可由回调改写形参的方言。
            self.copy_root_retirements
                .producers
                .retain(|temp| !self.readonly_parameter_copies.contains_key(temp));
            for roots in self
                .copy_root_retirements
                .releases
                .values_mut()
                .chain(self.copy_root_retirements.after_releases.values_mut())
            {
                roots.retain(|temp| !self.readonly_parameter_copies.contains_key(temp));
            }
        }
        let source_ends = self
            .copy_root_retirements
            .producers
            .iter()
            .filter_map(|temp| {
                let def = &dataflow.defs[temp.index()];
                let LowInstr::Move(copy) = &proto.instrs[def.instr.index()] else {
                    return None;
                };
                let SsaValue::Def(source_def) = dataflow.use_value(def.instr, copy.src) else {
                    return None;
                };
                let source = TempId(source_def.index());
                if fixed_temps.get(source.index()) != Some(&source)
                    || dataflow.reg_is_reference_captured(copy.src)
                {
                    return None;
                }
                let end = TempId(
                    dataflow
                        .unobserved_root_overwrite_after_last_use(source_def, cfg)?
                        .index(),
                );
                if fixed_temps.get(end.index()) != Some(&end) {
                    return None;
                }
                let endpoint = dataflow.defs[end.index()].instr;
                if !emitted(dataflow.defs[source.index()].instr) || !emitted(endpoint) {
                    return None;
                }
                // source 与独立副本各有自己的 home。直接源值的最后读取后无观察
                // 覆盖已经由共享 Dataflow 证明；纯写入前可结束源 holder，不能让
                // 被 label/debug 身份提升的旧 call result 继续保活到下一轮。
                (matches!(&proto.instrs[endpoint.index()], LowInstr::Move(move_)
                    if move_.src != move_.dst)
                    || matches!(
                        &proto.instrs[endpoint.index()],
                        LowInstr::LoadNil(_)
                            | LowInstr::LoadBool(_)
                            | LowInstr::LoadConst(_)
                            | LowInstr::LoadInteger(_)
                            | LowInstr::LoadNumber(_)
                    ))
                .then_some((source, endpoint))
            })
            .collect::<Vec<_>>();
        for (source, endpoint) in source_ends {
            if !self.copy_root_retirements.producers.contains(&source)
                && self.copy_root_retirements.defined_sources.insert(source)
            {
                self.copy_root_retirements
                    .boundaries
                    .extend([dataflow.defs[source.index()].instr, endpoint]);
                self.copy_root_retirements
                    .releases
                    .entry(endpoint)
                    .or_default()
                    .push(source);
            }
        }
        // 真实 COPY 支配全部退休点且留在同一发射作用域时，声明可从原定义开始。
        // 循环 header 先于 body producer、debug scope 或观察后释放仍需原入口 holder。
        // 按退休边一次筛选候选，不为每个 producer 重扫完整释放表。
        let mut defined = self
            .copy_root_retirements
            .producers
            .iter()
            .copied()
            .filter(|temp| debug_scopes[temp.index()].is_none())
            .collect::<BTreeSet<_>>();
        for (&endpoint, roots) in &self.copy_root_retirements.releases {
            let block = cfg.instr_to_block[endpoint.index()];
            for &temp in roots {
                let def = &dataflow.defs[temp.index()];
                if !graph.dominates(def.block, block)
                    || (def.block == block && def.instr.index() >= endpoint.index())
                    || emission.scope_owner(def.block) != emission.scope_owner(block)
                {
                    defined.remove(&temp);
                }
            }
        }
        for roots in self.copy_root_retirements.after_releases.values() {
            for temp in roots {
                defined.remove(temp);
            }
        }
        for temp in defined {
            self.copy_root_retirements.producers.remove(&temp);
            self.copy_root_retirements.defined_sources.insert(temp);
        }
    }

    pub(super) fn copy_root_temps(&self) -> &BTreeSet<TempId> {
        &self.copy_root_retirements.producers
    }

    /// 只在一个无观察覆盖点退休的入口 holder；消费者仍须证明原初始化与 binding。
    pub(super) fn single_copy_root_before_releases(&self) -> BTreeMap<TempId, InstrRef> {
        let mut sites = BTreeMap::new();
        for (&site, roots) in &self.copy_root_retirements.releases {
            for &root in roots {
                sites
                    .entry(root)
                    .and_modify(|prior| {
                        if *prior != Some(site) {
                            *prior = None;
                        }
                    })
                    .or_insert(Some(site));
            }
        }
        for roots in self.copy_root_retirements.after_releases.values() {
            for root in roots {
                sites.remove(root);
            }
        }
        sites
            .into_iter()
            .filter_map(|(root, site)| {
                self.copy_root_retirements
                    .producers
                    .contains(&root)
                    .then_some((root, site?))
            })
            .collect()
    }

    pub(super) fn protect_copy_root_temps(&self) -> BTreeSet<TempId> {
        self.copy_root_retirements
            .producers
            .iter()
            .chain(&self.copy_root_retirements.defined_sources)
            .chain(&self.copy_scoped_temps)
            .copied()
            .collect()
    }

    /// 原 MOVE 链读取未写且未引用捕获的低槽 Luau 参数。只证明值身份；
    /// COPY 的目标覆盖仍须保留，不以参数持有同一对象授权删除原物理写。
    pub(super) fn readonly_parameter_copy(&self, temp: TempId) -> Option<ParamId> {
        let param = *self.readonly_parameter_copies.get(&temp)?;
        (self.trusted_param_home_slot(param)?.slot() < self.trusted_temp_home_slot(temp)?.slot())
            .then_some(param)
    }

    pub(super) fn copy_scoped_temps(&self) -> &BTreeSet<TempId> {
        &self.copy_scoped_temps
    }

    /// COPY 的原声明已承接实际覆盖：高槽窗口在 NEWTABLE 前结束，低槽原 binding
    /// 接收其后 MOVE。两者继续保留物理前缀，不再为同一次覆盖另发 holder 清空。
    pub(super) fn record_allocation_copy_scopes(&mut self, roots: BTreeSet<TempId>) {
        for root in &roots {
            self.copy_root_retirements.producers.remove(root);
            self.copy_root_retirements.defined_sources.remove(root);
        }
        for releases in self
            .copy_root_retirements
            .releases
            .values_mut()
            .chain(self.copy_root_retirements.after_releases.values_mut())
        {
            releases.retain(|root| !roots.contains(root));
        }
        self.copy_scoped_temps.extend(roots);
    }

    pub(super) fn install_copy_root_scopes(&mut self, scopes: Vec<(TempId, TempId, InstrRef)>) {
        let mut holders = BTreeMap::new();
        for (source, holder, last) in scopes {
            self.copy_root_retirements.producers.remove(&source);
            self.copy_root_retirements.producers.insert(holder);
            self.copy_scoped_temps.insert(source);
            self.copy_scope_handoffs
                .entry(last)
                .or_default()
                .push((source, holder));
            self.copy_root_retirements.boundaries.insert(last);
            self.record_home_free_temp(holder);
            holders.insert(source, holder);
        }
        for roots in self.copy_root_retirements.releases.values_mut() {
            for root in roots {
                if let Some(holder) = holders.get(root) {
                    *root = *holder;
                }
            }
        }
    }

    pub(super) fn copy_scope_handoffs(&self, instr: InstrRef) -> &[(TempId, TempId)] {
        self.copy_scope_handoffs
            .get(&instr)
            .map_or(&[], Vec::as_slice)
    }

    pub(super) fn copy_root_before_releases(&self, instr: InstrRef) -> &[TempId] {
        self.copy_root_retirements
            .releases
            .get(&instr)
            .map_or(&[], Vec::as_slice)
    }

    pub(super) fn copy_root_after_releases(&self, instr: InstrRef) -> &[TempId] {
        self.copy_root_retirements
            .after_releases
            .get(&instr)
            .map_or(&[], Vec::as_slice)
    }

    pub(super) fn observing_copy_root_temps(&self) -> BTreeSet<TempId> {
        self.copy_root_retirements
            .after_releases
            .values()
            .flatten()
            .copied()
            .collect()
    }

    pub(super) fn has_copy_root_boundary(&self, range: std::ops::Range<usize>) -> bool {
        self.copy_root_retirements
            .boundaries
            .range(InstrRef(range.start)..InstrRef(range.end))
            .next()
            .is_some()
    }
    /// 查询原始参数 producer 候选；消费者仍须匹配当前唯一 definition 与具体 call 参数端点。
    pub(super) fn temp_is_transferred_call_argument(&self, temp: TempId) -> bool {
        self.trusted_temp_home_slot(temp).is_some() && self.argument_root_producers.contains(&temp)
    }

    /// 原调用的独立源槽、准备副本或结果写回，必须由完整帧共同消费。
    pub(super) fn temp_requires_call_frame(&self, temp: TempId) -> bool {
        self.call_frame_temps.contains(&temp)
    }

    /// 活动低槽的原 callee/receiver COPY 是完整赋值帧的准备事件；即使两槽此时同值，
    /// 普通 carried-copy 清理也不能先删掉它，让后层再猜从哪一个低槽重发准备。
    pub(super) fn call_preparation_local_copies(
        &self,
    ) -> impl Iterator<Item = (LocalId, LocalId)> + '_ {
        self.calls.values().filter_map(|call| {
            let [source, preparation, _] = call.assignment_copies?;
            Some((
                self.promoted_local_for_temp(preparation)?,
                self.promoted_local_for_temp(source)?,
            ))
        })
    }

    /// 源 call result 在最后值读取后、首个观察前已有精确同 home 覆盖。
    /// 这仅约束物理 root 后缀，当前 producer 单写/单读和移动到消费点的求值顺序仍由 HIR 证明。
    pub(super) fn call_result_root_ends_after_value_use(&self, temp: TempId) -> bool {
        let Some(home) = self.trusted_temp_home_slot(temp) else {
            return false;
        };
        self.unobserved_call_result_ends
            .get(&temp)
            .is_some_and(|ends| {
                !ends.is_empty()
                    && ends
                        .iter()
                        .all(|end| self.trusted_temp_home_slot(*end) == Some(home))
            })
    }

    /// 最终数值 for 协议接管的三个控制槽；不从折叠后的 HIR operand 重建寄存器。
    pub(super) fn numeric_for_header(&self, init: InstrRef) -> NativeNumericForHeader {
        self.numeric_for_headers[&init]
    }

    /// 原 LOADNIL 的全部 canonical 定义，按真实槽序保存；不从当前相邻 nil 反猜批次。
    pub(super) fn nil_write_temps(&self, first: TempId) -> Option<&[TempId]> {
        self.nil_write_temps.get(&first).map(Vec::as_slice)
    }

    pub(super) fn has_nil_writes(&self) -> bool {
        !self.nil_write_temps.is_empty()
    }

    pub(super) fn nil_write_groups(&self) -> impl Iterator<Item = &[TempId]> {
        self.nil_write_temps.values().map(Vec::as_slice)
    }

    /// control_homes 来自原 NumericForProtocol，binding home 来自同一协议的语法绑定。
    /// 这里只验证两域组成连续源码声明区，不按方言猜隐藏槽数，也不重扫原 loops。
    pub(super) fn numeric_for_body_frame(
        &self,
        for_: &crate::hir::common::HirNumericFor,
    ) -> Option<NativeNumericForFrame> {
        let homes = self.possible_local_home_slots(for_.binding)?;
        let binding_slot = homes.first()?.slot();
        if homes.iter().any(|home| home.slot() != binding_slot) {
            return None;
        }
        let mut controls = for_.control_homes;
        controls.sort_unstable();
        let base = controls[0].slot();
        if controls
            .iter()
            .enumerate()
            .any(|(offset, home)| home.slot() != base + offset)
        {
            return None;
        }
        let controls_len = if binding_slot == controls[2].slot() {
            2
        } else if binding_slot == base + controls.len() {
            controls.len()
        } else {
            return None;
        };
        Some(NativeNumericForFrame {
            controls,
            controls_len,
            binding_slot,
        })
    }

    pub(super) fn generic_for_body_frame(
        &self,
        for_: &crate::hir::common::HirGenericFor,
    ) -> Option<&NativeGenericForFrame> {
        let source = for_.body_frame_source?;
        if self.source_proto != Some(source.proto) {
            return None;
        }
        let frame = self.generic_for_body_frames.get(&source.instr)?;
        if for_.bindings.len() != frame.bindings.len()
            || for_.dispatch_results.len() != frame.bindings.len()
        {
            return None;
        }
        for ((&binding, result), &home) in for_
            .bindings
            .iter()
            .zip(&for_.dispatch_results)
            .zip(&frame.bindings)
        {
            if result.success_binding != binding
                || self.trusted_local_home_slot(binding) != Some(home)
                || self.trusted_temp_home_slot(result.result_def) != Some(home)
            {
                return None;
            }
        }
        Some(frame)
    }

    /// 精确 dispatch 排除的原始 caller root；当前值流和求值前缀仍由 HIR 消费者核对。
    pub(super) fn call_frame_root_ends(&self, call: InstrRef) -> Vec<TempId> {
        self.frame_root_ends_by_call
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
        self.calls
            .get(&call)
            .map(|facts| facts.argument_roots.clone())
            .unwrap_or_default()
    }

    /// 原 CALL 的槽与宽度只用于完整表达式事务，不意味着零返回也会覆盖旧 callee。
    pub(super) fn native_call_frame(
        &self,
        call: &crate::hir::common::HirCallExpr,
    ) -> Option<call_roots::NativeCallFrame> {
        let source = call.source_site?;
        if self.source_proto != Some(source.proto) || call.fastcall.is_some() {
            return None;
        }
        let facts = self.calls.get(&source.instr)?;
        if facts.layout.fastcall.is_some() {
            return None;
        }
        let callee = facts.callee?;
        let layout = facts.layout;
        (self.trusted_temp_home_slot(callee) == Some(layout.home)).then_some(
            call_roots::NativeCallFrame {
                callee,
                home: layout.home,
                args: layout.args,
                results: layout.results,
                arguments_unaliased: layout.arguments_unaliased,
            },
        )
    }

    /// 物理参数区不因函数值的 phi/capture 身份未证而消失；不授权完整帧内联。
    pub(super) fn native_call_layout(
        &self,
        call: &crate::hir::common::HirCallExpr,
    ) -> Option<call_roots::NativeCallLayout> {
        let source = call.source_site?;
        if self.source_proto != Some(source.proto) || call.fastcall.is_some() {
            return None;
        }
        let layout = self.calls.get(&source.instr)?.layout;
        layout.fastcall.is_none().then_some(layout)
    }

    /// 当前原 CALL 仍持有标量后缀的三个定义及各自 home；后层还须匹配实际赋值，
    /// 不能把原常量协议用于已改变的值、参数身份或其它 CALL 的临时结果。
    pub(super) fn native_scalar_assignment(
        &self,
        call: &crate::hir::common::HirCallExpr,
    ) -> Option<call_roots::NativeScalarAssignment> {
        let frame = self.native_call_frame(call)?;
        let assignment = self
            .calls
            .get(&call.source_site?.instr)?
            .scalar_assignment?;
        (self.trusted_temp_home_slot(assignment.result) == Some(frame.home)
            && self.trusted_temp_home_slot(assignment.scalar) == Some(assignment.scalar_home)
            && self.trusted_temp_home_slot(assignment.writeback) == Some(assignment.target_home))
        .then_some(assignment)
    }

    /// 原固定结果的连续写回仍属于当前 CALL；按原指令顺序发布，不从 HIR Phi 的排列猜测。
    pub(super) fn native_result_writebacks(
        &self,
        call: &crate::hir::common::HirCallExpr,
    ) -> Option<&[call_roots::NativeResultWriteback]> {
        self.native_call_layout(call)?;
        self.calls
            .get(&call.source_site?.instr)?
            .result_writebacks
            .as_deref()
    }

    /// 原 CALL 直接消费的开放 VARARG 包；只持有原包起点，不从最终省略号外形猜槽。
    pub(super) fn call_vararg_tail_home(
        &self,
        call: &crate::hir::common::HirCallExpr,
    ) -> Option<HomeSlotKey> {
        let source = call.source_site?;
        (self.source_proto == Some(source.proto)).then_some(())?;
        self.calls.get(&source.instr)?.vararg_tail_home
    }

    /// 原 MOVE 覆盖的单个 Def；只连接仍有效的同一 home/epoch，不把 phi 猜成某个入口。
    pub(super) fn copy_predecessor(&self, result: TempId) -> Option<TempId> {
        let previous = *self.copy_predecessors.get(&result)?;
        let home = self.trusted_temp_home_slot(result)?;
        (self.trusted_temp_home_slot(previous) == Some(home)
            && !self.reference_aliased_move_temps.contains(&result))
        .then_some(previous)
    }

    /// 固定单结果原 CALL 在返回时覆盖自己的 callee 槽；这是身份连续性，不是帧内联许可。
    /// 当前 callee 必须仍是原 Def，结果也必须保留原操作身份，不能把后续 MOVE 当作 CALL 写。
    pub(super) fn same_slot_call_predecessor(
        &self,
        call: &crate::hir::common::HirCallExpr,
        result: TempId,
    ) -> Option<TempId> {
        let frame = self.native_call_frame(call)?;
        (!call.is_method()
            && call.callee == crate::hir::common::HirExpr::TempRef(frame.callee)
            && self.operation_result_temp(call.source_site?) == Some(result)
            && self.trusted_temp_home_slot(result) == Some(frame.home)
            && matches!(frame.results, Some(ResultPack::Fixed(pack)) if pack.len == 1)
            && self.operation_result_reference_unaliased(call.source_site?))
        .then_some(frame.callee)
    }

    /// 单次比较之后的两个 LOADBOOL 共同写原结果槽；没有比较前的 Boolean 预写。
    /// 这里只接受读取低槽身份的比较，因此目标复用不会另开操作数 scratch。
    pub(super) fn is_direct_comparison_result(
        &self,
        temp: TempId,
        value: &HirExpr,
        temp_is_local: impl Fn(TempId) -> bool,
    ) -> bool {
        let Some(home) = self.trusted_temp_home_slot(temp) else {
            return false;
        };
        self.local_comparison_result(temp, value, temp_is_local, Some(home.slot()))
    }

    /// 原 Boolean 结果写回既有 local 时，操作数只需仍在各自已声明的原槽。
    /// 高于写回目标的 local 同样直接参与比较；这不是允许新声明或 scratch 改址。
    pub(super) fn is_local_comparison_result(
        &self,
        temp: TempId,
        value: &HirExpr,
        temp_is_local: impl Fn(TempId) -> bool,
    ) -> bool {
        self.local_comparison_result(temp, value, temp_is_local, None)
    }

    fn local_comparison_result(
        &self,
        temp: TempId,
        value: &HirExpr,
        temp_is_local: impl Fn(TempId) -> bool,
        operand_ceiling: Option<usize>,
    ) -> bool {
        let Some(&predicate) = self.comparison_result_writes.get(&temp) else {
            return false;
        };
        if self.trusted_temp_home_slot(temp).is_none() {
            return false;
        }
        let binary = match value {
            HirExpr::Binary(binary)
                if matches!(
                    binary.op,
                    crate::hir::common::HirBinaryOpKind::Eq
                        | crate::hir::common::HirBinaryOpKind::Lt
                        | crate::hir::common::HirBinaryOpKind::Le
                ) =>
            {
                binary
            }
            HirExpr::Unary(unary) if unary.op == crate::hir::common::HirUnaryOpKind::Not => {
                let HirExpr::Binary(binary) = &unary.expr else {
                    return false;
                };
                if binary.op != crate::hir::common::HirBinaryOpKind::Eq {
                    return false;
                }
                binary
            }
            _ => return false,
        };
        if !binary
            .source_site
            .is_some_and(|site| Some(site.proto) == self.source_proto && site.instr == predicate)
        {
            return false;
        }
        let Some(layout) = self.native_binary_layout(binary) else {
            return false;
        };
        [&binary.lhs, &binary.rhs]
            .into_iter()
            .zip([layout.lhs, layout.rhs])
            .all(|(value, original)| {
                let source = match value {
                    HirExpr::TempRef(temp) if temp_is_local(*temp) => {
                        self.trusted_temp_home_slot(*temp)
                    }
                    HirExpr::LocalRef(local) => self.trusted_local_home_slot(*local),
                    HirExpr::ParamRef(param) => self.trusted_param_home_slot(*param),
                    _ => None,
                };
                source.is_some_and(|source| {
                    Some(source) == original
                        && operand_ceiling.is_none_or(|limit| source.slot() < limit)
                })
            })
    }

    /// 原比较的唯一 Boolean 写回身份；与 locals 共用已冻结的双分支写证明。
    /// 按谓词索引查询，避免每个字段扫描全 proto；失效 home 不签发结果槽。
    pub(super) fn direct_comparison_result_temp(&self, value: &HirExpr) -> Option<TempId> {
        let HirExpr::Binary(binary) = value else {
            return None;
        };
        let temp = self.comparison_result_temp(binary)?;
        self.is_direct_comparison_result(temp, value, |_| false)
            .then_some(temp)
    }

    /// 冻结谓词对应的唯一 Boolean 写回；交换为 Gt/Ge 只改变操作数方向，结果身份不变。
    /// 输入准备和原操作数布局由帧消费者另证。
    pub(super) fn comparison_result_temp(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
    ) -> Option<TempId> {
        if !matches!(
            binary.op,
            crate::hir::common::HirBinaryOpKind::Eq
                | crate::hir::common::HirBinaryOpKind::Lt
                | crate::hir::common::HirBinaryOpKind::Le
                | crate::hir::common::HirBinaryOpKind::Gt
                | crate::hir::common::HirBinaryOpKind::Ge
        ) {
            return None;
        }
        let source = binary.source_site?;
        if self.source_proto != Some(source.proto) {
            return None;
        }
        let temp = (*self.comparison_results_by_predicate.get(&source.instr)?)?;
        self.trusted_temp_home_slot(temp)?;
        Some(temp)
    }

    /// FASTCALL 的完整帧保持其 builtin 与参数求值域，不能借 fallback CALL 改成普通帧。
    pub(super) fn native_fastcall_frame(
        &self,
        call: &crate::hir::common::HirCallExpr,
    ) -> Option<call_roots::NativeCallFrame> {
        let source = call.source_site?;
        let protocol = call.fastcall?;
        if self.source_proto != Some(source.proto) {
            return None;
        }
        let facts = self.calls.get(&source.instr)?;
        let layout = facts.layout;
        let callee = facts.callee?;
        (layout.fastcall == Some(protocol)
            && self.trusted_temp_home_slot(callee) == Some(layout.home))
        .then_some(call_roots::NativeCallFrame {
            callee,
            home: layout.home,
            args: layout.args,
            results: layout.results,
            arguments_unaliased: layout.arguments_unaliased,
        })
    }

    /// 原 FASTCALL callee Def 先于所有 fallback 参数 COPY；仍须原位重发 direct 参数。
    pub(super) fn fastcall_callee_precedes_copies(
        &self,
        call: &crate::hir::common::HirCallExpr,
    ) -> bool {
        self.native_fastcall_frame(call).is_some()
            && call
                .source_site
                .and_then(|source| self.calls.get(&source.instr))
                .is_some_and(|facts| facts.fastcall_callee_before_copies)
    }

    /// 原 CLOSURE 与唯一紧邻 callee COPY 的完整写域；只证明声明和调用的两槽布局。
    /// 缩域还需当前树中单写、唯一直接读取及后继完整覆盖，不能从这里提前释放闭包。
    pub(super) fn closure_statement_home(
        &self,
        local: LocalId,
        closure: &crate::hir::common::HirClosureExpr,
        call: &crate::hir::common::HirCallExpr,
    ) -> Option<HomeSlotKey> {
        self.statement_result_home(local, closure.source_site?, call)
    }

    /// CALL 固定单结果与原 callee COPY 共用 CLOSURE 的两槽写域证明；结果是否
    /// 必为闭包另由返回值 owner 提供，物理 home 相同不能替代值类型证明。
    pub(super) fn call_result_statement_home(
        &self,
        local: LocalId,
        inner: &crate::hir::common::HirCallExpr,
        outer: &crate::hir::common::HirCallExpr,
    ) -> Option<HomeSlotKey> {
        let frame = self.native_call_frame(inner)?;
        if !matches!(frame.results, Some(ResultPack::Fixed(pack))
            if pack.start.index() == frame.home.slot() && pack.len == 1)
        {
            return None;
        }
        let home = self.statement_result_home(local, inner.source_site?, outer)?;
        (home == frame.home).then_some(home)
    }

    fn statement_result_home(
        &self,
        local: LocalId,
        source: crate::hir::common::HirSourceSite,
        call: &crate::hir::common::HirCallExpr,
    ) -> Option<HomeSlotKey> {
        let frame = self.native_call_frame(call)?;
        let original = self.operation_result_temp(source)?;
        let home = self.trusted_temp_home_slot(original)?;
        let [copy] = self.trusted_immediate_moves(original)? else {
            return None;
        };
        (frame.results == Some(ResultPack::Ignore)
            && frame.home.slot() == home.slot() + 1
            && self.promoted_local_for_temp(original) == Some(local)
            && self.trusted_local_home_slot(local) == Some(home)
            && copy.source == Some(original)
            && copy.source_home == home
            && copy.target == frame.callee
            && copy.target_home == frame.home
            && self
                .complete_local_definition_write_homes(local)
                .iter()
                .copied()
                .eq([home, frame.home]))
        .then_some(home)
    }

    /// 调用参数的原值版本，独立于 LocalId 的后续复用；不签发参数根退休许可。
    /// CALL 索引已绑定原 Def，可信 home 保留该 Def 的 epoch；参数布局只核对槽距。
    pub(super) fn call_argument_value(
        &self,
        call: &crate::hir::common::HirCallExpr,
        argument: usize,
    ) -> Option<TempId> {
        let site = call.source_site?;
        if self.source_proto != Some(site.proto) {
            return None;
        }
        let facts = self.calls.get(&site.instr)?;
        let start = match facts.layout.args {
            crate::transformer::ValuePack::Fixed(pack) => pack.start,
            crate::transformer::ValuePack::Open(start) => start,
        };
        let value = *facts.argument_values.get(argument)?.as_ref()?;
        (facts.layout.fastcall == call.fastcall
            && self
                .trusted_temp_home_slot(value)
                .is_some_and(|home| home.slot() == start.index() + argument))
        .then_some(value)
    }

    /// 参数内嵌读取与原 CALL 的唯一 use→Def；值、物理槽及当前调用协议须同时匹配。
    pub(super) fn call_argument_preparation(
        &self,
        call: &crate::hir::common::HirCallExpr,
        argument: usize,
        value: &crate::hir::common::HirExpr,
    ) -> Option<HomeSlotKey> {
        let original = self.call_argument_value(call, argument)?;
        let preparation = self
            .calls
            .get(&call.source_site?.instr)?
            .argument_preparations
            .get(&argument)?;
        (preparation.temp == original && preparation.matches(value)).then_some(preparation.home)
    }

    /// 连续展开体使用原参数准备指令配对操作，不能仅凭相同的字面量猜测来源。
    pub(super) fn call_argument_preparation_instruction(
        &self,
        call: &crate::hir::common::HirCallExpr,
        argument: usize,
        value: &HirExpr,
    ) -> Option<InstrRef> {
        self.call_argument_preparation(call, argument, value)?;
        Some(
            self.calls
                .get(&call.source_site?.instr)?
                .argument_preparations
                .get(&argument)?
                .read,
        )
    }

    /// 参数 MOVE 的原 use→Def 与当前调用共同签证，不能沿 Local 名称追溯旧值。
    pub(super) fn call_argument_copy(
        &self,
        call: &crate::hir::common::HirCallExpr,
        argument: usize,
    ) -> Option<call_roots::NativeArgumentCopy> {
        let original = self.call_argument_value(call, argument)?;
        let copy = *self
            .calls
            .get(&call.source_site?.instr)?
            .argument_copies
            .get(&argument)?;
        (copy.target == original
            && self.trusted_temp_home_slot(copy.source) == Some(copy.source_home)
            && self.trusted_temp_home_slot(copy.target) == Some(copy.target_home))
        .then_some(copy)
    }

    /// 固定结果包每项的原 Def；与承接它的 Local 后续复用版本分离。
    /// 结果可写入 CLOSE 后的新 cell，不能把连续槽布局误解为 epoch 必须为零。
    pub(super) fn fixed_call_result(
        &self,
        call: &crate::hir::common::HirCallExpr,
        offset: usize,
    ) -> Option<TempId> {
        let site = call.source_site?;
        if self.source_proto != Some(site.proto) {
            return None;
        }
        let facts = self.calls.get(&site.instr)?;
        let Some(ResultPack::Fixed(pack)) = facts.layout.results else {
            return None;
        };
        let temp = *facts.fixed_results.as_ref()?.get(offset)?;
        (facts.layout.fastcall == call.fastcall
            && self
                .trusted_temp_home_slot(temp)
                .is_some_and(|home| home.slot() == pack.start.index() + offset))
        .then_some(temp)
    }

    /// 完整 FASTCALL 事务使用的原 fallback COPY；不等同于参数根单独退休。
    pub(super) fn fastcall_argument_copies(
        &self,
        call: &crate::hir::common::HirCallExpr,
    ) -> Option<&[call_roots::FastCallArgumentCopy]> {
        let source = call.source_site?;
        if self.source_proto != Some(source.proto) {
            return None;
        }
        let facts = self.calls.get(&source.instr)?;
        (facts.layout.fastcall == call.fastcall
            && call.fastcall.is_some()
            && facts.fastcall_argument_copies.iter().all(|copy| {
                self.trusted_temp_home_slot(copy.producer) == Some(copy.home)
                    && copy.source.is_none_or(|source| {
                        self.trusted_temp_home_slot(source) == Some(copy.source_home)
                    })
            }))
        .then_some(facts.fastcall_argument_copies.as_slice())
    }

    pub(super) fn boolean_argument_prewrite(
        &self,
        call: &crate::hir::common::HirCallExpr,
        argument: usize,
    ) -> Option<call_roots::BooleanArgumentPrewrite> {
        self.boolean_argument_prewrites(call)
            .find(|write| write.argument == argument)
    }

    /// ValueDecision 的入口预写属于结果值；经 COPY 用作参数也不能丢掉此配对。
    /// 两个身份均保留同一原 home 时，完整 initializer 可重发同槽预写。
    pub(super) fn boolean_value_prewrites(
        &self,
    ) -> impl Iterator<Item = (TempId, TempId, HomeSlotKey, bool)> + '_ {
        self.boolean_value_prewrites
            .iter()
            .filter_map(|(&result, _)| self.boolean_value_prewrite(result))
    }

    pub(super) fn boolean_value_prewrite(
        &self,
        result: TempId,
    ) -> Option<(TempId, TempId, HomeSlotKey, bool)> {
        let &(initial, value) = self.boolean_value_prewrites.get(&result)?;
        let home = self.trusted_temp_home_slot(result)?;
        (self.trusted_temp_home_slot(initial) == Some(home))
            .then_some((initial, result, home, value))
    }

    pub(super) fn has_upvalue_writes(&self) -> bool {
        !self.upvalue_writes.is_empty()
    }

    pub(super) fn has_environment_writes(&self) -> bool {
        self.table_write_layouts
            .values()
            .any(|layout| matches!(layout, NativeTableWriteLayout::Environment { .. }))
    }

    pub(super) fn copy_value_prewrites(
        &self,
    ) -> impl Iterator<Item = (TempId, TempId, HomeSlotKey)> + '_ {
        self.copy_value_prewrites
            .iter()
            .filter_map(|(&result, &initial)| {
                let (_, home) = self.copy_value_prewrite(result)?;
                Some((initial, result, home))
            })
    }

    pub(super) fn copy_value_prewrite(&self, result: TempId) -> Option<(TempId, HomeSlotKey)> {
        let initial = *self.copy_value_prewrites.get(&result)?;
        let home = self.trusted_temp_home_slot(result)?;
        (self.trusted_temp_home_slot(initial) == Some(home)).then_some((initial, home))
    }

    /// 合流入口的原 MOVE 保留高槽结果与低槽写回身份，不从展示 local 猜原槽。
    pub(super) fn value_result_copy(&self, result: TempId) -> Option<&ImmediateMoveWrite> {
        let copy = self.value_result_copies.get(&result)?;
        (self.trusted_temp_home_slot(result) == Some(copy.source_home)
            && self.trusted_temp_home_slot(copy.target) == Some(copy.target_home))
        .then_some(copy)
    }

    /// 入口清零事实和原 SETUPVAL 输入共同证明 nil 来自哪个原槽，不从字面量猜测。
    pub(super) fn entry_nil_upvalue_write(
        &self,
        assign: &crate::hir::common::HirAssign,
    ) -> Option<(InstrRef, UpvalueId, HomeSlotKey)> {
        let site = assign.upvalue_write_source?;
        if self.source_proto != Some(site.proto) || assign.is_phi_transfer {
            return None;
        }
        let (target, UpvalueWriteInput::EntryNil(home)) = *self.upvalue_writes.get(&site.instr)?
        else {
            return None;
        };
        (assign.targets.as_slice() == [crate::hir::common::HirLValue::Upvalue(target)]
            && assign.values.fixed.as_slice() == [HirExpr::Nil]
            && assign.values.tail.is_none())
        .then_some((site.instr, target, home))
    }

    /// 直接写上值的原 SSA 输入仍是同一 Boolean 决策结果；RHS 树由完整帧另行验证。
    pub(super) fn boolean_upvalue_prewrite(
        &self,
        assign: &crate::hir::common::HirAssign,
    ) -> Option<(TempId, TempId, HomeSlotKey, bool)> {
        let site = assign.upvalue_write_source?;
        if self.source_proto != Some(site.proto) || assign.is_phi_transfer {
            return None;
        }
        let (target, UpvalueWriteInput::Temp(result)) = *self.upvalue_writes.get(&site.instr)?
        else {
            return None;
        };
        if assign.targets.as_slice() != [crate::hir::common::HirLValue::Upvalue(target)] {
            return None;
        }
        let &(initial, value) = self.boolean_value_prewrites.get(&result)?;
        let home = self.trusted_temp_home_slot(result)?;
        (self.trusted_temp_home_slot(initial) == Some(home))
            .then_some((initial, result, home, value))
    }

    /// 当前原 CALL 的全部可信预写；清理 owner 一次收集需求，不按参数反复查找同一列表。
    pub(super) fn boolean_argument_prewrites(
        &self,
        call: &crate::hir::common::HirCallExpr,
    ) -> impl Iterator<Item = call_roots::BooleanArgumentPrewrite> + '_ {
        call.source_site
            .filter(|source| self.source_proto == Some(source.proto))
            .and_then(|source| self.calls.get(&source.instr))
            .into_iter()
            .flat_map(|facts| facts.boolean_prewrites.iter().copied())
            .filter(|prewrite| {
                self.trusted_temp_home_slot(prewrite.initial) == Some(prewrite.home)
                    && self.trusted_temp_home_slot(prewrite.result) == Some(prewrite.home)
            })
    }

    pub(super) fn native_return_frame(
        &self,
        ret: &crate::hir::common::HirReturn,
    ) -> Option<NativeReturnFrame> {
        let source = ret.frame_source?;
        if self.source_proto != Some(source.proto) || ret.pending_cleanup_source.is_some() {
            return None;
        }
        self.return_frames.get(&source.instr).copied()
    }

    /// 共用返回布局的所有原 RETURN 在该位置读取同一 Def 时，才发布版本身份。
    /// 布局等价不代表值等价；分支合并后不同来源的成员仍只消费布局证明。
    pub(super) fn fixed_return_input(
        &self,
        ret: &crate::hir::common::HirReturn,
        index: usize,
    ) -> Option<TempId> {
        let frame = self.native_return_frame(ret)?;
        let input = (*self
            .return_fixed_inputs
            .get(&ret.frame_source?.instr)?
            .get(index)?)?;
        (self.trusted_temp_home_slot(input)?.slot() == frame.home.slot() + index).then_some(input)
    }

    /// 只读参数判定树的唯一结果槽；仍须由消费者核对当前 HIR 与源码首空槽。
    pub(super) fn parameter_return_scratch(&self) -> Option<HomeSlotKey> {
        self.parameter_return_scratch
    }

    /// 仅用于无实参、丢弃结果的调用；不把“本体无观察”当作返回后没有物理覆盖差异。
    pub(super) fn empty_call_preserves_frame(&self) -> bool {
        self.empty_call_preserves_frame
    }

    /// 原高返回 COPY 的低槽输入必须先持有声明身份，后续完整帧才能重发原准备区。
    pub(super) fn return_copy_roots(&self) -> impl Iterator<Item = TempId> + '_ {
        self.return_copy_roots.iter().copied()
    }

    /// 入口参数残根及其独立 COPY 准备；caller 可在返回后观察高槽，原准备不能提前内联。
    pub(super) fn entry_parameter_copy_roots(&self) -> impl Iterator<Item = TempId> + '_ {
        self.entry_parameter_copy_roots.iter().copied()
    }

    pub(super) fn native_table_batch_layout(
        &self,
        batch: &crate::hir::common::HirTableSetList,
    ) -> Option<NativeTableBatchLayout> {
        let source = batch.source_site?;
        let layout = *self.table_batch_layouts.get(&source.instr)?;
        (self.source_proto == Some(source.proto) && batch.start_index == layout.start_index)
            .then_some(layout)
    }

    /// SETLIST 各固定元素的原值版本；同 Local 的后续 COPY 或调用结果不属于本批写域。
    pub(super) fn table_batch_value(
        &self,
        batch: &crate::hir::common::HirTableSetList,
        index: usize,
    ) -> Option<TempId> {
        let source = batch.source_site?;
        let layout = self.native_table_batch_layout(batch)?;
        let value = (*self.table_batch_values.get(&source.instr)?.get(index)?)?;
        (self
            .trusted_temp_home_slot(value)
            .is_some_and(|home| home.slot() == layout.buffer.slot() + index))
        .then_some(value)
    }

    /// 已吸收进构造器的唯一批次指令；互斥 allocation 不能共用一个 debug 结束身份。
    pub(super) fn native_allocation_batch_site(
        &self,
        table: &crate::hir::common::HirTableConstructor,
    ) -> Option<crate::hir::common::HirSourceSite> {
        let crate::hir::common::HirOperationSources::Single(source) = table.sources else {
            return None;
        };
        self.operation_result_home(source)?;
        Some(crate::hir::common::HirSourceSite {
            proto: source.proto,
            instr: match self.allocation_batches.get(&source.instr)?.as_slice() {
                [batch] => *batch,
                _ => return None,
            },
        })
    }

    /// 已完成构造器的原数组缓冲布局；布局相同不表示各批次具有相同指令身份。
    pub(super) fn native_allocation_batch_layout(
        &self,
        table: &crate::hir::common::HirTableConstructor,
    ) -> Option<NativeTableBatchLayout> {
        let mut result = None;
        table.sources.try_for_each_known(|source| {
            self.operation_result_home(source)?;
            let [batch] = self.allocation_batches.get(&source.instr)?.as_slice() else {
                return None;
            };
            let layout = *self.table_batch_layouts.get(batch)?;
            if result.is_some_and(|previous| previous != layout) {
                return None;
            }
            result = Some(layout);
            Some(())
        })?;
        result
    }

    /// 完整分配的有序 SETLIST 批次；候选仍须证明连续索引、缓冲复用与实际字段数。
    pub(super) fn native_allocation_batches(
        &self,
        table: &crate::hir::common::HirTableConstructor,
    ) -> Option<Vec<NativeTableBatchLayout>> {
        let crate::hir::common::HirOperationSources::Single(source) = table.sources else {
            return None;
        };
        self.operation_result_home(source)?;
        self.allocation_batches
            .get(&source.instr)?
            .iter()
            .map(|batch| self.table_batch_layouts.get(batch).copied())
            .collect()
    }

    /// 相同结果 home/宽度且无开放引用的返回共享布局身份；不把诊断指令号当语义差异。
    pub(super) fn return_frame_source(
        &self,
        instr: InstrRef,
    ) -> Option<crate::hir::common::HirSourceSite> {
        Some(crate::hir::common::HirSourceSite {
            proto: self.source_proto?,
            instr: *self.return_frame_sources.get(&instr)?,
        })
    }

    /// 原一元操作仍在当前表达式中写回哪个 home；不是操作前可释放旧根的许可。
    pub(super) fn unary_result_home(
        &self,
        unary: &crate::hir::common::HirUnaryExpr,
    ) -> Option<HomeSlotKey> {
        self.operation_result_home(unary.source_site?)
    }

    /// 原一元操作的寄存器输入；内联成数字后仍须保留该 scratch 的写入位置。
    pub(super) fn unary_operand_home(
        &self,
        unary: &crate::hir::common::HirUnaryExpr,
    ) -> Option<HomeSlotKey> {
        let source = unary.source_site?;
        self.operation_result_home(source)?;
        self.unary_operands
            .get(&source.instr)
            .map(|input| input.home)
    }

    /// 原单值操作的 canonical Def 写回槽；site 必须属于当前 proto，不能反推内部操作。
    pub(super) fn operation_result_home(
        &self,
        source: crate::hir::common::HirSourceSite,
    ) -> Option<HomeSlotKey> {
        self.trusted_temp_home_slot(self.operation_result_temp(source)?)
    }

    /// 同一原单值操作的定义身份；后层可区分复用 Local 的不同 value epoch。
    /// OPEN/多结果 CALL 不属于这个域，不能借局部 instr_defs 宽度推断固定结果。
    pub(super) fn operation_result_temp(
        &self,
        source: crate::hir::common::HirSourceSite,
    ) -> Option<TempId> {
        if self.source_proto != Some(source.proto) {
            return None;
        }
        let temp = self.operation_results.get(&source.instr)?.temp;
        self.trusted_temp_home_slot(temp)?;
        Some(temp)
    }

    /// 未来相同 home 的 capture 不回溯到这次原操作；仍需消费完整原 home 和事件事务。
    pub(super) fn operation_result_reference_unaliased(
        &self,
        source: crate::hir::common::HirSourceSite,
    ) -> bool {
        self.operation_result_temp(source)
            .is_some_and(|temp| self.temp_definition_reference_unaliased(temp))
    }

    /// 原 fixed 写入时尚无打开的引用捕获；后续实际捕获该值的 binding 仍须单独保护。
    /// 不将稍后复用同槽的新 cell 回溯到旧值；合并或 home 失效后不能借用这份证明。
    pub(super) fn temp_definition_reference_unaliased(&self, temp: TempId) -> bool {
        self.trusted_temp_home_slot(temp).is_some()
            && self.reference_unaliased_temps.contains(&temp)
    }

    /// 原 MOVE 涉及已暴露的引用 cell，不能穿透其来源链读取初始化值。
    /// 后续复用同槽的 capture 不回溯到当前操作；跨 Close 的旧来源也不重获透明性。
    pub(super) fn move_crosses_reference_cell(&self, temp: TempId) -> bool {
        self.reference_aliased_move_temps.contains(&temp)
    }

    /// 单条隐式环境/环境 upvalue 常量键读取从结果槽开始准备；寄存器环境和动态键
    /// 另有输入 scratch，不可只凭 GlobalRef 外形推断入口。
    pub(super) fn direct_global_read_home(
        &self,
        source: crate::hir::common::HirSourceSite,
    ) -> Option<HomeSlotKey> {
        let home = self.operation_result_home(source)?;
        self.operation_results[&source.instr]
            .direct_global_read
            .then_some(home)
    }

    pub(super) fn global_read_frame(
        &self,
        global: &crate::hir::common::HirGlobalRef,
        dialect: crate::decompile::DecompileDialect,
    ) -> Option<HomeSlotKey> {
        if !global
            .key
            .as_utf8()
            .is_some_and(|name| dialect.is_identifier_name(name))
        {
            return None;
        }
        let mut result = None;
        global.sources.try_for_each_known(|source| {
            let home = self.direct_global_read_home(source)?;
            if result.is_some_and(|previous| previous != home) {
                return None;
            }
            result = Some(home);
            Some(())
        })?;
        result
    }

    /// 环境 GETTABUP 已投影为全局名时，原寄存器 key 仍归该读取所有，
    /// 不能再作为独立未使用声明物化。来源保持原 use→Def 身份。
    pub(super) fn global_read_key_preparation(
        &self,
        global: &crate::hir::common::HirGlobalRef,
    ) -> Option<TempId> {
        let crate::hir::common::HirOperationSources::Single(source) = global.sources else {
            return None;
        };
        self.operation_result_home(source)?;
        let (_, crate::hir::common::HirExpr::TempRef(temp)) =
            self.upvalue_table_reads.get(&source.instr)?
        else {
            return None;
        };
        self.trusted_temp_home_slot(*temp).map(|_| *temp)
    }

    /// 互斥分配合并后，所有原来源必须写回同一个可信 home；未知分支不能借用其它来源。
    pub(super) fn allocation_result_home(
        &self,
        table: &crate::hir::common::HirTableConstructor,
    ) -> Option<HomeSlotKey> {
        let mut result = None;
        table.sources.try_for_each_known(|source| {
            let home = self.operation_result_home(source)?;
            if result.is_some_and(|previous| previous != home) {
                return None;
            }
            result = Some(home);
            Some(())
        })?;
        result
    }

    /// 捕获许可同样对全部原分配时点求交，不以最终共享表达式的位置替代它们。
    pub(super) fn allocation_result_reference_unaliased(
        &self,
        table: &crate::hir::common::HirTableConstructor,
    ) -> bool {
        table
            .sources
            .try_for_each_known(|source| {
                self.operation_result_reference_unaliased(source)
                    .then_some(())
            })
            .is_some()
    }

    /// `({f()}) and 7 or 7` 经值化简后仍保留原 table/phi 关系。这里只接受单一
    /// 分配来源；合并、capture 或 home 失效不能借用旧的专属结果证书。
    pub(super) fn table_value_result(
        &self,
        table: &crate::hir::common::HirTableConstructor,
    ) -> Option<NativeConditionalValueResult> {
        let crate::hir::common::HirOperationSources::Single(source) = table.sources else {
            return None;
        };
        self.conditional_value_result(source)
    }

    pub(super) fn conditional_root_ended_by(&self, endpoint: TempId) -> Option<TempId> {
        self.conditional_root_endpoints.get(&endpoint).copied()
    }

    /// 两个当前单一来源仍属于原 OR/phi，且未合并身份或打开引用时才发布共同结果槽。
    pub(super) fn short_circuit_table_home(
        &self,
        input: crate::hir::common::HirSourceSite,
        alternative: crate::hir::common::HirSourceSite,
    ) -> Option<HomeSlotKey> {
        let frame = (*self
            .short_circuit_table_frames
            .get(&(input.instr, alternative.instr))?)?;
        let home = self.trusted_temp_home_slot(frame.result)?;
        (self.operation_result_temp(input) == Some(frame.input)
            && self.operation_result_temp(alternative) == Some(frame.alternative)
            && self.operation_result_reference_unaliased(input)
            && self.operation_result_reference_unaliased(alternative)
            && self.trusted_temp_home_slot(frame.input) == Some(home)
            && self.trusted_temp_home_slot(frame.alternative) == Some(home))
        .then_some(home)
    }

    pub(super) fn conditional_value_result(
        &self,
        source: crate::hir::common::HirSourceSite,
    ) -> Option<NativeConditionalValueResult> {
        let result = (*self.conditional_value_results.get(&source.instr)?)?;
        (self.operation_result_temp(source) == Some(result.input)
            && self.operation_result_reference_unaliased(source)
            && self.trusted_temp_home_slot(result.result).is_some())
        .then_some(result)
    }

    /// 当前 CALL、备用值与 AND/OR 仍匹配原单判定 phi，返回原输入和合流槽。
    pub(super) fn short_circuit_call_homes(
        &self,
        call: &crate::hir::common::HirCallExpr,
        alternative: &HirExpr,
        logical_and: bool,
    ) -> Option<(HomeSlotKey, HomeSlotKey)> {
        let source = call.source_site?;
        let frame = (*self.short_circuit_call_frames.get(&source.instr)?)?;
        let input = self.trusted_temp_home_slot(frame.input)?;
        let result = self.trusted_temp_home_slot(frame.result)?;
        let matches_alternative = match (frame.value, alternative) {
            (short_circuit_frames::ShortCircuitCallValue::Scalar(value), alternative) => {
                value.matches_hir_expr(alternative)
            }
            (
                short_circuit_frames::ShortCircuitCallValue::CopyTemp(source),
                HirExpr::LocalRef(local),
            ) => {
                self.promoted_local_for_temp(source) == Some(*local)
                    && self.trusted_temp_home_slot(source).is_some_and(|home| {
                        home.slot() < result.slot()
                            && self.trusted_local_home_slot(*local) == Some(home)
                    })
            }
            (
                short_circuit_frames::ShortCircuitCallValue::CopyParam(source),
                HirExpr::ParamRef(param),
            ) => {
                source == *param
                    && self
                        .trusted_param_home_slot(*param)
                        .is_some_and(|home| home.slot() < result.slot())
            }
            _ => false,
        };
        (frame.logical_and == logical_and
            && matches_alternative
            && self.operation_result_temp(source) == Some(frame.input)
            && self.operation_result_reference_unaliased(source)
            && self.trusted_temp_home_slot(frame.kept) == Some(result)
            && self.trusted_temp_home_slot(frame.alternative) == Some(result))
        .then_some((input, result))
    }

    /// canonical 原二元操作输入布局；结果槽相同不能证明可省略原 LOADK 输入准备。
    pub(super) fn native_binary_layout(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
    ) -> Option<NativeBinaryLayout> {
        let mut layout = self.native_binary_layout_at(binary.source_site?)?;
        if matches!(
            binary.op,
            crate::hir::common::HirBinaryOpKind::Gt | crate::hir::common::HirBinaryOpKind::Ge
        ) {
            std::mem::swap(&mut layout.lhs, &mut layout.rhs);
        }
        Some(layout)
    }

    pub(super) fn record_binary_local_inputs(
        &mut self,
        inputs: impl Iterator<Item = (InstrRef, [Option<LocalId>; 2])>,
    ) {
        self.binary_local_inputs.extend(inputs);
    }

    pub(super) fn binary_value_operand(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        operand: usize,
    ) -> Option<TempId> {
        let layout = self.native_binary_layout(binary)?;
        let home = [layout.lhs, layout.rhs].get(operand).copied().flatten()?;
        let result = *self
            .binary_value_operands
            .get(&(binary.source_site?.instr, Reg(home.slot())))?;
        (self.trusted_temp_home_slot(result) == Some(home)).then_some(result)
    }

    /// 当前操作数直接读取原指令位置的同一 local；只证明读取，不退休或合并 cell。
    pub(super) fn direct_binary_operand_home(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        operand: usize,
    ) -> Option<HomeSlotKey> {
        let layout = self.native_binary_layout(binary)?;
        let home = [layout.lhs, layout.rhs].get(operand).copied().flatten()?;
        let value = *[&binary.lhs, &binary.rhs].get(operand)?;
        let direct = match value {
            HirExpr::LocalRef(local) => self.trusted_local_home_slot(*local),
            HirExpr::ParamRef(param) => self.trusted_param_home_slot(*param),
            _ => None,
        }?;
        if direct == home {
            return Some(home);
        }
        let HirExpr::LocalRef(local) = value else {
            return None;
        };
        let original = if matches!(
            binary.op,
            crate::hir::common::HirBinaryOpKind::Gt | crate::hir::common::HirBinaryOpKind::Ge
        ) {
            1 - operand
        } else {
            operand
        };
        // 比较的 source-site 和输入方向仍匹配，且该 local 未被异槽重写失效。
        // epoch 差异只能由 lowering 在该读取点签发的 owner 解释，槽号相同不够。
        (direct.slot() == home.slot()
            && self.binary_local_inputs.get(&binary.source_site?.instr)?[original] == Some(*local))
        .then_some(home)
    }

    /// lowering 尚未选择源码关系方向时消费原规范化的两侧，不借合成表达式查询。
    pub(super) fn native_binary_layout_at(
        &self,
        source: crate::hir::common::HirSourceSite,
    ) -> Option<NativeBinaryLayout> {
        if self.source_proto != Some(source.proto) {
            return None;
        }
        let layout = *self.binary_layouts.get(&source.instr)?;
        layout
            .lhs
            .into_iter()
            .chain(layout.rhs)
            .all(|home| self.physical_home_universe.contains(&home))
            .then_some(layout)
    }

    /// 比较的单个寄存器操作数仍来自同一次准备；内嵌右操作数不占额外 scratch。
    /// Branch 没有结果 Def，不能使用要求运算结果槽的 operation_input_preparation。
    pub(super) fn comparison_read_preparation(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        value: &crate::hir::common::HirExpr,
    ) -> Option<(TempId, HomeSlotKey)> {
        let layout = self.native_binary_layout(binary)?;
        if layout.rhs.is_some() {
            return None;
        }
        self.comparison_operand_preparation(binary, 0, value)
    }

    /// 按当前关系方向核对原比较的一侧输入；Branch 无结果 Def，证书仍绑定唯一 use。
    pub(super) fn comparison_operand_preparation(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        operand: usize,
        value: &crate::hir::common::HirExpr,
    ) -> Option<(TempId, HomeSlotKey)> {
        let layout = self.native_binary_layout(binary)?;
        let home = [layout.lhs, layout.rhs].get(operand).copied().flatten()?;
        let original = if matches!(
            binary.op,
            crate::hir::common::HirBinaryOpKind::Gt | crate::hir::common::HirBinaryOpKind::Ge
        ) {
            1 - operand
        } else {
            operand
        };
        let preparation =
            self.operand_preparations.get(&binary.source_site?.instr)?[original].as_ref()?;
        (home == preparation.home
            && preparation.matches(value)
            && self.trusted_temp_home_slot(preparation.temp) == Some(preparation.home))
        .then_some((preparation.temp, preparation.home))
    }

    /// 精确准备指令用于连续展开帧；值与槽匹配仍沿用比较输入的同一证书。
    pub(super) fn comparison_preparation_instruction(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        operand: usize,
        value: &HirExpr,
    ) -> Option<InstrRef> {
        let (temp, _) = self.comparison_operand_preparation(binary, operand, value)?;
        self.operand_preparations
            .get(&binary.source_site?.instr)?
            .iter()
            .flatten()
            .find(|preparation| preparation.temp == temp)
            .map(|preparation| preparation.read)
    }

    /// 当前左 operand 仍是原单次上值/字面量准备，右侧仍为证书配对的普通 CALL。
    /// 这里只恢复入口；后层仍须验证整个声明前缀，不能用相同 upvalue/home 替代调用身份。
    pub(super) fn comparison_preparation_frame(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
    ) -> Option<HomeSlotKey> {
        use crate::hir::common::HirBinaryOpKind;
        if !matches!(
            binary.op,
            HirBinaryOpKind::Eq
                | HirBinaryOpKind::Lt
                | HirBinaryOpKind::Le
                | HirBinaryOpKind::Gt
                | HirBinaryOpKind::Ge
        ) {
            return None;
        }
        let source = binary.source_site?;
        if self.source_proto != Some(source.proto) {
            return None;
        }
        let preparation = self.comparison_preparations.get(&source.instr)?;
        let reversed = matches!(
            binary.op,
            crate::hir::common::HirBinaryOpKind::Gt | crate::hir::common::HirBinaryOpKind::Ge
        );
        if preparation.lhs == reversed
            || !preparation.operand.matches(&binary.lhs)
            || self.trusted_temp_home_slot(preparation.operand.temp)
                != Some(preparation.operand.home)
        {
            return None;
        }
        let HirExpr::Call(call) = &binary.rhs else {
            return None;
        };
        let call_source = call.source_site?;
        if call.is_method()
            || call_source.proto != source.proto
            || call_source.instr != preparation.call
            || self.operation_result_temp(call_source) != Some(preparation.call_result)
        {
            return None;
        }
        let frame = self.native_call_layout(call)?;
        let layout = self.native_binary_layout(binary)?;
        (layout.lhs == Some(preparation.operand.home)
            && layout.rhs == Some(frame.home)
            && frame.home.slot() == preparation.operand.home.slot() + 1)
            .then_some(preparation.operand.home)
    }

    /// 完整帧 builder 使用原 Def 身份消费尚未树化的两个 operand；消费后仍须调用
    /// comparison_preparation_frame 核对当前值、CALL 来源及最终槽距。
    pub(super) fn comparison_preparation_inputs(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
    ) -> Option<(TempId, TempId, HomeSlotKey)> {
        let source = binary.source_site?;
        if self.source_proto != Some(source.proto) {
            return None;
        }
        let preparation = self.comparison_preparations.get(&source.instr)?;
        let reversed = matches!(
            binary.op,
            crate::hir::common::HirBinaryOpKind::Gt | crate::hir::common::HirBinaryOpKind::Ge
        );
        (preparation.lhs != reversed).then_some((
            preparation.operand.temp,
            preparation.call_result,
            preparation.operand.home,
        ))
    }

    /// 一元或二元操作的首个输入准备；该输入仍是原快照，结果原位写回时才能将
    /// 准备入口向上组合。不是仅凭结果 home 猜测上值读取位置。
    pub(super) fn operation_operand_preparation(
        &self,
        source: crate::hir::common::HirSourceSite,
        value: &crate::hir::common::HirExpr,
    ) -> Option<HomeSlotKey> {
        let result = self.operation_result_home(source)?;
        let (_, home) = self.operation_input_preparation(source, value)?;
        (result == home).then_some(home)
    }

    /// 原单次输入身份与 home；输入可在待写结果上方准备，不能把二者强制合为一个槽。
    pub(super) fn operation_input_preparation(
        &self,
        source: crate::hir::common::HirSourceSite,
        value: &crate::hir::common::HirExpr,
    ) -> Option<(TempId, HomeSlotKey)> {
        self.operation_result_home(source)?;
        if let HirExpr::Binary(binary) = value
            && let Some(input) = self.unary_operands.get(&source.instr)
            && let Some(result) = self.comparison_result_temp(binary)
        {
            // 比较的 Boolean 来自双分支 Phi，不是单条 producer Def。
            // 原一元 use 必须读取这个确切结果版本，不能仅凭同槽猜测准备身份。
            return (input.value == Some(result)
                && self.trusted_temp_home_slot(result) == Some(input.home))
            .then_some((result, input.home));
        }
        let mut matching = self
            .operand_preparations
            .get(&source.instr)?
            .iter()
            .flatten()
            .filter(|preparation| preparation.matches(value));
        let preparation = matching.next()?;
        if matching.next().is_some() {
            return None;
        }
        (self.trusted_temp_home_slot(preparation.temp) == Some(preparation.home))
            .then_some((preparation.temp, preparation.home))
    }

    /// 原直接上值字段读取不准备一个额外 base 寄存器；保留其单次 GETTABLE 来源、
    /// 上值及常量键或原 Entry 参数键后，才可把结果槽作为整个字段链的首入口。
    pub(super) fn upvalue_table_read_frame(
        &self,
        access: &crate::hir::common::HirTableAccess,
    ) -> Option<HomeSlotKey> {
        use crate::hir::common::{HirExpr, HirOperationSources};
        let HirOperationSources::Single(source) = access.sources else {
            return None;
        };
        if !self.operation_result_reference_unaliased(source) {
            return None;
        }
        let (upvalue, key) = self.upvalue_table_reads.get(&source.instr)?;
        let same_key = match (key, &access.key) {
            (HirExpr::Number(original), HirExpr::Number(current)) => {
                original.to_bits() == current.to_bits()
            }
            _ => key == &access.key,
        };
        (matches!(&access.base, HirExpr::UpvalueRef(current) if current == upvalue) && same_key)
            .then(|| self.operation_result_home(source))
            .flatten()
    }

    /// GETTABUP 的动态 key 独占准备区，base 上值由原操作直接读取。
    pub(super) fn upvalue_table_read_key(
        &self,
        access: &crate::hir::common::HirTableAccess,
    ) -> Option<(TempId, HomeSlotKey)> {
        let crate::hir::common::HirOperationSources::Single(source) = access.sources else {
            return None;
        };
        self.table_read_facts_at(source)?;
        let (upvalue, HirExpr::TempRef(temp)) = self.upvalue_table_reads.get(&source.instr)? else {
            return None;
        };
        let same_key = access.key == HirExpr::TempRef(*temp)
            || matches!(access.key, HirExpr::LocalRef(local)
                if self.promoted_local_for_temp(*temp) == Some(local));
        (access.base == HirExpr::UpvalueRef(*upvalue) && same_key)
            .then(|| self.trusted_temp_home_slot(*temp).map(|home| (*temp, home)))?
    }

    /// PUC 的动态上值索引从 free-base+1 准备 key，再准备 free-base 上的 base。
    /// 返回整个表达式所需的空闲前缀，不把结果槽误称为首次物理写的位置。
    pub(super) fn table_preparation_frame(
        &self,
        access: &crate::hir::common::HirTableAccess,
        dialect: crate::decompile::DecompileDialect,
    ) -> Option<HomeSlotKey> {
        use crate::hir::common::{HirExpr, HirOperationSources};
        if !matches!(
            dialect,
            crate::decompile::DecompileDialect::Lua54 | crate::decompile::DecompileDialect::Lua55
        ) || !matches!(
            (&access.base, &access.key),
            (HirExpr::UpvalueRef(_), HirExpr::UpvalueRef(_))
        ) {
            return None;
        }
        let HirOperationSources::Single(source) = access.sources else {
            return None;
        };
        let result = self.operation_result_home(source)?;
        let preparation = self.table_preparations.get(&source.instr)?;
        let base = preparation.base.as_ref()?;
        (base.matches(&access.base)
            && preparation.key.matches(&access.key)
            && preparation.key.read.index() < base.read.index()
            && base.home == result
            && preparation.key.home.slot() == result.slot() + 1
            && self.trusted_temp_home_slot(base.temp) == Some(base.home)
            && self.trusted_temp_home_slot(preparation.key.temp) == Some(preparation.key.home))
        .then_some(result)
    }

    /// 动态键树化后仍须匹配原 GETTABLE 的唯一准备 Def，不能给同名 upvalue 猜 home。
    pub(super) fn table_key_preparation(
        &self,
        access: &crate::hir::common::HirTableAccess,
    ) -> Option<HomeSlotKey> {
        self.table_key_value_preparation(access)
            .map(|(_, home)| home)
    }

    pub(super) fn table_key_value_preparation(
        &self,
        access: &crate::hir::common::HirTableAccess,
    ) -> Option<(TempId, HomeSlotKey)> {
        let crate::hir::common::HirOperationSources::Single(source) = access.sources else {
            return None;
        };
        let layout = self.native_table_read_layout(access)?;
        let key = &self.table_preparations.get(&source.instr)?.key;
        ((key.matches(&access.key)
            || matches!(access.key, HirExpr::LocalRef(local)
                if self.promoted_local_for_temp(key.temp) == Some(local)))
            && layout.key == Some(key.home)
            && self.trusted_temp_home_slot(key.temp) == Some(key.home))
        .then_some((key.temp, key.home))
    }

    /// 原 CONCAT 的连续 operand 区必须没有打开的引用捕获；输入身份保留读取时的 epoch。
    /// 单值结果身份与该区分别核对，不从右结合 AST 猜寄存器或把复用槽视作入口版本。
    pub(super) fn native_concat_buffer(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
    ) -> Option<crate::transformer::RegRange> {
        let source = binary.source_site?;
        if !self.operation_result_reference_unaliased(source) {
            return None;
        }
        self.concat_frames
            .get(&source.instr)
            .map(|frame| frame.buffer)
    }

    /// 展开体直接写 caller 的 cell，结果槽可以被捕获；原输入缓冲仍由单次准备证明。
    /// 此 query 不授权单独树化 CONCAT，消费者必须重放覆盖 buffer 的完整展开帧。
    pub(super) fn captured_concat_buffer(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        target: LocalId,
    ) -> Option<crate::transformer::RegRange> {
        let source = binary.source_site?;
        let frame = self.concat_frames.get(&source.instr)?;
        let (input, suffix) = frame.captured_update.as_ref()?;
        (self.operation_result_home(source) == Some(*input)
            && self.trusted_local_home_slot(target) == Some(*input)
            && binary.lhs == HirExpr::LocalRef(target)
            && binary.rhs == HirExpr::String(suffix.clone()))
        .then_some(frame.buffer)
    }

    /// 原 CONCAT 各输入独立于输出的同槽 Local 复用，沿用 CALL 参数的精确值版本规则。
    pub(super) fn concat_operand_value(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        operand: usize,
    ) -> Option<TempId> {
        self.native_concat_buffer(binary)?;
        let source = binary.source_site?;
        let frame = self.concat_frames.get(&source.instr)?;
        let temp = *frame.operands.get(operand)?.as_ref()?;
        (self.trusted_temp_home_slot(temp) == Some(*frame.operand_homes.get(operand)?))
            .then_some(temp)
    }

    /// 互斥访问必须在全部原 GETTABLE 上具有同一结果槽，未知来源不签许可。
    pub(super) fn table_read_result_home(
        &self,
        access: &crate::hir::common::HirTableAccess,
    ) -> Option<HomeSlotKey> {
        let mut result = None;
        access.sources.try_for_each_known(|source| {
            let home = if self.table_read_layouts.contains_key(&source.instr) {
                self.table_read_facts_at(source)?.result_home
            } else {
                // GETTABUP/隐式环境读取没有寄存器 base，沿用自身的单次操作事实。
                self.operation_result_home(source)?
            };
            if result.is_some_and(|previous| previous != home) {
                return None;
            }
            result = Some(home);
            Some(())
        })?;
        result
    }

    /// canonical GETTABLE 输入布局对全部来源求交，不能从最终结果槽反推原 LOADK。
    pub(super) fn native_table_read_layout(
        &self,
        access: &crate::hir::common::HirTableAccess,
    ) -> Option<NativeTableReadLayout> {
        let mut result = None;
        access.sources.try_for_each_known(|source| {
            let layout = self.native_table_read_layout_at(source)?;
            if result.is_some_and(|previous| previous != layout) {
                return None;
            }
            result = Some(layout);
            Some(())
        })?;
        result
    }

    pub(super) fn native_table_read_layout_at(
        &self,
        source: crate::hir::common::HirSourceSite,
    ) -> Option<NativeTableReadLayout> {
        let layout = self.table_read_facts_at(source)?.layout?;
        std::iter::once(layout.base)
            .chain(layout.key)
            .all(|home| self.physical_home_universe.contains(&home))
            .then_some(layout)
    }

    fn table_read_facts_at(
        &self,
        source: crate::hir::common::HirSourceSite,
    ) -> Option<&NativeTableReadFacts> {
        if self.source_proto != Some(source.proto) {
            return None;
        }
        let read = self.table_read_layouts.get(&source.instr)?;
        (self.trusted_temp_home_slot(read.result) == Some(read.result_home)).then_some(read)
    }

    /// 当前查表表达式对应的原结果绑定；不把后继 COPY 的同值目标当作原写入。
    pub(super) fn table_read_result_local(
        &self,
        access: &crate::hir::common::HirTableAccess,
    ) -> Option<LocalId> {
        let crate::hir::common::HirOperationSources::Single(source) = access.sources else {
            return None;
        };
        self.promoted_local_for_temp(self.table_read_facts_at(source)?.result)
    }

    /// 原 GETTABLE 的 base SSA 身份；完整帧消费时仍须核对其定义与准备事件。
    pub(super) fn table_read_base_value(
        &self,
        access: &crate::hir::common::HirTableAccess,
    ) -> Option<TempId> {
        let crate::hir::common::HirOperationSources::Single(source) = access.sources else {
            return None;
        };
        let temp = *self.table_read_bases.get(&source.instr)?;
        (self.trusted_temp_home_slot(temp) == Some(self.native_table_read_layout(access)?.base))
            .then_some(temp)
    }

    /// GETTABLE 当前读取的 base 版本；异槽 Local 复用不抹去原 use→Def 的 home。
    /// 这里只证明读取位置，不授权删除该 binding 或提前读取其值。
    pub(super) fn table_read_base_home(
        &self,
        access: &crate::hir::common::HirTableAccess,
    ) -> Option<HomeSlotKey> {
        let layout = self.native_table_read_layout(access)?;
        let binding = HirBinding::from_expr(&access.base)?;
        let direct = match binding {
            HirBinding::Local(local) => self.trusted_local_home_slot(local),
            HirBinding::Param(param) => self.trusted_param_home_slot(param),
            _ => None,
        };
        if direct == Some(layout.base) {
            return direct;
        }
        access.sources.try_for_each_known(|source| {
            let temp = *self.table_read_bases.get(&source.instr)?;
            let matches = match binding {
                HirBinding::Local(local) => self.promoted_local_for_temp(temp) == Some(local),
                HirBinding::Temp(value) => value == temp,
                _ => false,
            };
            (matches && self.trusted_temp_home_slot(temp) == Some(layout.base)).then_some(())
        })?;
        Some(layout.base)
    }

    /// SETTABLE 原输入布局独立于读取结果，全部来源必须属于当前 proto 且布局相同。
    pub(super) fn native_table_write_layout(
        &self,
        access: &crate::hir::common::HirTableAccess,
    ) -> Option<NativeRegisterTableWriteLayout> {
        self.native_record_write_layout(&access.sources)
    }

    pub(super) fn record_table_write_local_inputs(
        &mut self,
        inputs: impl Iterator<Item = (InstrRef, [Option<LocalId>; 2])>,
    ) {
        self.table_write_local_inputs.extend(inputs);
    }

    /// operand 0/1 分别为表和 key；跨 epoch 的 local 必须仍是原读取位置的 owner。
    pub(super) fn direct_table_write_input_home(
        &self,
        access: &crate::hir::common::HirTableAccess,
        operand: usize,
    ) -> Option<HomeSlotKey> {
        let layout = self.native_write_layout(&access.sources)?;
        let homes = match layout {
            NativeTableWriteLayout::Register(layout) => [Some(layout.base), layout.key],
            NativeTableWriteLayout::Upvalue(layout) => [None, layout.key],
            NativeTableWriteLayout::Environment { key, .. } => [None, key],
        };
        let home = homes.get(operand).copied().flatten()?;
        let value = *[&access.base, &access.key].get(operand)?;
        let direct = match value {
            HirExpr::LocalRef(local) => self.trusted_local_home_slot(*local),
            HirExpr::ParamRef(param) => self.trusted_param_home_slot(*param),
            _ => return None,
        };
        if direct == Some(home) {
            return Some(home);
        }
        let HirExpr::LocalRef(local) = value else {
            return None;
        };
        if self.local_home_was_invalidated(*local)
            || !self.possible_local_home_slots(*local).is_some_and(|homes| {
                !homes.is_empty() && homes.iter().all(|possible| possible.slot() == home.slot())
            })
        {
            return None;
        }
        // 同槽的循环 header/latch home 不包含每次 capture 激活；所有原写来源都须
        // 明确读取当前 local，不能从共同槽号认回另一个 epoch 的独立快照。
        access.sources.try_for_each_known(|source| {
            (self.table_write_local_inputs.get(&source.instr)?[operand] == Some(*local))
                .then_some(())
        })?;
        Some(home)
    }

    /// Luau 的低槽固定字段写仍需在原 RHS scratch 加载字面量；供赋值事务及
    /// 作用域预览重建同一入口，不把 SETTABLE 的 value 槽当成可省略的 RK。
    pub(super) fn luau_literal_table_write_frame(
        &self,
        access: &crate::hir::common::HirTableAccess,
        value: &HirExpr,
    ) -> Option<HomeSlotKey> {
        if !matches!(
            value,
            HirExpr::Nil
                | HirExpr::Boolean(_)
                | HirExpr::Integer(_)
                | HirExpr::Number(_)
                | HirExpr::String(_)
        ) || !matches!(&access.key, HirExpr::String(key)
                if key.as_utf8().is_some_and(|key|
                    crate::decompile::DecompileDialect::Luau.is_identifier_name(key)))
        {
            return None;
        }
        let layout = self.native_table_write_layout(access)?;
        let home = layout.value?;
        let base = match access.base {
            HirExpr::LocalRef(local) => self.trusted_local_home_slot(local)?,
            HirExpr::ParamRef(param) => self.trusted_param_home_slot(param)?,
            _ => return None,
        };
        (layout.key.is_none() && base == layout.base && base.slot() < home.slot()).then_some(home)
    }

    /// Luau 分配赋值的入口：低槽表/key 不新增准备，上值目标保留原 GETUPVAL 快照槽。
    pub(super) fn luau_allocation_table_write_frame(
        &self,
        access: &crate::hir::common::HirTableAccess,
        value: &HirExpr,
    ) -> Option<HomeSlotKey> {
        let layout = self.native_table_write_layout(access)?;
        let home = match value {
            HirExpr::Closure(closure) => self.operation_result_home(closure.source_site?)?,
            HirExpr::TableConstructor(table) => self.allocation_result_home(table)?,
            _ => return None,
        };
        let (base, entry) = match access.base {
            HirExpr::LocalRef(_) => (self.direct_table_write_input_home(access, 0)?, home),
            HirExpr::ParamRef(param) => (self.trusted_param_home_slot(param)?, home),
            HirExpr::UpvalueRef(_) => {
                let (_, base) = self.table_write_base_preparation(access, &access.base)?;
                // 普通字段赋值先读取目标，再在相邻槽分配 RHS；不能交换这两个事件。
                if home != HomeSlotKey::new(base.slot() + 1, 0) {
                    return None;
                }
                (base, base)
            }
            _ => return None,
        };
        (layout.base == base
            && base.slot() < home.slot()
            && match layout.key {
                Some(key) => {
                    self.direct_table_write_input_home(access, 1) == Some(key)
                        && key.slot() < entry.slot()
                }
                None => matches!(access.key, HirExpr::String(_) | HirExpr::Integer(_)),
            }
            && layout.value == Some(home))
        .then_some(entry)
    }

    /// 字段并入构造器后继续消费原显式写来源，不从完成后的字段形状猜 SETTABLE 布局。
    pub(super) fn native_record_write_layout(
        &self,
        sources: &crate::hir::common::HirOperationSources,
    ) -> Option<NativeRegisterTableWriteLayout> {
        let NativeTableWriteLayout::Register(layout) = self.native_write_layout(sources)? else {
            return None;
        };
        Some(layout)
    }

    /// SETTABUP 在 RHS 完成后读取原上值 cell；它没有需要提前物化的 base 寄存器。
    pub(super) fn native_upvalue_table_write_layout(
        &self,
        access: &crate::hir::common::HirTableAccess,
    ) -> Option<NativeUpvalueTableWriteLayout> {
        let NativeTableWriteLayout::Upvalue(layout) = self.native_write_layout(&access.sources)?
        else {
            return None;
        };
        Some(layout)
    }

    /// 归一化的全局目标仍须来自无 base 准备槽的原环境写；动态 key 不借用裸名字许可。
    pub(super) fn global_write_value_home(
        &self,
        global: &crate::hir::common::HirGlobalRef,
        dialect: crate::decompile::DecompileDialect,
    ) -> Option<HomeSlotKey> {
        if !global
            .key
            .as_utf8()
            .is_some_and(|name| dialect.is_identifier_name(name))
        {
            return None;
        }
        let NativeTableWriteLayout::Environment { key: None, value } =
            self.native_write_layout(&global.sources)?
        else {
            return None;
        };
        value
    }

    /// 环境写的 RHS 仍绑定原单次 use→Def，不从常量值或相邻槽号推测准备身份。
    pub(super) fn global_write_value_preparation(
        &self,
        global: &crate::hir::common::HirGlobalRef,
        value: &HirExpr,
    ) -> Option<(TempId, HomeSlotKey)> {
        self.write_value_preparation(&global.sources, value)
    }

    /// 仅提供批量 LOADNIL 的精确输入成员；调用方必须完整消费原写组。
    pub(super) fn global_nil_batch_preparation(
        &self,
        global: &crate::hir::common::HirGlobalRef,
    ) -> Option<(TempId, HomeSlotKey)> {
        let crate::hir::common::HirOperationSources::Single(source) = global.sources else {
            return None;
        };
        if self.source_proto != Some(source.proto) {
            return None;
        }
        let preparation = self.operand_preparations.get(&source.instr)?[1].as_ref()?;
        (preparation.is_nil_batch_member()
            && self.trusted_temp_home_slot(preparation.temp) == Some(preparation.home))
        .then_some((preparation.temp, preparation.home))
    }

    /// 并列字段写只能由完整 LOADNIL 帧消费这些成员。
    pub(super) fn table_nil_batch_preparation(
        &self,
        access: &crate::hir::common::HirTableAccess,
    ) -> Option<(TempId, HomeSlotKey)> {
        let crate::hir::common::HirOperationSources::Single(source) = access.sources else {
            return None;
        };
        if self.source_proto != Some(source.proto) {
            return None;
        }
        let preparation = self.operand_preparations.get(&source.instr)?[1].as_ref()?;
        (preparation.is_nil_batch_member()
            && self.trusted_temp_home_slot(preparation.temp) == Some(preparation.home))
        .then_some((preparation.temp, preparation.home))
    }

    /// 环境键和值均来自常量域时没有准备槽；与缺失布局的未知写区分。
    pub(super) fn global_write_has_no_preparation(
        &self,
        global: &crate::hir::common::HirGlobalRef,
        dialect: crate::decompile::DecompileDialect,
    ) -> bool {
        global
            .key
            .as_utf8()
            .is_some_and(|name| dialect.is_identifier_name(name))
            && matches!(
                self.native_write_layout(&global.sources),
                Some(NativeTableWriteLayout::Environment {
                    key: None,
                    value: None
                })
            )
    }

    fn native_write_layout(
        &self,
        sources: &crate::hir::common::HirOperationSources,
    ) -> Option<NativeTableWriteLayout> {
        let mut result = None;
        sources.try_for_each_known(|source| {
            if self.source_proto != Some(source.proto) {
                return None;
            }
            let layout = *self.table_write_layouts.get(&source.instr)?;
            let homes = match layout {
                NativeTableWriteLayout::Register(layout) => {
                    [Some(layout.base), layout.key, layout.value]
                }
                NativeTableWriteLayout::Upvalue(layout) => [None, layout.key, layout.value],
                NativeTableWriteLayout::Environment { key, value } => [None, key, value],
            };
            if !homes
                .into_iter()
                .flatten()
                .all(|home| self.physical_home_universe.contains(&home))
                || result.is_some_and(|previous| previous != layout)
            {
                return None;
            }
            result = Some(layout);
            Some(())
        })?;
        result
    }

    /// SETTABLE 的原 base 单次读取，独立于 key 求值前对同名上值的读取。
    pub(super) fn table_write_base_preparation(
        &self,
        access: &crate::hir::common::HirTableAccess,
        value: &crate::hir::common::HirExpr,
    ) -> Option<(TempId, HomeSlotKey)> {
        let crate::hir::common::HirOperationSources::Single(source) = access.sources else {
            return None;
        };
        if self.source_proto != Some(source.proto) {
            return None;
        }
        let preparation = self.operand_preparations.get(&source.instr)?[0].as_ref()?;
        (preparation.matches(value)
            && self.trusted_temp_home_slot(preparation.temp) == Some(preparation.home))
        .then_some((preparation.temp, preparation.home))
    }

    /// SETTABLE 的原 RHS 准备，值身份与目标表快照分开核对。
    pub(super) fn table_write_value_preparation(
        &self,
        access: &crate::hir::common::HirTableAccess,
        value: &HirExpr,
    ) -> Option<(TempId, HomeSlotKey)> {
        self.write_value_preparation(&access.sources, value)
    }

    fn write_value_preparation(
        &self,
        sources: &crate::hir::common::HirOperationSources,
        value: &HirExpr,
    ) -> Option<(TempId, HomeSlotKey)> {
        let crate::hir::common::HirOperationSources::Single(source) = *sources else {
            return None;
        };
        if self.source_proto != Some(source.proto) {
            return None;
        }
        let preparation = self.operand_preparations.get(&source.instr)?[1].as_ref()?;
        (preparation.matches(value)
            && self.trusted_temp_home_slot(preparation.temp) == Some(preparation.home))
        .then_some((preparation.temp, preparation.home))
    }

    /// 已并入 record 的上值读取仍绑定原 SETTABLE value Def，不借字段名推测 scratch。
    pub(super) fn record_value_preparation(
        &self,
        record: &crate::hir::common::HirRecordField,
    ) -> Option<HomeSlotKey> {
        let crate::hir::common::HirOperationSources::Single(source) = record.write_sources else {
            return None;
        };
        if self.source_proto != Some(source.proto) {
            return None;
        }
        let preparation = self.operand_preparations.get(&source.instr)?[1].as_ref()?;
        (preparation.matches(&record.value)
            && self.trusted_temp_home_slot(preparation.temp) == Some(preparation.home))
        .then_some(preparation.home)
    }

    /// Artifact owner 重排 proto arena 时同步原指令索引的作用域；synthetic proto 不因此获得证书。
    pub(super) fn relocate_proto_owner(&mut self, proto: crate::hir::common::HirProtoRef) {
        if self.source_proto.is_some() {
            self.source_proto = Some(proto);
        }
    }

    /// 从 canonical def 与最终 value plan 提取当前 proto 的 temp -> home slot 对照表。
    #[expect(
        clippy::too_many_arguments,
        reason = "借用同一 proto 的冻结事实与已绑定 temp 映射"
    )]
    pub(super) fn from_plan(
        proto: &LoweredProto,
        source: crate::decompile::DecompileDialect,
        source_proto: crate::hir::common::HirProtoRef,
        cfg: &Cfg,
        graph: &GraphFacts,
        dataflow: &DataflowFacts,
        plan: &StructurePlan,
        debug_bindings: &crate::structure::DebugBindingFacts,
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
        let parallel_frames = copy_assignments::collect_parallel(
            proto,
            source,
            cfg,
            dataflow,
            slot_epochs,
            fixed_temps,
            phi_temps,
        );
        let parallel_target_seeds = parallel_frames
            .values()
            .flat_map(|frame| frame.previous.iter().copied())
            .collect();
        let prewrites =
            call_roots::boolean_prewrites(proto, dataflow, graph, plan, fixed_temps, phi_temps);
        let boolean_value_prewrites = prewrites
            .values()
            .map(|&(initial, result, initial_value)| (result, (initial, initial_value)))
            .collect();
        let calls = call_roots::collect(
            proto,
            cfg,
            dataflow,
            slot_epochs,
            fixed_temps,
            phi_temps,
            &prewrites,
        );
        let mut call_frame_temps = calls
            .values()
            .filter_map(|call| call.assignment_copies)
            .flatten()
            .collect::<BTreeSet<_>>();
        let immediate_move_writes = collect_immediate_move_writes(
            proto,
            dataflow,
            slot_epochs,
            fixed_temps,
            total_temps,
            &call_frame_temps,
        );
        // 参数 COPY 读取的低槽别名仍占 caller 前缀。提前折叠中间 COPY 会让
        // 后续完整帧只剩末端 home，却缺少其前面的声明；值快照相等不能代替槽序证明。
        let mut copy_inputs = calls
            .values()
            .flat_map(|call| {
                call.argument_values
                    .iter()
                    .flatten()
                    .chain(call.callee.iter())
                    .map(|&temp| (call.layout.home.slot(), temp))
            })
            .collect::<Vec<_>>();
        copy_inputs.sort_unstable_by(|left, right| right.cmp(left));
        let mut visited_copies = vec![false; dataflow.defs.len()];
        for (base, mut temp) in copy_inputs {
            let mut has_prefix_copy = false;
            // 按前缀上界递减处理；共享 MOVE 链首次遍历即拥有最宽需求，每个 Def 只访一次。
            while temp.index() < dataflow.defs.len() && !visited_copies[temp.index()] {
                let def = crate::structure::DefId(temp.index());
                let site = dataflow.def_instr(def);
                // 链首的 CALL/计算也占原低槽；不能只保留 COPY 后再把源值挪进首个别名。
                let LowInstr::Move(copy) = &proto.instrs[site.index()] else {
                    if has_prefix_copy && fixed_temps[def.index()] == temp {
                        call_frame_temps.insert(temp);
                    }
                    break;
                };
                visited_copies[temp.index()] = true;
                // 声明前缀由低槽向高槽展开；反向 MOVE 是结果写回或槽复用，
                // 由已有 assignment/root owner 核对，不能在此冻结成新的前缀声明。
                if copy.src.index() >= copy.dst.index() {
                    break;
                }
                if dataflow.def_reg(def).index() < base && fixed_temps[def.index()] == temp {
                    call_frame_temps.insert(temp);
                    has_prefix_copy = true;
                }
                let SsaValue::Def(source) = dataflow.use_value(site, copy.src) else {
                    break;
                };
                temp = TempId(source.index());
            }
        }
        let scalar_values = if source == crate::decompile::DecompileDialect::Luau {
            scalar_copy_values(proto, cfg, dataflow)
        } else {
            Vec::new()
        };
        let scalar_copy_temps = scalar_values
            .iter()
            .copied()
            .take(dataflow.defs.len())
            .enumerate()
            .filter_map(|(index, inert)| {
                (inert && fixed_temps[index] == TempId(index)).then_some(TempId(index))
            })
            .collect();
        let copy_roots =
            collect_copy_root_facts(proto, cfg, graph, dataflow, fixed_temps, &scalar_copy_temps);
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

        call_frame_temps.extend(parallel_frames.values().flat_map(|frame| {
            frame
                .moves()
                .flat_map(|write| [write.target, write.source])
                .chain(frame.previous.iter().copied())
        }));
        let mut operation_results = BTreeMap::new();
        let mut table_write_layouts = BTreeMap::new();
        let mut table_batch_layouts = BTreeMap::new();
        let mut table_batch_values = BTreeMap::new();
        let mut allocation_batches = BTreeMap::new();
        let mut table_read_layouts = BTreeMap::new();
        let mut table_read_bases = BTreeMap::new();
        let mut binary_layouts = BTreeMap::new();
        let mut comparison_preparations = BTreeMap::new();
        let mut operand_preparations = BTreeMap::new();
        let mut upvalue_writes = BTreeMap::new();
        let mut upvalue_table_reads = BTreeMap::new();
        let mut table_preparations = BTreeMap::new();
        let mut unary_operands = BTreeMap::new();
        let mut concat_frames = BTreeMap::new();
        let mut return_frames = BTreeMap::<InstrRef, NativeReturnFrame>::new();
        let mut return_fixed_inputs = BTreeMap::<InstrRef, Vec<Option<TempId>>>::new();
        let mut return_copy_roots = BTreeSet::new();
        let mut return_frame_sources = BTreeMap::new();
        let mut return_layouts = BTreeMap::new();
        for (index, instr) in proto.instrs.iter().enumerate() {
            let site = InstrRef(index);
            if let LowInstr::GetTable(get) = instr
                && matches!(
                    get.kind,
                    crate::transformer::GetTableKind::Normal
                        | crate::transformer::GetTableKind::Import
                )
                && let [def] = dataflow.instr_defs[index].as_slice()
            {
                table_read_layouts.insert(
                    site,
                    NativeTableReadFacts {
                        layout: NativeTableReadLayout::for_access(
                            get.base,
                            get.key,
                            site,
                            slot_epochs,
                        ),
                        result: fixed_temps[def.index()],
                        result_home: HomeSlotKey::new(
                            get.dst.index(),
                            slot_epochs.epoch_at(get.dst, site),
                        ),
                    },
                );
                if let crate::transformer::AccessBase::Reg(reg) = get.base
                    && let Some(temp) = canonical_value_temp(
                        dataflow.use_value(site, reg),
                        dataflow.defs.len(),
                        fixed_temps,
                        phi_temps,
                    )
                {
                    table_read_bases.insert(site, temp);
                }
            }
            if let LowInstr::GetTable(get) = instr
                && get.kind == crate::transformer::GetTableKind::Normal
                && let crate::transformer::AccessBase::Reg(_) = get.base
                && let crate::transformer::AccessKey::Reg(key) = get.key
                && let Some(key) = operand_preparations::collect(
                    proto,
                    cfg,
                    dataflow,
                    slot_epochs,
                    fixed_temps,
                    site,
                    key,
                )
            {
                table_preparations.insert(
                    site,
                    operand_preparations::TablePreparation {
                        base: match get.base {
                            crate::transformer::AccessBase::Reg(reg) => {
                                operand_preparations::collect(
                                    proto,
                                    cfg,
                                    dataflow,
                                    slot_epochs,
                                    fixed_temps,
                                    site,
                                    reg,
                                )
                            }
                            _ => None,
                        },
                        key,
                    },
                );
            }
            if let LowInstr::GetTable(get) = instr
                && get.kind == crate::transformer::GetTableKind::Normal
                && let crate::transformer::AccessBase::Upvalue(upvalue)
                | crate::transformer::AccessBase::EnvironmentUpvalue(upvalue) = get.base
            {
                let key = match get.key {
                    // 直接读取参数槽不需要 key 准备；保留同一 Entry 身份，
                    // 不能把已重写的寄存器值当成初始参数。
                    crate::transformer::AccessKey::Reg(reg)
                        if reg.index() < usize::from(proto.signature.num_params)
                            && dataflow.use_value(site, reg) == SsaValue::Entry(reg) =>
                    {
                        Some(HirExpr::ParamRef(ParamId(reg.index())))
                    }
                    crate::transformer::AccessKey::Reg(reg) => canonical_value_temp(
                        dataflow.use_value(site, reg),
                        dataflow.defs.len(),
                        fixed_temps,
                        phi_temps,
                    )
                    .map(HirExpr::TempRef),
                    crate::transformer::AccessKey::Const(key) => {
                        match &proto.constants[key.index()] {
                            crate::parser::RawLiteralConst::String(value) => {
                                Some(HirExpr::String(crate::LuaString::from_raw(value)))
                            }
                            crate::parser::RawLiteralConst::Integer(value) => {
                                Some(HirExpr::Integer(*value))
                            }
                            crate::parser::RawLiteralConst::Number(value) => {
                                Some(HirExpr::Number(*value))
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                };
                if let Some(key) = key {
                    upvalue_table_reads.insert(site, (UpvalueId(upvalue.index()), key));
                }
            }
            match instr {
                LowInstr::SetUpvalue(write) => {
                    if let crate::transformer::ValueOperand::Reg(reg) = write.src {
                        let value = dataflow.use_value(site, reg);
                        let input = canonical_value_temp(
                            value,
                            dataflow.defs.len(),
                            fixed_temps,
                            phi_temps,
                        )
                        .map(UpvalueWriteInput::Temp)
                        .or_else(|| {
                            let params = usize::from(proto.signature.num_params);
                            (proto.clears_entry_scratch
                                && value == SsaValue::Entry(reg)
                                && reg.index() >= params
                                && !(proto.signature.has_vararg_param_reg && reg.index() == params))
                                .then_some(UpvalueWriteInput::EntryNil(HomeSlotKey::new(
                                    reg.index(),
                                    slot_epochs.epoch_at(reg, site),
                                )))
                        });
                        let (crate::transformer::UpvalueOperand::Env(target)
                        | crate::transformer::UpvalueOperand::Upvalue(target)) = write.dst;
                        if let Some(input) = input {
                            upvalue_writes.insert(site, (UpvalueId(target.index()), input));
                        }
                    }
                }
                LowInstr::Branch(branch) => {
                    if let crate::transformer::BranchSubject::Compare { lhs, rhs, .. } =
                        branch.cond.subject
                    {
                        let home = |operand| match operand {
                            crate::transformer::CondOperand::Reg(reg) => native_operand_home(
                                crate::transformer::ValueOperand::Reg(reg),
                                site,
                                slot_epochs,
                            ),
                            _ => None,
                        };
                        binary_layouts.insert(
                            site,
                            NativeBinaryLayout {
                                lhs: home(lhs),
                                rhs: home(rhs),
                            },
                        );
                        let preparations = [lhs, rhs].map(|operand| {
                            let crate::transformer::CondOperand::Reg(reg) = operand else {
                                return None;
                            };
                            operand_preparations::collect(
                                proto,
                                cfg,
                                dataflow,
                                slot_epochs,
                                fixed_temps,
                                site,
                                reg,
                            )
                        });
                        if preparations.iter().any(Option::is_some) {
                            operand_preparations.insert(site, preparations);
                        }
                        if let Some(preparation) = comparison_preparations::collect(
                            proto,
                            cfg,
                            dataflow,
                            slot_epochs,
                            fixed_temps,
                            site,
                            [lhs, rhs],
                        ) {
                            comparison_preparations.insert(site, preparation);
                        }
                    }
                }
                LowInstr::SetList(batch) => {
                    if let Some(SsaValue::Def(def)) =
                        dataflow.canonical_move_value(dataflow.use_value(site, batch.base))
                        && matches!(
                            proto.instrs[dataflow.def_instr(def).index()],
                            LowInstr::NewTable(_)
                        )
                    {
                        allocation_batches
                            .entry(dataflow.def_instr(def))
                            .or_insert_with(Vec::new)
                            .push(site);
                    }
                    let (buffer, fixed_width) = match batch.values {
                        crate::transformer::ValuePack::Fixed(pack) => (pack.start, Some(pack.len)),
                        crate::transformer::ValuePack::Open(start) => (start, None),
                    };
                    if let crate::transformer::ValuePack::Fixed(pack) = batch.values {
                        table_batch_values.insert(
                            site,
                            (0..pack.len)
                                .map(|offset| {
                                    canonical_value_temp(
                                        dataflow.use_value(site, Reg(pack.start.index() + offset)),
                                        dataflow.defs.len(),
                                        fixed_temps,
                                        phi_temps,
                                    )
                                })
                                .collect(),
                        );
                    }
                    table_batch_layouts.insert(
                        site,
                        NativeTableBatchLayout {
                            base: HomeSlotKey::new(
                                batch.base.index(),
                                slot_epochs.epoch_at(batch.base, site),
                            ),
                            buffer: HomeSlotKey::new(
                                buffer.index(),
                                slot_epochs.epoch_at(buffer, site),
                            ),
                            fixed_width,
                            vararg_tail_home: if fixed_width.is_none() {
                                let sources = &dataflow.open_use_sources[site.index()];
                                if !sources.has_entry() && sources.defs().len() == 1 {
                                    let def = &dataflow.open_defs
                                        [sources.defs().first().unwrap().index()];
                                    (def.block == cfg.instr_to_block[site.index()]
                                        && def.instr.index() + 1 == site.index()
                                        && matches!(
                                            proto.instrs[def.instr.index()],
                                            LowInstr::VarArg(_)
                                        ))
                                    .then_some(
                                        HomeSlotKey::new(
                                            def.start_reg.index(),
                                            slot_epochs.epoch_at(def.start_reg, site),
                                        ),
                                    )
                                } else {
                                    None
                                }
                            } else {
                                None
                            },
                            start_index: batch.start_index,
                        },
                    );
                }
                LowInstr::Return(ret) => {
                    let inputs = match ret.values {
                        crate::transformer::ValuePack::Fixed(_) => fixed_return_copy_roots(
                            proto,
                            cfg,
                            dataflow,
                            fixed_temps,
                            site,
                            ret.values,
                        ),
                        crate::transformer::ValuePack::Open(start)
                            if source == crate::decompile::DecompileDialect::Luau =>
                        {
                            open_return_copy_roots(
                                proto,
                                cfg,
                                dataflow,
                                fixed_temps,
                                phi_temps,
                                site,
                                start,
                            )
                        }
                        crate::transformer::ValuePack::Open(_) => None,
                    };
                    if let Some(inputs) = inputs {
                        return_copy_roots.extend(inputs);
                    }
                    let (start, end) = match ret.values {
                        crate::transformer::ValuePack::Fixed(pack) => {
                            (pack.start, pack.start.index() + pack.len)
                        }
                        crate::transformer::ValuePack::Open(start) => {
                            (start, usize::from(proto.frame.max_stack_size))
                        }
                    };
                    if (start.index()..end)
                        .all(|slot| !slot_epochs.reference_capture_may_be_open(Reg(slot), site))
                    {
                        let home =
                            HomeSlotKey::new(start.index(), slot_epochs.epoch_at(start, site));
                        let width = match ret.values {
                            crate::transformer::ValuePack::Fixed(pack) => Some(pack.len),
                            crate::transformer::ValuePack::Open(_) => None,
                        };
                        let representative = *return_layouts.entry((home, width)).or_insert(site);
                        if let crate::transformer::ValuePack::Fixed(pack) = ret.values {
                            let inputs = (0..pack.len)
                                .map(|offset| {
                                    canonical_value_temp(
                                        dataflow.use_value(site, Reg(pack.start.index() + offset)),
                                        dataflow.defs.len(),
                                        fixed_temps,
                                        phi_temps,
                                    )
                                })
                                .collect::<Vec<_>>();
                            return_fixed_inputs
                                .entry(representative)
                                .and_modify(|previous| {
                                    for (previous, input) in previous.iter_mut().zip(&inputs) {
                                        if previous != input {
                                            *previous = None;
                                        }
                                    }
                                })
                                .or_insert(inputs);
                        }
                        return_frames
                            .entry(representative)
                            .or_insert(NativeReturnFrame {
                                home,
                                values: ret.values,
                            });
                        return_frame_sources.insert(site, representative);
                    }
                }
                LowInstr::UnaryOp(_)
                | LowInstr::BinaryOp(_)
                | LowInstr::Concat(_)
                | LowInstr::GetTable(_)
                | LowInstr::NewTable(_)
                | LowInstr::Closure(_)
                | LowInstr::Call(_) => {
                    if let LowInstr::Call(call) = instr
                        && !matches!(call.results, crate::transformer::ResultPack::Fixed(range)
                            if range.len == 1
                                && dataflow.instr_defs[index].as_slice().first()
                                    .is_some_and(|def| dataflow.def_reg(*def) == range.start))
                    {
                        continue;
                    }
                    if let [def] = dataflow.instr_defs[index].as_slice() {
                        let temp = TempId(def.index());
                        if fixed_temps[def.index()] == temp {
                            let first_input = match instr {
                                LowInstr::UnaryOp(unary) => Some(unary.src),
                                LowInstr::Concat(concat) => Some(concat.src.start),
                                LowInstr::BinaryOp(binary) => match binary.lhs {
                                    crate::transformer::ValueOperand::Reg(reg) => Some(reg),
                                    _ => None,
                                },
                                LowInstr::GetTable(get) => match get.base {
                                    crate::transformer::AccessBase::Reg(base) => Some(base),
                                    _ => None,
                                },
                                _ => None,
                            };
                            let second_input = match instr {
                                LowInstr::BinaryOp(binary) => match binary.rhs {
                                    crate::transformer::ValueOperand::Reg(reg) => Some(reg),
                                    _ => None,
                                },
                                _ => None,
                            };
                            let preparations = [first_input, second_input].map(|input| {
                                input.and_then(|reg| {
                                    operand_preparations::collect(
                                        proto,
                                        cfg,
                                        dataflow,
                                        slot_epochs,
                                        fixed_temps,
                                        site,
                                        reg,
                                    )
                                })
                            });
                            if preparations.iter().any(Option::is_some) {
                                operand_preparations.insert(site, preparations);
                            }
                            operation_results.insert(
                                site,
                                NativeOperationResult {
                                    temp,
                                    direct_global_read: matches!(instr,
                                        LowInstr::GetTable(get)
                                            if matches!(get.base, crate::transformer::AccessBase::Env
                                                | crate::transformer::AccessBase::EnvironmentUpvalue(_))
                                                && matches!(get.key, crate::transformer::AccessKey::Const(_))),
                                },
                            );
                            if let LowInstr::UnaryOp(unary) = instr {
                                unary_operands.insert(
                                    site,
                                    NativeUnaryOperand {
                                        home: HomeSlotKey::new(
                                            unary.src.index(),
                                            slot_epochs.epoch_at(unary.src, site),
                                        ),
                                        value: canonical_value_temp(
                                            dataflow.use_value(site, unary.src),
                                            dataflow.defs.len(),
                                            fixed_temps,
                                            phi_temps,
                                        ),
                                    },
                                );
                            }
                            if let LowInstr::BinaryOp(binary) = instr {
                                binary_layouts.insert(
                                    site,
                                    NativeBinaryLayout {
                                        lhs: native_operand_home(binary.lhs, site, slot_epochs),
                                        rhs: native_operand_home(binary.rhs, site, slot_epochs),
                                    },
                                );
                            }
                            if let LowInstr::Concat(concat) = instr
                                && (0..concat.src.len).all(|offset| {
                                    let reg = Reg(concat.src.start.index() + offset);
                                    !slot_epochs.reference_capture_may_be_open(reg, site)
                                })
                            {
                                concat_frames.insert(
                                    site,
                                    NativeConcatFrame {
                                        buffer: concat.src,
                                        captured_update: (|| {
                                            if concat.src.len != 2 || index < 2 {
                                                return None;
                                            }
                                            let LowInstr::Move(copy) = &proto.instrs[index - 2]
                                            else {
                                                return None;
                                            };
                                            let LowInstr::LoadConst(load) =
                                                &proto.instrs[index - 1]
                                            else {
                                                return None;
                                            };
                                            let crate::parser::RawLiteralConst::String(suffix) =
                                                &proto.constants[load.value.index()]
                                            else {
                                                return None;
                                            };
                                            let home = HomeSlotKey::new(
                                                copy.src.index(),
                                                slot_epochs.epoch_at(copy.src, site),
                                            );
                                            (copy.src == concat.dst
                                                && copy.dst == concat.src.start
                                                && load.dst.index() == concat.src.start.index() + 1
                                                && slot_epochs
                                                    .epoch_at(copy.src, InstrRef(index - 2))
                                                    == home.epoch
                                                && cfg.instr_to_block[index - 2]
                                                    == cfg.instr_to_block[index])
                                                .then(|| (home, crate::LuaString::from_raw(suffix)))
                                        })(
                                        ),
                                        // 输入身份按 CONCAT 读取时的 epoch 冻结，不能因
                                        // 先前循环已关闭旧 cell 就丢弃新的连续缓冲帧。
                                        operand_homes: (0..concat.src.len)
                                            .map(|offset| {
                                                let reg = Reg(concat.src.start.index() + offset);
                                                HomeSlotKey::new(
                                                    reg.index(),
                                                    slot_epochs.epoch_at(reg, site),
                                                )
                                            })
                                            .collect(),
                                        operands: (0..concat.src.len)
                                            .map(|offset| {
                                                canonical_value_temp(
                                                    dataflow.use_value(
                                                        site,
                                                        Reg(concat.src.start.index() + offset),
                                                    ),
                                                    dataflow.defs.len(),
                                                    fixed_temps,
                                                    phi_temps,
                                                )
                                            })
                                            .collect(),
                                    },
                                );
                            }
                        }
                    }
                }
                LowInstr::SetTable(set) if set.kind == crate::transformer::SetTableKind::Normal => {
                    if matches!(
                        set.base,
                        crate::transformer::AccessBase::Env
                            | crate::transformer::AccessBase::EnvironmentUpvalue(_)
                    ) {
                        let key = match set.key {
                            crate::transformer::AccessKey::Reg(reg) => Some(HomeSlotKey::new(
                                reg.index(),
                                slot_epochs.epoch_at(reg, site),
                            )),
                            crate::transformer::AccessKey::Const(_)
                            | crate::transformer::AccessKey::Integer(_) => None,
                        };
                        table_write_layouts.insert(
                            site,
                            NativeTableWriteLayout::Environment {
                                key,
                                value: native_operand_home(set.value, site, slot_epochs),
                            },
                        );
                        if let Some(home) = native_operand_home(set.value, site, slot_epochs)
                            && let Some(preparation) = operand_preparations::collect(
                                proto,
                                cfg,
                                dataflow,
                                slot_epochs,
                                fixed_temps,
                                site,
                                crate::transformer::Reg(home.slot()),
                            )
                        {
                            operand_preparations.insert(site, [None, Some(preparation)]);
                        }
                        continue;
                    }
                    if let crate::transformer::AccessBase::Upvalue(base) = set.base {
                        let key = match set.key {
                            crate::transformer::AccessKey::Reg(reg) => Some(HomeSlotKey::new(
                                reg.index(),
                                slot_epochs.epoch_at(reg, site),
                            )),
                            crate::transformer::AccessKey::Const(_)
                            | crate::transformer::AccessKey::Integer(_) => None,
                        };
                        table_write_layouts.insert(
                            site,
                            NativeTableWriteLayout::Upvalue(NativeUpvalueTableWriteLayout {
                                base: crate::hir::common::UpvalueId(base.index()),
                                key,
                                value: native_operand_home(set.value, site, slot_epochs),
                            }),
                        );
                        continue;
                    }
                    let Some(access) =
                        NativeTableReadLayout::for_access(set.base, set.key, site, slot_epochs)
                    else {
                        continue;
                    };
                    let value = native_operand_home(set.value, site, slot_epochs);
                    let preparations = [Some(access.base), value].map(|home| {
                        operand_preparations::collect(
                            proto,
                            cfg,
                            dataflow,
                            slot_epochs,
                            fixed_temps,
                            site,
                            crate::transformer::Reg(home?.slot()),
                        )
                    });
                    if preparations.iter().any(Option::is_some) {
                        operand_preparations.insert(site, preparations);
                    }
                    table_write_layouts.insert(
                        site,
                        NativeTableWriteLayout::Register(NativeRegisterTableWriteLayout {
                            base: access.base,
                            key: access.key,
                            value,
                            initializer: (|| {
                                let base = dataflow
                                    .use_value(site, crate::transformer::Reg(access.base.slot()));
                                let SsaValue::Def(def) = base else {
                                    return None;
                                };
                                let scope = debug_bindings.for_value(base)?;
                                (scope.initializer_end_instr == Some(site)
                                    && fixed_temps[def.index()] == TempId(def.index()))
                                .then_some((TempId(def.index()), scope.scope))
                            })(),
                        }),
                    );
                }
                _ => {}
            }
        }
        let argument_root_producers = calls
            .values()
            .flat_map(|call| &call.argument_roots)
            .map(|root| root.producer)
            .collect();
        // CONCAT 的原输入 COPY 从低于整批缓冲的常量 local 读取时，那个独立声明
        // 仍是后继完整帧的低槽前缀。只内联其 LOADCONST 会让结果声明提前占低一槽，
        // 例如 `suffix="tail"; key="slot_"..suffix; t={...}` 丢掉 suffix 的原 r0。
        // 复用已发布的每个 CONCAT 输入 Def 和 cached MOVE 来源；不把 CALL/闭包等
        // 有独立生命周期的源纳入这项纯标量保留，也不逐候选重扫整个指令后缀。
        call_frame_temps.extend(concat_frames.values().flat_map(|frame| {
            frame.operands.iter().flatten().filter_map(|temp| {
                if temp.index() >= dataflow.defs.len() {
                    return None;
                }
                let input = crate::structure::DefId(temp.index());
                let site = dataflow.def_instr(input);
                let LowInstr::Move(copy) = &proto.instrs[site.index()] else {
                    return None;
                };
                let SsaValue::Def(source) =
                    dataflow.canonical_move_value(dataflow.use_value(site, copy.src))?
                else {
                    return None;
                };
                (fixed_temps[source.index()] == TempId(source.index())
                    && dataflow.def_reg(source).index() < frame.buffer.start.index()
                    && matches!(
                        proto.instrs[dataflow.def_instr(source).index()],
                        LowInstr::LoadConst(_)
                    ))
                .then_some(TempId(source.index()))
            })
        }));
        for (&site, frame) in &concat_frames {
            let Some(result) = operation_results.get(&site) else {
                continue;
            };
            let Some(writes) = immediate_move_writes.get(result.temp.index()) else {
                continue;
            };
            if matches!(proto.instrs[site.index()], LowInstr::Concat(concat)
                if concat.dst.index() < frame.buffer.start.index()
                    && frame.operands.iter().flatten().any(|input|
                        dataflow.defs.get(input.index()).is_some_and(|def|
                            matches!(proto.instrs[def.instr.index()], LowInstr::Move(copy)
                                if copy.src == concat.dst))))
                || writes
                    .steps
                    .iter()
                    .any(|step| step.target_home.slot() < frame.buffer.start.index())
            {
                // 同槽旧值参与输入才证明自更新；Luau 的预留结果槽同样低于输入区，
                // 却可能只是上值赋值的临时结果，不能凭槽距冻结其独立声明。
                // CONCAT 低槽写回与高槽输入准备属于同一赋值帧；先消去返回前的
                // MOVE 或把结果树化进 RETURN，会丢掉已有 local 的更新身份。
                call_frame_temps.insert(result.temp);
                call_frame_temps.extend(writes.steps.iter().map(|step| step.target));
            }
        }
        // 无返回值调用的具名闭包由 statement owner 恢复；原低槽 CLOSURE 是 caller
        // 前缀中的独立分配，不能把其定义身份换成高槽 callee COPY。
        // 保留这个 canonical 定义，让 locals 按原 home 声明；完整调用帧再消费 COPY。
        // 否则闭包移进 COPY 后只剩目标槽，既使后缀前缀证明拒绝，也会跨过原覆盖点
        // 保留此前无读取的根。每个 CALL 只查缓存的 MOVE 源，不回扫指令或闭包子树。
        call_frame_temps.extend(calls.values().filter_map(|call| {
            if call.layout.results != Some(ResultPack::Ignore) {
                return None;
            }
            let callee = call.callee?;
            if callee.index() >= dataflow.defs.len() {
                return None;
            }
            let SsaValue::Def(def) = dataflow
                .canonical_move_value(SsaValue::Def(crate::structure::DefId(callee.index())))?
            else {
                return None;
            };
            (fixed_temps[def.index()] == TempId(def.index())
                && dataflow.def_reg(def).index() < call.layout.home.slot()
                && matches!(
                    proto.instrs[dataflow.def_instr(def).index()],
                    LowInstr::Closure(_)
                ))
            .then_some(TempId(def.index()))
        }));
        // callee lookup 的表若分配或由单结果 CALL 写在调用槽以下，就是原 caller 前缀。
        // 普通 temp-inline 不得先把它塞进高槽 callee，再要求完整帧猜回丢失的前缀；
        // 例如 local t={f}; math.max(value,t[1]()) 的 t 由完整帧负责保留或消费。
        // 每个 CALL 只查询直接 callee 和一次 canonical base，不扫描调用子树或后缀。
        call_frame_temps.extend(calls.values().filter_map(|call| {
            let callee = call.callee?;
            if callee.index() >= dataflow.defs.len() {
                return None;
            }
            let site = dataflow.def_instr(crate::structure::DefId(callee.index()));
            let LowInstr::GetTable(access) = &proto.instrs[site.index()] else {
                return None;
            };
            let crate::transformer::AccessBase::Reg(base) = access.base else {
                return None;
            };
            let SsaValue::Def(def) =
                dataflow.canonical_move_value(dataflow.use_value(site, base))?
            else {
                return None;
            };
            (fixed_temps[def.index()] == TempId(def.index())
                && dataflow.def_reg(def).index() < call.layout.home.slot()
                && (matches!(proto.instrs[dataflow.def_instr(def).index()], LowInstr::NewTable(_))
                    || matches!(proto.instrs[dataflow.def_instr(def).index()],
                        LowInstr::Call(ref source) if matches!(source.results,
                            ResultPack::Fixed(pack) if pack.len == 1 && pack.start == dataflow.def_reg(def)))))
            .then_some(TempId(def.index()))
        }));
        // FASTCALL 低槽源与 fallback 参数 COPY 是不同定义。若先把比较等表达式
        // 移进 COPY，就丢失快路径读取的原槽，完整帧只能反复新增参数声明。
        call_frame_temps.extend(
            calls
                .values()
                .flat_map(|call| &call.fastcall_argument_copies)
                .filter_map(|copy| copy.source),
        );
        for (&site, call) in &calls {
            if !matches!(call.layout.results, Some(ResultPack::Fixed(pack)) if pack.len == 1) {
                continue;
            }
            let Some(result) = operation_results.get(&site) else {
                continue;
            };
            let Some(writes) = immediate_move_writes.get(result.temp.index()) else {
                continue;
            };
            // 写入已打开的捕获 cell 后，回调仍能改写该目标；低槽副本不能
            // 替代原 CALL 结果根。完整帧结合后继下界决定源槽声明与写回形式。
            if writes.steps.iter().any(|step| {
                step.target_home.slot() < call.layout.home.slot()
                    && slot_epochs.reference_capture_may_be_open(
                        crate::transformer::Reg(step.target_home.slot()),
                        site,
                    )
            }) {
                call_frame_temps.insert(result.temp);
            }
            if writes.steps.len() > 1
                && writes
                    .steps
                    .iter()
                    .all(|step| step.target_home.slot() < call.layout.home.slot())
            {
                // CALL 后的连续结果写是一项完整物理事务；只保留首尾会让中间 COPY
                // 消失而仅剩 home 集合，后层无法再核对原写入顺序。
                call_frame_temps.extend(writes.steps.iter().map(|step| step.target));
            }
        }
        let phi_predicates = single_phi_predicates(plan);
        let comparison_result_writes = collect_comparison_result_writes(
            proto,
            cfg,
            dataflow,
            plan,
            fixed_temps,
            phi_temps,
            &phi_predicates,
        );
        for call in calls.values().filter(|call| call.layout.fastcall.is_some()) {
            for result in call.argument_values.iter().flatten() {
                let Some(&predicate) = comparison_result_writes.get(result) else {
                    continue;
                };
                let LowInstr::Branch(branch) = &proto.instrs[predicate.index()] else {
                    continue;
                };
                let crate::transformer::BranchSubject::Compare { lhs, rhs, .. } =
                    branch.cond.subject
                else {
                    continue;
                };
                for operand in [lhs, rhs] {
                    let crate::transformer::CondOperand::Reg(reg) = operand else {
                        continue;
                    };
                    let SsaValue::Def(def) = dataflow.use_value(predicate, reg) else {
                        continue;
                    };
                    let temp = TempId(def.index());
                    if reg.index() < call.layout.home.slot() && fixed_temps[def.index()] == temp {
                        // 比较读取的低槽属于 FASTCALL 前缀，不是 Boolean 参数 scratch。
                        // 即使该 Def 是常量，也先保留其身份，避免内联后整个调用下移。
                        call_frame_temps.insert(temp);
                    }
                }
            }
        }
        let conditional_value_results = collect_conditional_value_results(
            proto,
            cfg,
            dataflow,
            plan,
            fixed_temps,
            phi_temps,
            &phi_predicates,
        );
        let conditional_inputs = conditional_value_results
            .values()
            .flatten()
            .map(|result| result.input)
            .collect::<BTreeSet<_>>();
        let conditional_root_endpoints = dataflow
            .defs
            .iter()
            .enumerate()
            .filter_map(|(index, _)| {
                let endpoint = fixed_temps[index];
                if endpoint != TempId(index) {
                    return None;
                }
                let SsaValue::Def(previous) =
                    dataflow.def_overwritten_value(crate::structure::DefId(index))?
                else {
                    return None;
                };
                let input = fixed_temps[previous.index()];
                (input == TempId(previous.index()) && conditional_inputs.contains(&input))
                    .then_some((endpoint, input))
            })
            .collect();
        let mut comparison_results_by_predicate = BTreeMap::new();
        for (&temp, &predicate) in &comparison_result_writes {
            comparison_results_by_predicate
                .entry(predicate)
                .and_modify(|result| *result = None)
                .or_insert(Some(temp));
        }
        Self {
            call_frame_temps,
            closed_capture_temps: BTreeSet::new(),
            comparison_result_writes,
            boolean_value_prewrites,
            copy_value_prewrites: call_roots::copy_prewrites(
                proto,
                dataflow,
                plan,
                fixed_temps,
                phi_temps,
            ),
            value_result_copies: call_roots::value_result_copies(
                proto,
                cfg,
                dataflow,
                slot_epochs,
                plan,
                fixed_temps,
                phi_temps,
            ),
            comparison_results_by_predicate,
            conditional_value_results,
            short_circuit_call_frames: short_circuit_frames::collect_calls(
                proto,
                cfg,
                dataflow,
                plan,
                fixed_temps,
                phi_temps,
                &phi_predicates,
            ),
            short_circuit_table_frames: short_circuit_frames::collect(
                proto,
                cfg,
                dataflow,
                plan,
                fixed_temps,
                phi_temps,
                &phi_predicates,
            ),
            conditional_root_endpoints,
            calls,
            return_frames,
            return_fixed_inputs,
            parameter_return_scratch: parameter_return_scratch(proto, dataflow),
            empty_call_preserves_frame: proto.signature.num_params == 0
                && !proto.signature.is_vararg
                && dataflow.instr_effects.iter().all(|effect| {
                    effect.fixed_must_defs().is_empty() && effect.open_must_def.is_none()
                })
                && dataflow.effect_summaries.iter().all(|effect| {
                    !effect.may_observe_gc_roots()
                        && matches!(
                            effect.root_observation,
                            crate::structure::RootObservation::None
                                | crate::structure::RootObservation::FrameExit
                        )
                }),
            return_copy_roots,
            entry_parameter_copy_roots: entry_parameter_copy_roots(
                proto,
                source,
                cfg,
                dataflow,
                fixed_temps,
            ),
            return_frame_sources,
            source_proto: Some(source_proto),
            operation_results,
            parallel_frames,
            lookup_assignment_frames: if source == crate::decompile::DecompileDialect::Luau {
                BTreeMap::new()
            } else {
                copy_assignments::lookups::collect(proto, cfg, dataflow, slot_epochs)
            },
            parallel_target_seeds,
            scalar_pair_frames: copy_assignments::collect_scalar_pairs(
                proto,
                cfg,
                dataflow,
                slot_epochs,
                fixed_temps,
                phi_temps,
            ),
            swap_frames: copy_assignments::collect(
                proto,
                cfg,
                dataflow,
                slot_epochs,
                fixed_temps,
                phi_temps,
            ),
            table_write_layouts,
            table_write_local_inputs: BTreeMap::new(),
            table_batch_layouts,
            table_batch_values,
            allocation_batches,
            table_read_layouts,
            table_read_bases,
            binary_layouts,
            binary_local_inputs: BTreeMap::new(),
            // 比较/算术可以读取仍独立物化的 phi，也可以读取已归入内部操作数的 phi。
            // 两者沿用同一原 use 身份；这不授权合并控制域或退休有其它读取的 binding。
            binary_value_operands: dataflow
                .phi_uses
                .iter()
                .enumerate()
                .flat_map(|(index, uses)| {
                    uses.iter().filter_map(move |site| {
                        if !matches!(
                            proto.instrs[site.instr.index()],
                            LowInstr::Branch(_) | LowInstr::BinaryOp(_)
                        ) {
                            return None;
                        }
                        let temp = canonical_value_temp(
                            SsaValue::Phi(crate::structure::PhiId(index)),
                            dataflow.defs.len(),
                            fixed_temps,
                            phi_temps,
                        )?;
                        Some(((site.instr, site.reg), temp))
                    })
                })
                .collect(),
            comparison_preparations,
            operand_preparations,
            upvalue_writes,
            upvalue_table_reads,
            table_preparations,
            unary_operands,
            concat_frames,
            numeric_for_headers: plan
                .loops()
                .filter_map(|(loop_id, _)| match plan.loop_protocol(loop_id) {
                    Some(LoopVmProtocol::NumericFor(protocol)) => Some((
                        protocol.init_instr,
                        NativeNumericForHeader {
                            homes: [protocol.index, protocol.limit, protocol.step].map(|reg| {
                                HomeSlotKey::new(
                                    reg.index(),
                                    slot_epochs.epoch_at(reg, protocol.init_instr),
                                )
                            }),
                            values: [protocol.index, protocol.limit, protocol.step].map(|reg| {
                                canonical_value_temp(
                                    dataflow.use_value(protocol.init_instr, reg),
                                    dataflow.defs.len(),
                                    fixed_temps,
                                    phi_temps,
                                )
                            }),
                        },
                    )),
                    _ => None,
                })
                .collect(),
            nil_write_temps: proto
                .instrs
                .iter()
                .enumerate()
                .filter_map(|(index, instr)| {
                    let LowInstr::LoadNil(nil) = instr else {
                        return None;
                    };
                    let defs = &dataflow.instr_defs[index];
                    if defs.len() != nil.dst.len
                        || defs.is_empty()
                        || defs.iter().enumerate().any(|(offset, def)| {
                            fixed_temps[def.index()] != TempId(def.index())
                                || dataflow.def_reg(*def).index() != nil.dst.start.index() + offset
                        })
                    {
                        return None;
                    }
                    let temps = defs
                        .iter()
                        .map(|def| TempId(def.index()))
                        .collect::<Vec<_>>();
                    Some((temps[0], temps))
                })
                .collect(),
            generic_for_body_frames: plan
                .loops()
                .filter_map(|(loop_id, _)| {
                    let Some(LoopVmProtocol::GenericFor(protocol)) = plan.loop_protocol(loop_id)
                    else {
                        return None;
                    };
                    let LowInstr::GenericForCall(call) = &proto.instrs[protocol.call_instr.index()]
                    else {
                        return None;
                    };
                    let mut controls = vec![call.iterator, call.state, call.control];
                    if let Some(prep) = protocol.prep_instr {
                        let LowInstr::GenericForPrep(prep) = proto.instrs[prep.index()] else {
                            return None;
                        };
                        if prep.control_target != call.control {
                            return None;
                        }
                        controls.push(prep.closing_target);
                    }
                    // Lua 5.5 将 control 与第一个成功 binding 共用一槽；隐式前缀只有
                    // iterator/state/closing，初始化仍接收四个值。两种宽度不可混为一谈。
                    if call.control == protocol.bindings.start {
                        controls.retain(|reg| *reg != call.control);
                    }
                    controls.sort_unstable_by_key(|reg| reg.index());
                    if controls.len() + usize::from(call.control == protocol.bindings.start)
                        != protocol.iterator.len
                        || controls.first().copied() != Some(protocol.iterator.start)
                        || controls.iter().enumerate().any(|(index, reg)| {
                            reg.index() != protocol.iterator.start.index() + index
                        })
                        || protocol.bindings.start.index()
                            != protocol.iterator.start.index() + controls.len()
                    {
                        return None;
                    }
                    let body = cfg.edges[protocol.body_edge.index()].to;
                    let entry = cfg.blocks[body.index()].instrs.start;
                    let home =
                        |reg: Reg| HomeSlotKey::new(reg.index(), slot_epochs.epoch_at(reg, entry));
                    Some((
                        protocol.call_instr,
                        NativeGenericForFrame {
                            initializers: (0..protocol.iterator.len)
                                .map(|offset| home(Reg(protocol.iterator.start.index() + offset)))
                                .collect(),
                            controls: controls.into_iter().map(home).collect(),
                            bindings: (0..protocol.bindings.len)
                                .map(|offset| home(Reg(protocol.bindings.start.index() + offset)))
                                .collect(),
                            binding_padding: usize::from(
                                source == crate::decompile::DecompileDialect::Luau
                                    && protocol.bindings.len == 1,
                            ),
                        },
                    ))
                })
                .collect(),
            copy_root_retirements: Default::default(),
            readonly_parameter_copies: Default::default(),
            copy_scoped_temps: Default::default(),
            copy_scope_handoffs: Default::default(),
            argument_root_producers,
            frame_root_ends_by_call: call_roots::collect_frame_root_ends(
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
            reference_unaliased_temps: dataflow
                .defs
                .iter()
                .filter_map(|def| {
                    let temp = TempId(def.id.index());
                    (fixed_temps[def.id.index()] == temp
                        && !slot_epochs.reference_capture_may_be_open(def.reg, def.instr))
                    .then_some(temp)
                })
                .chain(dataflow.phi_candidates.iter().filter_map(|phi| {
                    let temp = phi_temps[phi.id.index()];
                    (temp == TempId(dataflow.defs.len() + phi.id.index())
                        && !slot_epochs.reference_capture_may_be_open(
                            phi.reg,
                            cfg.blocks[phi.block.index()].instrs.start,
                        ))
                    .then_some(temp)
                }))
                .collect(),
            reference_unaliased_locals: BTreeMap::new(),
            reference_aliased_move_temps: dataflow
                .defs
                .iter()
                .filter_map(|def| {
                    let LowInstr::Move(copy) = proto.instrs[def.instr.index()] else {
                        return None;
                    };
                    let source = dataflow.use_values[def.instr.index()].fixed.get(copy.src)?;
                    let source_site = match source {
                        SsaValue::Def(source) => dataflow.def_instr(source),
                        _ => def.instr,
                    };
                    let crosses_closed_cell = dataflow.reg_is_reference_captured(copy.src)
                        && slot_epochs.epoch_at(copy.src, source_site)
                            != slot_epochs.epoch_at(copy.src, def.instr);
                    (slot_epochs.reference_capture_may_be_open(copy.src, def.instr)
                        || slot_epochs.reference_capture_may_be_open(copy.dst, def.instr)
                        || crosses_closed_cell)
                        .then_some(fixed_temps[def.id.index()])
                })
                .collect(),
            immediate_move_writes,
            copy_predecessors: dataflow
                .defs
                .iter()
                .filter_map(|def| {
                    if !matches!(proto.instrs[def.instr.index()], LowInstr::Move(_))
                        || fixed_temps[def.id.index()] != TempId(def.id.index())
                    {
                        return None;
                    }
                    let SsaValue::Def(previous) = dataflow.def_overwritten_value(def.id)? else {
                        return None;
                    };
                    (fixed_temps[previous.index()] == TempId(previous.index()))
                        .then_some((TempId(def.id.index()), TempId(previous.index())))
                })
                .collect(),
            inert_home_overwrites: collect_inert_home_overwrites(
                proto,
                dataflow,
                fixed_temps,
                &scalar_values,
            ),
            unknown_scratch_write_temps: dataflow
                .defs
                .iter()
                .filter_map(|def| {
                    let temp = TempId(def.id.index());
                    (fixed_temps.get(def.id.index()) == Some(&temp)
                        && dataflow.def_overwrites_unknown_scratch(def.id))
                    .then_some(temp)
                })
                .collect(),
            scratch_overwrite_temps: collect_scratch_overwrite_temps(
                proto,
                dataflow,
                fixed_temps,
                phi_temps,
            ),
            entry_nil_phi_temps: collect_entry_nil_phi_temps(proto, dataflow, plan, phi_temps),
            entry_nil_phi_locals: BTreeSet::new(),
            repeat_condition_prefix_temps: collect_repeat_condition_prefix_temps(
                cfg,
                dataflow,
                plan,
                fixed_temps,
            ),
            direct_table_seed_temps: collect_direct_table_seed_temps(proto, dataflow, fixed_temps),
            direct_table_seed_locals: BTreeSet::new(),
            loop_carrier_temps: collect_loop_carrier_temps(plan, phi_temps),
            phi_carrier_temps: plan
                .phis()
                .filter_map(|phi| {
                    let temp = phi_temps[phi.phi.index()];
                    (temp == TempId(dataflow.defs.len() + phi.phi.index())).then_some(temp)
                })
                .collect(),
            implicit_root_scope_fences,
            scalar_copy_temps,
            scope_end_copy_root_temps: copy_roots.scope_end,
            copy_root_overwrites: copy_roots.overwrites,
            retargeted_scalar_roots: BTreeSet::new(),
            copy_root_endpoint_producers,
            promoted_local_by_temp: BTreeMap::new(),
            consumed_local_bindings: BTreeMap::new(),
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
            tbc_homes: proto
                .instrs
                .iter()
                .enumerate()
                .filter_map(|(index, instr)| {
                    let LowInstr::Tbc(tbc) = instr else {
                        return None;
                    };
                    let origin = InstrRef(index);
                    Some((
                        origin,
                        HomeSlotKey::new(tbc.reg.index(), slot_epochs.epoch_at(tbc.reg, origin)),
                    ))
                })
                .collect(),
            physical_home_universe,
            compact_home_slots: false,
            method_setup_protocols: Vec::new(),
            method_setup_protocol_by_call: BTreeMap::new(),
            method_setup_protocol_by_get: BTreeMap::new(),
        }
    }

    pub(super) fn record_closed_capture_temps(&mut self, temps: &BTreeSet<TempId>) {
        self.closed_capture_temps.extend(temps);
    }

    /// 已证明在显式 CLOSE 窗口内定义和使用的捕获值，不继承窗口外的匿名 cell。
    pub(super) fn is_closed_capture_temp(&self, temp: TempId) -> bool {
        self.closed_capture_temps.contains(&temp)
    }

    pub(super) fn is_direct_table_seed_temp(&self, temp: TempId) -> bool {
        self.direct_table_seed_temps.contains(&temp)
    }

    /// 多个静态 definition 合为一个 carrier 后，home 仍精确，但原 producer 的专属
    /// 正向证书不再代表整个 binding。物理根负向事实由合并入口保护，不在此处删除。
    pub(super) fn retire_coalesced_definition_facts(&mut self, temps: &BTreeSet<TempId>) {
        self.readonly_parameter_copies
            .retain(|temp, _| !temps.contains(temp));
        self.short_circuit_call_frames.retain(|_, frame| {
            frame.is_none_or(|frame| {
                ![frame.input, frame.kept, frame.alternative, frame.result]
                    .iter()
                    .any(|temp| temps.contains(temp))
                    && !matches!(frame.value, short_circuit_frames::ShortCircuitCallValue::CopyTemp(source) if temps.contains(&source))
            })
        });
        self.short_circuit_table_frames.retain(|_, frame| {
            frame.is_none_or(|frame| {
                ![frame.input, frame.alternative, frame.result]
                    .iter()
                    .any(|temp| temps.contains(temp))
            })
        });
        self.parallel_frames.retain(|_, frame| {
            frame
                .moves()
                .all(|write| !temps.contains(&write.target) && !temps.contains(&write.source))
                && frame.previous.iter().all(|temp| !temps.contains(temp))
        });
        self.scalar_pair_frames.retain(|frame| {
            frame.temps.iter().all(|temp| !temps.contains(temp))
                && frame
                    .copied_input
                    .is_none_or(|(temp, _)| !temps.contains(&temp))
                && frame
                    .copied_tail
                    .is_none_or(|(temp, _)| !temps.contains(&temp))
        });
        self.lookup_assignment_frames.retain(|_, frame| {
            frame.reads.iter().all(|read| !temps.contains(&read.value))
                && frame
                    .writes
                    .iter()
                    .all(|write| write.target.is_none_or(|(temp, _)| !temps.contains(&temp)))
        });
        self.parallel_target_seeds
            .retain(|temp| !temps.contains(temp));
        self.boolean_value_prewrites
            .retain(|result, (initial, _)| !temps.contains(result) && !temps.contains(initial));
        self.copy_value_prewrites
            .retain(|result, initial| !temps.contains(result) && !temps.contains(initial));
        self.comparison_result_writes
            .retain(|temp, _| !temps.contains(temp));
        self.comparison_results_by_predicate
            .retain(|_, temp| temp.is_none_or(|temp| !temps.contains(&temp)));
        self.conditional_value_results.retain(|_, result| {
            result.is_none_or(|result| {
                !temps.contains(&result.input)
                    && !temps.contains(&result.result)
                    && result
                        .writes
                        .iter()
                        .flatten()
                        .all(|write| !temps.contains(write))
            })
        });
        self.conditional_root_endpoints
            .retain(|endpoint, input| !temps.contains(endpoint) && !temps.contains(input));
        self.inert_home_overwrites
            .retain(|temp, _| !temps.contains(temp));
        self.entry_nil_phi_temps
            .retain(|temp| !temps.contains(temp));
        self.direct_table_seed_temps
            .retain(|temp| !temps.contains(temp));
        self.repeat_condition_prefix_temps
            .retain(|temp| !temps.contains(temp));
        self.loop_carrier_temps.retain(|temp| !temps.contains(temp));
        self.phi_carrier_temps.retain(|temp| !temps.contains(temp));
        self.promoted_local_by_temp
            .retain(|temp, _| !temps.contains(temp));
        self.argument_root_producers
            .retain(|temp| !temps.contains(temp));
        self.call_frame_temps.retain(|temp| !temps.contains(temp));
        self.unobserved_call_result_ends.retain(|producer, ends| {
            !temps.contains(producer) && ends.iter().all(|end| !temps.contains(end))
        });
        self.frame_root_ends_by_call.retain(|_, roots| {
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

    /// 该 local 来自仍含同槽 `Entry(nil)` incoming 的 canonical phi。
    pub(super) fn is_entry_nil_phi_temp(&self, temp: TempId) -> bool {
        self.entry_nil_phi_temps.contains(&temp)
    }

    pub(super) fn is_entry_nil_phi_local(&self, local: LocalId) -> bool {
        self.entry_nil_phi_locals.contains(&local)
    }

    pub(super) fn record_entry_nil_phi_promotion(&mut self, temp: TempId, local: LocalId) {
        if self.entry_nil_phi_temps.contains(&temp) {
            self.entry_nil_phi_locals.insert(local);
        }
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

    /// 原合流身份没有独立指令写；其空声明能否消除仍须证明所有读取前已有路径写入。
    pub(super) fn is_phi_carrier_temp(&self, temp: TempId) -> bool {
        self.phi_carrier_temps.contains(&temp)
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

    pub(super) fn record_retargeted_scalar_roots(&mut self, roots: BTreeSet<TempId>) {
        self.retargeted_scalar_roots.extend(roots);
    }

    pub(super) fn has_retargeted_scalar_root(&self, temp: TempId) -> bool {
        !self.temp_home_was_invalidated(temp) && self.retargeted_scalar_roots.contains(&temp)
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
    /// consumer 用当前定义索引排除已消失的 producer；原始 home 有效不等于原定义仍存在。
    pub(super) fn is_copy_root_endpoint(
        &self,
        temp: TempId,
        producer_is_present: impl Fn(TempId) -> bool,
    ) -> bool {
        if self.temp_home_was_invalidated(temp) {
            return false;
        }
        self.copy_root_endpoint_producers
            .get(&temp)
            .is_some_and(|producers| {
                producers.iter().any(|producer| {
                    producer_is_present(*producer)
                        && self
                            .copy_root_overwrites(*producer)
                            .is_some_and(|overwrites| {
                                overwrites.iter().any(|overwrite| overwrite.temp() == temp)
                            })
                })
            })
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

    /// 读取 binding 的完整 home；upvalue 属于父 frame，不占当前 proto 的物理槽。
    /// 这里只投影来源，定义处的隐藏 MOVE 写入仍由相应 write query 单独提供。
    pub(super) fn complete_binding_home_slots(&self, binding: HirBinding) -> HomeSlots<'_> {
        match binding {
            HirBinding::Param(param) => self.complete_param_home_slots(param),
            HirBinding::Local(local) => self.complete_local_home_slots(local),
            HirBinding::Temp(temp) => self.complete_temp_home_slots(temp),
            HirBinding::Upvalue(_) => Cow::Owned(BTreeSet::new()),
        }
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
            | HirExpr::CaptureInitializer(_)
            | HirExpr::Unresolved(_) => false,
        }
    }

    /// Returns physical homes written by an immediately following transparent MOVE chain.
    ///
    /// This is intentionally separate from `home_slot`: a compiler MOVE can be elided from HIR
    /// while its adjacent destination write remains observable through GC root lifetime. A MOVE
    /// separated from its producer is excluded because HIR no longer retains its exact timing.
    /// 显式保留的调用 COPY 承接其后写入；原 producer 只负责到该 COPY 的写，后续准备
    /// 由独立 Def 查询。canonical 值别名不因此变化，也不重复计算下一次调用的写责任。
    pub(super) fn trusted_immediate_move_write_homes(
        &self,
        temp: TempId,
    ) -> Option<&BTreeSet<HomeSlotKey>> {
        (!self.temp_home_was_invalidated(temp))
            .then(|| {
                self.immediate_move_writes
                    .get(temp.index())
                    .map(|writes| &writes.homes)
            })
            .flatten()
    }

    /// 原连续 MOVE 的身份与顺序；消费者可区分已吸收写和仍由独立 COPY 承担的写。
    pub(super) fn trusted_immediate_moves(&self, temp: TempId) -> Option<&[ImmediateMoveWrite]> {
        (!self.temp_home_was_invalidated(temp))
            .then(|| {
                self.immediate_move_writes
                    .get(temp.index())
                    .map(|writes| writes.steps.as_slice())
            })
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

    /// 排除原相邻 MOVE 链后，定义自身及身份合并继承的写入责任。
    /// 完整帧消费独立 COPY 证书时仍须核对此域，不能用相同 home 掩盖其它来源的写。
    pub(super) fn complete_temp_non_move_write_homes(&self, temp: TempId) -> HomeSlots<'_> {
        Self::with_supplemental_write_homes(
            self.complete_temp_home_slots(temp),
            self.propagated_temp_definition_write_homes
                .get(&temp)
                .map(Cow::Borrowed)
                .unwrap_or_default(),
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

    fn with_supplemental_write_homes<'a>(
        mut homes: HomeSlots<'a>,
        writes: HomeSlots<'a>,
    ) -> HomeSlots<'a> {
        if !writes.is_subset(&homes) {
            if homes.is_empty() {
                return writes;
            }
            homes.to_mut().extend(writes.iter().copied());
        }
        homes
    }

    pub(super) fn supplemental_temp_definition_write_homes(&self, temp: TempId) -> HomeSlots<'_> {
        let homes = if self
            .possible_temp_home_slots(temp)
            .is_some_and(|homes| homes.is_empty())
        {
            Cow::Owned(BTreeSet::new())
        } else {
            self.trusted_immediate_move_write_homes(temp)
                .map(Cow::Borrowed)
                .unwrap_or_default()
        };
        if let Some(propagated) = self.propagated_temp_definition_write_homes.get(&temp) {
            return Self::with_supplemental_write_homes(homes, Cow::Borrowed(propagated));
        }
        homes
    }

    pub(super) fn supplemental_local_definition_write_homes(
        &self,
        local: LocalId,
    ) -> HomeSlots<'_> {
        self.propagated_local_definition_write_homes
            .get(&local)
            .map(Cow::Borrowed)
            .unwrap_or_default()
    }

    pub(super) fn supplemental_param_definition_write_homes(
        &self,
        param: ParamId,
    ) -> HomeSlots<'_> {
        self.propagated_param_definition_write_homes
            .get(&param)
            .map(Cow::Borrowed)
            .unwrap_or_default()
    }

    pub(super) fn merge_param_definition_write_homes(
        &mut self,
        param: ParamId,
        homes: BTreeSet<HomeSlotKey>,
    ) {
        if homes.is_empty() {
            return;
        }
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
        if homes.is_empty() {
            return;
        }
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
        if homes.is_empty() {
            return;
        }
        self.propagated_temp_definition_write_homes
            .entry(temp)
            .or_default()
            .extend(homes);
    }

    /// 注册 TBC 时的原始物理槽；不受后续 value/binding 合并影响。
    /// origin 由 lowering 发布，重写只能保留或删除，缺项表示内部来源事实丢失。
    pub(super) fn tbc_home(&self, origin: InstrRef) -> HomeSlotKey {
        self.tbc_homes[&origin]
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

    pub(super) fn record_temp_to_local_merge(&mut self, temp: TempId, local: LocalId) {
        let definition_write_homes = self
            .supplemental_temp_definition_write_homes(temp)
            .into_owned();
        self.merge_local_definition_write_homes(local, definition_write_homes);
        self.record_temp_local_binding(temp, local);
        let source_home = self.trusted_temp_home_slot(temp);
        let target_home = self.trusted_local_home_slot(local);
        if source_home.is_none() || source_home != target_home {
            self.record_local_home_merge(
                local,
                self.possible_temp_home_slots(temp).map(Cow::into_owned),
            );
        }
    }

    /// lowering 已按 debug/词法身份决定的绑定不构成槽合并；其 local home 另由声明事实提供。
    pub(super) fn record_temp_local_binding(&mut self, temp: TempId, local: LocalId) {
        let unaliased = self.temp_definition_reference_unaliased(temp);
        self.reference_unaliased_locals
            .entry(local)
            .and_modify(|known| *known &= unaliased)
            .or_insert(unaliased);
        self.promoted_local_by_temp.insert(temp, local);
    }

    /// 身份合并按交集传播，未来同槽的新 capture 不回溯到已证明的原定义。
    pub(super) fn local_definitions_reference_unaliased(&self, local: LocalId) -> bool {
        self.trusted_local_home_slot(local).is_some()
            && self.reference_unaliased_locals.get(&local) == Some(&true)
    }

    pub(super) fn promoted_local_for_temp(&self, temp: TempId) -> Option<LocalId> {
        self.promoted_local_by_temp.get(&temp).copied()
    }

    /// 只登记已删除声明且全部读写已转移的 binding；局部 use 改写不能迁移原 Def。
    pub(super) fn record_consumed_local_binding(&mut self, source: LocalId, target: HirBinding) {
        assert_ne!(HirBinding::Local(source), target);
        if let HirBinding::Local(target) = target {
            let unaliased = self.reference_unaliased_locals.get(&source) == Some(&true);
            self.reference_unaliased_locals
                .entry(target)
                .and_modify(|known| *known &= unaliased)
                .or_insert(unaliased);
        }
        self.consumed_local_bindings.insert(source, target);
    }

    pub(super) fn finish_consumed_local_bindings(&mut self) {
        let rewrites = std::mem::take(&mut self.consumed_local_bindings);
        if rewrites.is_empty() {
            return;
        }
        let mut resolved = BTreeMap::new();
        let mut path = Vec::new();
        // 每条重定向只展开一次；多个原 Def 共用 local 时复用已压缩的最终身份。
        for &source in rewrites.keys() {
            let mut target = HirBinding::Local(source);
            while let HirBinding::Local(local) = target {
                if let Some(&known) = resolved.get(&local) {
                    target = known;
                    break;
                }
                let Some(&next) = rewrites.get(&local) else {
                    break;
                };
                target = next;
                assert!(
                    path.len() < rewrites.len(),
                    "consumed local binding rewrites must be acyclic"
                );
                path.push(local);
            }
            for local in path.drain(..) {
                resolved.insert(local, target);
            }
        }
        self.promoted_local_by_temp.retain(|_, local| {
            match resolved.get(local) {
                Some(HirBinding::Local(target)) => *local = *target,
                Some(_) => return false,
                None => {}
            }
            true
        });
    }

    /// 并行赋值覆盖的原低槽版本先交完整帧，不能因没有读取而提前删除声明前缀。
    pub(super) fn parallel_target_seeds(&self) -> impl Iterator<Item = TempId> + '_ {
        self.parallel_target_seeds.iter().copied()
    }

    pub(super) fn is_parallel_target_seed(&self, temp: TempId) -> bool {
        self.parallel_target_seeds.contains(&temp)
    }

    pub(super) fn native_parallel_assignment(
        &self,
        call: &crate::hir::common::HirCallExpr,
    ) -> Option<&copy_assignments::ParallelFrame> {
        let source = call.source_site?;
        (self.source_proto == Some(source.proto)).then_some(())?;
        let frame = self.parallel_frames.get(&source.instr)?;
        frame
            .moves()
            .all(|write| self.trusted_temp_home_slot(write.target) == Some(write.home))
            .then_some(frame)
    }

    /// 原查表组按指令来源查询；合并或失效后的 home 不再签发原帧许可。
    pub(super) fn lookup_assignment_frame(
        &self,
        access: &crate::hir::common::HirTableAccess,
    ) -> Option<&copy_assignments::lookups::LookupFrame> {
        let crate::hir::common::HirOperationSources::Single(source) = access.sources else {
            return None;
        };
        if self.source_proto != Some(source.proto) {
            return None;
        }
        let frame = self.lookup_assignment_frames.get(&source.instr)?;
        (frame
            .reads
            .iter()
            .all(|read| self.trusted_temp_home_slot(read.value) == Some(read.home))
            && frame.writes.iter().all(|write| {
                write
                    .target
                    .is_none_or(|(temp, home)| self.trusted_temp_home_slot(temp) == Some(home))
            }))
        .then_some(frame)
    }

    /// 标量并列写只消费原三个 Def；同 Local 的其它值版本不能代替这些来源。
    pub(super) fn local_scalar_pair_frames(
        &self,
    ) -> impl Iterator<
        Item = (
            [LocalId; 3],
            Option<LocalId>,
            HirExpr,
            &copy_assignments::ScalarPairFrame,
        ),
    > + '_ {
        self.scalar_pair_frames.iter().filter_map(|frame| {
            let mut locals = [LocalId(0); 3];
            for (index, (&temp, &home)) in frame.temps.iter().zip(&frame.homes).enumerate() {
                let local = self.promoted_local_for_temp(temp)?;
                if self.trusted_temp_home_slot(temp) != Some(home)
                    || self.trusted_local_home_slot(local) != Some(home)
                {
                    return None;
                }
                locals[index] = local;
            }
            let copied_input = if let Some((temp, home)) = frame.copied_input {
                let local = self.promoted_local_for_temp(temp)?;
                if self.trusted_temp_home_slot(temp) != Some(home)
                    || self.trusted_local_home_slot(local) != Some(home)
                {
                    return None;
                }
                Some(local)
            } else {
                None
            };
            let tail = if let Some((temp, home)) = frame.copied_tail {
                let local = self.promoted_local_for_temp(temp)?;
                if self.trusted_temp_home_slot(temp) != Some(home)
                    || self.trusted_local_home_slot(local) != Some(home)
                {
                    return None;
                }
                HirExpr::LocalRef(local)
            } else {
                frame.tail.clone()
            };

            Some((locals, copied_input, tail, frame))
        })
    }

    /// 原交换事实只有三个身份仍有可信 home 且均已物化时才可被完整帧消费。
    pub(super) fn local_swap_frames(
        &self,
    ) -> impl Iterator<Item = (LocalId, LocalId, LocalId, HomeSlotKey)> + '_ {
        self.swap_frames.iter().filter_map(|frame| {
            let snapshot = self.promoted_local_for_temp(frame.snapshot)?;
            let local = |binding| match binding {
                HirBinding::Local(local) => Some(local),
                HirBinding::Temp(temp) => self.promoted_local_for_temp(temp),
                _ => None,
            };
            let (left, right) = (local(frame.left)?, local(frame.right)?);
            (self.trusted_temp_home_slot(frame.snapshot) == Some(frame.home)
                && self.trusted_local_home_slot(snapshot) == Some(frame.home)
                && Some(frame.left_home) == self.trusted_local_home_slot(left)
                && Some(frame.right_home) == self.trusted_local_home_slot(right)
                && self.trusted_local_home_slot(left)?.slot() < frame.home.slot()
                && self.trusted_local_home_slot(right)?.slot() < frame.home.slot())
            .then_some((snapshot, left, right, frame.home))
        })
    }

    /// 写回的值版本可以退休，但交换的输入 binding 随已证明的整体身份改写一起更新。
    pub(super) fn rewrite_copy_assignment_bindings(
        &mut self,
        rewrite: impl Fn(HirBinding) -> HirBinding,
    ) {
        for frame in &mut self.swap_frames {
            frame.left = rewrite(frame.left);
            frame.right = rewrite(frame.right);
        }
    }

    /// 原无读 fixed 写清除旧残值，供 dead-temp 保留原写；不签发新值保活/退休协议。
    pub(super) fn write_clears_unknown_scratch(&self, temp: TempId) -> bool {
        self.unknown_scratch_write_temps.contains(&temp)
            && self.trusted_temp_home_slot(temp).is_some()
    }

    /// 原 COPY 清除了入口或调用留下的未知槽值；新值相同不授权省略这次物理写。
    pub(super) fn overwrites_unknown_scratch(&self, temp: TempId) -> bool {
        self.scratch_overwrite_temps.contains(&temp) && self.trusted_temp_home_slot(temp).is_some()
    }

    pub(super) fn physical_copy_prefix_locals(
        &self,
        physical_roots: &BTreeSet<LocalId>,
    ) -> BTreeSet<LocalId> {
        self.scratch_overwrite_temps
            .iter()
            .filter_map(|temp| self.promoted_local_for_temp(*temp))
            // 普通 fixed 写只为 dead-temp 已认领的原点覆盖请求前缀，不能把每个有值
            // lookup/CALL 结果都变成新的独立 root 或额外声明。
            .chain(self.unknown_scratch_write_temps.iter().filter_map(|temp| {
                self.promoted_local_for_temp(*temp)
                    .filter(|local| physical_roots.contains(local))
            }))
            // 返回后的旧参数副本及 COPY 准备也需要原槽；只保留末端 Local 仍会左移。
            .chain(
                self.entry_parameter_copy_roots
                    .iter()
                    .chain(&self.copy_scoped_temps)
                    .filter_map(|temp| {
                        self.promoted_local_for_temp(*temp)
                            .filter(|local| physical_roots.contains(local))
                    }),
            )
            .filter(|local| self.trusted_local_home_slot(*local).is_some())
            .collect()
    }

    pub(super) fn record_method_setup_protocol(
        &mut self,
        call: InstrRef,
        get: InstrRef,
        callee_temp: TempId,
        receiver_temp: Option<TempId>,
        prior_callee_root_temp: Option<TempId>,
        method_key: crate::LuaString,
    ) {
        let id = HirMethodSetupProtocolId::new(self.method_setup_protocols.len());
        self.method_setup_protocols.push(HirMethodSetupProtocol {
            callee_temp,
            receiver_temp,
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
        let definition_write_homes = self
            .supplemental_local_definition_write_homes(local)
            .into_owned();
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

impl crate::hir::visit::HirVisitor<'_> for CapturedHomeSlotCollector<'_> {
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

/// 参数副本没有本函数内的 GC 观察也不能直接退休。`first=flag; ...; return count`
/// 的高槽可以在 caller 覆写低参数槽后继续保根；例如 alias_09 的原/折叠函数分别
/// 让返回后的 __index 观察到 table/nil。这里只签入口块、全 proto 唯一写的原参数 COPY，
/// 且该槽始终低于每次观察的安全前缀；捕获、清理、尾调用及 vararg 不借此推断寿命。
/// 透明 COPY 链消费 Dataflow 的值根，但必须连同每条独立原准备一起保留；
/// `r1=p0; r2=r1; r3=r2` 只留下 r2/r3 会让声明左移。准备输入不是新的返回存活证明，
/// 其后续实际覆盖仍由原 lifetime/locals owner 处理。
/// 该残根协议只由 PUC 原 VM 证据支持；LuaJIT/Luau 不借目标方言推导源 VM 寿命。
/// 两次顺序扫描加已有按槽 Def 索引，不为每个 COPY 重走控制流或后缀。
fn entry_parameter_copy_roots(
    proto: &LoweredProto,
    source: crate::decompile::DecompileDialect,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
) -> BTreeSet<TempId> {
    use crate::decompile::DecompileDialect;

    if !matches!(
        source,
        DecompileDialect::Lua51
            | DecompileDialect::Lua52
            | DecompileDialect::Lua53
            | DecompileDialect::Lua54
            | DecompileDialect::Lua55
    ) || proto.signature.is_vararg
        || !proto.children.is_empty()
    {
        return BTreeSet::new();
    }
    let mut rooted_prefix = usize::from(proto.frame.max_stack_size);
    let mut has_return = false;
    for (instr, effects) in proto.instrs.iter().zip(&dataflow.effect_summaries) {
        if matches!(
            instr,
            LowInstr::TailCall(_) | LowInstr::Close(_) | LowInstr::Tbc(_)
        ) {
            return BTreeSet::new();
        }
        has_return |= matches!(instr, LowInstr::Return(_));
        match effects.root_observation {
            RootObservation::Call { caller_end } => {
                rooted_prefix = rooted_prefix.min(caller_end.index())
            }
            RootObservation::PrefixLowerBound { end } => rooted_prefix = rooted_prefix.min(end),
            RootObservation::None | RootObservation::FrameExit => {}
            RootObservation::Close { .. } => return BTreeSet::new(),
        }
    }
    if !has_return {
        return BTreeSet::new();
    }
    let mut roots = BTreeSet::new();
    let mut inputs = BTreeMap::new();
    for (index, instr) in proto.instrs.iter().enumerate() {
        if cfg.instr_to_block[index] != cfg.instr_to_block[0] {
            break;
        }
        let LowInstr::Move(copy) = instr else {
            continue;
        };
        let Some(SsaValue::Entry(parameter)) =
            dataflow.canonical_move_value(dataflow.use_value(InstrRef(index), copy.src))
        else {
            continue;
        };
        if parameter.index() >= usize::from(proto.signature.num_params)
            || copy.dst.index() < usize::from(proto.signature.num_params)
            || copy.dst.index() >= rooted_prefix
        {
            continue;
        }
        let Some(def) = dataflow.instr_def_for_reg(InstrRef(index), copy.dst) else {
            continue;
        };
        if fixed_temps[def.index()] != TempId(def.index()) {
            continue;
        }
        let input = match dataflow.use_value(InstrRef(index), copy.src) {
            SsaValue::Entry(source) if source == parameter => None,
            SsaValue::Def(input) if inputs.contains_key(&input) => Some(input),
            // 候选拒绝[ProofIncomplete]：透明值根不证明原准备区可物化；跨块、Phi 或
            // 已合并 Def 不能仅凭同值跳过其实际写入。
            _ => continue,
        };
        inputs.insert(def, input);
        if dataflow.fixed_defs_for_reg(copy.dst) == [def] {
            roots.insert(fixed_temps[def.index()]);
        }
    }
    // 每个共享准备最多入队一次，不为链上的每个残根重复回溯整条 COPY 链。
    let mut pending = roots
        .iter()
        .map(|temp| crate::structure::DefId(temp.index()))
        .collect::<Vec<_>>();
    while let Some(def) = pending.pop() {
        if let Some(Some(input)) = inputs.get(&def)
            && roots.insert(fixed_temps[input.index()])
        {
            pending.push(*input);
        }
    }
    roots
}

/// 冻结终端 COPY 帧仍需保留的低槽 binding，不将 frame exit 当作物理根退休。
/// `r2=p0; r3=p1; r4=r2; r5=r3; return r4,r5` 须先保留 r2/r3 的身份；
/// 高槽 COPY 仍交给 native 完整返回帧消费，不能先内联成参数而丢失原返回槽距。
fn fixed_return_copy_roots(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
    site: InstrRef,
    values: crate::transformer::ValuePack,
) -> Option<Vec<TempId>> {
    let crate::transformer::ValuePack::Fixed(pack) = values else {
        return None;
    };
    if pack.len < 2 {
        return None;
    }
    let start = site.index().checked_sub(pack.len)?;
    let mut inputs = Vec::new();
    for (offset, instr) in proto.instrs[start..site.index()].iter().enumerate() {
        let LowInstr::Move(copy) = instr else {
            return None;
        };
        if copy.dst.index() != pack.start.index() + offset
            || (pack.start.index()..pack.start.index() + pack.len).contains(&copy.src.index())
            || cfg.instr_to_block[start + offset] != cfg.instr_to_block[site.index()]
        {
            return None;
        }
        if copy.src.index() >= pack.start.index() + pack.len {
            // 从高槽结果区写回低槽 RETURN 区时，须保留目标 COPY；保护源值
            // 无法阻止后层把 RETURN 提到高槽，改变原写回和声明前缀。
            let target = dataflow.instr_def_for_reg(InstrRef(start + offset), copy.dst)?;
            let temp = TempId(target.index());
            if fixed_temps[target.index()] != temp {
                return None;
            }
            inputs.push(temp);
            continue;
        }
        match dataflow.use_value(InstrRef(start + offset), copy.src) {
            SsaValue::Def(def) if fixed_temps[def.index()] == TempId(def.index()) => {
                inputs.push(fixed_temps[def.index()]);
            }
            SsaValue::Entry(_) => {}
            SsaValue::Def(_) | SsaValue::Phi(_) => return None,
        }
    }
    Some(inputs)
}

/// Luau 开放尾 CALL 之前的固定返回前缀仍有独立 COPY 身份。`return result, f()` 中
/// result 可以来自条件 phi；只保护原低槽来源，完整返回帧仍负责高槽 COPY 与尾 CALL。
/// 每项按 RETURN 的 reaching Def 查询，不回扫 CALL 准备区；同块 COPY 只属于该块的返回。
fn open_return_copy_roots(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
    site: InstrRef,
    start: Reg,
) -> Option<Vec<TempId>> {
    let tail_site = site.index().checked_sub(1)?;
    let block = cfg.instr_to_block[site.index()];
    let LowInstr::Call(call) = &proto.instrs[tail_site] else {
        return None;
    };
    let ResultPack::Open(tail) = call.results else {
        return None;
    };
    if cfg.instr_to_block[tail_site] != block
        || tail != call.callee
        || tail.index() <= start.index()
    {
        return None;
    }
    let mut inputs = Vec::new();
    for slot in start.index()..tail.index() {
        let SsaValue::Def(def) = dataflow.use_value(site, Reg(slot)) else {
            return None;
        };
        let definition = &dataflow.defs[def.index()];
        let LowInstr::Move(copy) = &proto.instrs[definition.instr.index()] else {
            return None;
        };
        if definition.block != block
            || definition.instr.index() >= tail_site
            || copy.dst != Reg(slot)
            || copy.src.index() >= start.index()
        {
            return None;
        }
        let value = dataflow.use_value(definition.instr, copy.src);
        if matches!(value, SsaValue::Entry(_)) {
            continue;
        }
        inputs.push(canonical_value_temp(
            value,
            dataflow.defs.len(),
            fixed_temps,
            phi_temps,
        )?);
    }
    Some(inputs)
}

/// 无调用、捕获或循环的参数判定树只写首个非参数槽，并从该槽固定返回一值。
/// 原槽可能带旧根，许可只允许整树重发同槽结果，不能删除某条叶 COPY 后直接返回参数。
fn parameter_return_scratch(proto: &LoweredProto, dataflow: &DataflowFacts) -> Option<HomeSlotKey> {
    use crate::transformer::{BranchSubject, CondOperand, ValuePack};
    if proto.signature.is_vararg || !proto.children.is_empty() {
        return None;
    }
    let slot = usize::from(proto.signature.num_params);
    let mut returns = Vec::new();
    for (index, instr) in proto.instrs.iter().enumerate() {
        let accepted = match instr {
            LowInstr::Move(copy) => copy.dst.index() == slot && copy.src.index() < slot,
            LowInstr::LoadConst(load) => load.dst.index() == slot,
            LowInstr::LoadBool(load) => load.dst.index() == slot,
            LowInstr::LoadInteger(load) => load.dst.index() == slot,
            LowInstr::LoadNumber(load) => load.dst.index() == slot,
            LowInstr::LoadNil(load) => load.dst.start.index() == slot && load.dst.len == 1,
            LowInstr::Branch(branch) => {
                (match branch.cond.subject {
                    BranchSubject::Truthy(CondOperand::Reg(reg)) => reg.index() < slot,
                    BranchSubject::Compare {
                        predicate: crate::transformer::BranchPredicate::Eq,
                        lhs,
                        rhs,
                    } => {
                        // nil/Boolean 与参数比较不会调用 __eq，也不需要额外 operand scratch。
                        // 保留该显式比较，仅让原结果槽承接两条返回路径。
                        matches!((lhs, rhs), (CondOperand::Reg(reg), CondOperand::Nil | CondOperand::Boolean(_))
                            | (CondOperand::Nil | CondOperand::Boolean(_), CondOperand::Reg(reg)) if reg.index() < slot)
                    }
                    _ => false,
                }) && branch.then_target.index() > index
                    && branch.else_target.index() > index
            }
            LowInstr::Jump(jump) => jump.target.index() > index,
            LowInstr::Return(ret) => {
                returns.push(dataflow.use_value(InstrRef(index), Reg(slot)));
                matches!(ret.values, ValuePack::Fixed(pack) if pack.start.index() == slot && pack.len == 1)
            }
            _ => false,
        };
        if !accepted {
            // 候选拒绝[ProofIncomplete]：其它写槽、求值事件或控制协议不属于此完整返回树。
            return None;
        }
    }
    let leaves = dataflow.leaf_values_from(returns);
    (!leaves.is_empty()
        && leaves.iter().all(
            |value| matches!(value, SsaValue::Def(def) if dataflow.def_reg(*def).index() == slot),
        ))
    .then_some(HomeSlotKey::new(slot, 0))
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

#[derive(Debug, Clone, Default)]
struct ImmediateMoveWrites {
    homes: BTreeSet<HomeSlotKey>,
    steps: Vec<ImmediateMoveWrite>,
}

#[derive(Debug, Clone, Copy)]
pub(super) struct ImmediateMoveWrite {
    pub(super) source: Option<TempId>,
    pub(super) target: TempId,
    pub(super) source_home: HomeSlotKey,
    pub(super) target_home: HomeSlotKey,
}

/// 两个 incoming 共同所属的单判定 owner；不从指令位置重建 branch containment。
fn single_phi_predicate(plan: &StructurePlan, phi: &crate::structure::PhiPlan) -> Option<InstrRef> {
    let [left, right] = phi.incomings.as_slice() else {
        return None;
    };
    if let Some(owner) = plan.value_decision_owner(phi.phi) {
        let decision = plan.value_decision(owner)?;
        if decision.result_phi != phi.phi {
            let operand = &decision.operands[decision
                .operands
                .binary_search_by_key(&phi.phi, |operand| operand.phi)
                .ok()?];
            let [node] = operand.nodes.as_slice() else {
                return None;
            };
            // 只数直接所属谓词；子操作数准备不增加该 phi 自身的 Boolean 写回条件。
            return Some(decision.nodes[node.index()].predicate);
        }
        let mut operand_nodes = vec![false; decision.nodes.len()];
        for operand in &decision.operands {
            for node in &operand.nodes {
                operand_nodes[node.index()] = true;
            }
        }
        let mut nodes = decision
            .nodes
            .iter()
            .filter(|node| !operand_nodes[node.id.index()]);
        let test = nodes.next()?;
        if nodes.next().is_some() {
            return None;
        }
        Some(test.predicate)
    } else {
        let PhiIncomingDisposition::RegionResult(owner) = left.disposition else {
            return None;
        };
        if right.disposition != left.disposition {
            return None;
        }
        let RegionPlan::Branch { plan: branch, .. } = plan.region(owner)? else {
            return None;
        };
        let condition = plan.condition(plan.branch(*branch)?.condition)?;
        let [test] = condition.nodes.as_slice() else {
            return None;
        };
        Some(test.predicate)
    }
}

/// 一次索引冻结控制树中的单判定结果，包括外层 Decision 吸收的内部物理 phi。
/// 内部 phi 的两条 terminal leaf 必须仍对应原 incoming，不能把整个外层 DAG 当成单判定。
fn single_phi_predicates(plan: &StructurePlan) -> BTreeMap<PhiId, InstrRef> {
    let mut predicates = plan
        .phis()
        .filter_map(|phi| {
            single_phi_predicate(plan, phi).map(|predicate| (phi.phi, Some(predicate)))
        })
        .collect::<BTreeMap<_, _>>();
    for (_, decision) in plan.value_decisions() {
        for node in &decision.nodes {
            let leaf = |target| match target {
                crate::structure::ValueDecisionTarget::Leaf(id)
                | crate::structure::ValueDecisionTarget::CurrentValue(id) => {
                    Some(&decision.leaves[id.index()])
                }
                crate::structure::ValueDecisionTarget::Node(_) => None,
            };
            let (Some(left), Some(right)) = (leaf(node.truthy.target), leaf(node.falsy.target))
            else {
                continue;
            };
            let SsaValue::Phi(phi_id) = left.physical_value else {
                continue;
            };
            let Some(phi) = plan.phi_plan(phi_id) else {
                continue;
            };
            let [first, second] = phi.incomings.as_slice() else {
                continue;
            };
            if right.physical_value != left.physical_value
                || left.physical_pred != phi.block
                || right.physical_pred != phi.block
                || !((first.value == left.value && second.value == right.value)
                    || (first.value == right.value && second.value == left.value))
            {
                continue;
            }
            predicates
                .entry(phi_id)
                .and_modify(|predicate| {
                    if *predicate != Some(node.predicate) {
                        *predicate = None;
                    }
                })
                .or_insert(Some(node.predicate));
        }
    }
    predicates
        .into_iter()
        .filter_map(|(phi, predicate)| predicate.map(|predicate| (phi, predicate)))
        .collect()
}

/// 分配/CALL 被直接测试，无事件叶只在测试后写同一标量结果。保留原关系，允许 HIR
/// 先把值表达式化简；例如 table 在 r3、结果在 r2 的关系不能退化成额外 nil 声明。
fn collect_conditional_value_results(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
    predicates: &BTreeMap<PhiId, InstrRef>,
) -> BTreeMap<InstrRef, Option<NativeConditionalValueResult>> {
    use crate::transformer::{BranchSubject, CondOperand};
    let mut results = BTreeMap::new();
    for phi in plan.phis() {
        let candidate = || {
            let predicate = *predicates.get(&phi.phi)?;
            let LowInstr::Branch(branch) = &proto.instrs[predicate.index()] else {
                return None;
            };
            let BranchSubject::Truthy(CondOperand::Reg(reg)) = branch.cond.subject else {
                return None;
            };
            let SsaValue::Def(table) = dataflow.use_value(predicate, reg) else {
                return None;
            };
            let allocation = dataflow.def_instr(table);
            if !matches!(proto.instrs[allocation.index()], LowInstr::NewTable(_))
                && !matches!(&proto.instrs[allocation.index()], LowInstr::Call(call)
                    if call.results == ResultPack::Fixed(crate::transformer::RegRange { start: reg, len: 1 }))
            {
                return None;
            }
            if dataflow.defs[table.index()].block != cfg.instr_to_block[predicate.index()]
                || allocation.index() >= predicate.index()
            {
                return None;
            }
            let merge = cfg.blocks[phi.block.index()].instrs.start;
            let mut value = None;
            let mut writes = [None; 2];
            if phi.incomings.len() != 2 {
                return None;
            }
            for (arm, incoming) in phi.incomings.iter().enumerate() {
                let SsaValue::Def(def) = incoming.value else {
                    return None;
                };
                let instr = dataflow.def_instr(def);
                let LowInstr::LoadInteger(load) = &proto.instrs[instr.index()] else {
                    return None;
                };
                let block = &cfg.blocks[dataflow.defs[def.index()].block.index()];
                // 只消费原两臂各一条 LOADINT（及到 merge 的 jump）；不能吞掉其它事件。
                if instr.index() <= predicate.index()
                    || load.dst != phi.reg
                    || (instr != branch.then_target && instr != branch.else_target)
                    || block.instrs.start != instr
                    || !match block.instrs.len {
                        1 => instr.index() + 1 == merge.index(),
                        2 => {
                            matches!(proto.instrs[instr.index() + 1], LowInstr::Jump(jump) if jump.target == merge)
                        }
                        _ => false,
                    }
                    || value.is_some_and(|previous| previous != load.value)
                {
                    return None;
                }
                value = Some(load.value);
                let temp = fixed_temps[def.index()];
                if temp != TempId(def.index()) {
                    return None;
                }
                writes[arm] = Some(temp);
            }
            Some((
                allocation,
                NativeConditionalValueResult {
                    input: fixed_temps[table.index()],
                    result: phi_temps[phi.phi.index()],
                    value: CopyRootScalarValue::Integer(value?),
                    writes,
                },
            ))
        };
        if let Some((allocation, result)) = candidate() {
            // 同一分配有多个结果 owner 时不任选其一；后续消费需要专属初始化关系。
            results
                .entry(allocation)
                .and_modify(|entry| *entry = None)
                .or_insert(Some(result));
        }
    }
    // 两个分支直接汇到同一条常量写时没有 phi，仍由 canonical SSA 发布输入/结果。
    // CALL 结果可能在待写结果槽本身或上方；原 TEST 不能退化成 `f(); 9`。
    for (index, instr) in proto.instrs.iter().enumerate() {
        let candidate = || {
            let LowInstr::Branch(branch) = instr else {
                return None;
            };
            if branch.then_target != branch.else_target || branch.then_target.index() != index + 1 {
                return None;
            }
            let BranchSubject::Truthy(CondOperand::Reg(reg)) = branch.cond.subject else {
                return None;
            };
            let SsaValue::Def(input) = dataflow.use_value(InstrRef(index), reg) else {
                return None;
            };
            let source = dataflow.def_instr(input);
            if dataflow.defs[input.index()].block != cfg.instr_to_block[index]
                || !matches!(&proto.instrs[source.index()], LowInstr::Call(call)
                    if call.results == ResultPack::Fixed(crate::transformer::RegRange { start: reg, len: 1 }))
            {
                return None;
            }
            let [result] = dataflow.instr_defs[index + 1].as_slice() else {
                return None;
            };
            let write = proto.instrs.get(index + 1)?;
            let value =
                direct_scalar_overwrite_value(write, dataflow.def_reg(*result)).or_else(|| {
                    let LowInstr::LoadConst(load) = write else {
                        return None;
                    };
                    match proto.constants.get(load.value.index())? {
                        crate::parser::RawLiteralConst::Integer(value) => {
                            Some(CopyRootScalarValue::Integer(*value))
                        }
                        crate::parser::RawLiteralConst::Number(value) => {
                            Some(CopyRootScalarValue::Number(*value))
                        }
                        _ => None,
                    }
                })?;
            if fixed_temps[input.index()] != TempId(input.index())
                || fixed_temps[result.index()] != TempId(result.index())
            {
                return None;
            }
            Some((
                source,
                NativeConditionalValueResult {
                    input: fixed_temps[input.index()],
                    result: fixed_temps[result.index()],
                    value,
                    writes: [Some(fixed_temps[result.index()]), None],
                },
            ))
        };
        if let Some((source, result)) = candidate() {
            results
                .entry(source)
                .and_modify(|entry| *entry = None)
                .or_insert(Some(result));
        }
    }
    results
}

/// 冻结的 region/值决策已证明控制流；保留比较结束后的 Boolean 结果写时点。
fn collect_comparison_result_writes(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
    predicates: &BTreeMap<PhiId, InstrRef>,
) -> BTreeMap<TempId, InstrRef> {
    let mut results = plan
        .phis()
        .filter_map(|phi| {
            let [left, right] = phi.incomings.as_slice() else {
                return None;
            };
            let predicate = *predicates.get(&phi.phi)?;
            let value = |incoming: &crate::structure::PhiIncomingPlan| {
                let SsaValue::Def(def) = incoming.value else {
                    return None;
                };
                let instr = dataflow.def_instr(def);
                let LowInstr::LoadBool(load) = &proto.instrs[instr.index()] else {
                    return None;
                };
                if instr.index() <= predicate.index() || load.dst != phi.reg {
                    return None;
                }
                Some(load.value)
            };
            (value(left)? != value(right)?).then_some((phi_temps[phi.phi.index()], predicate))
        })
        .collect::<BTreeMap<_, _>>();
    // 无使用的比较结果不进入 SSA Phi，但 Structure 已证明两臂的共同初始化。
    // 消费 bindings 实际合并后的身份，不能要求这类结果凭空具有 Phi provenance。
    for (owner, _) in plan.regions() {
        let Some(initializer) = plan.unused_comparison_initializer(owner, proto, cfg, dataflow)
        else {
            continue;
        };
        let [first, second] = initializer.defs;
        let result = fixed_temps[first.index()];
        if fixed_temps[second.index()] == result {
            results.insert(result, initializer.predicate);
        }
    }
    results
}

fn collect_immediate_move_writes(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    slot_epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
    total_temps: usize,
    retained_copies: &BTreeSet<TempId>,
) -> Vec<ImmediateMoveWrites> {
    let mut writes = vec![ImmediateMoveWrites::default(); total_temps];
    let mut write_owner = (0..total_temps).map(TempId).collect::<Vec<_>>();
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

            let SsaValue::Def(source) = dataflow.use_value(def.instr, move_.src) else {
                continue;
            };
            let source = fixed_temps[source.index()];
            let temp = write_owner[source.index()];
            let target = fixed_temps[def.id.index()];
            // 已被调用赋值合同保留的 COPY 是独立写 owner。其后的 SELF/callee 准备
            // 读取该 Def，不再把高槽写追溯挂到前次 CALL。这里分配写责任而不删除写；
            // 完整帧仍分别核对原 CALL+低槽写回与下一次准备，canonical 值身份不变。
            write_owner[target.index()] = if retained_copies.contains(&target) {
                target
            } else {
                temp
            };
            let epoch = slot_epochs.epoch_at(def.reg, def.instr);
            if let Some(writes) = writes.get_mut(temp.index()) {
                let target_home = HomeSlotKey::new(def.reg.index(), epoch);
                writes.homes.insert(target_home);
                writes.steps.push(ImmediateMoveWrite {
                    source: Some(source),
                    target,
                    source_home: HomeSlotKey::new(
                        move_.src.index(),
                        slot_epochs.epoch_at(move_.src, def.instr),
                    ),
                    target_home,
                });
            }
            last_instr_by_root.insert(root, (instr_index, def.block));
        }
    }
    writes
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum InertHomeOverwrite {
    EntryNil,
    DefinedScalar,
}

/// COPY 的旧槽责任沿同寄存器 phi 传给 region result，不能仅保留 canonical Def。
/// 例如 `flag and x or x` 可合成一个值，但两个分支写入的 scratch 仍有覆盖责任。
/// 复用 Dataflow 的反向 phi 边，每条边只随首次标记传播，不扫描后续指令。
fn collect_scratch_overwrite_temps(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
) -> BTreeSet<TempId> {
    let mut temps = BTreeSet::new();
    let mut marked = vec![false; dataflow.phi_candidates.len()];
    let mut pending = VecDeque::new();
    for def in &dataflow.defs {
        if !matches!(proto.instrs[def.instr.index()], LowInstr::Move(_))
            || !dataflow.instr_overwrites_unknown_scratch(def.instr, def.reg)
        {
            continue;
        }
        if let Some(&temp) = fixed_temps.get(def.id.index()) {
            temps.insert(temp);
        }
        for &phi in &dataflow.def_phi_uses[def.id.index()] {
            if dataflow.phi_candidates[phi.index()].reg == def.reg && !marked[phi.index()] {
                marked[phi.index()] = true;
                pending.push_back(phi);
            }
        }
    }
    while let Some(phi) = pending.pop_front() {
        if let Some(&temp) = phi_temps.get(phi.index()) {
            temps.insert(temp);
        }
        for &consumer in &dataflow.phi_phi_uses[phi.index()] {
            if dataflow.phi_candidates[consumer.index()].reg
                == dataflow.phi_candidates[phi.index()].reg
                && !marked[consumer.index()]
            {
                marked[consumer.index()] = true;
                pending.push_back(consumer);
            }
        }
    }
    temps
}

fn collect_inert_home_overwrites(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
    scalar_values: &[bool],
) -> BTreeMap<TempId, InertHomeOverwrite> {
    let param_count = usize::from(proto.signature.num_params);
    let vararg_param_reg = proto.signature.has_vararg_param_reg.then_some(param_count);
    let mut overwrites = BTreeMap::new();
    for def in &dataflow.defs {
        let direct = TempId(def.id.index());
        if fixed_temps.get(def.id.index()) != Some(&direct)
            || dataflow.def_overwrites_unknown_scratch(def.id)
        {
            continue;
        }
        if !dataflow.reference_capture_may_be_open(def.reg, def.instr)
            && dataflow.def_overwritten_value(def.id).is_some_and(|value| {
                let index = match value {
                    SsaValue::Def(def) => def.index(),
                    SsaValue::Phi(phi) => dataflow.defs.len() + phi.index(),
                    SsaValue::Entry(_) => return false,
                };
                scalar_values.get(index) == Some(&true)
            })
        {
            overwrites.insert(direct, InertHomeOverwrite::DefinedScalar);
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
    // Entry phi 的逻辑未定义值不能证明物理槽已清空；该许可只能来自 VM 入口协议。
    if !proto.clears_entry_scratch {
        return BTreeSet::new();
    }
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
                                | PhiIncomingDisposition::RegionInput(_)
                                | PhiIncomingDisposition::LoopCarried(_)
                        )
                }))
            .then_some(direct)
        })
        .collect()
}

fn collect_repeat_condition_prefix_temps(
    cfg: &Cfg,
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

    condition_headers
        .into_iter()
        .flat_map(|header| dataflow.fixed_defs_in_block(cfg, header))
        .filter_map(|def| {
            let direct = TempId(def.index());
            (fixed_temps.get(def.index()) == Some(&direct)).then_some(direct)
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
/// `HirExprSafety::result_is_gc_inert` 复核恢复后的 producer 值，并要求 producer 单写。
/// 通常只物化无读值；已读 constructor 仅消费完整 overwrite 事务，不新增 scope-end 保活。
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
    pub(super) fn into_hir_expr(self) -> HirExpr {
        match self {
            Self::Nil => HirExpr::Nil,
            Self::Boolean(value) => HirExpr::Boolean(value),
            Self::Integer(value) => HirExpr::Integer(value),
            Self::Number(value) => HirExpr::Number(value),
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
    graph: &GraphFacts,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
    inert: &BTreeSet<TempId>,
) -> CopyRootFacts {
    let mut facts = CopyRootFacts::default();
    for def in &dataflow.defs {
        let Some(instr) = proto.instrs.get(def.instr.index()) else {
            continue;
        };

        let direct = TempId(def.id.index());
        if fixed_temps.get(def.id.index()) != Some(&direct)
            || !low_instr_def_may_hold_gc_root(instr, def.reg)
            || inert.contains(&direct)
        {
            continue;
        }
        // COPY 不会把确定的 nil/boolean/number 变成 GC 对象。与 endpoint 共用
        // canonical 值身份，避免给全局声明等标量准备制造并不存在的根事务。
        if let Some(SsaValue::Def(source)) = dataflow.canonical_move_value(SsaValue::Def(def.id))
            && direct_scalar_overwrite_value(
                &proto.instrs[dataflow.def_instr(source).index()],
                dataflow.def_reg(source),
            )
            .is_some()
        {
            continue;
        }
        if let Some(root_end) =
            copy_root_end(proto, cfg, graph, dataflow, fixed_temps, def.instr, def.reg)
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

/// Luau 没有 debug.setlocal；未按引用捕获的标量经过 MOVE/phi 仍不持有 GC 根。
/// 一次 worklist 传播全部定义，避免每个 COPY 重新展开共享 phi 图。循环只有在所有
/// 输入已有证明时才接受，不把自引用当作标量证据；未知入口和捕获 cell 留在未知域。
fn scalar_copy_values(proto: &LoweredProto, cfg: &Cfg, dataflow: &DataflowFacts) -> Vec<bool> {
    let count = dataflow.defs.len();
    let mut inert = vec![false; count + dataflow.phi_candidates.len()];
    let mut pending = vec![usize::MAX; inert.len()];
    let mut users = vec![Vec::new(); inert.len()];
    let mut ready = Vec::new();
    let index = |value: SsaValue| match value {
        SsaValue::Def(def) => Some(def.index()),
        SsaValue::Phi(phi) => Some(count + phi.index()),
        _ => None,
    };
    for def in &dataflow.defs {
        if dataflow.reference_capture_may_be_open(def.reg, def.instr) {
            continue;
        }
        let instr = &proto.instrs[def.instr.index()];
        if !low_instr_def_may_hold_gc_root(instr, def.reg) {
            ready.push(def.id.index());
        } else if let LowInstr::Move(copy) = instr
            && !dataflow.reference_capture_may_be_open(copy.src, def.instr)
            && let Some(input) = index(dataflow.use_value(def.instr, copy.src))
        {
            pending[def.id.index()] = 1;
            users[input].push(def.id.index());
        }
    }
    for phi in &dataflow.phi_candidates {
        if dataflow
            .reference_capture_may_be_open(phi.reg, cfg.blocks[phi.block.index()].instrs.start)
            || phi.incoming.is_empty()
        {
            continue;
        }
        let Some(inputs) = phi
            .incoming
            .iter()
            .map(|input| index(input.value))
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        let target = count + phi.id.index();
        pending[target] = inputs.len();
        for input in inputs {
            users[input].push(target);
        }
    }
    while let Some(value) = ready.pop() {
        if std::mem::replace(&mut inert[value], true) {
            continue;
        }
        for &user in &users[value] {
            pending[user] -= 1;
            if pending[user] == 0 {
                ready.push(user);
            }
        }
    }
    inert
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
        LowInstr::NumericForInit(init) if init.normalizes_slot(reg) => false,
        // body 可改写独立用户槽，退出边未必再写它；JIT dual-number 溢出也可先退出。
        // 这里只保留内部 index 的数值事实，binding 与它共槽时自然消费同一保证。
        LowInstr::NumericForLoop(loop_) if loop_.index == reg => false,
        _ => true,
    }
}

fn copy_root_end(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph: &GraphFacts,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
    producer: InstrRef,
    home: Reg,
) -> Option<CopyRootEnd> {
    let inputs = CopyRootCfgInputs {
        proto,
        cfg,
        graph,
        dataflow,
        fixed_temps,
        home,
    };
    let mut observed = false;
    let mut current_block = *cfg.instr_to_block.get(producer.index())?;
    let mut index = producer.index() + 1;

    while index < proto.instrs.len() {
        let instr_block = *cfg.instr_to_block.get(index)?;
        if instr_block != current_block {
            if copy_root_forward_block_successor(cfg, current_block) != Some(instr_block)
                || cfg.blocks.get(instr_block.index())?.instrs.start != InstrRef(index)
            {
                return copy_root_cfg_end(inputs, current_block, observed);
            }
            current_block = instr_block;
        }
        let range = cfg.blocks.get(current_block.index())?.instrs;
        match scan_copy_root_cfg_block(inputs, current_block, index, observed)? {
            CopyRootCfgBlockEnd::End(end) => return end.is_complete().then_some(end),
            CopyRootCfgBlockEnd::Continue { observed: next } => observed = next,
        }
        if proto.instrs[range.last()?.index()].is_control_terminator() {
            return copy_root_cfg_end(inputs, current_block, observed);
        }
        index = range.end();
    }

    None
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
    inputs: CopyRootCfgInputs<'_>,
    source: BlockRef,
    observed: bool,
) -> Option<CopyRootEnd> {
    let region = copy_root_cfg_region(
        &inputs.proto.instrs,
        inputs.cfg,
        inputs.graph,
        inputs.dataflow,
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
        let start = inputs.cfg.blocks[block.index()].instrs.start.index();
        match scan_copy_root_cfg_block(inputs, block, start, observed)? {
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

#[derive(Clone, Copy)]
struct CopyRootCfgInputs<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    graph: &'a GraphFacts,
    dataflow: &'a DataflowFacts,
    fixed_temps: &'a [TempId],
    home: Reg,
}

fn copy_root_cfg_region(
    instrs: &[LowInstr],
    cfg: &Cfg,
    graph: &GraphFacts,
    dataflow: &DataflowFacts,
    source: BlockRef,
    home: Reg,
) -> Option<BTreeSet<BlockRef>> {
    let mut region = BTreeSet::new();
    let mut pending = VecDeque::from(copy_root_cfg_successors(cfg, source)?);
    while let Some(block) = pending.pop_front() {
        if !region.insert(block) {
            continue;
        }
        if block == source || !graph.dominates(source, block) {
            // 候选拒绝[ProofIncomplete]：普通声明证书未覆盖不经过 source 的入口
            // （regress_545）或新一轮 producer epoch；独立 holder 由 copy_root_retirement 另证。
            // 共享支配事实在入口处排除多入口尾部，不为每个 producer 遍历整段尾部。
            return None;
        }
        let range = cfg.blocks.get(block.index())?.instrs;
        if matches!(
            cfg.terminator(instrs, block),
            Some(LowInstr::Return(_) | LowInstr::TailCall(_))
        ) || dataflow
            .first_must_write_in_range(home, range.start.index()..range.end())
            .is_some()
        {
            continue;
        }
        pending.extend(copy_root_cfg_successors(cfg, block)?);
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
    start: usize,
    mut observed: bool,
) -> Option<CopyRootCfgBlockEnd> {
    let range = inputs.cfg.blocks.get(block.index())?.instrs;
    let last = range.last()?;
    let overwrite = inputs
        .dataflow
        .first_must_write_in_range(inputs.home, start..range.end());
    let stop = overwrite.map_or(range.end(), |instr| instr.index());
    // 线性与 CFG 路径消费同一冻结区间；覆盖本条的观察不属于旧 root transaction。
    if let Some(prefix) = inputs.dataflow.minimum_rooted_prefix(start..stop) {
        if inputs.home.index() >= prefix {
            // 候选拒绝[SemanticBarrier:Lifetime]：观察前缀外的槽不能继续保活（regress_416）。
            return None;
        }
        observed = true;
    }
    if overwrite == Some(InstrRef(stop)) {
        // 即使此路没有观察，也必须保存端点；其它路径的观察可能要求同一 root 保活。
        let end = root_end_at_overwrite(
            inputs.proto,
            inputs.dataflow,
            inputs.fixed_temps,
            stop,
            inputs.home,
        )?
        .with_observation(observed);
        return Some(CopyRootCfgBlockEnd::End(end));
    }
    if inputs.dataflow.effect_summaries[last.index()].root_observation == RootObservation::FrameExit
    {
        return Some(CopyRootCfgBlockEnd::End(
            CopyRootEnd::scope_end().with_observation(observed),
        ));
    }
    Some(CopyRootCfgBlockEnd::Continue { observed })
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
    dataflow
        .has_unobserved_forward_exit_after(InstrRef(index))
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

fn direct_scalar_overwrite(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
    index: usize,
    home: Reg,
) -> Option<CopyRootOverwrite> {
    let def = dataflow.instr_def_for_reg(InstrRef(index), home)?;
    // TESTSET 的条件写已在 LIR 分成独立 MOVE；值取 canonical Def，
    // 退休点仍是写入旧 home 的原指令，不能误用常量准备槽的定义。
    let SsaValue::Def(source) = dataflow.canonical_move_value(SsaValue::Def(def))? else {
        return None;
    };
    let value = direct_scalar_overwrite_value(
        proto.instrs.get(dataflow.def_instr(source).index())?,
        dataflow.def_reg(source),
    )?;
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
