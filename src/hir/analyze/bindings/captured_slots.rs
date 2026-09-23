//! 收集闭包捕获槽目标、声明区域与 capture 后写入；依赖 CFG、slot epoch 和 region tree，
//! 不负责 temp 映射；loop body 块直接借用 Structure 的 containment 索引；例如把同一槽
//! 的不同时代分成独立 local。capture 后写入按 slot/epoch 批量消费 GraphFacts 的 SCC
//! 拓扑与前驱；例如无环块内先写后捕获不需要写回，回边上的同一次静态写则可能再次执行。
//! CLOSE 窗口还区分互斥分支的独立 cell 激活；两个分支都在 r2 捕获并关闭自己的 value，
//! 不能仅因物理 epoch 相同就共用只在 then 声明的 LocalId。未关闭的共同外层 cell 不拆分。
//! 共同 cell 的初始化若支配所有捕获与后续写，直接以该写声明；后续 Phi 不另造 nil carrier。
//! 同一遍捕获枚举也保留全部 capture home 和已接受 debug scope；例如旧 r2 cell 关闭后，
//! 新的未捕获 `next_first` 可沿自己的 nil 声明绑定，不能被旧 epoch 的捕获永久阻止。
//! RETURN/TAILCALL 的非 TBC 关闭由同源的紧邻终结指令承接 activation，不恢复成提前结束的 do；
//! 例如 `local x=1; local f=function() return x end; return f` 保持函数作用域及返回求值。
//! 显式 CLOSE 和资源 cleanup 仍沿原词法窗口处理，不能借终端关闭放宽普通 scope 边界。

use super::*;
use crate::structure::SccId;

/// 每个物理 epoch 按原 low 起点索引互不重叠的已关闭 cell 激活。
type CapturedActivationWindows = BTreeMap<CapturedSlotKey, BTreeMap<usize, usize>>;

pub(super) struct CapturedSlotTargets {
    pub(super) slot_targets: BTreeMap<CapturedSlotKey, CapturedSlotBinding>,
    pub(super) capture_targets: BTreeMap<(usize, usize), LocalId>,
    pub(super) lexical_scopes: Vec<LexicalScope>,
    /// 只读引用捕获也保留独立激活；不因此提前分配可变 cell。
    pub(super) closed_capture_defs: BTreeSet<DefId>,
    activation_windows: CapturedActivationWindows,
    pub(super) entry_local_decls: Vec<LocalId>,
    /// Entry nil cell 属于从指令 0 开始的 CLOSE 窗口，声明须留在该窗口内。
    pub(super) closed_entry_local_decls: Vec<LocalId>,
    pub(super) region_local_decls: BTreeMap<RegionId, Vec<LocalId>>,
    captured_homes: BTreeSet<HomeSlotKey>,
    reference_captured_homes: BTreeSet<HomeSlotKey>,
    captured_debug_scopes: BTreeSet<usize>,
    value_captured_versions: BTreeSet<SsaValue>,
}

impl CapturedSlotTargets {
    /// 已证明的新 cell 起点；入口 binding 和同槽后继 activation 不共享源码声明。
    pub(super) fn activation_starts(&self) -> impl Iterator<Item = (Reg, usize)> + '_ {
        self.activation_windows
            .iter()
            .flat_map(|(key, windows)| windows.keys().map(move |&start| (Reg(key.slot), start)))
    }

    /// 引用捕获保留整个 cell epoch；按值捕获只保留被捕获的源码 scope。
    /// 旧 ByValue 快照不占用同槽后续 debug 变量的 cell，不能让无 CLOSE 的槽永远被禁用。
    pub(super) fn debug_binding_is_uncaptured(&self, home: HomeSlotKey, scope: usize) -> bool {
        !self.reference_captured_homes.contains(&home)
            && !self.captured_debug_scopes.contains(&scope)
    }

    pub(super) fn home_is_uncaptured(&self, home: HomeSlotKey) -> bool {
        !self.captured_homes.contains(&home)
    }

    /// ByValue 只冻结被读取的 SSA 版本；同槽的旧快照不阻止新循环状态写回。
    pub(super) fn version_is_uncaptured(&self, home: HomeSlotKey, value: SsaValue) -> bool {
        !self.reference_captured_homes.contains(&home)
            && !self.value_captured_versions.contains(&value)
    }

    pub(super) fn target_at(
        &self,
        reg: Reg,
        instr: InstrRef,
        epochs: &SlotEpochFacts,
    ) -> Option<LocalId> {
        let mut key = CapturedSlotKey::new(reg.index(), epochs.epoch_at(reg, instr));
        key.activation = activation_at(&self.activation_windows, key, instr.index());
        self.slot_targets
            .get(&key)
            .filter(|binding| instr.index() >= binding.start_instr)
            .map(|binding| binding.target)
    }
}

/// 同一物理 epoch 的独立 CLOSE 窗口互不重叠；按原指令位置查本次 cell 激活。
fn activation_at(
    windows: &CapturedActivationWindows,
    key: CapturedSlotKey,
    instr: usize,
) -> Option<usize> {
    let (&start, &end) = windows.get(&key)?.range(..=instr).next_back()?;
    (instr < end).then_some(start)
}

#[derive(Debug, Clone, Copy)]
pub(super) struct CapturedSlotBinding {
    pub(super) target: LocalId,
    pub(super) start_instr: usize,
}

pub(super) struct CapturedSlotUse {
    instr_index: usize,
    reg: Reg,
    key: CapturedSlotKey,
    start_instr: usize,
    requires_local: bool,
    entry_local_safe: bool,
}

#[derive(Default)]
pub(super) struct CapturedSlotWriteQueries {
    uses: Vec<usize>,
    defs: BTreeMap<SccId, usize>,
}

pub(super) struct CapturedSlotStartWorkspace {
    epoch: usize,
    seen_phi_epoch: Vec<usize>,
    pending: Vec<SsaValue>,
}

impl CapturedSlotStartWorkspace {
    pub(super) fn new(phi_count: usize) -> Self {
        Self {
            epoch: 0,
            seen_phi_epoch: vec![0; phi_count],
            pending: Vec::new(),
        }
    }

    pub(super) fn begin(&mut self, root: SsaValue) {
        if self.epoch == usize::MAX {
            self.seen_phi_epoch.fill(0);
            self.epoch = 1;
        } else {
            self.epoch += 1;
        }
        self.pending.clear();
        self.pending.push(root);
    }

    pub(super) fn visit(&mut self, phi: PhiId) -> bool {
        let Some(seen_epoch) = self.seen_phi_epoch.get_mut(phi.index()) else {
            return false;
        };
        if *seen_epoch == self.epoch {
            return false;
        }
        *seen_epoch = self.epoch;
        true
    }
}

pub(super) struct CapturedSlotInputs<'a> {
    pub(super) proto: &'a LoweredProto,
    pub(super) cfg: &'a Cfg,
    pub(super) graph: &'a GraphFacts,
    pub(super) dataflow: &'a DataflowFacts,
    pub(super) structure: &'a ReadyStructureFacts,
    pub(super) emission: &'a HirEmissionFacts<'a>,
    pub(super) epochs: &'a SlotEpochFacts,
    pub(super) child_mutable_upvalues: &'a [&'a [bool]],
    pub(super) numeric_binding_phis: &'a [bool],
}

pub(super) fn collect_captured_slot_targets(
    inputs: CapturedSlotInputs<'_>,
    entry_local_regs: &mut BTreeMap<Reg, LocalId>,
    local_count: &mut usize,
    local_debug_hints: &mut Vec<Option<String>>,
) -> CapturedSlotTargets {
    let CapturedSlotInputs {
        proto,
        cfg,
        graph,
        dataflow,
        structure,
        emission,
        epochs,
        child_mutable_upvalues,
        numeric_binding_phis,
    } = inputs;
    let mut slot_targets = BTreeMap::<CapturedSlotKey, CapturedSlotBinding>::new();
    let mut capture_targets = BTreeMap::new();
    let mut captured_homes = BTreeSet::new();
    let mut reference_captured_homes = BTreeSet::new();
    let mut captured_debug_scopes = BTreeSet::new();
    let mut value_captured_versions = BTreeSet::new();
    let mut value_capture_pending = Vec::new();
    let mut captured_uses = Vec::new();
    let mut entry_initializers = BTreeMap::new();
    if proto.debug_locals.is_empty()
        && let Some(prefix) = emission.regular_prefix(cfg.entry_block)
    {
        // 剥离 debug 后只认入口槽的第一笔字面量写。它虽被所有分支覆盖，仍是
        // 原帧的一次初始化；不能把它删掉或在同槽 Phi 旁另造一个空 carrier。
        // 非字面量和已读取的准备不在这里推断声明身份，原 debug scope 则由其 owner 负责。
        for def in &dataflow.defs {
            if cfg.instr_to_block[def.instr.index()] == cfg.entry_block {
                entry_initializers.entry(def.reg).or_insert(def.id);
            }
        }
        entry_initializers.retain(|_, def| {
            let instr = dataflow.def_instr(*def);
            prefix.contains(&instr.index())
                && dataflow.def_uses[def.index()].is_empty()
                && dataflow.def_phi_uses[def.index()].is_empty()
                && matches!(
                    proto.instrs[instr.index()],
                    LowInstr::LoadNil(_)
                        | LowInstr::LoadBool(_)
                        | LowInstr::LoadConst(_)
                        | LowInstr::LoadInteger(_)
                        | LowInstr::LoadNumber(_)
                )
        });
    }
    let mut loop_owned_slots = BTreeSet::new();
    for (loop_id, loop_plan) in structure.plan().loops() {
        let Some(binding_blocks) = loop_binding_blocks(structure.plan(), loop_id) else {
            continue;
        };
        for &block in binding_blocks {
            match loop_plan.source_bindings {
                Some(LoopSourceBindings::Numeric(binding)) => {
                    // `block_local_regs` 已为该槽分配 numeric-for local，其词法 cell 会逐轮
                    // 重建并关闭；body capture 必须复用这个 owner，不能另分配 epoch local。
                    loop_owned_slots.insert((block, binding));
                }
                Some(LoopSourceBindings::Generic(bindings)) => {
                    for offset in 0..bindings.len {
                        loop_owned_slots.insert((block, Reg(bindings.start.index() + offset)));
                    }
                }
                None => {}
            }
            // header_values 只是 SSA carried 状态，不是循环语法声明的独立 cell。
            // 其捕获、回边与出口仍由同一 slot epoch 绑定，不能跳过 capture owner。
        }
    }
    let mut write_queries = BTreeMap::<CapturedSlotKey, CapturedSlotWriteQueries>::new();
    let mut start_workspace = CapturedSlotStartWorkspace::new(structure.plan().phis().len());
    let mut entry_decl_keys = BTreeSet::new();
    let mut region_decl_keys = BTreeMap::new();
    let mut conflicting_region_decl_keys = BTreeSet::new();
    let mut entry_safe_by_key = BTreeMap::new();

    for (instr_index, instr) in proto.instrs.iter().enumerate() {
        let LowInstr::Closure(closure) = instr else {
            continue;
        };
        for (capture_index, capture) in closure.captures.iter().enumerate() {
            if let CaptureSource::ByReference(reg) | CaptureSource::ByValue(reg) = capture.source {
                let instr = InstrRef(instr_index);
                captured_homes.insert(HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, instr)));
                if matches!(capture.source, CaptureSource::ByReference(_)) {
                    reference_captured_homes
                        .insert(HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, instr)));
                } else {
                    let value = if reg == closure.dst {
                        SsaValue::Def(
                            dataflow
                                .instr_def_for_reg(instr, reg)
                                .expect("closure defines its self-captured value"),
                        )
                    } else {
                        dataflow.use_value(instr, reg)
                    };
                    value_capture_pending.push(value);
                }
                if let Some(fact) = structure
                    .debug_bindings()
                    .for_value(dataflow.use_value(instr, reg))
                {
                    captured_debug_scopes.insert(fact.scope);
                }
                // 捕获可能读取该 scope 内重赋值后的 Def；它不必是 debug 入口 SSA。
                if let Some(hint) = debug_local_hint_for_reg_at_instr(proto, reg, instr) {
                    captured_debug_scopes.insert(hint.scope);
                }
            }
            let CaptureSource::ByReference(reg) = capture.source else {
                continue;
            };
            if reg == closure.dst
                || reg.index() < usize::from(proto.signature.num_params)
                || matches!(
                    dataflow.use_value(InstrRef(instr_index), reg),
                    SsaValue::Phi(phi)
                        if numeric_binding_phis.get(phi.index()).copied().unwrap_or(false)
                )
                || loop_owned_slots.contains(&(cfg.instr_to_block[instr_index], reg))
            {
                continue;
            }
            let has_no_reaching_value =
                capture_has_no_reaching_value(dataflow, InstrRef(instr_index), reg);
            let start_instr = captured_slot_start_instr(
                dataflow,
                structure.plan(),
                InstrRef(instr_index),
                reg,
                has_no_reaching_value,
                &mut start_workspace,
            );
            // 原 debug 声明可以早于捕获时的 reaching Def；先确定同一源码 cell
            // 的入口，再划分终止窗口，不能把后续赋值伪装成第二次声明。
            let debug_initializer =
                captured_debug_initializer(proto, structure, dataflow, instr_index, reg).filter(
                    |&source| {
                        source <= start_instr
                            && epochs.epoch_at(reg, InstrRef(source))
                                == epochs.epoch_at(reg, InstrRef(start_instr))
                    },
                );
            let initializer = debug_initializer.or_else(|| {
                let initial = dataflow.def_instr(*entry_initializers.get(&reg)?).index();
                let capture_block = cfg.instr_to_block[instr_index];
                if graph.block_is_cyclic(capture_block) {
                    // 入口初始化不参与回边，且捕获仍处于同一 CLOSE epoch，才证明是
                    // 跨轮共享 cell。每轮关闭的槽在 loop header 有 merge epoch，不能
                    // 将其初始化外提；每轮先覆盖再捕获时无需存在活的 carried phi。
                    if graph.block_is_cyclic(cfg.entry_block)
                        || !graph.dominates(cfg.entry_block, capture_block)
                        || epochs.epoch_at(reg, InstrRef(initial))
                            != epochs.epoch_at(reg, InstrRef(instr_index))
                    {
                        return None;
                    }
                } else if !matches!(
                    dataflow.use_value(InstrRef(instr_index), reg),
                    SsaValue::Phi(_)
                ) {
                    return None;
                }
                (initial < start_instr
                    && epochs.epoch_at(reg, InstrRef(initial))
                        == epochs.epoch_at(reg, InstrRef(start_instr)))
                .then_some(initial)
            });
            let start_instr = initializer.unwrap_or(start_instr);
            let entry_local_safe = epochs.spans_entry(reg);
            let key =
                CapturedSlotKey::new(reg.index(), epochs.epoch_at(reg, InstrRef(start_instr)));
            let child_writes = child_mutable_upvalues
                .get(closure.proto.index())
                .and_then(|mutable| mutable.get(capture_index))
                .copied()
                .unwrap_or(false);
            // 捕获虽只读，debug 声明或已证明的入口槽初始化仍应接收后续重赋值。
            // 只物化最终 reaching phi 会把分支写拆成临时身份并在出口交接。
            let source_reassigned = initializer.is_some_and(|initial| {
                dataflow
                    .instr_def_for_reg(InstrRef(initial), reg)
                    .is_some_and(|def| {
                        dataflow.use_value(InstrRef(instr_index), reg) != SsaValue::Def(def)
                    })
            });
            let requires_local = child_writes || has_no_reaching_value || source_reassigned;
            let use_index = captured_uses.len();
            captured_uses.push(CapturedSlotUse {
                instr_index,
                reg,
                key,
                start_instr,
                requires_local,
                entry_local_safe,
            });
            if !requires_local {
                write_queries.entry(key).or_default().uses.push(use_index);
            }
        }
    }

    resolve_parent_writes_after_capture(
        cfg,
        graph,
        dataflow,
        epochs,
        &mut write_queries,
        &mut captured_uses,
    );
    // 同一 LOADNIL 声明组已有可变 cell 时，其后才被只读捕获的成员也占据原前缀。
    // 若把后者的 MOVE 另声明为高槽快照，前缀恢复会再补一份 nil，抬高后续帧。
    // 先建立整组 initializer，再分配 activation；否则先激活的成员会使其余成员
    // 失去同一 LOADNIL 前缀。原 nil 与 reaching initializer 须在同一基本块；
    // 后续捕获可在其支配的块内，但仍须属于同一未关闭 epoch。debug 身份由原窗口决定。
    let nil_starts = captured_uses
        .iter()
        .filter(|capture| capture.requires_local)
        .map(|capture| capture.start_instr)
        .collect::<BTreeSet<_>>();
    let mut nil_members = BTreeMap::new();
    for start in nil_starts {
        let LowInstr::LoadNil(nil) = &proto.instrs[start] else {
            continue;
        };
        if nil.dst.len < 2 {
            continue;
        }
        for offset in 0..nil.dst.len {
            let reg = Reg(nil.dst.start.index() + offset);
            let key = CapturedSlotKey::new(reg.index(), epochs.epoch_at(reg, InstrRef(start)));
            nil_members.entry(key).or_insert(start);
        }
    }
    for capture in &captured_uses {
        if nil_members.get(&capture.key).is_some_and(|&start| {
            start > capture.start_instr
                || cfg.instr_to_block[start] != cfg.instr_to_block[capture.start_instr]
                || !graph.dominates(
                    cfg.instr_to_block[start],
                    cfg.instr_to_block[capture.instr_index],
                )
                || debug_local_hint_for_reg_at_instr(
                    proto,
                    capture.reg,
                    InstrRef(capture.instr_index),
                )
                .is_some()
        }) {
            nil_members.remove(&capture.key);
        }
    }
    for capture in &mut captured_uses {
        if let Some(&start) = nil_members.get(&capture.key) {
            capture.start_instr = start;
            capture.requires_local = true;
        }
    }
    let (lexical_scopes, activation_windows) = collect_lexical_close_scopes(inputs, &captured_uses);
    let closed_capture_defs = captured_uses
        .iter()
        .filter_map(|capture| {
            let SsaValue::Def(def) = dataflow.use_value(InstrRef(capture.instr_index), capture.reg)
            else {
                return None;
            };
            let start = activation_at(&activation_windows, capture.key, capture.instr_index)?;
            let end = *activation_windows.get(&capture.key)?.get(&start)?;
            (start..end)
                .contains(&dataflow.def_instr(def).index())
                .then_some((def, start, end))
        })
        // 同一只读值可以被许多闭包捕获；只为其唯一激活扫描一次全部 use。
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter_map(|(def, start, end)| {
            (!captured_definition_escapes(dataflow, def, start, end, None)).then_some(def)
        })
        .collect();
    for captured in &mut captured_uses {
        captured.key.activation =
            activation_at(&activation_windows, captured.key, captured.instr_index);
        if captured.key.activation == Some(0)
            && dataflow.use_value(InstrRef(captured.instr_index), captured.reg)
                == SsaValue::Entry(captured.reg)
        {
            captured.start_instr = 0;
        }
        // 入口声明已有绑定 owner，但同槽后继捕获仍须参与 CLOSE 窗口分析。
        // 是否分配新 local 与是否恢复原词法边界是两项不同的事实。
        if entry_local_regs.contains_key(&captured.reg) && captured.key.activation != Some(0) {
            captured.requires_local = false;
        }
        if captured.key.activation.is_some() {
            // 原窗口首写建立 cell，关闭后销毁；不能改为入口 cell 或跨兄弟分支复用。
            captured.entry_local_safe = false;
        }
    }
    let initializers = dominating_cell_initializers(
        proto,
        cfg,
        graph,
        dataflow,
        structure,
        epochs,
        &activation_windows,
        &captured_uses,
    );
    // 父先子后传播最外层 single-pass 的外部 owner，避免逐 cell 回扫整条祖先链。
    let plan = structure.plan();
    let mut single_pass_owners = vec![None; plan.regions().len()];
    for &region in plan.region_postorder().iter().rev() {
        let parent = plan.region(region).and_then(RegionPlan::parent);
        single_pass_owners[region.index()] = parent
            .and_then(|parent| single_pass_owners[parent.index()])
            .or_else(|| plan.single_pass_for_region(region).and(parent));
    }
    for (&key, &start) in &initializers {
        // 显式 CLOSE 激活窗口仍由原词法 scope 拥有，不能外提成跨窗口共享 cell。
        if key.activation.is_some() {
            continue;
        }
        let Some(region) = plan.region_for_block(cfg.instr_to_block[start]) else {
            continue;
        };
        if let Some(owner) = single_pass_owners[region.index()] {
            // 支配写仍在原位置执行，但 single-pass 的 repeat 壳不是原 cell 的词法域。
            // 在壳外声明身份，避免后继 return/phi 读取变成域外引用；原初始化写不前移。
            // branch_24_nested_branch_escape 的 trace 同时被 guard closure 和出口读取。
            region_decl_keys.insert(key, owner);
        }
    }
    for captured in &mut captured_uses {
        if let Some(&start) = initializers.get(&captured.key) {
            captured.start_instr = start;
            if let SsaValue::Phi(phi) =
                dataflow.use_value(InstrRef(captured.instr_index), captured.reg)
                && structure.plan().value_decision_owner(phi).is_none()
            {
                // 支配初始化与同 epoch 的分支写共同形成捕获值。即使闭包只读，
                // 也须让原写回落在该 cell；另物化 reaching phi 会拆出无意义的快照。
                // initializers 已核对全部捕获、写入、phi 的支配及未打开的激活边界。
                captured.requires_local = true;
            }
        }
    }
    for captured in &captured_uses {
        entry_safe_by_key
            .entry(captured.key)
            .and_modify(|safe| *safe &= captured.entry_local_safe)
            .or_insert(captured.entry_local_safe);
        if captured.requires_local
            && !initializers.contains_key(&captured.key)
            && captured.entry_local_safe
            && (dataflow.use_value(InstrRef(captured.instr_index), captured.reg)
                == SsaValue::Entry(captured.reg)
                || graph.block_is_cyclic(cfg.instr_to_block[captured.instr_index]))
        {
            // VM 入口 nil 已占据低槽；延迟到首次捕获才声明会交换它与此前高槽
            // initializer 的物理位置，令后续整帧恢复失去原前缀。
            entry_decl_keys.insert(captured.key);
        }
        if captured.requires_local
            && !initializers.contains_key(&captured.key)
            && let Some(region) = captured_slot_declaration_region(
                dataflow,
                structure.plan(),
                InstrRef(captured.instr_index),
                captured.reg,
            )
            && !conflicting_region_decl_keys.contains(&captured.key)
        {
            match region_decl_keys.get(&captured.key).copied() {
                None => {
                    region_decl_keys.insert(captured.key, region);
                }
                Some(existing) if existing == region => {}
                Some(_) => {
                    region_decl_keys.remove(&captured.key);
                    conflicting_region_decl_keys.insert(captured.key);
                }
            }
        }
    }

    let mut closed_entry_local_decls = BTreeMap::new();
    for captured in captured_uses
        .iter()
        .filter(|captured| captured.requires_local)
    {
        let target = if let Some(binding) = slot_targets.get_mut(&captured.key) {
            binding.start_instr = binding.start_instr.min(captured.start_instr);
            binding.target
        } else {
            let local = if let Some(&local) = entry_local_regs
                .get(&captured.reg)
                .filter(|_| captured.key.epoch == 0 && captured.key.activation == Some(0))
            {
                local
            } else {
                let local = LocalId(*local_count);
                *local_count += 1;
                local_debug_hints.push(debug_local_name_for_reg_at_instr(
                    proto,
                    captured.reg,
                    InstrRef(captured.instr_index),
                ));
                local
            };
            let target = local;
            slot_targets.insert(
                captured.key,
                CapturedSlotBinding {
                    target,
                    start_instr: captured.start_instr,
                },
            );
            target
        };
        if captured.entry_local_safe {
            entry_local_regs.entry(captured.reg).or_insert(target);
        }
        if captured.key.activation == Some(0)
            && dataflow.use_value(InstrRef(captured.instr_index), captured.reg)
                == SsaValue::Entry(captured.reg)
        {
            entry_local_regs.entry(captured.reg).or_insert(target);
            closed_entry_local_decls.insert(captured.reg, target);
        }
    }

    for captured in captured_uses {
        if let Some(binding) = slot_targets.get_mut(&captured.key) {
            binding.start_instr = binding.start_instr.min(captured.start_instr);
            capture_targets.insert((captured.instr_index, captured.reg.index()), binding.target);
        }
    }

    entry_decl_keys.extend(
        conflicting_region_decl_keys
            .into_iter()
            .filter(|key| entry_safe_by_key.get(key).copied().unwrap_or(false)),
    );
    for key in &entry_decl_keys {
        region_decl_keys.remove(key);
    }
    let entry_local_decls = entry_decl_keys
        .iter()
        .filter_map(|key| slot_targets.get(key))
        .map(|binding| binding.target)
        .collect();
    let mut region_local_decls = BTreeMap::<RegionId, Vec<LocalId>>::new();
    for (key, region) in region_decl_keys {
        let Some(binding) = slot_targets.get(&key) else {
            continue;
        };
        region_local_decls
            .entry(region)
            .or_default()
            .push(binding.target);
    }
    // 每个 Phi 只展开一次；保留所有可能被快照读取的输入，不为各循环重复追溯。
    while let Some(value) = value_capture_pending.pop() {
        if value_captured_versions.insert(value)
            && let SsaValue::Phi(phi) = value
            && let Some(phi) = structure.plan().phi_plan(phi)
        {
            value_capture_pending.extend(phi.incomings.iter().map(|incoming| incoming.value));
        }
    }
    CapturedSlotTargets {
        slot_targets,
        capture_targets,
        lexical_scopes,
        closed_capture_defs,
        activation_windows,
        entry_local_decls,
        closed_entry_local_decls: closed_entry_local_decls.into_values().collect(),
        region_local_decls,
        captured_homes,
        reference_captured_homes,
        captured_debug_scopes,
        value_captured_versions,
    }
}

/// 原支配初始化已经声明 cell 时，后续 reaching Phi 不再触发另一份 region 空声明。
/// 同一 key 的全部捕获、固定写和正常 phi 都由该写支配；Entry 活读保持入口 owner。
#[expect(
    clippy::too_many_arguments,
    reason = "仅在 binding owner 汇合同一快照的 source、SSA、支配与 cell 激活事实"
)]
fn dominating_cell_initializers(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph: &GraphFacts,
    dataflow: &DataflowFacts,
    structure: &ReadyStructureFacts,
    epochs: &SlotEpochFacts,
    activations: &CapturedActivationWindows,
    captures: &[CapturedSlotUse],
) -> BTreeMap<CapturedSlotKey, usize> {
    struct Candidate {
        start: usize,
        source_init: Option<usize>,
        source_consistent: bool,
    }
    let mut groups = BTreeMap::<CapturedSlotKey, Candidate>::new();
    for capture in captures {
        let source_init = captured_debug_initializer(
            proto,
            structure,
            dataflow,
            capture.instr_index,
            capture.reg,
        );
        groups
            .entry(capture.key)
            .and_modify(|group| {
                group.start = group.start.min(capture.start_instr);
                group.source_consistent &= group.source_init == source_init;
            })
            .or_insert(Candidate {
                start: capture.start_instr,
                source_init,
                source_consistent: true,
            });
    }
    let key_at = |reg: Reg, instr: InstrRef| {
        let mut key = CapturedSlotKey::new(reg.index(), epochs.epoch_at(reg, instr));
        key.activation = activation_at(activations, key, instr.index());
        key
    };
    for phi in structure.plan().phis() {
        let Some(SsaValue::Def(input)) = phi.loop_carried().map(|carried| carried.input) else {
            continue;
        };
        let header = cfg.blocks[phi.block.index()].instrs.start;
        let initial = dataflow.def_instr(input);
        let key = key_at(phi.reg, header);
        if dataflow.def_reg(input) == phi.reg
            && key_at(phi.reg, initial) == key
            && let Some(group) = groups.get_mut(&key)
        {
            // 第一次捕获可能读取循环内的更新 Def；cell 的声明仍属于 carried phi
            // 已证明的唯一入口。下方继续核对支配、未激活及全部写域，不按槽号回扫首写。
            group.start = group.start.min(initial.index());
        }
    }
    let mut entry_observed = BTreeMap::new();
    let mut initializers = groups
        .into_iter()
        .filter_map(|(key, candidate)| {
            let reg = Reg(key.slot);
            let start = candidate
                .source_init
                .filter(|&source| {
                    candidate.source_consistent
                        && source <= candidate.start
                        && key_at(reg, InstrRef(source)) == key
                })
                .unwrap_or(candidate.start);
            let instr = InstrRef(start);
            if dataflow.instr_def_for_reg(instr, reg).is_none()
                || key_at(reg, instr) != key
                || epochs.reference_capture_may_be_open(reg, instr)
                || (key.activation.is_none()
                    && key.epoch == 0
                    && *entry_observed
                        .entry(reg)
                        .or_insert_with(|| entry_reg_is_observed(dataflow, structure.plan(), reg)))
            {
                return None;
            }
            Some((key, start))
        })
        .collect::<BTreeMap<_, _>>();
    let dominates = |start: usize, instr: usize| {
        graph.dominates(cfg.instr_to_block[start], cfg.instr_to_block[instr])
            && (cfg.instr_to_block[start] != cfg.instr_to_block[instr] || start <= instr)
    };
    for capture in captures {
        if initializers
            .get(&capture.key)
            .is_some_and(|&start| !dominates(start, capture.instr_index))
        {
            initializers.remove(&capture.key);
        }
    }
    // 批量验证真正会投影到该 binding 的写入，不为每个 cell 重扫后缀。
    for def in &dataflow.defs {
        let key = key_at(def.reg, def.instr);
        if initializers.get(&key).is_some_and(|&start| {
            def.instr.index() >= start && !dominates(start, def.instr.index())
        }) {
            initializers.remove(&key);
        }
    }
    for phi in structure
        .plan()
        .phis()
        .filter(|phi| phi_participates_in_normal_binding(phi))
    {
        let instr = cfg.blocks[phi.block.index()].instrs.start;
        let key = key_at(phi.reg, instr);
        if initializers
            .get(&key)
            .is_some_and(|&start| instr.index() >= start && !dominates(start, instr.index()))
        {
            initializers.remove(&key);
        }
    }
    initializers
}

fn collect_lexical_close_scopes(
    inputs: CapturedSlotInputs<'_>,
    captured_uses: &[CapturedSlotUse],
) -> (Vec<LexicalScope>, CapturedActivationWindows) {
    let CapturedSlotInputs {
        proto,
        cfg,
        graph,
        dataflow,
        structure,
        emission,
        epochs,
        ..
    } = inputs;
    let plan = structure.plan();
    // 返回配对不抹除原 debug 的独立块终点。按结束指令一次索引，避免每次 CLOSE
    // 重扫 debug 表；已在终结指令前离域的 captured binding 仍走原词法窗口。
    let mut debug_exit_ends = BTreeMap::<usize, BTreeSet<Reg>>::new();
    for fact in structure.debug_bindings().accepted() {
        if let Some(end) = fact.end_instr
            && proto.debug_locals[fact.scope].is_source()
            && dataflow.reg_is_reference_captured(fact.reg)
            && matches!(
                proto.instrs.get(end.index()),
                Some(LowInstr::Return(_) | LowInstr::TailCall(_))
            )
        {
            debug_exit_ends
                .entry(end.index())
                .or_default()
                .insert(fact.reg);
        }
    }
    // 每个 capture 只入队一次，Close 按槽范围退休组；内部条件不清空尚未关闭的 cell。
    // 候选在消费处核对支配与窗口边界，不为每条 Close 重扫历史 capture。
    let local_keys = captured_uses
        .iter()
        .filter(|captured| captured.requires_local)
        .map(|captured| captured.key)
        .collect::<BTreeSet<_>>();
    let captured_regs = dataflow.reference_captured_regs().collect::<Vec<_>>();
    // Lua 5.1 可省略入口 local 的 LOADNIL。只有确切的 Entry SSA 才能以入口
    // 作为初始化边界；未知 reaching value 仍不足以证明 cell 的词法起点。
    let mut entry_nil_last_reads = captured_uses
        .iter()
        .filter(|capture| {
            capture.key.epoch == 0
                && dataflow.use_value(InstrRef(capture.instr_index), capture.reg)
                    == SsaValue::Entry(capture.reg)
        })
        .map(|capture| (capture.key, 0))
        .collect::<BTreeMap<_, _>>();
    for (instr, uses) in dataflow.use_values.iter().enumerate() {
        for (_, value) in uses.fixed.iter() {
            if let SsaValue::Entry(reg) = value
                && let Some(last) =
                    entry_nil_last_reads.get_mut(&CapturedSlotKey::new(reg.index(), 0))
            {
                *last = instr;
            }
        }
    }
    // 合流 Entry 的所有后继读取尚未证明属于此窗口时，保留原入口 owner。
    for phi in plan
        .phis()
        .filter(|phi| phi_participates_in_normal_binding(phi))
    {
        for incoming in &phi.incomings {
            if phi_incoming_is_normal(incoming.disposition)
                && let SsaValue::Entry(reg) = incoming.value
            {
                entry_nil_last_reads.remove(&CapturedSlotKey::new(reg.index(), 0));
            }
        }
    }
    let mut pending = BTreeMap::<CapturedSlotKey, BTreeSet<usize>>::new();
    let mut capture_cursor = 0;
    let mut candidates = Vec::new();
    let mut activations = CapturedActivationWindows::new();
    for (close_instr, instr) in proto.instrs.iter().enumerate() {
        let close_block = cfg.instr_to_block[close_instr];
        while let Some(captured) = captured_uses.get(capture_cursor)
            && captured.instr_index == close_instr
        {
            pending
                .entry(captured.key)
                .or_default()
                .insert(captured.start_instr);
            capture_cursor += 1;
        }
        if matches!(instr, LowInstr::Return(_) | LowInstr::TailCall(_)) {
            // RETURN/TAILCALL 关闭整个 activation；不新增 do 或提前结束返回值、callee/参数准备。
            // 外层旧 cell 可以同时存在，逐个核对新 cell 的声明支配本块全部捕获即可。
            for (key, slot_starts) in std::mem::take(&mut pending) {
                let &first = slot_starts
                    .first()
                    .expect("pending cell has an initializer");
                let Some(entry) = graph
                    .dominator_tree
                    .nearest_common_ancestor(cfg.instr_to_block[first], close_block)
                else {
                    continue;
                };
                // 条件初始化的首个 Def 只在一臂；cell 的激活窗口从共同控制头开始。
                // 下方闭合窗口与 phi 输入验证仍排除外部值、旁路入口和提前出口。
                let window_start = if entry == cfg.instr_to_block[first] {
                    first
                } else {
                    cfg.blocks[entry.index()].instrs.start.index()
                };
                let defs = dataflow.fixed_defs_for_reg(Reg(key.slot));
                let first_def =
                    defs.partition_point(|&def| dataflow.def_instr(def).index() < first);
                if local_keys.contains(&key)
                    // Entry/no-reaching 的 start 只是坐标，不是一次新 cell 初始化写。
                    // 它必须保留入口 owner，否则后续 Entry 读取会退化为 nil。
                    && dataflow.instr_def_for_reg(InstrRef(first), Reg(key.slot)).is_some()
                    && slot_starts.iter().all(|&start| {
                        start <= close_instr
                            && graph.dominates(entry, cfg.instr_to_block[start])
                    })
                    // 内部短路不结束 activation；跨块时仍须是共同发射域内的闭合窗口。
                    && (entry == close_block
                        || (emission.scope_owner(entry) == emission.scope_owner(close_block)
                            && graph.closed_instruction_window(cfg, window_start..close_instr + 1)))
                    && !epochs.reference_capture_may_be_open(Reg(key.slot), InstrRef(window_start))
                    // 内部合流不是 cell 逃逸；每个候选窗口一次验证完整 phi 闭包，
                    // 再由各 fixed Def 核对读取和出边，不逐 Def 重走 phi 图。
                    && let Some(closed_phis) = dataflow.closed_phis_in_instruction_window(
                        cfg, window_start..close_instr + 1, Reg(key.slot)..=Reg(key.slot),
                    )
                    && !defs[first_def..]
                        .iter()
                        .copied()
                        .take_while(|&def| dataflow.def_instr(def).index() <= close_instr)
                        .filter(|&def| {
                            epochs.epoch_at(Reg(key.slot), dataflow.def_instr(def)) == key.epoch
                        })
                        .any(|def| {
                            captured_definition_escapes(dataflow, def, window_start, close_instr + 1, Some(&closed_phis))
                        })
                {
                    activations
                        .entry(key)
                        .or_default()
                        .insert(window_start, close_instr + 1);
                }
            }
            continue;
        }
        let LowInstr::Close(close) = instr else {
            continue;
        };
        let paired_exit = match close.kind {
            crate::transformer::CloseKind::Return(source) => {
                source == InstrRef(close_instr + 1)
                    && matches!(proto.instrs.get(source.index()), Some(LowInstr::Return(_)))
            }
            crate::transformer::CloseKind::TailCall(source) => {
                source == InstrRef(close_instr + 1)
                    && matches!(
                        proto.instrs.get(source.index()),
                        Some(LowInstr::TailCall(_))
                    )
            }
            crate::transformer::CloseKind::Explicit => false,
        };
        if paired_exit
            && cfg.instr_to_block[close_instr + 1] == close_block
            && !debug_exit_ends
                .get(&(close_instr + 1))
                .is_some_and(|regs| regs.range(close.from..).next().is_some())
            && matches!(
                plan.cleanup_disposition(InstrRef(close_instr)),
                Some(CleanupDisposition::LexicalScope(_))
            )
        {
            // Transformer 已证明完整退出协议的关闭与返回配对；这里不能
            // 在传值前另造源码词法末端。TAILCALL 也先准备 callee/参数，再关闭原 cell；
            // 保留 pending，交给上面的原终结指令 activation。
            // TBC 的 ExplicitClose 不在此域，资源回调与返回值的先后仍由 cleanup owner 保证。
            continue;
        }
        let closed = pending.split_off(&CapturedSlotKey::new(close.from.index(), 0));
        if !matches!(
            plan.cleanup_disposition(InstrRef(close_instr)),
            Some(CleanupDisposition::LexicalScope(_))
        ) {
            continue;
        }
        let mut start = None;
        let mut exact = true;
        let mut closed_keys = Vec::new();
        for (key, slot_starts) in closed {
            if key.epoch != epochs.epoch_at(Reg(key.slot), InstrRef(close_instr)) {
                exact = false;
                break;
            }
            let &first = slot_starts
                .first()
                .expect("pending cell has a capture initializer");
            let entry_nil = entry_nil_last_reads.get(&key).is_some_and(|&last| {
                last < close_instr
                    && emission
                        .regular_prefix(cfg.instr_to_block[0])
                        .is_some_and(|range| range.contains(&0))
            });
            let first = if entry_nil { 0 } else { first };
            if (!entry_nil
                && dataflow
                    .instr_def_for_reg(InstrRef(first), Reg(key.slot))
                    .is_none())
                || slot_starts.iter().any(|&slot_start| {
                    slot_start >= close_instr
                        || !graph.dominates(cfg.instr_to_block[slot_start], close_block)
                })
                || epochs.reference_capture_may_be_open(Reg(key.slot), InstrRef(first))
            {
                exact = false;
                break;
            }
            // 后续重赋值仍使用已经打开的同一 cell；仅最早初始化之前必须没有旧捕获。
            let scope_start = if entry_nil {
                Some(0)
            } else if matches!(&proto.instrs[first], LowInstr::LoadNil(nil)
                if nil.dst.start < close.from && close.from.index() < nil.dst.start.index() + nil.dst.len)
            {
                // 同批 nil 没有求值事件；仅高槽属于关闭窗口，低槽原写仍在窗口外。
                // 在最终 scope 中发布分界，不能让整条 LOADNIL 吞掉外层声明。
                Some(first)
            } else {
                lexical_scope_evaluation_start(
                    proto,
                    dataflow,
                    cfg,
                    cfg.instr_to_block[first],
                    close.from,
                    first,
                )
            };
            let Some(scope_start) = scope_start else {
                exact = false;
                break;
            };
            start = Some(start.map_or(scope_start, |current: usize| current.min(scope_start)));
            // activation 是捕获身份事实，不以是否需要提前分配 LocalId 为条件。
            closed_keys.push(key);
        }
        if exact
            && let Some(start) = start
            // 内部条件不结束 cell 的词法窗口；跨块候选仍须是同一发射域内的闭合图区间。
            // 分支私有初始化不支配合流 CLOSE，外来入口或提前出口也不能并入窗口。
            && (cfg.instr_to_block[start] == close_block
                || (emission.scope_owner(cfg.instr_to_block[start]) == emission.scope_owner(close_block)
                    && emission.regular_prefix(cfg.instr_to_block[start]).is_some_and(|range| range.contains(&start))
                    && emission.regular_prefix(close_block).is_some_and(|range| range.contains(&close_instr))
                    && graph.closed_instruction_window(cfg, start..close_instr + 1)))
            // CLOSE 关闭整个后缀；不能遗漏从前驱传入、在本块没有再次 capture 的旧 cell。
            // 查询范围受 VM 固定槽数约束，不随闭包/声明总数增长。
            && captured_regs[captured_regs.partition_point(|reg| reg.index() < close.from.index())..]
                .iter().all(|&reg| !epochs.reference_capture_may_be_open(reg, InstrRef(start)))
            && let Some(closed_phis) = dataflow.closed_phis_in_instruction_window(
                cfg, start..close_instr, close.from..,
            )
            && !scope_window_local_def_escapes(
                dataflow,
                epochs,
                &local_keys,
                start,
                close_instr,
                close.from,
                &closed_phis,
            )
            && !scope_window_open_def_escapes(dataflow, start, close_instr, close.from)
        {
            let end = close_instr + 1;
            let initial_nil_floor = (matches!(&proto.instrs[start], LowInstr::LoadNil(nil)
                if nil.dst.start < close.from && close.from.index() < nil.dst.start.index() + nil.dst.len)
                || (start == 0 && closed_keys.iter().any(|key| entry_nil_last_reads.contains_key(key))))
                .then_some(close.from);
            for key in closed_keys {
                activations.entry(key).or_default().insert(start, end);
            }
            candidates.push(LexicalScope {
                start,
                end,
                initial_nil_floor,
            });
        }
    }
    (candidates, activations)
}

fn scope_window_local_def_escapes(
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    local_keys: &BTreeSet<CapturedSlotKey>,
    start: usize,
    close: usize,
    from: Reg,
    closed_phis: &BTreeSet<PhiId>,
) -> bool {
    (start..close)
        .flat_map(|instr| dataflow.instr_defs.get(instr).into_iter().flatten())
        .filter(|def| {
            let reg = dataflow.def_reg(**def);
            reg.index() >= from.index()
                && local_keys.contains(&CapturedSlotKey::new(
                    reg.index(),
                    epochs.epoch_at(reg, dataflow.def_instr(**def)),
                ))
        })
        .any(|def| captured_definition_escapes(dataflow, *def, start, close, Some(closed_phis)))
}

/// 绑定的原 fixed/phi 读取必须落在激活窗口；CLOSE 不含本条，RETURN 包含原返回读取。
fn captured_definition_escapes(
    dataflow: &DataflowFacts,
    def: DefId,
    start: usize,
    end: usize,
    closed_phis: Option<&BTreeSet<PhiId>>,
) -> bool {
    dataflow.def_uses.get(def.index()).is_none_or(|uses| {
        uses.iter()
            .any(|site| site.instr.index() < start || site.instr.index() >= end)
    }) || dataflow.def_phi_uses.get(def.index()).is_none_or(|uses| {
        uses.iter().any(|phi| {
            !dataflow.phi_is_truly_dead(*phi) && !closed_phis.is_some_and(|phis| phis.contains(phi))
        })
    })
}

fn scope_window_open_def_escapes(
    dataflow: &DataflowFacts,
    start: usize,
    close: usize,
    from: Reg,
) -> bool {
    let candidates = dataflow
        .open_defs
        .iter()
        .filter(|def| {
            (start..close).contains(&def.instr.index()) && def.start_reg.index() >= from.index()
        })
        .map(|def| def.id)
        .collect::<BTreeSet<_>>();
    if candidates.is_empty() {
        return false;
    }

    dataflow
        .instr_effects
        .iter()
        .enumerate()
        .filter(|(instr, effect)| !((start..close).contains(instr)) && effect.open_use.is_some())
        .any(|(instr, _)| {
            // 候选拒绝[SemanticBarrier:ValueArity]：块内 open producer 的动态尾包若由
            // Close 后的 call/return 消费，块边界不能把该 VM value pack 截断或根声明化。
            !dataflow
                .open_use_sources_at(InstrRef(instr))
                .defs()
                .is_disjoint(&candidates)
        })
}

pub(super) fn lexical_scope_evaluation_start(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    cfg: &Cfg,
    block: BlockRef,
    from: Reg,
    slot_start: usize,
) -> Option<usize> {
    // A source local's scope starts before its initializer, not at the result write. Recover the
    // complete fixed-register evaluation slice above `Close.from`; declining on phi/open inputs
    // or lower-slot writes prevents the new block from swallowing an outer lexical owner.
    let mut included = BTreeSet::from([slot_start]);
    let mut pending = vec![slot_start];
    while let Some(instr_index) = pending.pop() {
        let effect = dataflow.instr_effects.get(instr_index)?;
        if effect.open_use.is_some() || effect.open_must_def.is_some() {
            return None;
        }
        for &reg in effect.fixed_uses_from(from) {
            // local function 的自引用捕获的是本次写入的 cell，不读取旧函数值。
            // 这里只证明 ByReference cell 初始化；按值自捕获的独立结果身份另由 lowering 建立。
            if matches!(&proto.instrs[instr_index], LowInstr::Closure(closure)
                if closure.dst == reg && closure.captures.iter().all(|capture|
                    capture.source != CaptureSource::ByValue(reg)))
            {
                continue;
            }
            let SsaValue::Def(def) = dataflow.use_value(InstrRef(instr_index), reg) else {
                return None;
            };
            let dependency = dataflow.def_instr(def).index();
            if dependency >= instr_index || cfg.instr_to_block.get(dependency) != Some(&block) {
                return None;
            }
            if included.insert(dependency) {
                pending.push(dependency);
            }
        }
    }

    let earliest = included.iter().next().copied()?;
    for instr_index in earliest..=slot_start {
        let effect = dataflow.instr_effects.get(instr_index)?;
        if effect
            .fixed_must_defs()
            .iter()
            .any(|reg| reg.index() < from.index())
            || effect.open_use.is_some()
            || effect.open_must_def.is_some()
        {
            return None;
        }
        let touches_scope_window = effect
            .fixed_uses()
            .iter()
            .chain(effect.fixed_must_defs().iter())
            .any(|reg| reg.index() >= from.index());
        if !included.contains(&instr_index) && !touches_scope_window {
            return None;
        }
    }
    Some(earliest)
}

pub(super) fn captured_slot_declaration_region(
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    capture_instr: InstrRef,
    reg: Reg,
) -> Option<RegionId> {
    let SsaValue::Phi(phi_id) = dataflow.use_value(capture_instr, reg) else {
        return None;
    };
    let phi = plan.phi_plan(phi_id)?;
    let mut owner = None;
    for incoming in phi
        .incomings
        .iter()
        .filter(|incoming| phi_incoming_is_normal(incoming.disposition))
    {
        let region = match incoming.disposition {
            // RegionInput copy 在进入 region 的 edge 上执行；声明若放在 target region
            // prefix，会排在首次写入之后并把刚写入的 capture slot 重置为 nil。
            PhiIncomingDisposition::RegionInput(region) => {
                plan.region(region)?.parent().unwrap_or(plan.root())
            }
            PhiIncomingDisposition::RegionResult(region)
            | PhiIncomingDisposition::LoopCarried(region) => region,
            PhiIncomingDisposition::EdgeCopy => {
                let relation = plan.edge_region_relation(incoming.edge?)?;
                relation
                    .lca
                    .or(relation.source_owner)
                    .or(relation.target_owner)?
            }
            PhiIncomingDisposition::Dead | PhiIncomingDisposition::DiagnosticUnresolved => {
                continue;
            }
        };
        owner = Some(owner.map_or(region, |owner| {
            captured_slot_common_owner(plan, owner, region).unwrap_or(plan.root())
        }));
    }
    captured_slot_lexical_owner(plan, owner?)
}

pub(super) fn captured_slot_common_owner(
    plan: &StructurePlan,
    mut left: RegionId,
    right: RegionId,
) -> Option<RegionId> {
    loop {
        if plan.region_contains(left, right) {
            return Some(left);
        }
        left = plan.region(left)?.parent()?;
    }
}

pub(super) fn captured_slot_lexical_owner(
    plan: &StructurePlan,
    owner: RegionId,
) -> Option<RegionId> {
    let mut declaration = owner;
    let mut cursor = Some(owner);
    while let Some(region) = cursor {
        let parent = plan.region(region)?.parent();
        if plan.single_pass_for_region(region).is_some() {
            declaration = parent?;
        }
        cursor = parent;
    }
    Some(declaration)
}

pub(super) fn resolve_parent_writes_after_capture(
    cfg: &Cfg,
    graph: &GraphFacts,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    queries_by_key: &mut BTreeMap<CapturedSlotKey, CapturedSlotWriteQueries>,
    captured_uses: &mut [CapturedSlotUse],
) {
    if queries_by_key.is_empty() {
        return;
    }
    for def in &dataflow.defs {
        let key = CapturedSlotKey::new(def.reg.index(), epochs.epoch_at(def.reg, def.instr));
        let Some(queries) = queries_by_key.get_mut(&key) else {
            continue;
        };
        let Some(scc) = graph.scc_id(def.block) else {
            continue;
        };
        queries
            .defs
            .entry(scc)
            .and_modify(|last| *last = (*last).max(def.instr.index()))
            .or_insert(def.instr.index());
    }

    let mut reached = vec![0; graph.scc_count()];
    let mut pending = Vec::new();
    for (index, queries) in queries_by_key.values().enumerate() {
        let Some(first_capture) = queries
            .uses
            .iter()
            .filter_map(|&index| graph.scc_id(cfg.instr_to_block[captured_uses[index].instr_index]))
            .min()
        else {
            continue;
        };
        // 每个 slot/epoch 只反向传播一次“存在后续写”。SCC 拓扑下界排除最早
        // capture 之前的无关前缀；一张时间戳 arena 复用，不保存 SCC×SCC 传递闭包。
        // 同 SCC 的指令次序另查最后写入，不能把无环块中 capture 前的写算作未来写。
        let stamp = index + 1;
        for (&scc, _) in queries.defs.range(first_capture..) {
            pending.extend_from_slice(graph.scc_predecessors(scc));
        }
        while let Some(scc) = pending.pop() {
            if scc < first_capture || reached[scc.index()] == stamp {
                continue;
            }
            reached[scc.index()] = stamp;
            pending.extend_from_slice(graph.scc_predecessors(scc));
        }
        for &use_index in &queries.uses {
            let captured = &mut captured_uses[use_index];
            let block = cfg.instr_to_block[captured.instr_index];
            captured.requires_local = graph.scc_id(block).is_some_and(|scc| {
                reached[scc.index()] == stamp
                    || queries.defs.get(&scc).is_some_and(|&last| {
                        last > captured.instr_index || graph.block_is_cyclic(block)
                    })
            });
        }
    }
}

fn captured_debug_initializer(
    proto: &LoweredProto,
    structure: &ReadyStructureFacts,
    dataflow: &DataflowFacts,
    instr: usize,
    reg: Reg,
) -> Option<usize> {
    let hint = debug_local_hint_for_reg_at_instr(proto, reg, InstrRef(instr))?;
    let fact = structure.debug_bindings().for_scope(hint.scope)?;
    let SsaValue::Def(def) = fact.value.ssa()? else {
        return None;
    };
    (fact.reg == reg).then(|| dataflow.def_instr(def).index())
}

pub(super) fn captured_slot_start_instr(
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    capture_instr: InstrRef,
    reg: Reg,
    has_no_reaching_value: bool,
    workspace: &mut CapturedSlotStartWorkspace,
) -> usize {
    if has_no_reaching_value {
        return capture_instr.index();
    }

    let mut earliest = None;
    workspace.begin(dataflow.use_value(capture_instr, reg));
    while let Some(value) = workspace.pending.pop() {
        match value {
            SsaValue::Entry(_) => {}
            SsaValue::Def(def) => {
                let instr = dataflow.def_instr(def).index();
                earliest = Some(earliest.map_or(instr, |current: usize| current.min(instr)));
            }
            SsaValue::Phi(phi_id) => {
                if !workspace.visit(phi_id) {
                    continue;
                }
                if let Some(phi) = plan.phi_plan(phi_id) {
                    workspace.pending.extend(
                        phi.incomings
                            .iter()
                            .filter(|incoming| phi_incoming_is_normal(incoming.disposition))
                            .map(|incoming| incoming.value),
                    );
                }
            }
        }
    }
    earliest.unwrap_or(capture_instr.index())
}

pub(super) fn capture_has_no_reaching_value(
    dataflow: &DataflowFacts,
    instr_ref: InstrRef,
    reg: Reg,
) -> bool {
    dataflow
        .use_values_at(instr_ref)
        .get(reg)
        .is_none_or(|value| matches!(value, crate::structure::SsaValue::Entry(_)))
}
