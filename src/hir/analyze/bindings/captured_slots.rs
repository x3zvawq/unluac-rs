//! 收集闭包捕获槽目标、声明区域与 capture 后写入；依赖 CFG、slot epoch 和 region tree，
//! 不负责 temp 映射；loop body 块直接借用 Structure 的 containment 索引；例如把同一槽
//! 的不同时代分成独立 local。capture 后写入按 slot/epoch 批量消费 GraphFacts 的 SCC
//! 拓扑与前驱；例如无环块内先写后捕获不需要写回，回边上的同一次静态写则可能再次执行。

use super::*;
use crate::structure::SccId;

pub(super) struct CapturedSlotTargets {
    pub(super) slot_targets: BTreeMap<CapturedSlotKey, CapturedSlotBinding>,
    pub(super) capture_targets: BTreeMap<(usize, usize), LocalId>,
    pub(super) lexical_scopes: Vec<std::ops::Range<usize>>,
    pub(super) entry_local_decls: Vec<LocalId>,
    pub(super) region_local_decls: BTreeMap<RegionId, Vec<LocalId>>,
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
        epochs,
        child_mutable_upvalues,
        numeric_binding_phis,
    } = inputs;
    let mut slot_targets = BTreeMap::<CapturedSlotKey, CapturedSlotBinding>::new();
    let mut capture_targets = BTreeMap::new();
    let mut captured_uses = Vec::new();
    let mut loop_owned_slots = BTreeSet::new();
    for (loop_id, loop_plan) in structure.plan().loops() {
        let Some(body_blocks) = loop_body_region(structure.plan(), loop_id)
            .map(|body| structure.plan().region_blocks(body))
        else {
            continue;
        };
        for &block in body_blocks {
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
            for value in &loop_plan.header_values {
                if matches!(
                    loop_plan.source_bindings,
                    Some(LoopSourceBindings::Numeric(binding)) if value.reg == binding
                ) {
                    continue;
                }
                loop_owned_slots.insert((block, value.reg));
            }
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
            let CaptureSource::ByReference(reg) = capture.source else {
                continue;
            };
            if reg == closure.dst
                || reg.index() < usize::from(proto.signature.num_params)
                || entry_local_regs.contains_key(&reg)
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
            let entry_local_safe = epochs.spans_entry(reg);
            let key =
                CapturedSlotKey::new(reg.index(), epochs.epoch_at(reg, InstrRef(start_instr)));
            let child_writes = child_mutable_upvalues
                .get(closure.proto.index())
                .and_then(|mutable| mutable.get(capture_index))
                .copied()
                .unwrap_or(false);
            let requires_local = child_writes || has_no_reaching_value;
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
    let lexical_scopes = collect_lexical_close_scopes(
        proto,
        cfg,
        dataflow,
        structure.plan(),
        epochs,
        &captured_uses,
    );
    for captured in &captured_uses {
        entry_safe_by_key
            .entry(captured.key)
            .and_modify(|safe| *safe &= captured.entry_local_safe)
            .or_insert(captured.entry_local_safe);
        if captured.requires_local
            && captured.entry_local_safe
            && graph.block_is_cyclic(cfg.instr_to_block[captured.instr_index])
        {
            entry_decl_keys.insert(captured.key);
        }
        if captured.requires_local
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

    for captured in captured_uses
        .iter()
        .filter(|captured| captured.requires_local)
    {
        let target = if let Some(binding) = slot_targets.get_mut(&captured.key) {
            binding.start_instr = binding.start_instr.min(captured.start_instr);
            binding.target
        } else {
            let local = LocalId(*local_count);
            *local_count += 1;
            local_debug_hints.push(debug_local_name_for_reg_at_instr(
                proto,
                captured.reg,
                InstrRef(captured.instr_index),
            ));
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
    CapturedSlotTargets {
        slot_targets,
        capture_targets,
        lexical_scopes,
        entry_local_decls,
        region_local_decls,
    }
}

fn collect_lexical_close_scopes(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    epochs: &SlotEpochFacts,
    captured_uses: &[CapturedSlotUse],
) -> Vec<std::ops::Range<usize>> {
    let mut starts_by_key = BTreeMap::<CapturedSlotKey, BTreeSet<usize>>::new();
    let local_keys = captured_uses
        .iter()
        .filter(|captured| captured.requires_local)
        .map(|captured| captured.key)
        .collect::<BTreeSet<_>>();
    for captured in captured_uses {
        starts_by_key
            .entry(captured.key)
            .or_default()
            .insert(captured.start_instr);
    }

    let mut candidates = Vec::new();
    for (close_instr, instr) in proto.instrs.iter().enumerate() {
        let LowInstr::Close(close) = instr else {
            continue;
        };
        if !matches!(
            plan.cleanup_disposition(InstrRef(close_instr)),
            Some(CleanupDisposition::LexicalScope(_))
        ) {
            continue;
        }
        let close_block = cfg.instr_to_block[close_instr];
        let mut start = None;
        let mut exact = true;
        for (key, slot_starts) in &starts_by_key {
            if key.slot < close.from.index()
                || key.epoch != epochs.epoch_at(Reg(key.slot), InstrRef(close_instr))
            {
                continue;
            }
            for &slot_start in slot_starts {
                if slot_start >= close_instr || cfg.instr_to_block[slot_start] != close_block {
                    exact = false;
                    break;
                }
                let Some(scope_start) = lexical_scope_evaluation_start(
                    dataflow,
                    cfg,
                    close_block,
                    close.from,
                    slot_start,
                ) else {
                    exact = false;
                    break;
                };
                start = Some(start.map_or(scope_start, |current: usize| current.min(scope_start)));
            }
            if !exact {
                break;
            }
        }
        if exact
            && let Some(start) = start
            && !scope_window_local_def_escapes(
                dataflow,
                epochs,
                &local_keys,
                start,
                close_instr,
                close.from,
            )
            && !scope_window_open_def_escapes(dataflow, start, close_instr, close.from)
        {
            candidates.push(start..close_instr + 1);
        }
    }

    candidates
}

fn scope_window_local_def_escapes(
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    local_keys: &BTreeSet<CapturedSlotKey>,
    start: usize,
    close: usize,
    from: Reg,
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
        .any(|def| {
            // 候选拒绝[SemanticBarrier:Scope]：`requires_local` 的精确 slot epoch 会在
            // 窗口内降低成 LocalDecl；若其 def/phi use 逃到 Close 后，提前结束词法块会
            // 让 `Close r0; return r0` 的读取失去同一 binding（regress342）。不属于这些
            // key 的 fixed def 仍是函数级 TempId，跨 HIR Block handoff 不改变身份
            // （regress154）。
            dataflow.def_uses.get(def.index()).is_none_or(|uses| {
                uses.iter()
                    .any(|site| site.instr.index() < start || site.instr.index() >= close)
            }) || dataflow
                .def_phi_uses
                .get(def.index())
                .is_none_or(|uses| uses.iter().any(|phi| !dataflow.phi_is_truly_dead(*phi)))
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
