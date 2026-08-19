//! 收集闭包捕获槽目标、声明区域与 capture 后写入；依赖 CFG、slot epoch 和 region tree，不负责 temp 映射；例如把同一槽的不同时代分成独立 local。

use super::*;

pub(super) struct CapturedSlotTargets {
    pub(super) slot_targets: BTreeMap<CapturedSlotKey, CapturedSlotBinding>,
    pub(super) capture_targets: BTreeMap<(usize, usize), BoundSlotTarget>,
    pub(super) entry_local_decls: Vec<LocalId>,
    pub(super) region_local_decls: BTreeMap<RegionId, Vec<LocalId>>,
}

#[derive(Debug, Clone, Copy)]
pub(super) struct CapturedSlotBinding {
    pub(super) target: BoundSlotTarget,
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
    defs: Vec<(usize, BlockRef)>,
}

pub(super) struct CapturedSlotWriteWorkspace {
    epoch: usize,
    def_epoch: Vec<usize>,
    last_def_instr: Vec<usize>,
    def_blocks: Vec<BlockRef>,
    reach_epoch: Vec<usize>,
    pending: VecDeque<BlockRef>,
}

impl CapturedSlotWriteWorkspace {
    pub(super) fn new(block_count: usize) -> Self {
        Self {
            epoch: 0,
            def_epoch: vec![0; block_count],
            last_def_instr: vec![0; block_count],
            def_blocks: Vec::new(),
            reach_epoch: vec![0; block_count],
            pending: VecDeque::new(),
        }
    }

    pub(super) fn analyze(&mut self, cfg: &Cfg, defs: &[(usize, BlockRef)]) {
        self.begin();
        for &(instr_index, block) in defs {
            if !cfg.reachable_blocks.contains(&block) {
                continue;
            }
            if self.def_epoch[block.index()] != self.epoch {
                self.def_epoch[block.index()] = self.epoch;
                self.last_def_instr[block.index()] = instr_index;
                self.def_blocks.push(block);
            } else {
                self.last_def_instr[block.index()] =
                    self.last_def_instr[block.index()].max(instr_index);
            }
        }

        // Def block 本身不是 seed：从 predecessor 开始才表示“至少经过一条边”。
        // 这使同块且位于 capture 之前的 def 只有在真实回路中才会命中。
        for index in 0..self.def_blocks.len() {
            let def_block = self.def_blocks[index];
            for edge_ref in &cfg.preds[def_block.index()] {
                self.enqueue(cfg, cfg.edges[edge_ref.index()].from);
            }
        }
        while let Some(block) = self.pending.pop_front() {
            for edge_ref in &cfg.preds[block.index()] {
                self.enqueue(cfg, cfg.edges[edge_ref.index()].from);
            }
        }
    }

    pub(super) fn has_write_after(&self, cfg: &Cfg, capture_instr: usize) -> bool {
        let block = cfg.instr_to_block[capture_instr];
        // Closure 只定义 dst，且收集阶段已排除 dst 自捕获，所以不存在同指令
        // 定义 capture reg 的 equality 形状；若 Closure effect 改为多定义，必须重审此谓词。
        cfg.reachable_blocks.contains(&block)
            && ((self.def_epoch[block.index()] == self.epoch
                && self.last_def_instr[block.index()] > capture_instr)
                || self.reach_epoch[block.index()] == self.epoch)
    }

    pub(super) fn begin(&mut self) {
        if self.epoch == usize::MAX {
            self.def_epoch.fill(0);
            self.reach_epoch.fill(0);
            self.epoch = 1;
        } else {
            self.epoch += 1;
        }
        self.def_blocks.clear();
        self.pending.clear();
    }

    pub(super) fn enqueue(&mut self, cfg: &Cfg, block: BlockRef) {
        if cfg.reachable_blocks.contains(&block) && self.reach_epoch[block.index()] != self.epoch {
            self.reach_epoch[block.index()] = self.epoch;
            self.pending.push_back(block);
        }
    }
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
    pub(super) structure: &'a StructureFacts,
    pub(super) epochs: &'a SlotEpochFacts,
    pub(super) child_mutable_upvalues: &'a [Vec<bool>],
    pub(super) numeric_binding_phis: &'a [bool],
}

pub(super) fn collect_captured_slot_targets(
    inputs: CapturedSlotInputs<'_>,
    entry_local_regs: &mut BTreeMap<Reg, LocalId>,
    locals: &mut Vec<LocalId>,
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
        let Some(body) = loop_body_region(structure.plan(), loop_id) else {
            continue;
        };
        for block in region_blocks(structure.plan(), body) {
            match loop_plan.source_bindings {
                Some(LoopSourceBindings::Numeric(_)) => {}
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
        dataflow,
        epochs,
        &mut write_queries,
        &mut captured_uses,
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
            let local = LocalId(locals.len());
            locals.push(local);
            local_debug_hints.push(debug_local_name_for_reg_at_instr(
                proto,
                captured.reg,
                InstrRef(captured.instr_index),
            ));
            let target = BoundSlotTarget::Local(local);
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
            let BoundSlotTarget::Local(local) = target;
            entry_local_regs.entry(captured.reg).or_insert(local);
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
        .map(|binding| {
            let BoundSlotTarget::Local(local) = binding.target;
            local
        })
        .collect();
    let mut region_local_decls = BTreeMap::<RegionId, Vec<LocalId>>::new();
    for (key, region) in region_decl_keys {
        let Some(binding) = slot_targets.get(&key) else {
            continue;
        };
        let BoundSlotTarget::Local(local) = binding.target;
        region_local_decls.entry(region).or_default().push(local);
    }
    CapturedSlotTargets {
        slot_targets,
        capture_targets,
        entry_local_decls,
        region_local_decls,
    }
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
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    queries_by_key: &mut BTreeMap<CapturedSlotKey, CapturedSlotWriteQueries>,
    captured_uses: &mut [CapturedSlotUse],
) {
    for def in &dataflow.defs {
        let key = CapturedSlotKey::new(def.reg.index(), epochs.epoch_at(def.reg, def.instr));
        let Some(queries) = queries_by_key.get_mut(&key) else {
            continue;
        };
        let instr_index = def.instr.index();
        queries
            .defs
            .push((instr_index, cfg.instr_to_block[instr_index]));
    }

    let mut workspace = CapturedSlotWriteWorkspace::new(cfg.blocks.len());
    for queries in queries_by_key.values() {
        workspace.analyze(cfg, &queries.defs);
        for &use_index in &queries.uses {
            let captured = &mut captured_uses[use_index];
            captured.requires_local = workspace.has_write_after(cfg, captured.instr_index);
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
