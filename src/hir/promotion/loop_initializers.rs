//! 从原数值及泛型循环的固定低槽写证明循环外 nil 声明批次的归属。
//! 初始化、每次写入和分支 phi 保留独立身份，不伪造跨迭代的唯一覆盖前驱。

use super::*;

#[derive(Debug, Clone)]
pub(super) struct LoopInitializers {
    pub(super) temps: Vec<TempId>,
    pub(super) owners: Vec<(HomeSlotKey, BTreeSet<TempId>)>,
}

#[expect(
    clippy::too_many_arguments,
    reason = "共用冻结的循环、SSA 与物理槽事实"
)]
pub(super) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
) -> BTreeMap<NativeLoopInitializerHeader, Vec<LoopInitializers>> {
    let forest = graph.natural_loop_forest();
    let mut phis = BTreeMap::<_, BTreeMap<Reg, BTreeSet<TempId>>>::new();
    for phi in &dataflow.phi_candidates {
        if let Some(owner) = forest.innermost_loop(phi.block) {
            phis.entry(owner)
                .or_default()
                .entry(phi.reg)
                .or_default()
                .insert(phi_temps[phi.id.index()]);
        }
    }
    let mut seen = BTreeSet::new();
    let mut result = BTreeMap::<_, Vec<_>>::new();
    for (id, _) in plan.loops() {
        let (header, control_base, init, latch, preheader, loop_header) = match plan
            .loop_protocol(id)
        {
            Some(LoopVmProtocol::NumericFor(protocol)) => {
                let Some(latch) = protocol.loop_instr else {
                    continue;
                };
                let header = NativeNumericForHeader {
                    homes: [protocol.index, protocol.limit, protocol.step].map(|reg| {
                        HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, protocol.init_instr))
                    }),
                    values: [protocol.index, protocol.limit, protocol.step].map(|reg| {
                        canonical_value_temp(
                            dataflow.use_value(protocol.init_instr, reg),
                            dataflow.defs.len(),
                            fixed_temps,
                            phi_temps,
                        )
                    }),
                };
                (
                    NativeLoopInitializerHeader::Numeric(header),
                    [protocol.index, protocol.limit, protocol.step]
                        .into_iter()
                        .map(Reg::index)
                        .min()
                        .unwrap(),
                    protocol.init_instr,
                    latch,
                    cfg.instr_to_block[protocol.init_instr.index()],
                    cfg.edges[protocol.body_edge.index()].to,
                )
            }
            Some(LoopVmProtocol::GenericFor(protocol)) => {
                let loop_header = cfg.instr_to_block[protocol.call_instr.index()];
                let mut entries = cfg.preds[loop_header.index()].iter().filter_map(|edge| {
                    let from = cfg.edges[edge.index()].from;
                    (cfg.reachable_blocks.contains(&from) && !graph.dominates(loop_header, from))
                        .then_some(from)
                });
                let Some(preheader) = entries.next() else {
                    continue;
                };
                if entries.any(|other| other != preheader) {
                    // 候选拒绝[ProofIncomplete:ControlFlow]：原 nil 到达多个入口的关系尚未冻结。
                    continue;
                }
                let Some(init) = cfg.blocks[preheader.index()]
                    .instrs
                    .end()
                    .checked_sub(1)
                    .map(InstrRef)
                else {
                    continue;
                };
                (
                    NativeLoopInitializerHeader::Generic(protocol.call_instr),
                    protocol.iterator.start.index(),
                    init,
                    protocol.loop_instr,
                    preheader,
                    loop_header,
                )
            }
            _ => continue,
        };
        let Some(owner) = forest.loop_for_header(loop_header) else {
            continue;
        };
        // 候选拒绝[ProofIncomplete:ControlFlow]：嵌套循环的低槽身份另有归属，
        // 不把其写复制给祖先；每个直接 block 至多分析一次。
        if !seen.insert(owner) || forest.children_of(owner).next().is_some() {
            continue;
        }
        let mut writes = BTreeMap::<Reg, (BTreeSet<HomeSlotKey>, BTreeSet<TempId>)>::new();
        let mut open_floor = None;
        for &block in forest.direct_blocks(owner) {
            let range = cfg.blocks[block.index()].instrs;
            for index in range.start.index()..range.end() {
                if let Some(reg) = dataflow.instr_effects[index].open_must_def {
                    open_floor =
                        Some(open_floor.map_or(reg.index(), |old: usize| old.min(reg.index())));
                }
                for &def in &dataflow.instr_defs[index] {
                    let reg = dataflow.def_reg(def);
                    if reg.index() < control_base {
                        let (homes, versions) = writes.entry(reg).or_default();
                        homes.insert(HomeSlotKey::new(
                            reg.index(),
                            epochs.epoch_at(reg, InstrRef(index)),
                        ));
                        versions.insert(fixed_temps[def.index()]);
                    }
                }
            }
        }
        let groups = writes
            .keys()
            .filter_map(|&reg| {
                let initial = dataflow.last_fixed_def_in_range(reg, 0..init.index())?;
                let site = dataflow.def_instr(initial);
                matches!(proto.instrs[site.index()], LowInstr::LoadNil(_)).then_some(site)
            })
            .collect::<BTreeSet<_>>();
        for site in groups {
            let definitions = &dataflow.instr_defs[site.index()];
            let mut owners = Vec::with_capacity(definitions.len());
            for &initial in definitions {
                let reg = dataflow.def_reg(initial);
                let temp = TempId(initial.index());
                let home = HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, site));
                if reg.index() >= control_base
                    || dataflow.last_fixed_def_in_range(reg, 0..init.index()) != Some(initial)
                {
                    // 候选拒绝[ProofIncomplete]：完整批次成员不能已属于另一次初始化。
                    break;
                }
                let (homes, mut versions) = writes.remove(&reg).unwrap_or_default();
                if !graph.dominates(cfg.instr_to_block[site.index()], preheader)
                    || dataflow
                        .first_must_write_in_range(reg, site.index() + 1..init.index())
                        .is_some()
                    || dataflow
                        .first_close_in_range(reg, site.index() + 1..latch.index() + 1)
                        .is_some()
                    || open_floor.is_some_and(|floor| floor <= reg.index())
                    || dataflow.reg_is_captured(reg)
                    || fixed_temps[initial.index()] != temp
                    || !dataflow.def_uses[initial.index()].is_empty()
                    || !dataflow.def_phi_uses[initial.index()].is_empty()
                    || reg.index() < usize::from(proto.signature.num_params)
                    || proto.signature.has_vararg_param_reg
                        && reg.index() == usize::from(proto.signature.num_params)
                    || !homes.is_empty() && !homes.iter().copied().eq([home])
                {
                    // 候选拒绝[ProofIncomplete]：原 nil 必须仍到达循环入口；开放写、
                    // CLOSE、捕获及旧值读取不能仅凭低槽写归并为一个外层声明。
                    break;
                }
                if let Some(phi_versions) = phis.get(&owner).and_then(|phis| phis.get(&reg)) {
                    versions.extend(phi_versions.iter().copied());
                }
                // 无写版本的成员仍保留原 nil 槽；后层只原位物化它，不与其它声明合并。
                owners.push((home, versions));
            }
            if owners.len() != definitions.len() {
                continue;
            }
            let temps = definitions.iter().map(|def| TempId(def.index())).collect();
            result
                .entry(header)
                .or_default()
                .push(LoopInitializers { temps, owners });
        }
    }
    result
}
