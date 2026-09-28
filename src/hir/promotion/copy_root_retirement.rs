//! 为独立 COPY holder 证明跨控制流的物理根退休时序。
//!
//! 消费 CFG、Dataflow 写集合与 RootObservation，区分求值前后覆盖责任。

use super::*;

#[derive(Clone, Debug, Default)]
pub(super) struct CopyRootRetirements {
    pub(super) producers: BTreeSet<TempId>,
    /// 已有原始定义支配退休写的值；保留结束写，但不需要入口 nil holder。
    pub(super) defined_sources: BTreeSet<TempId>,
    pub(super) releases: BTreeMap<InstrRef, Vec<TempId>>,
    pub(super) after_releases: BTreeMap<InstrRef, Vec<TempId>>,
    pub(super) boundaries: BTreeSet<InstrRef>,
}

impl CopyRootRetirements {
    pub(super) fn collect(
        proto: &LoweredProto,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
        fixed_temps: &[TempId],
        debug_scopes: &[Option<usize>],
        mut emitted: impl FnMut(InstrRef) -> bool,
        for_instr: impl Fn(InstrRef) -> bool,
    ) -> Self {
        let mut facts = Self::default();
        let mut by_home = BTreeMap::<Reg, Vec<(TempId, InstrRef)>>::new();
        for def in &dataflow.defs {
            let temp = TempId(def.id.index());
            if fixed_temps.get(def.id.index()) != Some(&temp)
                || !emitted(def.instr)
                || !dataflow.def_phi_uses[def.id.index()].is_empty()
                || dataflow.reg_is_reference_captured(def.reg)
                || !matches!(&proto.instrs[def.instr.index()], LowInstr::Move(move_)
                    if move_.src != move_.dst)
            {
                continue;
            }
            if let LowInstr::Move(copy) = proto.instrs[def.instr.index()]
                && let SsaValue::Def(source) = dataflow.use_value(def.instr, copy.src)
                && !dataflow.reg_is_reference_captured(dataflow.def_reg(source))
                && matches!(
                    proto.instrs[dataflow.def_instr(source).index()],
                    LowInstr::LoadNil(_)
                        | LowInstr::LoadBool(_)
                        | LowInstr::LoadConst(_)
                        | LowInstr::LoadInteger(_)
                        | LowInstr::LoadNumber(_)
                )
            {
                // 原 COPY 仍由求值帧消费；常量及常量池持有的值没有独立栈根寿命，
                // 不为跨循环的常量副本制造额外 holder 和 nil 退休写。
                continue;
            }
            by_home.entry(def.reg).or_default().push((temp, def.instr));
        }
        for (home, candidates) in by_home {
            for (temp, producer, releases) in
                retirement_points(proto, cfg, dataflow, home, &candidates)
            {
                let def = &dataflow.defs[temp.index()];
                if dataflow.def_overwrites_unknown_scratch(def.id)
                    && releases.iter().all(|release| {
                        release.instr.index() > producer.index()
                            && cfg.instr_to_block[release.instr.index()] == def.block
                    })
                {
                    // 同块 COPY 的写入还负责清除 CALL 残值，不能改为函数入口的额外
                    // home-free holder；它会抬高实际槽序。交给共享 scalar root owner，
                    // 由 scratch 覆盖事实保留原写入及同 home 终点，而非另造保活槽。
                    continue;
                }
                if !releases.iter().all(|release| emitted(release.instr))
                    // Entry 参数没有可交接的 producer 表达式，必须在此保存匿名快照。
                    // Def 值由后续表达式/root owner 复核；for 操作数由循环协议保有，
                    // 普通退休 owner 不能另造 holder 阻止该协议的值与生命周期合并。
                    || (releases.iter().any(|release| release.after)
                        && (debug_scopes[temp.index()].is_some()
                            || dataflow.def_uses[temp.index()].iter().any(|site| for_instr(site.instr))
                            || !matches!(dataflow.canonical_move_value(SsaValue::Def(dataflow.defs[temp.index()].id)),
                                Some(SsaValue::Entry(reg)) if reg.index() < usize::from(proto.signature.num_params))))
                {
                    continue;
                }
                facts.producers.insert(temp);
                facts.boundaries.insert(producer);
                for release in releases {
                    facts.boundaries.insert(release.instr);
                    let points = if release.after {
                        &mut facts.after_releases
                    } else {
                        &mut facts.releases
                    };
                    points.entry(release.instr).or_default().push(temp);
                }
            }
        }
        // 不同 home 的求解顺序不改变同一释放点原有的 Def/Temp 顺序。
        for producers in facts
            .releases
            .values_mut()
            .chain(facts.after_releases.values_mut())
        {
            producers.sort_unstable();
        }
        facts
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct RetirementPoint {
    instr: InstrRef,
    after: bool,
}

#[derive(Default)]
struct BlockSummary {
    valid: bool,
    observed: bool,
    backedge: bool,
    release: Option<RetirementPoint>,
    successors: Vec<BlockRef>,
}

fn summarize_block(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    block: BlockRef,
    start: usize,
    home: Reg,
) -> Option<BlockSummary> {
    let range = cfg.blocks.get(block.index())?.instrs;
    let mut summary = BlockSummary {
        valid: true,
        ..Default::default()
    };
    let overwrite = dataflow.first_must_write_in_range(home, start..range.end());
    let close = dataflow.first_close_in_range(home, start..range.end());
    let stop = overwrite
        .into_iter()
        .chain(close)
        .map(|instr| instr.index())
        .min()
        .unwrap_or(range.end());
    // 不同 home 共用 Dataflow 区间事实，不逐槽重扫同一长块；覆盖本条另判写回时序。
    if let Some(prefix) = dataflow.minimum_rooted_prefix(start..stop) {
        if home.index() >= prefix {
            // 候选拒绝[SemanticBarrier:Lifetime]：前缀外的旧槽不能跨观察继续保活（regress_416）。
            return None;
        }
        summary.observed = true;
    }
    if overwrite == Some(InstrRef(stop)) {
        let instr = &proto.instrs[stop];
        // 无观察的常量或异槽 NOT 可在写入点退休旧根；NOT 不调用元方法，
        // 但原位 NOT 仍读取旧值，不能先清空它的输入。CALL/MOVE 另有交接协议。
        let pure = (matches!(
            instr,
            LowInstr::LoadNil(_)
                | LowInstr::LoadBool(_)
                | LowInstr::LoadConst(_)
                | LowInstr::LoadInteger(_)
                | LowInstr::LoadNumber(_)
        ) || matches!(instr, LowInstr::UnaryOp(unary)
            if unary.op == crate::transformer::UnaryOpKind::Not && unary.src != home))
            && !dataflow.effect_summaries[stop].may_observe_gc_roots();
        // 这些固定结果指令先执行完整求值（含 metamethod），然后才写回目标。
        // CALL 的栈顶/参数交接不同，不能据此推导它的退休时刻。
        let after = !pure
            && matches!(
                instr,
                LowInstr::GetTable(_) | LowInstr::BinaryOp(_) | LowInstr::UnaryOp(_)
            )
            && dataflow.effect_summaries[stop]
                .root_observation
                .keeps_home_rooted(home);
        if !pure && !after {
            return None;
        }
        summary.observed |= after;
        summary.release = Some(RetirementPoint {
            instr: InstrRef(stop),
            after,
        });
        return Some(summary);
    }
    if close == Some(InstrRef(stop)) {
        return None;
    }
    if range.last().is_some_and(|last| {
        dataflow.effect_summaries[last.index()].root_observation == RootObservation::FrameExit
    }) {
        // frame 退出是安全终点；收益由全部路径统一汇总，不依赖分支访问顺序。
        return Some(summary);
    }
    summary.successors = copy_root_cfg_successors(cfg, block)?;
    summary.backedge = summary
        .successors
        .iter()
        .any(|successor| cfg.blocks[successor.index()].instrs.start.index() < range.end());
    Some(summary)
}

#[derive(Clone, Copy, Default)]
struct SolvedComponent {
    valid: bool,
    observed: bool,
    backedge: bool,
    observed_overwrite: bool,
    retirement: Option<usize>,
}

struct RetirementNode {
    releases: Vec<RetirementPoint>,
    children: Vec<usize>,
}

#[derive(Default)]
struct RetirementDag {
    nodes: Vec<RetirementNode>,
}

impl RetirementDag {
    fn join(&mut self, releases: Vec<RetirementPoint>, children: BTreeSet<usize>) -> Option<usize> {
        if releases.is_empty() {
            match children.len() {
                0 => return None,
                1 => return children.first().copied(),
                _ => {}
            }
        }
        let id = self.nodes.len();
        self.nodes.push(RetirementNode {
            releases,
            children: children.into_iter().collect(),
        });
        Some(id)
    }

    fn expand(
        self,
        requests: Vec<(TempId, InstrRef, BTreeSet<usize>)>,
    ) -> Vec<(TempId, InstrRef, Vec<RetirementPoint>)> {
        let mut reads = vec![0usize; self.nodes.len()];
        let mut pending = Vec::new();
        for (_, _, roots) in &requests {
            for &root in roots {
                if reads[root] == 0 {
                    pending.push(root);
                }
                reads[root] += 1;
            }
        }
        while let Some(id) = pending.pop() {
            for &child in &self.nodes[id].children {
                if reads[child] == 0 {
                    pending.push(child);
                }
                reads[child] += 1;
            }
        }

        let mut values = vec![None; self.nodes.len()];
        // SCC 逆序发布 DAG，子节点 ID 总在父节点之前；只求实际候选需要的节点。
        for (id, node) in self.nodes.into_iter().enumerate() {
            if reads[id] == 0 {
                continue;
            }
            let mut result = node.releases.into_iter().collect::<BTreeSet<_>>();
            for child in node.children {
                merge_retirements(&mut result, child, &mut reads, &mut values);
            }
            values[id] = Some(result);
        }
        requests
            .into_iter()
            .map(|(temp, instr, roots)| {
                let mut result = BTreeSet::new();
                for root in roots {
                    merge_retirements(&mut result, root, &mut reads, &mut values);
                }
                (temp, instr, result.into_iter().collect())
            })
            .collect()
    }
}

fn merge_retirements(
    result: &mut BTreeSet<RetirementPoint>,
    source: usize,
    reads: &mut [usize],
    values: &mut [Option<BTreeSet<RetirementPoint>>],
) {
    reads[source] -= 1;
    if reads[source] == 0 {
        let mut value = values[source]
            .take()
            .expect("retirement DAG child is evaluated before its last reader");
        if value.len() > result.len() {
            std::mem::swap(result, &mut value);
        }
        result.extend(value);
    } else {
        result.extend(
            values[source]
                .as_ref()
                .expect("retirement DAG retains values until their last reader")
                .iter()
                .copied(),
        );
    }
}

fn retirement_points(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    home: Reg,
    candidates: &[(TempId, InstrRef)],
) -> Vec<(TempId, InstrRef, Vec<RetirementPoint>)> {
    // producer 自身是该 home 的覆写屏障；同块多个候选的扫描最多重叠于一个末尾后缀。
    let sources = candidates
        .iter()
        .filter_map(|&(temp, instr)| {
            let block = *cfg.instr_to_block.get(instr.index())?;
            let summary = summarize_block(proto, cfg, dataflow, block, instr.index() + 1, home)?;
            (summary.release.is_some() || !summary.successors.is_empty())
                .then_some((temp, instr, summary))
        })
        .collect::<Vec<_>>();
    if sources.is_empty() {
        return Vec::new();
    }

    let root = cfg.blocks.len();
    let mut summaries = (0..root + 1)
        .map(|_| BlockSummary::default())
        .collect::<Vec<_>>();
    summaries[root] = BlockSummary {
        valid: true,
        successors: sources
            .iter()
            .flat_map(|(_, _, s)| s.successors.iter().copied())
            .collect(),
        ..Default::default()
    };
    // 虚拟根仅合并本 home 的真实查询域；不可达且未被候选请求的块不做摘要。
    let traversal = crate::graph::depth_first(
        root + 1,
        root,
        |id| id,
        |_| true,
        |id| {
            if id != root {
                let block = BlockRef(id);
                summaries[id] = summarize_block(
                    proto,
                    cfg,
                    dataflow,
                    block,
                    cfg.blocks[id].instrs.start.index(),
                    home,
                )
                .unwrap_or_default();
            }
            summaries[id]
                .successors
                .iter()
                .map(|b| b.index())
                .collect::<Vec<_>>()
        },
    );
    let mut predecessors = vec![Vec::new(); root + 1];
    for &id in &traversal.preorder {
        for next in &summaries[id].successors {
            predecessors[next.index()].push(id);
        }
    }
    let components = crate::graph::strongly_connected_components(
        root + 1,
        &traversal.postorder,
        |id| id,
        |id| predecessors[id].iter().copied(),
    );
    let mut component_by_block = vec![0; root + 1];
    for (id, nodes) in components.iter().enumerate() {
        for &node in nodes {
            component_by_block[node] = id;
        }
    }
    let mut solved = vec![SolvedComponent::default(); components.len()];
    let mut retirements = RetirementDag::default();
    for (id, nodes) in components.iter().enumerate().rev() {
        let mut result = SolvedComponent {
            valid: true,
            ..Default::default()
        };
        let mut releases = Vec::new();
        let mut children = BTreeSet::new();
        for &node in nodes {
            let summary = &summaries[node];
            result.valid &= summary.valid;
            result.observed |= summary.observed;
            result.backedge |= summary.backedge;
            result.observed_overwrite |= summary.release.is_some_and(|release| release.after);
            releases.extend(summary.release);
            for next in &summary.successors {
                let next = component_by_block[next.index()];
                if next != id {
                    let next = solved[next];
                    result.valid &= next.valid;
                    result.observed |= next.observed;
                    result.backedge |= next.backedge;
                    result.observed_overwrite |= next.observed_overwrite;
                    children.extend(next.retirement);
                }
            }
        }
        if result.valid {
            result.retirement = retirements.join(releases, children);
        }
        solved[id] = result;
    }
    let requests = sources
        .into_iter()
        .filter_map(|(temp, instr, source)| {
            let mut valid = true;
            let mut observed = source.observed;
            let mut backedge = source.backedge;
            let mut observed_overwrite = source.release.is_some_and(|release| release.after);
            let mut roots = BTreeSet::new();
            if let Some(release) = source.release {
                roots.extend(retirements.join(vec![release], BTreeSet::new()));
            }
            for next in source.successors {
                let next = solved[component_by_block[next.index()]];
                valid &= next.valid;
                observed |= next.observed;
                backedge |= next.backedge;
                observed_overwrite |= next.observed_overwrite;
                roots.extend(next.retirement);
            }
            // 非循环的普通纯覆盖仍由现有 copy-root owner 消费；可观察写回也需要
            // 精确退休，即使 producer 与端点之间没有回边。
            (valid && observed && (backedge || observed_overwrite) && !roots.is_empty())
                .then_some((temp, instr, roots))
        })
        .collect();
    retirements.expand(requests)
}
