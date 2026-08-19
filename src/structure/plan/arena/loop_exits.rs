//! 循环提前退出、正常尾部与透明 pad 的证明。输入 CFG、loop domain 和 scope barriers，输出 break arms、normal tail 与可转发 exit routes；不负责创建 RegionPlan。例如 while 的共享尾只有在 normal/early 出口合同闭合时才会冻结。

use super::*;

pub(super) fn closed_linear_terminal_arm(
    proto: &LoweredProto,
    cfg: &Cfg,
    entry: BlockRef,
    owner: &BTreeSet<BlockRef>,
) -> Option<Vec<BlockRef>> {
    let mut blocks = Vec::new();
    let mut visited = vec![false; cfg.blocks.len()];
    let mut block = entry;
    loop {
        if block == cfg.exit_block || std::mem::replace(&mut visited[block.index()], true) {
            return None;
        }
        if cfg.preds[block.index()].iter().any(|edge| {
            let source = cfg.edges[edge.index()].from;
            cfg.reachable_blocks.contains(&source)
                && !owner.contains(&source)
                && !visited[source.index()]
        }) {
            return None;
        }
        blocks.push(block);
        match cfg.terminator(&proto.instrs, block)? {
            LowInstr::Return(_) | LowInstr::TailCall(_) => return Some(blocks),
            LowInstr::Jump(_) => {
                let [edge] = cfg.succs[block.index()].as_slice() else {
                    return None;
                };
                block = cfg.edges[edge.index()].to;
            }
            _ => return None,
        }
    }
}

/// natural-loop SCC 不包含“进入一个结构化子图后只会 break/return”的词法 arm。
/// 这类 arm 若留在 loop 外，入口边只能退化为 goto；这里仅接纳单入口、且所有出口
/// 都直达当前 loop continuation 或函数出口的闭合子图。
pub(super) struct WhileBreakArmDomain<'a> {
    pub(super) candidate: &'a crate::structure::LoopCandidate,
    pub(super) natural: &'a BTreeSet<BlockRef>,
    pub(super) condition_blocks: Option<&'a BTreeSet<BlockRef>>,
    pub(super) continuation: Option<BlockRef>,
}

pub(super) fn verified_while_break_arms(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    context: &LoopPartitionContext,
    domain: WhileBreakArmDomain<'_>,
    workspace: &mut WhileBreakArmWorkspace,
) -> Result<BTreeSet<BlockRef>, StructureError> {
    let Some(continuation) = domain.continuation else {
        return Ok(BTreeSet::new());
    };
    let candidate = domain.candidate;
    let natural = domain.natural;
    workspace.begin_loop();
    for &block in natural {
        workspace.insert(block, WHILE_BREAK_OWNED)?;
        if workspace.insert(block, WHILE_BREAK_QUEUED)? {
            workspace.pending.push_back(block);
        }
    }
    for block in std::iter::once(candidate.header)
        .chain(candidate.control_blocks.iter().copied())
        .chain(domain.condition_blocks.into_iter().flatten().copied())
    {
        workspace.insert(block, WHILE_BREAK_EXCLUDED)?;
    }

    let mut added = Vec::new();
    while let Some(source) = workspace.pending.pop_front() {
        workspace.remove(source, WHILE_BREAK_QUEUED)?;
        if !workspace.contains(source, WHILE_BREAK_OWNED)?
            || workspace.contains(source, WHILE_BREAK_EXCLUDED)?
        {
            continue;
        }
        let successors = &cfg.succs[source.index()];
        if successors.len() != 2
            || !successors.iter().all(|edge| {
                matches!(
                    cfg.edges[edge.index()].kind,
                    EdgeKind::BranchTrue | EdgeKind::BranchFalse
                )
            })
        {
            continue;
        }
        for (entry_index, &entry_edge) in successors.iter().enumerate() {
            let entry = cfg.edges[entry_edge.index()].to;
            let sibling = cfg.edges[successors[1 - entry_index].index()].to;
            if entry == continuation
                || entry == cfg.exit_block
                || workspace.contains(entry, WHILE_BREAK_OWNED)?
                || !(workspace.contains(sibling, WHILE_BREAK_OWNED)? || sibling == continuation)
            {
                continue;
            }
            if !workspace.mark_attempted(entry_edge)?
                || !closed_break_arm(
                    cfg,
                    graph_facts,
                    context,
                    workspace,
                    source,
                    entry_edge,
                    continuation,
                )?
            {
                continue;
            }
            let arm_len = workspace.arm_blocks.len();
            for arm_index in 0..arm_len {
                let block = workspace.arm_blocks[arm_index];
                if !workspace.insert(block, WHILE_BREAK_OWNED)? {
                    return Err(StructureError::invalid(
                        "verified break arms overlap after ownership was frozen",
                    ));
                }
                added.push(block);
                if workspace.insert(block, WHILE_BREAK_QUEUED)? {
                    workspace.pending.push_back(block);
                }
                for &incoming in &cfg.preds[block.index()] {
                    let predecessor = cfg.edges[incoming.index()].from;
                    if workspace.contains(predecessor, WHILE_BREAK_OWNED)?
                        && workspace.insert(predecessor, WHILE_BREAK_QUEUED)?
                    {
                        workspace.pending.push_back(predecessor);
                    }
                }
            }
        }
    }
    Ok(added.into_iter().collect())
}

pub(super) fn closed_break_arm(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    context: &LoopPartitionContext,
    workspace: &mut WhileBreakArmWorkspace,
    source: BlockRef,
    entry_edge: EdgeRef,
    continuation: BlockRef,
) -> Result<bool, StructureError> {
    let entry = cfg
        .edges
        .get(entry_edge.index())
        .ok_or_else(|| StructureError::invalid("break arm entry edge is outside the CFG arena"))?
        .to;
    workspace.begin_arm();
    workspace.arm_pending.push(entry);
    let mut reaches_continuation = false;
    while let Some(block) = workspace.arm_pending.pop() {
        if block == continuation {
            reaches_continuation = true;
            continue;
        }
        if block == cfg.exit_block {
            continue;
        }
        if workspace.contains(block, WHILE_BREAK_OWNED)?
            || !context
                .reachable_by_block
                .get(block.index())
                .copied()
                .ok_or_else(|| {
                    StructureError::invalid("break arm block is outside the CFG arena")
                })?
            // 单入口闭合 arm 的 entry 必须支配其全部 block。这个 interval 检查使
            // 多入口共享尾在首个汇合点即失败，避免每个入口重复遍历同一长尾。
            || !graph_facts.dominates(entry, block)
            || context
                .unstructured_by_block
                .get(block.index())
                .copied()
                .ok_or_else(|| {
                    StructureError::invalid("break arm block is outside the CFG arena")
                })?
            || context
                .residual_incidents_by_block
                .get(block.index())
                .ok_or_else(|| {
                    StructureError::invalid("break arm block is outside the CFG arena")
                })?
                .iter()
                .any(|residual| *residual != entry_edge)
        {
            return Ok(false);
        }
        if !workspace.visit(block)? {
            continue;
        }
        workspace.arm_blocks.push(block);
        for edge in &cfg.succs[block.index()] {
            let target = cfg.edges[edge.index()].to;
            if workspace.contains(target, WHILE_BREAK_OWNED)? {
                return Ok(false);
            }
            if target == continuation {
                reaches_continuation = true;
            } else if target != cfg.exit_block {
                workspace.arm_pending.push(target);
            }
        }
    }
    if workspace.arm_blocks.is_empty() || !reaches_continuation {
        return Ok(false);
    }
    for &block in &workspace.arm_blocks {
        for incoming in &cfg.preds[block.index()] {
            let edge = cfg.edges.get(incoming.index()).ok_or_else(|| {
                StructureError::invalid("break arm predecessor edge is outside the CFG arena")
            })?;
            if !context
                .reachable_by_block
                .get(edge.from.index())
                .copied()
                .ok_or_else(|| {
                    StructureError::invalid("break arm predecessor is outside the CFG arena")
                })?
                || workspace.is_visited(edge.from)?
            {
                continue;
            }
            if block != entry || edge.from != source || *incoming != entry_edge {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

pub(super) fn continue_pad_sibling_reaches_target(
    cfg: &Cfg,
    edge: EdgeRef,
    reaches_target: &BTreeSet<BlockRef>,
) -> bool {
    let source = cfg.edges[edge.index()].from;
    if cfg.succs[source.index()].len() != 1 {
        return true;
    }
    cfg.preds[source.index()].iter().any(|incoming| {
        let predecessor = cfg.edges[incoming.index()].from;
        cfg.succs[predecessor.index()].iter().any(|sibling| {
            *sibling != *incoming && reaches_target.contains(&cfg.edges[sibling.index()].to)
        })
    })
}

pub(super) struct NormalLoopTailDomain<'a> {
    pub(super) candidate: &'a crate::structure::LoopCandidate,
    pub(super) preheader: Option<BlockRef>,
    pub(super) control: &'a BTreeSet<BlockRef>,
    pub(super) body: &'a BTreeSet<BlockRef>,
    pub(super) owned: &'a BTreeSet<BlockRef>,
    pub(super) continuation: Option<BlockRef>,
}

pub(super) fn detect_normal_loop_tail(
    proto: &LoweredProto,
    cfg: &Cfg,
    domain: NormalLoopTailDomain<'_>,
) -> Option<NormalTailPartition> {
    use crate::structure::LoopKindHint;

    let candidate = domain.candidate;
    let preheader = domain.preheader;
    let control = domain.control;
    let body = domain.body;
    let owned = domain.owned;
    if !matches!(
        candidate.kind_hint,
        LoopKindHint::WhileLike | LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
    ) {
        return None;
    }
    if candidate.kind_hint == LoopKindHint::GenericForLike
        && matches!(
            cfg.terminator(&proto.instrs, candidate.header),
            Some(LowInstr::GenericForLoop(instr))
                if crate::structure::loops::generic_for_immediate_break(proto, cfg, instr)
        )
    {
        // body 与零迭代出口相同，或后者先经单跳 pad 汇入 body 时，源码语义是
        // “首轮立即 break”，并不存在只应由正常出口执行的 tail。
        return None;
    }
    let continuation = domain.continuation?;
    let mut normal_exits = preheader
        .into_iter()
        .chain(control.iter().copied())
        .flat_map(|block| cfg.succs[block.index()].iter().copied())
        .filter(|edge| {
            let edge = cfg.edges[edge.index()];
            !owned.contains(&edge.to)
                && edge.to != cfg.exit_block
                && if matches!(
                    candidate.kind_hint,
                    LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
                ) {
                    edge.kind == EdgeKind::LoopExit
                } else {
                    !matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                }
        })
        .collect::<Vec<_>>();
    let entry = cfg.edges[normal_exits.first()?.index()].to;
    if normal_exits
        .iter()
        .any(|edge| cfg.edges[edge.index()].to != entry)
    {
        return None;
    }
    if entry == continuation || owned.contains(&entry) {
        return None;
    }

    // 候选阶段只证明存在 bypass；精确 guard 依赖最终 Break owner 与
    // forwarding target，由 plan finalizer 统一冻结。
    if !body
        .iter()
        .flat_map(|block| cfg.succs[block.index()].iter().copied())
        .any(|edge| {
            let edge_data = cfg.edges[edge.index()];
            edge_data.to == continuation
                && edge_data.kind != EdgeKind::LoopExit
                && candidate.backedges.binary_search(&edge).is_err()
        })
    {
        return None;
    }
    normal_exits.sort_by_key(|edge| edge.index());
    normal_exits.dedup();

    let mut blocks = BTreeSet::new();
    let mut pending = vec![entry];
    while let Some(current) = pending.pop() {
        if current == continuation || !blocks.insert(current) {
            continue;
        }
        if current == cfg.exit_block || owned.contains(&current) {
            return None;
        }
        for edge in &cfg.succs[current.index()] {
            let edge = cfg.edges[edge.index()];
            if matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                || edge.to == cfg.exit_block
                || owned.contains(&edge.to)
            {
                return None;
            }
            if edge.to != continuation {
                pending.push(edge.to);
            }
        }
    }

    let mut completion_exits = Vec::new();
    for block in &blocks {
        if cfg.preds[block.index()].iter().any(|edge| {
            let source = cfg.edges[edge.index()].from;
            cfg.reachable_blocks.contains(&source)
                && !blocks.contains(&source)
                && normal_exits.binary_search(edge).is_err()
        }) {
            return None;
        }
        for edge in &cfg.succs[block.index()] {
            let target = cfg.edges[edge.index()].to;
            if target == continuation {
                completion_exits.push(*edge);
            } else if !blocks.contains(&target) {
                return None;
            }
        }
    }
    if completion_exits.is_empty() {
        return None;
    }
    let mut indegree = vec![0usize; cfg.blocks.len()];
    for block in &blocks {
        for edge in &cfg.succs[block.index()] {
            let target = cfg.edges[edge.index()].to;
            if blocks.contains(&target) {
                indegree[target.index()] += 1;
            }
        }
    }
    let mut ready = blocks
        .iter()
        .copied()
        .filter(|block| indegree[block.index()] == 0)
        .collect::<Vec<_>>();
    let mut visited = 0usize;
    while let Some(block) = ready.pop() {
        visited += 1;
        for edge in &cfg.succs[block.index()] {
            let target = cfg.edges[edge.index()].to;
            if !blocks.contains(&target) {
                continue;
            }
            indegree[target.index()] -= 1;
            if indegree[target.index()] == 0 {
                ready.push(target);
            }
        }
    }
    if visited != blocks.len() {
        return None;
    }

    completion_exits.sort_by_key(|edge| edge.index());
    completion_exits.dedup();
    Some(NormalTailPartition {
        blocks,
        contract: LoopNormalTailPlan {
            entry,
            continuation,
            early_exits: Vec::new(),
            normal_exits,
            completion_exits,
        },
    })
}

pub(super) fn exclusive_break_forwarding_route(
    proto: &LoweredProto,
    cfg: &Cfg,
    entry: EdgeRef,
    target: BlockRef,
    barriers: &BTreeSet<BlockRef>,
    labels: &BTreeSet<BlockRef>,
) -> Option<Vec<EdgeRef>> {
    let mut incoming = entry;
    let mut block = cfg.edges.get(entry.index())?.to;
    let mut route = Vec::new();
    while block != target {
        if barriers.contains(&block)
            || labels.contains(&block)
            || cfg.preds.get(block.index())?.as_slice() != [incoming]
        {
            return None;
        }
        let range = cfg.blocks.get(block.index())?.instrs;
        let [edge] = cfg.succs.get(block.index())?.as_slice() else {
            return None;
        };
        if cfg.edges.get(edge.index())?.kind != EdgeKind::Jump {
            return None;
        }
        let end = range.last().map_or(range.end(), |last| {
            if proto.instrs[last.index()].is_control_terminator() {
                range.end() - 1
            } else {
                range.end()
            }
        });
        if !(range.start.index()..end).all(|index| matches!(proto.instrs[index], LowInstr::Move(_)))
        {
            return None;
        }
        route.push(*edge);
        incoming = *edge;
        block = cfg.edges[edge.index()].to;
    }
    (!route.is_empty()).then_some(route)
}

pub(super) fn block_has_non_control_prefix(
    proto: &LoweredProto,
    cfg: &Cfg,
    block: BlockRef,
) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    let end = range.last().map_or(range.end(), |last| {
        if proto.instrs[last.index()].is_control_terminator() {
            range.end() - 1
        } else {
            range.end()
        }
    });
    range.start.index() < end
}

pub(super) fn merged_natural_loop_domain(
    cfg: &Cfg,
    candidate: &crate::structure::LoopCandidate,
) -> BTreeSet<BlockRef> {
    let mut domain = BTreeSet::from([candidate.header]);
    let mut pending = candidate
        .backedges
        .iter()
        .filter_map(|edge| cfg.edges.get(edge.index()))
        .filter(|edge| edge.to == candidate.header)
        .map(|edge| edge.from)
        .collect::<Vec<_>>();
    while let Some(block) = pending.pop() {
        if !domain.insert(block) || block == candidate.header {
            continue;
        }
        pending.extend(cfg.preds[block.index()].iter().filter_map(|edge| {
            let source = cfg.edges[edge.index()].from;
            cfg.reachable_blocks.contains(&source).then_some(source)
        }));
    }
    domain
}

pub(super) const LOOP_EXIT_PAD_CANDIDATE: u8 = 1 << 0;
pub(super) const LOOP_EXIT_PAD_REACHES_EXIT: u8 = 1 << 1;
pub(super) const LOOP_EXIT_PAD_SELECTED: u8 = 1 << 2;
pub(super) const LOOP_EXIT_PAD_INVALID_QUEUED: u8 = 1 << 3;

#[derive(Clone, Copy, Default)]
pub(super) struct LoopExitPadBlockState {
    epoch: usize,
    flags: u8,
}

pub(super) struct LoopExitPadWorkspace {
    epoch: usize,
    blocks: Vec<LoopExitPadBlockState>,
    touched_pads: Vec<BlockRef>,
    pending: VecDeque<BlockRef>,
    invalid: VecDeque<BlockRef>,
}

impl LoopExitPadWorkspace {
    pub(super) fn new(block_count: usize) -> Self {
        Self {
            epoch: 0,
            blocks: vec![LoopExitPadBlockState::default(); block_count],
            touched_pads: Vec::new(),
            pending: VecDeque::new(),
            invalid: VecDeque::new(),
        }
    }

    fn begin(&mut self) -> Result<(), StructureError> {
        self.epoch = self
            .epoch
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("loop exit-pad workspace epoch overflows"))?;
        self.touched_pads.clear();
        self.pending.clear();
        self.invalid.clear();
        Ok(())
    }

    fn contains(&self, block: BlockRef, flag: u8) -> Result<bool, StructureError> {
        let state = self.blocks.get(block.index()).ok_or_else(|| {
            StructureError::invalid(format!(
                "loop exit-pad analysis references missing block {block}"
            ))
        })?;
        Ok(state.epoch == self.epoch && state.flags & flag != 0)
    }

    fn insert(&mut self, block: BlockRef, flag: u8) -> Result<bool, StructureError> {
        let state = self.blocks.get_mut(block.index()).ok_or_else(|| {
            StructureError::invalid(format!(
                "loop exit-pad analysis references missing block {block}"
            ))
        })?;
        if state.epoch != self.epoch {
            *state = LoopExitPadBlockState {
                epoch: self.epoch,
                flags: 0,
            };
        }
        let inserted = state.flags & flag == 0;
        state.flags |= flag;
        Ok(inserted)
    }

    fn remove(&mut self, block: BlockRef, flag: u8) -> Result<(), StructureError> {
        let state = self.blocks.get_mut(block.index()).ok_or_else(|| {
            StructureError::invalid(format!(
                "loop exit-pad analysis references missing block {block}"
            ))
        })?;
        if state.epoch == self.epoch {
            state.flags &= !flag;
        }
        Ok(())
    }

    fn select_pad(&mut self, block: BlockRef) -> Result<(), StructureError> {
        if self.insert(block, LOOP_EXIT_PAD_SELECTED)? {
            self.touched_pads.push(block);
        }
        Ok(())
    }

    fn selected_pads(&self) -> Result<BTreeSet<BlockRef>, StructureError> {
        let mut pads = BTreeSet::new();
        for block in self.touched_pads.iter().copied() {
            if self.contains(block, LOOP_EXIT_PAD_SELECTED)? {
                pads.insert(block);
            }
        }
        Ok(pads)
    }
}

pub(super) fn verified_loop_exit_pads(
    cfg: &Cfg,
    candidate: &crate::structure::LoopCandidate,
    continuation: Option<BlockRef>,
    owned: &BTreeSet<BlockRef>,
    control: &BTreeSet<BlockRef>,
    workspace: &mut LoopExitPadWorkspace,
) -> Result<BTreeSet<BlockRef>, StructureError> {
    workspace.begin()?;
    let control_exit_targets = control
        .iter()
        .flat_map(|block| cfg.succs[block.index()].iter())
        .map(|edge| cfg.edges[edge.index()].to)
        .filter(|target| !control.contains(target) && !owned.contains(target))
        .collect::<BTreeSet<_>>();
    let candidates = candidate
        .body_scope_blocks
        .iter()
        .copied()
        .chain(candidate.exits.iter().copied())
        .filter(|block| {
            !owned.contains(block)
                && Some(*block) != continuation
                && !control_exit_targets.contains(block)
                && Some(*block) != candidate.preheader
                && cfg.reachable_blocks.contains(block)
        })
        .collect::<BTreeSet<_>>();
    for block in &candidates {
        workspace.insert(*block, LOOP_EXIT_PAD_CANDIDATE)?;
    }
    for block in candidate.exits.iter().copied().chain(continuation) {
        if workspace.insert(block, LOOP_EXIT_PAD_REACHES_EXIT)? {
            workspace.pending.push_back(block);
        }
    }
    if candidate.exits.len() > 1 {
        let successors = candidate
            .exits
            .iter()
            .filter_map(|block| cfg.unique_reachable_successor(*block))
            .collect::<BTreeSet<_>>();
        if successors.len() == 1 {
            for block in successors {
                if workspace.insert(block, LOOP_EXIT_PAD_REACHES_EXIT)? {
                    workspace.pending.push_back(block);
                }
            }
        }
    }

    for block in candidates.iter().copied() {
        let [edge] = cfg.succs[block.index()].as_slice() else {
            continue;
        };
        let reachable_predecessors = cfg.preds[block.index()]
            .iter()
            .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
            .count();
        if reachable_predecessors == 1
            && matches!(
                cfg.edges[edge.index()].kind,
                EdgeKind::Return | EdgeKind::TailCall
            )
        {
            workspace.select_pad(block)?;
            if workspace.insert(block, LOOP_EXIT_PAD_REACHES_EXIT)? {
                workspace.pending.push_back(block);
            }
        }
    }

    while let Some(target) = workspace.pending.pop_front() {
        for incoming in &cfg.preds[target.index()] {
            let edge = cfg.edges[incoming.index()];
            let source = edge.from;
            if !workspace.contains(source, LOOP_EXIT_PAD_CANDIDATE)?
                || workspace.contains(source, LOOP_EXIT_PAD_SELECTED)?
                || source == target
            {
                continue;
            }
            let [only] = cfg.succs[source.index()].as_slice() else {
                continue;
            };
            if *only != *incoming || matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall) {
                continue;
            }
            workspace.select_pad(source)?;
            if workspace.insert(source, LOOP_EXIT_PAD_REACHES_EXIT)? {
                workspace.pending.push_back(source);
            }
        }
    }

    for index in 0..workspace.touched_pads.len() {
        let block = workspace.touched_pads[index];
        if !workspace.contains(block, LOOP_EXIT_PAD_SELECTED)? {
            continue;
        }
        let mut reachable_predecessors = 0usize;
        let mut has_external_predecessor = false;
        for incoming in &cfg.preds[block.index()] {
            let source = cfg.edges[incoming.index()].from;
            if !cfg.reachable_blocks.contains(&source) {
                continue;
            }
            reachable_predecessors += 1;
            has_external_predecessor |=
                !owned.contains(&source) && !workspace.contains(source, LOOP_EXIT_PAD_SELECTED)?;
        }
        if (reachable_predecessors == 0 || has_external_predecessor)
            && workspace.insert(block, LOOP_EXIT_PAD_INVALID_QUEUED)?
        {
            workspace.invalid.push_back(block);
        }
    }
    while let Some(block) = workspace.invalid.pop_front() {
        if !workspace.contains(block, LOOP_EXIT_PAD_SELECTED)? {
            continue;
        }
        workspace.remove(block, LOOP_EXIT_PAD_SELECTED)?;
        for outgoing in &cfg.succs[block.index()] {
            let target = cfg.edges[outgoing.index()].to;
            if workspace.contains(target, LOOP_EXIT_PAD_SELECTED)?
                && workspace.insert(target, LOOP_EXIT_PAD_INVALID_QUEUED)?
            {
                workspace.invalid.push_back(target);
            }
        }
    }
    workspace.selected_pads()
}

pub(super) fn for_latch_exit_control_pads(
    proto: &LoweredProto,
    cfg: &Cfg,
    control: &BTreeSet<BlockRef>,
    owned: &BTreeSet<BlockRef>,
) -> BTreeSet<BlockRef> {
    let mut pending = control
        .iter()
        .flat_map(|block| cfg.succs[block.index()].iter().copied())
        .filter(|edge| cfg.edges[edge.index()].kind == EdgeKind::LoopExit)
        .map(|edge| cfg.edges[edge.index()].to)
        .collect::<Vec<_>>();
    let mut pads = BTreeSet::new();
    while let Some(block) = pending.pop() {
        if !owned.contains(&block) || pads.contains(&block) {
            continue;
        }
        let range = cfg.blocks[block.index()].instrs;
        let [edge] = cfg.succs[block.index()].as_slice() else {
            continue;
        };
        if range.len != 1
            || !matches!(proto.instrs[range.start.index()], LowInstr::Jump(_))
            || cfg.edges[edge.index()].kind != EdgeKind::Jump
        {
            continue;
        }
        pads.insert(block);
        pending.push(cfg.edges[edge.index()].to);
    }
    pads
}
