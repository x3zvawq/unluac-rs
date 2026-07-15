//! 这个文件承载 HIR 结构恢复的主体实现。
//!
//! 外层 `structure/mod.rs` 只负责做入口和模块拼装，这里集中放真正的分支/merge/region
//! 结构恢复逻辑。这样后续继续拆 `branch merge`、`loop exits` 之类的细节时，
//! 不会再把 facade 文件重新撑回一个巨型实现。

mod branch_exit_assignments;
mod branch_stops;
mod branches;
mod entry_overrides;
mod escapes;
mod loop_controls;
mod path_checks;
mod prefix_temps;
mod short_circuits;
mod unstructured;
mod value_merges;

use std::{cell::RefCell, ops::Range};

use super::*;

/// 尝试基于现有结构候选恢复一个更接近源码的 HIR block。
pub(super) fn build_structured_body(
    target: AstTargetDialect,
    lowering: &ProtoLowering<'_>,
) -> Option<HirBlock> {
    if lowering
        .structure
        .goto_requirements
        .iter()
        .any(|requirement| {
            requirement.reason != GotoReason::UnstructuredContinueLike
                && lowering
                    .structure
                    .unstructured_region(lowering.cfg.edges[requirement.edge.index()].to)
                    .is_none()
        })
    {
        return None;
    }

    let mut lowerer = StructuredBodyLowerer::new(target, lowering);
    let body = lowerer.lower_region(lowering.cfg.entry_block, None, &BTreeMap::new())?;
    lowerer.all_reachable_blocks_covered().then_some(body)
}

pub(super) struct StructuredBodyLowerer<'a, 'b> {
    pub(super) target: AstTargetDialect,
    pub(super) lowering: &'b ProtoLowering<'a>,
    pub(super) branch_by_header: BTreeMap<BlockRef, &'b BranchCandidate>,
    pub(super) branch_regions_by_header: BTreeMap<BlockRef, &'b BranchRegionFact>,
    pub(super) branch_value_merges_by_header: BTreeMap<BlockRef, &'b BranchValueMergeCandidate>,
    pub(super) loop_headers: BTreeSet<BlockRef>,
    pub(super) loops_by_header: BTreeMap<BlockRef, Vec<(LoopCandidateId, &'b LoopCandidate)>>,
    pub(super) label_map: BTreeMap<BlockRef, HirLabelId>,
    pub(super) required_labels: BTreeSet<BlockRef>,
    pub(super) merge_allowed_blocks: BTreeMap<BlockRef, BTreeSet<BlockRef>>,
    pub(super) overrides: StructureOverrideState,
    pub(super) visited: TransactionalBlockSet,
    pub(super) active_loops: Vec<ActiveLoopContext>,
    reachability: RefCell<BTreeMap<BlockRef, BTreeSet<BlockRef>>>,
}

#[derive(Debug)]
pub(super) struct StructuredBranchPlan {
    pub(super) cond: HirExpr,
    pub(super) then_entry: BlockRef,
    pub(super) else_entry: Option<BlockRef>,
    pub(super) merge: Option<BlockRef>,
    pub(super) consumed_headers: Vec<BlockRef>,
    // 短路候选的语义节点只包含条件 header；某些出口会先经过空 jump pad 再到
    // truthy/falsy 出口。pad 不参与条件重写，但需要计入覆盖性检查。
    pub(super) consumed_blocks: Vec<BlockRef>,
}

#[derive(Debug, Clone)]
pub(super) struct LoopStateSlot {
    pub(super) phi_id: Option<PhiId>,
    pub(super) reg: Reg,
    pub(super) target: HirLValue,
    pub(super) init: HirExpr,
    pub(super) initialize_target: bool,
}

#[derive(Debug, Clone, Default)]
pub(super) struct LoopStatePlan {
    pub(super) states: Vec<LoopStateSlot>,
    pub(super) backedge_target_overrides: BTreeMap<TempId, HirLValue>,
    pub(super) owned_phis: BTreeSet<PhiId>,
}

#[derive(Debug, Clone)]
pub(super) struct ActiveLoopContext {
    pub(super) candidate_id: LoopCandidateId,
    pub(super) header: BlockRef,
    pub(super) loop_blocks: BTreeSet<BlockRef>,
    pub(super) post_loop: BlockRef,
    pub(super) downstream_post_loop: Option<BlockRef>,
    pub(super) continue_target: Option<BlockRef>,
    pub(super) body_stop: Option<BlockRef>,
    pub(super) continue_sources: BTreeSet<BlockRef>,
    pub(super) break_exits: BTreeMap<BlockRef, BreakExitBlock>,
    pub(super) state_slots: Vec<LoopStateSlot>,
}

#[derive(Debug, Clone)]
pub(super) struct BreakExitBlock {
    pub(super) block: HirBlock,
    pub(super) blocks: BTreeSet<BlockRef>,
}

#[derive(Debug)]
pub(super) struct TransactionalBlockSet {
    membership: Vec<bool>,
    inserted: Vec<BlockRef>,
}

impl TransactionalBlockSet {
    fn new(block_count: usize) -> Self {
        Self {
            membership: vec![false; block_count],
            inserted: Vec::new(),
        }
    }

    pub(super) fn contains(&self, block: &BlockRef) -> bool {
        self.membership[block.index()]
    }

    pub(super) fn insert(&mut self, block: BlockRef) -> bool {
        let member = &mut self.membership[block.index()];
        if *member {
            return false;
        }
        *member = true;
        self.inserted.push(block);
        true
    }

    pub(super) fn extend(&mut self, blocks: impl IntoIterator<Item = BlockRef>) {
        for block in blocks {
            self.insert(block);
        }
    }

    fn checkpoint(&self) -> usize {
        self.inserted.len()
    }

    fn rollback(&mut self, checkpoint: usize) {
        while self.inserted.len() > checkpoint {
            let block = self
                .inserted
                .pop()
                .expect("visited rollback length should be valid");
            self.membership[block.index()] = false;
        }
    }
}

#[derive(Debug, Clone)]
pub(super) struct StructureStateCheckpoint {
    required_labels: BTreeSet<BlockRef>,
    merge_allowed_blocks: BTreeMap<BlockRef, BTreeSet<BlockRef>>,
    overrides: StructureOverrideState,
    visited_len: usize,
    active_loops: Vec<ActiveLoopContext>,
    stmts_len: usize,
}

impl<'a, 'b> StructuredBodyLowerer<'a, 'b> {
    pub(super) fn checkpoint_state(&self, stmts_len: usize) -> StructureStateCheckpoint {
        StructureStateCheckpoint {
            required_labels: self.required_labels.clone(),
            merge_allowed_blocks: self.merge_allowed_blocks.clone(),
            overrides: self.overrides.clone(),
            visited_len: self.visited.checkpoint(),
            active_loops: self.active_loops.clone(),
            stmts_len,
        }
    }

    pub(super) fn restore_state_checkpoint(
        &mut self,
        checkpoint: StructureStateCheckpoint,
        stmts: &mut Vec<HirStmt>,
    ) {
        self.required_labels = checkpoint.required_labels;
        self.merge_allowed_blocks = checkpoint.merge_allowed_blocks;
        self.overrides = checkpoint.overrides;
        self.visited.rollback(checkpoint.visited_len);
        self.active_loops = checkpoint.active_loops;
        stmts.truncate(checkpoint.stmts_len);
    }

    fn new(target: AstTargetDialect, lowering: &'b ProtoLowering<'a>) -> Self {
        let branch_by_header = lowering.structure.branch_candidates_by_header().collect();
        let branch_value_merges_by_header = lowering
            .structure
            .branch_candidates_by_header()
            .filter_map(|(header, _)| {
                lowering
                    .structure
                    .branch_value_merge_for_header(header)
                    .map(|candidate| (header, candidate))
            })
            .collect();
        let branch_regions_by_header = lowering
            .structure
            .branch_region_facts
            .iter()
            .map(|fact| (fact.header, fact))
            .collect();
        let mut loops_by_header = BTreeMap::<BlockRef, Vec<_>>::new();
        for header in lowering.structure.loop_headers() {
            loops_by_header.insert(
                header,
                lowering
                    .structure
                    .loop_candidates_for_header(header)
                    .collect(),
            );
        }
        let loop_headers = loops_by_header.keys().copied().collect();
        let required_labels = lowering
            .structure
            .goto_requirements
            .iter()
            .map(|requirement| lowering.cfg.edges[requirement.edge.index()].to)
            .chain(
                lowering
                    .cfg
                    .block_order
                    .iter()
                    .copied()
                    .filter(|block| lowering.structure.unstructured_region(*block).is_some()),
            )
            .chain(
                lowering
                    .structure
                    .region_facts
                    .iter()
                    .filter(|region| !region.structureable)
                    .flat_map(|region| region.exits.iter().copied()),
            )
            .filter(|block| *block != lowering.cfg.exit_block)
            .collect();

        Self {
            target,
            lowering,
            branch_by_header,
            branch_regions_by_header,
            branch_value_merges_by_header,
            loop_headers,
            loops_by_header,
            label_map: build_label_map_for_summary(lowering.cfg),
            required_labels,
            merge_allowed_blocks: BTreeMap::new(),
            overrides: StructureOverrideState::default(),
            visited: TransactionalBlockSet::new(lowering.cfg.blocks.len()),
            active_loops: Vec::new(),
            reachability: RefCell::new(BTreeMap::new()),
        }
    }

    pub(super) fn can_reach(&self, from: BlockRef, to: BlockRef) -> bool {
        self.reachability
            .borrow_mut()
            .entry(from)
            .or_insert_with(|| {
                self.lowering
                    .cfg
                    .reachable_targets_within(from, &self.lowering.cfg.reachable_blocks)
            })
            .contains(&to)
    }

    fn all_reachable_blocks_covered(&self) -> bool {
        self.lowering
            .cfg
            .block_order
            .iter()
            .filter(|block| self.lowering.cfg.reachable_blocks.contains(block))
            .filter(|block| **block != self.lowering.cfg.exit_block)
            .all(|block| self.visited.contains(block))
    }

    pub(super) fn can_emit_continue_stmt(&self) -> bool {
        self.target.caps.continue_stmt
    }

    pub(super) fn lower_region(
        &mut self,
        start: BlockRef,
        stop: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirBlock> {
        self.lower_region_with_suppressed_loop(start, stop, target_overrides, None)
    }

    pub(super) fn lower_region_with_suppressed_loop(
        &mut self,
        start: BlockRef,
        stop: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
        suppressed_loop_id: Option<LoopCandidateId>,
    ) -> Option<HirBlock> {
        let mut current = Some(start);
        let mut stmts = Vec::new();

        while let Some(block) = current {
            if Some(block) == stop || block == self.lowering.cfg.exit_block {
                break;
            }
            if let Some(loop_escape_stmts) = self.active_loop_escape_stmts(block) {
                stmts.extend(loop_escape_stmts);
                break;
            }
            if !self.lowering.cfg.reachable_blocks.contains(&block) {
                return None;
            }
            if self.visited.contains(&block) {
                if self.block_is_terminal_exit(block) {
                    // 终止 return 块没有 fallthrough；多条源码路径共享同一个 return 尾块时，
                    // 后到达的路径可以安全克隆这段终止语句，而不应让整颗 proto 回退成
                    // label/goto fallback。每条运行时路径仍只执行一次 return。
                    let cloned = self.lower_terminal_exit_block_clone(block, target_overrides)?;
                    stmts.extend(cloned.stmts);
                    break;
                }
                if let Some(stop) = stop
                    && let Some(cloned) =
                        self.lower_shared_stop_tail_block_clone(block, stop, target_overrides)
                {
                    stmts.extend(cloned.stmts);
                    break;
                }
                return None;
            }

            self.emit_required_label(block, &mut stmts);

            if let Some(region_id) = self.lowering.structure.unstructured_region(block) {
                current = self.lower_unstructured_region(
                    block,
                    region_id,
                    stop,
                    &mut stmts,
                    target_overrides,
                )?;
                continue;
            }

            if let Some(next) =
                self.try_lower_unstructured_entry_branch(block, &mut stmts, target_overrides)
            {
                current = next;
                continue;
            }

            if let Some((candidate_id, _)) =
                self.loop_candidate_for_entry(block, suppressed_loop_id)
            {
                current =
                    self.lower_loop(block, candidate_id, stop, &mut stmts, target_overrides)?;
            } else if self.branch_by_header.contains_key(&block) {
                current = self.lower_branch(block, stop, &mut stmts, target_overrides)?;
            } else {
                current = self.lower_linear_block(block, stop, &mut stmts, target_overrides)?;
            }
        }

        Some(HirBlock { stmts })
    }

    pub(super) fn loop_candidate(
        &self,
        candidate_id: LoopCandidateId,
    ) -> Option<&'b LoopCandidate> {
        self.lowering.structure.loop_candidate(candidate_id)
    }

    pub(super) fn innermost_loop_candidate(
        &self,
        header: BlockRef,
    ) -> Option<(LoopCandidateId, &'b LoopCandidate)> {
        let candidates = self.loops_by_header.get(&header)?;
        let minimum = candidates
            .iter()
            .map(|(_, candidate)| candidate.blocks.len())
            .min()?;
        let mut matching = candidates
            .iter()
            .filter(|(_, candidate)| candidate.blocks.len() == minimum);
        let candidate = matching.next().copied()?;
        matching.next().is_none().then_some(candidate)
    }

    pub(super) fn unique_loop_candidate_matching(
        &self,
        header: BlockRef,
        mut matches: impl FnMut(&LoopCandidate) -> bool,
    ) -> Option<(LoopCandidateId, &'b LoopCandidate)> {
        let mut matching = self
            .loops_by_header
            .get(&header)?
            .iter()
            .filter(|(_, candidate)| matches(candidate));
        let candidate = matching.next().copied()?;
        matching.next().is_none().then_some(candidate)
    }

    pub(super) fn outermost_loop_candidate_matching(
        &self,
        header: BlockRef,
        mut matches: impl FnMut(LoopCandidateId, &LoopCandidate) -> bool,
    ) -> Option<(LoopCandidateId, &'b LoopCandidate)> {
        let candidates = self
            .loops_by_header
            .get(&header)?
            .iter()
            .filter(|(id, candidate)| matches(*id, candidate))
            .copied()
            .collect::<Vec<_>>();
        let maximum = candidates
            .iter()
            .map(|(_, candidate)| candidate.blocks.len())
            .max()?;
        let mut matching = candidates
            .into_iter()
            .filter(|(_, candidate)| candidate.blocks.len() == maximum);
        let candidate = matching.next()?;
        matching.next().is_none().then_some(candidate)
    }

    pub(super) fn nested_loop_owner_for_entry(
        &self,
        active: &LoopCandidate,
        entry: BlockRef,
    ) -> Option<&'b LoopCandidate> {
        let candidate = self.loop_candidate_from_preheader(entry).or_else(|| {
            self.outermost_loop_candidate_matching(entry, |_, candidate| {
                candidate.preheader.is_none()
                    && candidate.header != active.header
                    && candidate.blocks.is_subset(&active.binding_scope_blocks)
            })
            .map(|(_, candidate)| candidate)
        })?;
        (candidate.header != active.header
            && candidate.blocks.is_subset(&active.binding_scope_blocks))
        .then_some(candidate)
    }

    fn loop_candidate_for_entry(
        &self,
        header: BlockRef,
        suppressed_loop_id: Option<LoopCandidateId>,
    ) -> Option<(LoopCandidateId, &'b LoopCandidate)> {
        let active_parent = self
            .active_loops
            .iter()
            .rev()
            .find(|active| active.header == header)
            .and_then(|active| self.loop_candidate(active.candidate_id));
        self.outermost_loop_candidate_matching(header, |candidate_id, candidate| {
            Some(candidate_id) != suppressed_loop_id
                && !self
                    .active_loops
                    .iter()
                    .any(|active| active.candidate_id == candidate_id)
                && active_parent.is_none_or(|parent| {
                    candidate.blocks != parent.blocks && candidate.blocks.is_subset(&parent.blocks)
                })
        })
    }

    fn emit_required_label(&self, block: BlockRef, stmts: &mut Vec<HirStmt>) {
        if !self.required_labels.contains(&block) {
            return;
        }
        stmts.push(HirStmt::Label(Box::new(HirLabel {
            id: self.label_map[&block],
        })));
    }

    fn lower_linear_block(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let checkpoint = self.checkpoint_state(stmts.len());
        if let Some(next) = self.try_lower_numeric_for_init(block, stop, stmts, target_overrides) {
            return Some(next);
        }
        self.restore_state_checkpoint(checkpoint, stmts);

        let checkpoint = self.checkpoint_state(stmts.len());
        if let Some(next) =
            self.try_lower_generic_for_preheader(block, stop, stmts, target_overrides)
        {
            return Some(next);
        }
        self.restore_state_checkpoint(checkpoint, stmts);

        self.visited.insert(block);
        stmts.extend(self.lower_block_prefix(block, false, target_overrides)?);

        let Some((instr_ref, instr)) = self.block_terminator(block) else {
            return self.next_linear_successor(block, stop);
        };

        if !is_control_terminator(instr) {
            return self.next_linear_successor(block, stop);
        }

        match instr {
            LowInstr::Jump(jump) => {
                let target = self.lowering.cfg.instr_to_block[jump.target.index()];
                self.follow_linear_target(block, target, stop, stmts, target_overrides)
            }
            LowInstr::Branch(branch)
                if self.lowering.cfg.instr_to_block[branch.then_target.index()]
                    == self.lowering.cfg.instr_to_block[branch.else_target.index()] =>
            {
                let target = self.lowering.cfg.instr_to_block[branch.then_target.index()];
                // 两条边汇合不代表条件求值可删除：全局读取和比较都可能触发元方法。
                // 空 if 是 Lua 中保留一次任意条件求值而不引入伪绑定的最小表示。
                let cond = self.lower_branch_cond_for_target(block, target)?;
                let mut evaluation = vec![branch_stmt(cond, HirBlock::default(), None)];
                apply_loop_rewrites(&mut evaluation, target_overrides);
                stmts.extend(evaluation);
                self.follow_linear_target(block, target, stop, stmts, target_overrides)
            }
            LowInstr::Return(_) | LowInstr::TailCall(_) => {
                let empty_labels = BTreeMap::new();
                let mut lowered =
                    lower_control_instr(self.lowering, block, instr_ref, instr, &empty_labels);
                // return/tail-call 虽然是控制终结指令，但它们读取的表达式同样可能来自
                // loop state。这里必须和普通前缀指令一样应用 target overrides，否则
                // `return carried` 会退回成未物化的 phi temp。
                apply_loop_rewrites(&mut lowered, target_overrides);
                if let Some(entry_expr_overrides) = self.block_entry_expr_overrides(block) {
                    for stmt in &mut lowered {
                        rewrite_stmt_exprs(stmt, entry_expr_overrides);
                    }
                }
                stmts.extend(lowered);
                Some(None)
            }
            LowInstr::Branch(_)
            | LowInstr::NumericForInit(_)
            | LowInstr::NumericForLoop(_)
            | LowInstr::GenericForLoop(_) => None,
            _ => None,
        }
    }

    fn follow_linear_target(
        &mut self,
        block: BlockRef,
        target: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        if let Some(edge_ref) = self.required_goto_edge(block, target) {
            let mut edge_stmts = lower_edge_phi_copies_for_edge(self.lowering, edge_ref);
            apply_loop_rewrites(&mut edge_stmts, target_overrides);
            edge_stmts.extend(goto_block(self.label_map[&target]).stmts);
            stmts.extend(edge_stmts);
            return Some(None);
        }
        if Some(target) == stop || target == self.lowering.cfg.exit_block {
            return Some(if target == self.lowering.cfg.exit_block {
                None
            } else {
                Some(target)
            });
        }
        if let Some(loop_context) = self.active_loops.last() {
            if loop_context.continue_target == Some(target)
                && loop_context.continue_sources.contains(&block)
                && self.loop_continue_target_is_empty(target)
            {
                if !self.can_emit_continue_stmt() {
                    return None;
                }
                stmts.push(HirStmt::Continue);
                return Some(None);
            }
            if target == loop_context.header {
                return Some(None);
            }
            // Lua 5.2+ 的 loop break 常常直接跳到 post-loop continuation，
            // 而不会先经过额外的 break pad。这里如果继续把它当普通线性 successor，
            // body lowering 就会错误地走出当前 loop，最终把 numeric-for/while
            // 整体打回 unresolved。对当前活跃 loop 来说，这条边的语义就是 break。
            if target == loop_context.post_loop {
                stmts.push(HirStmt::Break);
                return Some(None);
            }
            if Some(target) == loop_context.downstream_post_loop {
                stmts.push(HirStmt::Break);
                return Some(None);
            }
            if let Some(break_block) = loop_context.break_exits.get(&target) {
                stmts.extend(break_block.block.stmts.clone());
                self.visited.extend(break_block.blocks.iter().copied());
                return Some(None);
            }
        }
        if self.lowering.cfg.reachable_blocks.contains(&target) {
            Some(Some(target))
        } else {
            None
        }
    }

    pub(super) fn lower_block_prefix(
        &self,
        block: BlockRef,
        expect_branch_terminator: bool,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Vec<HirStmt>> {
        let empty_allowed_blocks = BTreeSet::new();
        let allowed_blocks = self
            .merge_allowed_blocks
            .get(&block)
            .unwrap_or(&empty_allowed_blocks);
        let overridden_phis = self.overrides.block_phi_exprs(block);
        let mut stmts = overridden_phis
            .into_iter()
            .flat_map(|phi_exprs| phi_exprs.iter())
            .map(|(phi_id, value)| {
                let temp = self.lowering.bindings.phi_temps[phi_id.index()];
                assign_stmt(vec![HirLValue::Temp(temp)], vec![value.clone()])
            })
            .collect::<Vec<_>>();
        stmts.extend(lower_phi_materialization_with_allowed_blocks_except(
            self.lowering,
            block,
            |phi_id| self.overrides.phi_is_suppressed_for_block(block, phi_id),
            allowed_blocks,
        ));
        // phi 恢复会从 predecessor def 重新构造表达式，其中可能引用一个已由更早
        // 结构证明为 alias 的 phi temp；该寄存器若在当前 block 已不再 live，普通
        // block-entry 传播看不到它，因此必须先应用全局 SSA alias 事实。
        let phi_temp_aliases = self.overrides.phi_temp_aliases();
        if !phi_temp_aliases.is_empty() {
            for stmt in &mut stmts {
                rewrite_stmt_exprs(stmt, phi_temp_aliases);
            }
        }
        let entry_expr_overrides = self.block_entry_expr_overrides(block);
        if let Some(entry_expr_overrides) = entry_expr_overrides {
            for stmt in &mut stmts {
                rewrite_stmt_exprs(stmt, entry_expr_overrides);
            }
        }
        // entry override 先把跨结构边界传入的 SSA 身份还原成既有值槽，再应用
        // target override。这样 `entry phi -> 外层 state` 的两段映射能在同一条
        // 物化语句里完整收敛，不会留下只在 SSA 图中存在的中间 temp。
        if !target_overrides.is_empty() {
            let phi_expr_overrides = temp_expr_overrides(target_overrides);
            for stmt in &mut stmts {
                rewrite_stmt_exprs(stmt, &phi_expr_overrides);
                rewrite_stmt_targets(stmt, target_overrides);
            }
        }
        for instr_index in self.block_prefix_instr_indices(block, expect_branch_terminator)? {
            let instr_ref = InstrRef(instr_index);
            let instr = &self.lowering.proto.instrs[instr_index];
            if self.overrides.instr_is_suppressed(instr_ref) {
                continue;
            }
            if matches!(instr, LowInstr::Close(_) | LowInstr::Tbc(_)) {
                match self.lowering.structure.cleanup_disposition(instr_ref) {
                    CleanupDisposition::LexicalScope(_) | CleanupDisposition::Unreachable => {
                        continue;
                    }
                    CleanupDisposition::ExplicitTbc
                    | CleanupDisposition::GenericFor(_)
                    | CleanupDisposition::ExplicitTbcBoundary => {}
                }
            }
            let mut lowered = lower_regular_instr(self.lowering, block, instr_ref, instr);
            if !phi_temp_aliases.is_empty() {
                for stmt in &mut lowered {
                    rewrite_stmt_exprs(stmt, phi_temp_aliases);
                }
            }
            if let Some(entry_expr_overrides) = entry_expr_overrides {
                for stmt in &mut lowered {
                    rewrite_stmt_exprs(stmt, entry_expr_overrides);
                }
            }
            apply_loop_rewrites(&mut lowered, target_overrides);
            stmts.extend(lowered);
        }

        Some(stmts)
    }

    fn lower_shared_stop_tail_block_clone(
        &self,
        block: BlockRef,
        stop: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirBlock> {
        if self.required_labels.contains(&block)
            || self.branch_by_header.contains_key(&block)
            || self.loop_headers.contains(&block)
            || !self
                .lowering
                .dataflow
                .phi_candidates_in_block(block)
                .is_empty()
            || self.lowering.cfg.unique_reachable_successor(block) != Some(stop)
        {
            return None;
        }
        if let Some((_instr_ref, instr)) = self.block_terminator(block)
            && is_control_terminator(instr)
            && !matches!(instr, LowInstr::Jump(_))
        {
            return None;
        }

        // 多个嵌套分支可共享同一个直线 continuation block。这里复制的是“到当前
        // stop 为止”的无 phi 线性尾块，运行时仍只会沿被选中的分支执行一次。
        Some(HirBlock {
            stmts: self.lower_block_prefix(block, false, target_overrides)?,
        })
    }

    pub(in crate::hir::analyze::structure) fn build_plain_branch_plan(
        &self,
        block: BlockRef,
    ) -> Option<StructuredBranchPlan> {
        let candidate = *self.branch_by_header.get(&block)?;

        match candidate.kind {
            BranchKind::IfElse => Some(StructuredBranchPlan {
                cond: self.lower_candidate_cond(block, candidate)?,
                then_entry: candidate.then_entry,
                else_entry: candidate.else_entry,
                merge: candidate.merge,
                consumed_headers: vec![block],
                consumed_blocks: vec![block],
            }),
            BranchKind::IfThen | BranchKind::Guard => Some(StructuredBranchPlan {
                cond: self.lower_candidate_cond(block, candidate)?,
                then_entry: candidate.then_entry,
                else_entry: None,
                merge: candidate.merge,
                consumed_headers: vec![block],
                consumed_blocks: vec![block],
            }),
        }
    }

    pub(super) fn lower_candidate_cond(
        &self,
        block: BlockRef,
        candidate: &BranchCandidate,
    ) -> Option<HirExpr> {
        self.lower_branch_cond_for_target(block, candidate.then_entry)
    }

    pub(super) fn lower_branch_cond_for_target(
        &self,
        block: BlockRef,
        target: BlockRef,
    ) -> Option<HirExpr> {
        let (instr_ref, instr) = self.block_terminator(block)?;
        let LowInstr::Branch(branch) = instr else {
            return None;
        };
        let control_cond = lower_branch_cond(self.lowering, block, instr_ref, branch.cond);
        let (then_target, else_target) = self.branch_target_blocks(block)?;

        let mut cond = if target == then_target {
            control_cond
        } else if target == else_target {
            control_cond.negate()
        } else {
            return None;
        };

        let phi_temp_aliases = self.overrides.phi_temp_aliases();
        if !phi_temp_aliases.is_empty() {
            rewrite_expr_temps(&mut cond, phi_temp_aliases);
        }
        if let Some(entry_expr_overrides) = self.block_entry_expr_overrides(block) {
            rewrite_expr_temps(&mut cond, entry_expr_overrides);
        }

        Some(cond)
    }

    fn branch_target_blocks(&self, block: BlockRef) -> Option<(BlockRef, BlockRef)> {
        let (_instr_ref, instr) = self.block_terminator(block)?;
        let LowInstr::Branch(branch) = instr else {
            return None;
        };

        Some((
            self.lowering.cfg.instr_to_block[branch.then_target.index()],
            self.lowering.cfg.instr_to_block[branch.else_target.index()],
        ))
    }

    pub(super) fn block_terminator(&self, block: BlockRef) -> Option<(InstrRef, &LowInstr)> {
        let instr_ref = self.lowering.cfg.blocks[block.index()].instrs.last()?;
        Some((instr_ref, &self.lowering.proto.instrs[instr_ref.index()]))
    }

    pub(super) fn block_prefix_instr_indices(
        &self,
        block: BlockRef,
        expect_branch_terminator: bool,
    ) -> Option<Range<usize>> {
        let range = self.lowering.cfg.blocks[block.index()].instrs;
        if range.is_empty() {
            return Some(range.start.index()..range.start.index());
        }

        let end = if let Some((_instr_ref, instr)) = self.block_terminator(block) {
            if expect_branch_terminator && !matches!(instr, LowInstr::Branch(_)) {
                return None;
            }

            if is_control_terminator(instr) {
                range.end() - 1
            } else {
                range.end()
            }
        } else {
            range.end()
        };
        Some(range.start.index()..end)
    }

    fn next_linear_successor(
        &self,
        block: BlockRef,
        stop: Option<BlockRef>,
    ) -> Option<Option<BlockRef>> {
        match self.lowering.cfg.reachable_successor_shape(block) {
            ReachableSuccessorShape::Empty => Some(None),
            ReachableSuccessorShape::Single(succ) if succ == self.lowering.cfg.exit_block => {
                Some(None)
            }
            ReachableSuccessorShape::Single(succ) if Some(succ) == stop => Some(Some(succ)),
            ReachableSuccessorShape::Single(succ) => Some(Some(succ)),
            ReachableSuccessorShape::Multiple => None,
        }
    }
}

fn shared_target_expr_from_overrides(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    target_overrides: &BTreeMap<TempId, HirLValue>,
) -> Option<HirExpr> {
    shared_expr_for_defs(
        &lowering.bindings.fixed_temps,
        short
            .value_incomings
            .iter()
            .flat_map(|incoming| lowering.dataflow.leaf_defs(incoming.value)),
        target_overrides,
    )
}
