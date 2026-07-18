//! 这个文件承载 active loop context 的构建与 loop exit 分类。
//!
//! loop lowering 进入 body 前需要知道哪些出口是本地 break pad、哪个 block 是 continue
//! target、哪些 goto requirement 表示 continue-like 边。本文件只把 `StructureFacts` 中
//! 已有的 loop/exit/goto 信息整理成 `ActiveLoopContext`，不决定 loop state 身份，也
//! 不重新识别 branch 或 short-circuit 结构。
//!
//! 输入形状：`LoopCandidate { exits: [post, cleanup_pad], continue_target }`
//! 输出形状：`ActiveLoopContext { break_exits: cleanup_pad -> BreakExitBlock, ... }`

use super::*;

impl StructuredBodyLowerer<'_, '_> {
    pub(super) fn build_active_loop_context(
        &self,
        candidate_id: LoopCandidateId,
        candidate: &LoopCandidate,
        post_loop: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
        states: &[LoopStateSlot],
    ) -> Option<ActiveLoopContext> {
        let downstream_post_loop = self.normalized_post_loop_successor(post_loop);
        let mut break_exits = BTreeMap::new();
        let mut goto_exits = BTreeSet::new();
        let unstructured_region = self
            .lowering
            .structure
            .unstructured_region(candidate.header);
        for exit in candidate.exits.iter().copied().filter(|exit| {
            *exit != post_loop && !self.loop_exit_enters_nested_loop(candidate_id, *exit)
        }) {
            if unstructured_region.is_some()
                && self.lowering.structure.unstructured_region(exit) == unstructured_region
            {
                goto_exits.insert(exit);
                continue;
            }
            let Some(break_exit) = self.lower_loop_break_exit(
                candidate,
                exit,
                post_loop,
                downstream_post_loop,
                target_overrides,
                states,
            )?
            else {
                continue;
            };
            break_exits.insert(exit, break_exit);
        }
        let continue_target = candidate.continue_target;
        let continue_entries = candidate
            .continue_edges
            .iter()
            .map(|edge| self.lowering.cfg.edges[edge.index()].to)
            .collect();
        let mut continue_sources = if self.can_emit_continue_stmt() {
            candidate
                .continue_edges
                .iter()
                .map(|edge| self.lowering.cfg.edges[edge.index()].from)
                .collect::<BTreeSet<_>>()
        } else {
            BTreeSet::new()
        };
        if let Some(target) = continue_target {
            continue_sources.extend(
                self.lowering
                    .structure
                    .goto_requirements
                    .iter()
                    .filter(|requirement| {
                        let edge = self.lowering.cfg.edges[requirement.edge.index()];
                        requirement.reason == crate::structure::GotoReason::UnstructuredContinueLike
                            && edge.to == target
                            && candidate.blocks.contains(&edge.from)
                    })
                    .map(|requirement| self.lowering.cfg.edges[requirement.edge.index()].from),
            );
        }

        Some(ActiveLoopContext {
            candidate_id,
            header: candidate.header,
            loop_blocks: BTreeSet::new(),
            branch_region_header: None,
            post_loop,
            downstream_post_loop,
            continue_target,
            body_stop: None,
            continue_sources,
            continue_entries,
            break_exits,
            goto_exits,
            state_slots: Vec::new(),
            post_loop_break: None,
        })
    }

    pub(in crate::hir::analyze::structure) fn normalized_post_loop_successor(
        &self,
        post_loop: BlockRef,
    ) -> Option<BlockRef> {
        if !self
            .lower_block_prefix(post_loop, false, &BTreeMap::new())?
            .is_empty()
        {
            return None;
        }

        match self.block_terminator(post_loop) {
            Some((_instr_ref, LowInstr::Jump(jump))) => {
                Some(self.lowering.cfg.instr_to_block[jump.target.index()])
            }
            Some((_instr_ref, instr)) if !instr.is_control_terminator() => {
                self.lowering.cfg.unique_reachable_successor(post_loop)
            }
            None => self.lowering.cfg.unique_reachable_successor(post_loop),
            Some(_) => None,
        }
    }

    pub(super) fn loop_state_inside_exit_blocks(
        &self,
        candidate_id: LoopCandidateId,
        candidate: &LoopCandidate,
        post_loop: BlockRef,
    ) -> Option<BTreeSet<BlockRef>> {
        let downstream_post_loop = self.normalized_post_loop_successor(post_loop);
        let body_blocks = loop_body_blocks(candidate);
        let mut inside_blocks = body_blocks.clone();
        for exit in candidate.exits.iter().copied().filter(|exit| {
            *exit != post_loop && !self.loop_exit_enters_nested_loop(candidate_id, *exit)
        }) {
            if self
                .lower_loop_break_exit(
                    candidate,
                    exit,
                    post_loop,
                    downstream_post_loop,
                    &BTreeMap::new(),
                    &[],
                )?
                .is_some()
            {
                inside_blocks.insert(exit);
            }
        }
        Some(inside_blocks)
    }

    fn lower_loop_break_exit(
        &self,
        candidate: &LoopCandidate,
        exit: BlockRef,
        post_loop: BlockRef,
        downstream_post_loop: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
        states: &[LoopStateSlot],
    ) -> Option<Option<BreakExitBlock>> {
        if block_is_terminal_exit(self.lowering, exit)
            || self.loop_exit_region_is_terminal(candidate, exit, post_loop, downstream_post_loop)
            || downstream_post_loop == Some(exit)
        {
            return Some(None);
        }

        match self.lower_break_exit_pad(
            exit,
            post_loop,
            downstream_post_loop,
            target_overrides,
            states,
        ) {
            Some(break_exit) => Some(Some(break_exit)),
            // for-like 的 natural-loop core 会把仍在词法 body 内的入口也暴露为 exit。
            // 它不满足 break-pad 合同，应留给 body walker，而不应让整个 loop 回退。
            None if loop_body_blocks(candidate).contains(&exit) => Some(None),
            None => None,
        }
    }

    fn loop_exit_enters_nested_loop(&self, candidate_id: LoopCandidateId, exit: BlockRef) -> bool {
        // while 的 canonical body scope 刻意保持 natural-loop core；若某条分支进入内层
        // loop 后直接 break 外层，内层 blocks 不会回到外层 header，因而不可能是该 core
        // 的子集。header/preheader 已是 Structure 给出的精确入口 owner；当前 loop 的
        // canonical post 又已在调用处排除，因此这里不能再用 body-scope subset 否定它。
        let candidates = &self.lowering.structure.loop_candidates;
        let header = candidates[candidate_id.index()].header;
        candidates.iter().any(|nested| {
            nested.header != header && (nested.header == exit || nested.preheader == Some(exit))
        })
    }

    fn loop_exit_region_is_terminal(
        &self,
        candidate: &LoopCandidate,
        exit: BlockRef,
        post_loop: BlockRef,
        downstream_post_loop: Option<BlockRef>,
    ) -> bool {
        fn visit(
            lowerer: &StructuredBodyLowerer<'_, '_>,
            candidate: &LoopCandidate,
            block: BlockRef,
            post_loop: BlockRef,
            downstream_post_loop: Option<BlockRef>,
            visiting: &mut BTreeSet<BlockRef>,
            memo: &mut BTreeMap<BlockRef, bool>,
        ) -> bool {
            if block == post_loop
                || Some(block) == downstream_post_loop
                || candidate.blocks.contains(&block)
                || !lowerer.lowering.cfg.reachable_blocks.contains(&block)
            {
                return false;
            }
            if block == lowerer.lowering.cfg.exit_block
                || block_is_terminal_exit(lowerer.lowering, block)
            {
                return true;
            }
            if let Some(result) = memo.get(&block).copied() {
                return result;
            }
            if !visiting.insert(block) {
                return false;
            }

            let result = lowerer.lowering.cfg.succs[block.index()]
                .iter()
                .all(|edge_ref| {
                    let successor = lowerer.lowering.cfg.edges[edge_ref.index()].to;
                    visit(
                        lowerer,
                        candidate,
                        successor,
                        post_loop,
                        downstream_post_loop,
                        visiting,
                        memo,
                    )
                });
            visiting.remove(&block);
            memo.insert(block, result);
            result
        }

        // numeric/generic for 的 body 可能只有“命中后 return”的路径；CFG 上这会表现为
        // loop header 的一个非 post-loop exit，但它不是 break pad，不需要合成 break。
        // 只有当 exit region 的所有路径都在回到 post-loop 或 loop blocks 前终结时，
        // 才把它归为 terminal body exit。
        visit(
            self,
            candidate,
            exit,
            post_loop,
            downstream_post_loop,
            &mut BTreeSet::new(),
            &mut BTreeMap::new(),
        )
    }

    pub(super) fn loop_exit_terminates(&self, candidate: &LoopCandidate, exit: BlockRef) -> bool {
        // LuaJIT UCLO 会把源码 return/break 的词法收尾拆成 Close + Jump pad；
        // terminal owner 必须看完整出口 region，不能只看入口块的末条指令。
        block_is_terminal_exit(self.lowering, exit)
            || self.loop_exit_region_is_terminal(
                candidate,
                exit,
                self.lowering.cfg.exit_block,
                None,
            )
    }
}
