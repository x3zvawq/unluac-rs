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
        candidate: &LoopCandidate,
        post_loop: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
        states: &[LoopStateSlot],
    ) -> Option<ActiveLoopContext> {
        let downstream_post_loop = self.normalized_post_loop_successor(post_loop);
        let mut break_exits = BTreeMap::new();
        for exit in candidate
            .exits
            .iter()
            .copied()
            .filter(|exit| *exit != post_loop)
        {
            if block_is_terminal_exit(self.lowering, exit) {
                continue;
            }
            if self.loop_exit_region_is_terminal(candidate, exit, post_loop, downstream_post_loop) {
                continue;
            }
            // 有些 loop 的“直接退出块”只是一个线性 pad，真正的 post-loop continuation
            // 在这个 pad 后面。对这种形状，pad 的下游不应该再被当成额外的 break exit，
            // 否则 repeat/for 会被误判成“多出口 break loop”，整片结构都会回退。
            if downstream_post_loop == Some(exit) {
                continue;
            }
            break_exits.insert(
                exit,
                self.lower_break_exit_pad(
                    exit,
                    post_loop,
                    downstream_post_loop,
                    target_overrides,
                    states,
                )?,
            );
        }
        let continue_target = candidate.continue_target;
        let continue_sources = continue_target
            .map(|target| {
                self.lowering
                    .structure
                    .goto_requirements
                    .iter()
                    .filter(|requirement| {
                        requirement.reason == crate::structure::GotoReason::UnstructuredContinueLike
                            && requirement.to == target
                            && candidate.blocks.contains(&requirement.from)
                    })
                    .map(|requirement| requirement.from)
                    .collect::<BTreeSet<_>>()
            })
            .unwrap_or_default();

        Some(ActiveLoopContext {
            header: candidate.header,
            loop_blocks: BTreeSet::new(),
            post_loop,
            downstream_post_loop,
            continue_target,
            continue_sources,
            break_exits,
            state_slots: Vec::new(),
        })
    }

    pub(super) fn normalized_post_loop_successor(&self, post_loop: BlockRef) -> Option<BlockRef> {
        let (_instr_ref, instr) = self.block_terminator(post_loop)?;
        let LowInstr::Jump(jump) = instr else {
            return None;
        };
        let target = self.lowering.cfg.instr_to_block[jump.target.index()];
        self.lower_block_prefix(post_loop, false, &BTreeMap::new())?;
        Some(target)
    }

    pub(super) fn loop_state_inside_exit_blocks(
        &self,
        candidate: &LoopCandidate,
        post_loop: BlockRef,
    ) -> Option<BTreeSet<BlockRef>> {
        let downstream_post_loop = self.normalized_post_loop_successor(post_loop);
        let mut inside_blocks = candidate.blocks.clone();
        for exit in candidate
            .exits
            .iter()
            .copied()
            .filter(|exit| *exit != post_loop)
        {
            if block_is_terminal_exit(self.lowering, exit) {
                continue;
            }
            if self.loop_exit_region_is_terminal(candidate, exit, post_loop, downstream_post_loop) {
                continue;
            }
            if downstream_post_loop == Some(exit) {
                continue;
            }
            self.lower_break_exit_pad(
                exit,
                post_loop,
                downstream_post_loop,
                &BTreeMap::new(),
                &[],
            )?;
            inside_blocks.insert(exit);
        }
        Some(inside_blocks)
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
}
