//! 局部不可结构化 island 的保守 lowering。
//!
//! island 只扩到不可规约 SCC 及其通往唯一后支配 continuation 的空 jump pad。每个
//! block 仍按 `StructurePlan` 的直接 owner 分派：Branch 使用稳定 candidate identity，
//! plain Loop header 可按真实 CFG 边局部降低；numeric/generic-for 协议只复用既有 loop
//! candidate，不降级成 raw 控制。无法证明的 cleanup、循环控制或出口边界直接退让。

use super::*;

#[derive(Clone, Copy)]
struct UnstructuredEntryArm {
    pad: Option<BlockRef>,
    island_edge: crate::structure::EdgeRef,
    region_id: RegionId,
}

impl StructuredBodyLowerer<'_, '_> {
    pub(super) fn try_lower_unstructured_entry_branch(
        &mut self,
        block: BlockRef,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let BlockOwner::Branch(candidate_id) = self.lowering.structure.block_owner(block)? else {
            return None;
        };
        let candidate = self.lowering.structure.branch_candidate(candidate_id)?;
        let (then_edge, else_edge) = self.lowering.cfg.branch_edges(block)?;
        let then_target = self.lowering.cfg.edges[then_edge.index()].to;
        let else_target = self.lowering.cfg.edges[else_edge.index()].to;
        let (then_edge, else_edge) = if candidate.then_entry == then_target {
            (then_edge, else_edge)
        } else if candidate.then_entry == else_target {
            (else_edge, then_edge)
        } else {
            return None;
        };
        let then_arm = self.unstructured_entry_arm(then_edge)?;
        let else_arm = self.unstructured_entry_arm(else_edge)?;
        if then_arm.region_id != else_arm.region_id {
            return None;
        }
        let region = self.lowering.structure.region(then_arm.region_id)?;
        if self.visited.contains(&region.entry) {
            return None;
        }

        let mut cond = self.lower_candidate_cond(block, candidate)?;
        rewrite_expr_temps(&mut cond, &temp_expr_overrides(target_overrides));
        self.visited.insert(block);
        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        let next = Some(region.entry);
        stmts.push(branch_stmt(
            cond,
            self.lower_unstructured_entry_arm(then_arm, next, target_overrides)?,
            Some(self.lower_unstructured_entry_arm(else_arm, next, target_overrides)?),
        ));
        Some(Some(region.entry))
    }

    fn unstructured_entry_arm(
        &self,
        entry_edge: crate::structure::EdgeRef,
    ) -> Option<UnstructuredEntryArm> {
        let target = self.lowering.cfg.edges.get(entry_edge.index())?.to;
        if let Some(region_id) = self.lowering.structure.unstructured_region(target) {
            return matches!(
                self.lowering.structure.edge_owner(entry_edge),
                Some(EdgeOwner::Goto(_))
            )
            .then_some(UnstructuredEntryArm {
                pad: None,
                island_edge: entry_edge,
                region_id,
            });
        }

        if !matches!(
            self.lowering.structure.block_owner(target),
            Some(BlockOwner::Linear)
        ) || self.required_labels.contains(&target)
            || self.lowering.cfg.reachable_predecessors(target)
                != [self.lowering.cfg.edges[entry_edge.index()].from]
            || !matches!(self.block_terminator(target), Some((_, LowInstr::Jump(_))))
            || !self
                .block_prefix_instr_indices(target, false)?
                .all(|index| self.unstructured_prefix_instr_is_omitted(InstrRef(index)))
        {
            return None;
        }

        let mut outgoing = self.lowering.cfg.succs[target.index()]
            .iter()
            .copied()
            .filter(|edge| {
                self.lowering
                    .cfg
                    .reachable_blocks
                    .contains(&self.lowering.cfg.edges[edge.index()].to)
            });
        let island_edge = outgoing.next()?;
        if outgoing.next().is_some()
            || !matches!(
                self.lowering.structure.edge_owner(island_edge),
                Some(EdgeOwner::Goto(_))
            )
        {
            return None;
        }
        let region_id = self
            .lowering
            .structure
            .unstructured_region(self.lowering.cfg.edges[island_edge.index()].to)?;
        Some(UnstructuredEntryArm {
            pad: Some(target),
            island_edge,
            region_id,
        })
    }

    fn lower_unstructured_entry_arm(
        &mut self,
        arm: UnstructuredEntryArm,
        next: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirBlock> {
        let Some(pad) = arm.pad else {
            return self.lower_required_goto_edge(arm.island_edge, next, target_overrides);
        };

        if !self.visited.insert(pad) {
            return None;
        }
        let mut stmts = self.lower_block_prefix(pad, false, target_overrides)?;
        stmts.extend(
            self.lower_required_goto_edge(arm.island_edge, next, target_overrides)?
                .stmts,
        );
        Some(HirBlock { stmts })
    }

    pub(super) fn lower_unstructured_region(
        &mut self,
        start: BlockRef,
        region_id: RegionId,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        if !target_overrides.is_empty() {
            return None;
        }
        let region = self.lowering.structure.region(region_id)?;
        if !region.blocks.contains(&start) {
            return None;
        }
        let layout = self.lowering.structure.unstructured_layout(region_id)?;
        let continuation = layout.continuation;
        if stop.is_some_and(|stop| layout.blocks.contains(&stop)) {
            return None;
        }

        let mut blocks = self
            .lowering
            .cfg
            .block_order
            .iter()
            .copied()
            .filter(|block| layout.blocks.contains(block))
            .collect::<Vec<_>>();
        let start_index = blocks.iter().position(|block| *block == start)?;
        blocks.rotate_left(start_index);
        let continuation_is_loop_escape = self.unstructured_loop_escape_target(continuation);
        if continuation != self.lowering.cfg.exit_block {
            let has_outside_predecessor =
                self.lowering.cfg.preds[continuation.index()]
                    .iter()
                    .any(|edge_ref| {
                        let predecessor = self.lowering.cfg.edges[edge_ref.index()].from;
                        self.lowering.cfg.reachable_blocks.contains(&predecessor)
                            && !layout.blocks.contains(&predecessor)
                    });
            if has_outside_predecessor
                && self
                    .lowering
                    .dataflow
                    .phi_candidates_in_block(continuation)
                    .iter()
                    .any(|phi| !self.lowering.structure.phi_is_dead(phi.id))
            {
                return None;
            }
            if !has_outside_predecessor && !continuation_is_loop_escape {
                for phi in self.lowering.dataflow.phi_candidates_in_block(continuation) {
                    self.overrides.suppress_phi(phi.id);
                }
            }
        }

        for (index, block) in blocks.iter().copied().enumerate() {
            if self.visited.contains(&block) {
                continue;
            }
            if block != start {
                self.emit_required_label(block, stmts);
            }
            let checkpoint = self.checkpoint_state(stmts.len());
            if let Some(loop_next) = self
                .try_lower_unstructured_for(block, stop, stmts, target_overrides)
                .flatten()
            {
                let layout_next = blocks[index + 1..]
                    .iter()
                    .copied()
                    .find(|candidate| !self.visited.contains(candidate))
                    .or_else(|| (!continuation_is_loop_escape).then_some(continuation));
                if Some(loop_next) != layout_next {
                    if self.unstructured_loop_escape_target(loop_next) {
                        stmts.push(HirStmt::Break);
                    } else if loop_next != self.lowering.cfg.exit_block {
                        self.required_labels.insert(loop_next);
                        stmts.extend(goto_block(self.label_map[&loop_next]).stmts);
                    }
                }
                continue;
            }
            self.restore_state_checkpoint(checkpoint, stmts);
            if !self.visited.insert(block) {
                return None;
            }
            let next = blocks
                .get(index + 1)
                .copied()
                .or_else(|| (!continuation_is_loop_escape).then_some(continuation));
            stmts.extend(self.lower_unstructured_block(block, next)?);
        }

        Some(
            (continuation != self.lowering.cfg.exit_block && !continuation_is_loop_escape)
                .then_some(continuation),
        )
    }

    fn try_lower_unstructured_for(
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
        None
    }

    fn lower_unstructured_block(
        &mut self,
        block: BlockRef,
        next: Option<BlockRef>,
    ) -> Option<Vec<HirStmt>> {
        match self.lowering.structure.block_owner(block)? {
            BlockOwner::Branch(candidate_id) => {
                self.lower_unstructured_branch(block, candidate_id, next)
            }
            BlockOwner::Linear | BlockOwner::Loop(_) | BlockOwner::Unstructured(_) => {
                self.lower_unstructured_plain_block(block, next)
            }
            BlockOwner::Unreachable | BlockOwner::Exit => None,
        }
    }

    fn lower_unstructured_branch(
        &mut self,
        block: BlockRef,
        candidate_id: BranchCandidateId,
        next: Option<BlockRef>,
    ) -> Option<Vec<HirStmt>> {
        let candidate = self.lowering.structure.branch_candidate(candidate_id)?;
        if candidate.header != block {
            return None;
        }
        let (then_edge, else_edge) = self.lowering.cfg.branch_edges(block)?;
        let then_target = self.lowering.cfg.edges[then_edge.index()].to;
        let else_target = self.lowering.cfg.edges[else_edge.index()].to;
        let (owned_then, owned_else) = if candidate.then_entry == then_target {
            (then_edge, else_edge)
        } else if candidate.then_entry == else_target {
            (else_edge, then_edge)
        } else {
            return None;
        };

        let mut stmts = self.lower_unstructured_prefix(block, true)?;
        stmts.push(branch_stmt(
            self.lower_candidate_cond(block, candidate)?,
            self.lower_unstructured_edge(owned_then, next)?,
            Some(self.lower_unstructured_edge(owned_else, next)?),
        ));
        Some(stmts)
    }

    fn lower_unstructured_plain_block(
        &mut self,
        block: BlockRef,
        next: Option<BlockRef>,
    ) -> Option<Vec<HirStmt>> {
        let mut stmts = self.lower_unstructured_prefix(block, false)?;
        let Some((instr_ref, instr)) = self.block_terminator(block) else {
            if let Some(target) = self.lowering.cfg.unique_reachable_successor(block) {
                stmts.extend(self.lower_unstructured_edge_to(block, target, next)?.stmts);
            }
            return Some(stmts);
        };
        if !instr.is_control_terminator() {
            let target = self.lowering.cfg.unique_reachable_successor(block)?;
            stmts.extend(self.lower_unstructured_edge_to(block, target, next)?.stmts);
            return Some(stmts);
        }
        match instr {
            LowInstr::Jump(jump) => {
                let target = self.lowering.cfg.instr_to_block[jump.target.index()];
                stmts.extend(self.lower_unstructured_edge_to(block, target, next)?.stmts);
            }
            LowInstr::Return(_) | LowInstr::TailCall(_) => {
                stmts.extend(lower_control_instr(
                    self.lowering,
                    block,
                    instr_ref,
                    instr,
                    &BTreeMap::new(),
                ));
            }
            LowInstr::Branch(branch) => {
                let (then_edge, else_edge) = self.lowering.cfg.branch_edges(block)?;
                stmts.push(branch_stmt(
                    lower_branch_cond(self.lowering, block, instr_ref, branch.cond),
                    self.lower_unstructured_edge(then_edge, next)?,
                    Some(self.lower_unstructured_edge(else_edge, next)?),
                ));
            }
            LowInstr::NumericForInit(_)
            | LowInstr::NumericForLoop(_)
            | LowInstr::GenericForLoop(_) => return None,
            _ => return None,
        }
        Some(stmts)
    }

    fn lower_unstructured_prefix(
        &self,
        block: BlockRef,
        expect_branch: bool,
    ) -> Option<Vec<HirStmt>> {
        let mut stmts = Vec::new();
        for index in self.block_prefix_instr_indices(block, expect_branch)? {
            let instr_ref = InstrRef(index);
            if self.unstructured_prefix_instr_is_omitted(instr_ref) {
                continue;
            }
            if matches!(
                self.lowering.proto.instrs[index],
                LowInstr::Close(_) | LowInstr::Tbc(_)
            ) && matches!(
                self.lowering.structure.cleanup_disposition(instr_ref),
                CleanupDisposition::GenericFor(_)
            ) {
                return None;
            }
            stmts.extend(lower_regular_instr(
                self.lowering,
                block,
                instr_ref,
                &self.lowering.proto.instrs[index],
            ));
        }
        Some(stmts)
    }

    fn lower_unstructured_edge(
        &mut self,
        edge_ref: crate::structure::EdgeRef,
        next: Option<BlockRef>,
    ) -> Option<HirBlock> {
        let edge = self.lowering.cfg.edges.get(edge_ref.index())?;
        let mut stmts = lower_edge_phi_copies_for_edge(self.lowering, edge_ref);
        if self.unstructured_loop_escape_target(edge.to) {
            stmts.push(HirStmt::Break);
        } else if edge.to != self.lowering.cfg.exit_block && Some(edge.to) != next {
            self.required_labels.insert(edge.to);
            stmts.extend(goto_block(*self.label_map.get(&edge.to)?).stmts);
        }
        Some(HirBlock { stmts })
    }

    fn lower_unstructured_edge_to(
        &mut self,
        from: BlockRef,
        to: BlockRef,
        next: Option<BlockRef>,
    ) -> Option<HirBlock> {
        let mut matching = self.lowering.cfg.succs[from.index()]
            .iter()
            .copied()
            .filter(|edge_ref| self.lowering.cfg.edges[edge_ref.index()].to == to);
        let edge_ref = matching.next()?;
        if matching.next().is_some() {
            return None;
        }
        self.lower_unstructured_edge(edge_ref, next)
    }

    fn unstructured_loop_escape_target(&self, target: BlockRef) -> bool {
        self.active_loops.last().is_some_and(|loop_context| {
            target == loop_context.post_loop || Some(target) == loop_context.downstream_post_loop
        })
    }

    fn lower_required_goto_edge(
        &self,
        edge_ref: crate::structure::EdgeRef,
        next: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirBlock> {
        let edge = self.lowering.cfg.edges.get(edge_ref.index())?;
        let mut stmts = lower_edge_phi_copies_for_edge(self.lowering, edge_ref);
        apply_loop_rewrites(&mut stmts, target_overrides);
        if Some(edge.to) != next {
            stmts.extend(goto_block(*self.label_map.get(&edge.to)?).stmts);
        }
        Some(HirBlock { stmts })
    }

    fn unstructured_prefix_instr_is_omitted(&self, instr_ref: InstrRef) -> bool {
        matches!(
            self.lowering.proto.instrs[instr_ref.index()],
            LowInstr::Close(_) | LowInstr::Tbc(_)
        ) && matches!(
            self.lowering.structure.cleanup_disposition(instr_ref),
            CleanupDisposition::LexicalScope(_) | CleanupDisposition::Unreachable
        )
    }

    pub(super) fn required_goto_edge(
        &self,
        from: BlockRef,
        to: BlockRef,
    ) -> Option<crate::structure::EdgeRef> {
        let mut matching = self.lowering.cfg.succs[from.index()]
            .iter()
            .copied()
            .filter(|edge_ref| {
                self.lowering.cfg.edges[edge_ref.index()].to == to
                    && self
                        .lowering
                        .structure
                        .edge_owner(*edge_ref)
                        .and_then(|owner| match owner {
                            EdgeOwner::Goto(id) => self.lowering.structure.goto_requirement(id),
                            _ => None,
                        })
                        .is_some_and(|requirement| {
                            requirement.reason != GotoReason::UnstructuredContinueLike
                        })
            });
        let edge = matching.next()?;
        matching.next().is_none().then_some(edge)
    }
}
