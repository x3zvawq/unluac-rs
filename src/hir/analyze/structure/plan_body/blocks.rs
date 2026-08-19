//! 降低普通基本块、条件前缀和未决 phi；依赖稠密 terminator 计划，不负责边转移发射；例如跳过已被结构语法吸收的控制指令。

use super::*;

impl<'a, 'b> PlanBodyLowerer<'a, 'b> {
    pub(super) fn lower_block(
        &mut self,
        owner: RegionId,
        block: BlockRef,
    ) -> Result<HirBlock, HirLowerError> {
        #[cfg(debug_assertions)]
        self.mark_block_emitted(owner, block, "plan emits one basic block more than once")?;

        match self.lowering.structure.plan().block_emission(block) {
            Some(BlockEmissionPlan::Emit) => {}
            Some(BlockEmissionPlan::ForwardedControl { .. }) => {
                return Ok(HirBlock { stmts: Vec::new() });
            }
            None => return self.invalid_region(owner, "block has no dense emission plan"),
        }

        let mut stmts = Vec::new();
        let terminator = self.block_terminator(owner, block)?.clone();
        let range = terminator.instrs;
        let prefix_start = match self
            .lowering
            .structure
            .plan()
            .loop_exit_tail_for_block(block)
        {
            Some((_, tail))
                if tail.block == block
                    && tail.continuation == block
                    && tail.range.start == range.start
                    && tail.range.end() <= range.end() =>
            {
                tail.range.end()
            }
            Some(_) => {
                return self.invalid_region(owner, "loop exit tail block range is stale");
            }
            None => range.start.index(),
        };
        let prefix_end = terminator.kind.instr().map_or(range.end(), InstrRef::index);
        let jump_edge = match terminator.kind {
            BlockTerminatorKind::Jump { edge, .. } => Some(edge),
            _ => None,
        };
        let trailing_cleanup = jump_edge.and_then(|edge| {
            self.lowering
                .structure
                .plan()
                .edge_plan(edge)
                .and_then(EdgePlan::actions_before_trailing_cleanup)
        });
        let regular_end = if let Some(cleanup) = trailing_cleanup {
            if cleanup.is_empty()
                || cleanup.start.index() < prefix_start
                || cleanup.end() != prefix_end
            {
                return self.invalid_region(owner, "edge trailing-cleanup range is stale");
            }
            cleanup.start.index()
        } else {
            prefix_end
        };
        let placement = self
            .lowering
            .structure
            .plan()
            .label_for_block(block)
            .map(|label| {
                self.lowering
                    .structure
                    .plan()
                    .label(label)
                    .map(|label| label.placement)
                    .ok_or(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "block label has no frozen payload",
                    })
            })
            .transpose()?;
        let regular_start = match placement {
            Some(LabelPlacement::AfterCleanup(last)) => {
                if last.index() < prefix_start || last.index() >= regular_end {
                    return self.invalid_region(
                        owner,
                        "label cleanup placement is outside the regular block prefix",
                    );
                }
                for instr_index in prefix_start..=last.index() {
                    stmts.extend(self.lower_planned_regular(
                        owner,
                        block,
                        InstrRef(instr_index),
                    )?);
                }
                self.emit_label(block, LabelPlacement::AfterCleanup(last), &mut stmts)?;
                stmts.extend(self.lower_unresolved_phis(owner, block)?);
                last.index() + 1
            }
            Some(LabelPlacement::BeforeRegion(_)) => {
                stmts.extend(self.lower_unresolved_phis(owner, block)?);
                prefix_start
            }
            Some(LabelPlacement::BeforeBlock) | None => {
                self.emit_label(block, LabelPlacement::BeforeBlock, &mut stmts)?;
                stmts.extend(self.lower_unresolved_phis(owner, block)?);
                prefix_start
            }
        };
        for instr_index in regular_start..regular_end {
            let instr_ref = InstrRef(instr_index);
            stmts.extend(self.lower_planned_regular(owner, block, instr_ref)?);
        }

        if let Some(cleanup) = trailing_cleanup {
            let Some(edge) = jump_edge else {
                return self.invalid_region(owner, "cleanup placement has no source jump");
            };
            let edge_plan = self.planned_edge(owner, edge)?;
            stmts.extend(self.lower_edge_effects(owner, edge)?);
            for instr_index in cleanup.start.index()..cleanup.end() {
                stmts.extend(self.lower_planned_regular(owner, block, InstrRef(instr_index))?);
            }
            stmts.extend(self.lower_edge_after_effects(owner, edge, edge_plan)?);
            return Ok(HirBlock { stmts });
        }

        match terminator.kind {
            BlockTerminatorKind::Linear { edge } => {
                if let Some(edge) = edge {
                    stmts.extend(self.lower_edge(owner, edge)?.stmts);
                }
            }
            BlockTerminatorKind::Jump { edge, .. } => {
                stmts.extend(self.lower_edge(owner, edge)?.stmts);
            }
            BlockTerminatorKind::Branch {
                instr,
                truthy,
                falsy,
            } => {
                let Some(LowInstr::Branch(branch)) = self.lowering.proto.instrs.get(instr.index())
                else {
                    return self.invalid_region(
                        owner,
                        "branch terminator plan references a non-branch opcode",
                    );
                };
                stmts.push(branch_stmt(
                    lower_branch_cond(self.lowering, block, instr, branch.cond),
                    self.lower_edge(owner, truthy)?,
                    Some(self.lower_edge(owner, falsy)?),
                ));
            }
            BlockTerminatorKind::Return { instr, .. }
            | BlockTerminatorKind::TailCall { instr, .. } => {
                let Some(low) = self.lowering.proto.instrs.get(instr.index()) else {
                    return self.invalid_region(
                        owner,
                        "terminal plan references an instruction outside the proto",
                    );
                };
                let Some(terminal) = lower_terminal_instr(self.lowering, block, instr, low) else {
                    return self.invalid_region(owner, "planned terminal lowering rejected opcode");
                };
                stmts.extend(terminal);
            }
            BlockTerminatorKind::NumericForInit { .. }
            | BlockTerminatorKind::NumericForLoop { .. }
            | BlockTerminatorKind::GenericForLoop { .. } => {
                return self
                    .invalid_region(owner, "for control block is not owned by a loop region");
            }
            BlockTerminatorKind::SyntheticExit => {
                return self.invalid_region(owner, "synthetic exit is owned by an emitted region");
            }
        }
        Ok(HirBlock { stmts })
    }

    pub(super) fn single_block_region(&self, region: RegionId) -> Result<BlockRef, HirLowerError> {
        self.index
            .single_plain_block
            .get(region.index())
            .copied()
            .flatten()
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "region does not contain exactly one plain block",
            })
    }

    pub(super) fn lower_condition_prefix(
        &mut self,
        owner: RegionId,
        block: BlockRef,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        #[cfg(debug_assertions)]
        self.mark_block_emitted(
            owner,
            block,
            "plan emits one condition block more than once",
        )?;
        let terminator = self.block_terminator(owner, block)?.clone();
        let BlockTerminatorKind::Branch { instr, .. } = terminator.kind else {
            return self.invalid_region(owner, "condition block has no frozen branch terminator");
        };
        let mut stmts = Vec::new();
        self.emit_label(block, LabelPlacement::BeforeBlock, &mut stmts)?;
        stmts.extend(self.lower_unresolved_phis(owner, block)?);
        for instr_index in terminator.instrs.start.index()..instr.index() {
            let instr_ref = InstrRef(instr_index);
            stmts.extend(self.lower_planned_regular(owner, block, instr_ref)?);
        }
        Ok(stmts)
    }

    pub(super) fn lower_planned_regular(
        &self,
        owner: RegionId,
        block: BlockRef,
        instr_ref: InstrRef,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let Some(instr) = self.lowering.proto.instrs.get(instr_ref.index()) else {
            return self
                .invalid_region(owner, "regular instruction reference is outside the proto");
        };
        let absorbed_region_result_move = self
            .index
            .absorbed_region_result_moves
            .get(instr_ref.index())
            .copied()
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "RegionResult Move index does not cover one regular instruction",
            })?;
        if absorbed_region_result_move {
            if !matches!(instr, LowInstr::Move(_)) {
                return self.invalid_region(
                    owner,
                    "RegionResult Move index marks a non-Move instruction",
                );
            }
            return Ok(Vec::new());
        }
        if matches!(instr, LowInstr::GenericForPrep(_)) {
            return self.invalid_region(owner, "generic-for prep escaped its selected loop");
        }
        if let Some((_, tail)) = self
            .lowering
            .structure
            .plan()
            .loop_exit_tail_for_cleanup_instr(instr_ref)
        {
            if tail.cleanup_block != block {
                return self.invalid_region(owner, "loop exit tail cleanup index is stale");
            }
            return Ok(Vec::new());
        }
        if matches!(instr, LowInstr::Close(_) | LowInstr::Tbc(_)) {
            let disposition = self
                .lowering
                .structure
                .plan()
                .cleanup_disposition(instr_ref)
                .ok_or(HirLowerError::InvalidPlanRegion {
                    proto: self.proto.index(),
                    region: owner.index(),
                    detail: "cleanup instruction has no final disposition",
                })?;
            match disposition {
                CleanupDisposition::Unreachable | CleanupDisposition::LexicalScope(_) => {
                    return Ok(Vec::new());
                }
                // 退出块可以同时承载 loop 词法 cleanup 和循环后的用户指令，因此它
                // 不一定还是 loop region 的 child。最终 disposition 已在 Structure
                // 校验过 owner 与边界位置；HIR 只消费该结论，不能再按 lowering 栈重判。
                CleanupDisposition::LoopTbcBoundary(_) => return Ok(Vec::new()),
                CleanupDisposition::ExplicitTbcExit(_) => return Ok(Vec::new()),
                CleanupDisposition::ExplicitTbc | CleanupDisposition::ExplicitTbcBoundary(_) => {}
            }
        }
        lower_regular_instr(self.lowering, block, instr_ref, instr).ok_or(
            HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "regular block contains an unplanned control instruction",
            },
        )
    }

    pub(super) fn lower_unresolved_phis(
        &self,
        owner: RegionId,
        block: BlockRef,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let plan = self.lowering.structure.plan();
        let stmts = plan
            .phis_in_block(block)
            .iter()
            .map(|phi_id| {
                let phi = plan
                    .phi_plan(*phi_id)
                    .ok_or(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "block references a missing phi plan",
                    })?;
                if !phi.has_unresolved() {
                    return Ok(None);
                }
                if self
                    .index
                    .unresolved_requirement
                    .get(phi.phi.index())
                    .copied()
                    .flatten()
                    != Some((phi.block, phi.reg))
                {
                    return Err(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "unresolved phi has no matching plan requirement",
                    });
                }
                let target = self
                    .lowering
                    .bindings
                    .phi_temps
                    .get(phi.phi.index())
                    .copied()
                    .ok_or(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "unresolved phi has no HIR temp target",
                    })?;
                let incoming = phi
                    .incomings
                    .iter()
                    .map(|incoming| {
                        let edge = incoming
                            .edge
                            .map_or_else(|| "entry".to_owned(), |edge| edge.to_string());
                        format!("{edge}:{}", incoming.value)
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                Ok(Some(assign_stmt(
                    vec![self.lowering.bindings.lvalue_for_temp(target)],
                    vec![super::super::super::helpers::unresolved_expr(format!(
                        "unresolved {} for {} at block {}; incoming [{}]",
                        phi.phi, phi.reg, phi.block, incoming
                    ))],
                )))
            })
            .collect::<Result<Vec<_>, HirLowerError>>()?;
        Ok(stmts.into_iter().flatten().collect())
    }
}
