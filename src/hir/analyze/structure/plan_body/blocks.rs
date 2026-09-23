//! 降低普通基本块、条件前缀和未决 phi；依赖稠密 terminator 计划，不负责边转移发射；例如跳过已被结构语法吸收的控制指令。

use super::*;

impl<'a, 'b> PlanBodyLowerer<'a, 'b> {
    pub(super) fn lower_block(
        &mut self,
        owner: RegionId,
        block: BlockRef,
    ) -> Result<PlannedBlock, HirLowerError> {
        #[cfg(debug_assertions)]
        self.mark_block_emitted(owner, block, "plan emits one basic block more than once")?;

        match self.lowering.structure.plan().block_emission(block) {
            Some(BlockEmissionPlan::Emit) => {}
            Some(BlockEmissionPlan::ForwardedControl { .. }) => {
                return Ok(PlannedBlock::new());
            }
            None => return self.invalid_region(owner, "block has no dense emission plan"),
        }

        let mut stmts = PlannedBlock::new();
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
        let regular_start =
            self.lower_block_entry(owner, block, prefix_start, regular_end, &mut stmts)?;
        stmts.append(self.lower_regular_range(owner, block, regular_start, regular_end)?);

        if let Some(cleanup) = trailing_cleanup {
            let Some(edge) = jump_edge else {
                return self.invalid_region(owner, "cleanup placement has no source jump");
            };
            stmts.extend_plain(self.lower_edge_source_effects(owner, edge)?);
            stmts.append(self.lower_regular_range(
                owner,
                block,
                cleanup.start.index(),
                cleanup.end(),
            )?);
            stmts.extend_plain(self.lower_edge_entry_effects(owner, edge)?);
            let edge_plan = self.planned_edge(owner, edge)?;
            stmts.extend_plain(self.lower_edge_after_effects(owner, edge, edge_plan)?);
            return Ok(stmts);
        }

        match terminator.kind {
            BlockTerminatorKind::Linear { edge } => {
                if let Some(edge) = edge {
                    stmts.extend_plain(self.lower_edge(owner, edge)?.stmts);
                }
            }
            BlockTerminatorKind::Jump { edge, .. } => {
                stmts.extend_plain(self.lower_edge(owner, edge)?.stmts);
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
                let then_block = self.lower_edge(owner, truthy)?;
                let else_block = self.lower_edge(owner, falsy)?;
                let mut cond = branch.cond;
                if branch.then_target == branch.else_target
                    && then_block.stmts.is_empty()
                    && else_block.stmts.is_empty()
                {
                    // 同一后继且两边均无边效果时，跳转极性不承载源码控制差异。
                    // 保留原 subject 的一次检查，去掉控制反转，避免空 if 重编译后反复翻转。
                    cond.negated = false;
                }
                let mut lowered = branch_stmt(
                    lower_branch_cond(self.lowering, block, instr, cond),
                    then_block,
                    Some(else_block),
                );
                if branch.then_target == branch.else_target
                    && let HirStmt::If(if_stmt) = &mut lowered
                {
                    if_stmt.preserves_empty_test = true;
                }
                stmts.push(lowered);
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
                stmts.extend_plain(terminal);
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
        Ok(stmts)
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
    ) -> Result<PlannedBlock, HirLowerError> {
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
        let mut stmts = PlannedBlock::new();
        self.emit_label(block, LabelPlacement::BeforeBlock, &mut stmts)?;
        stmts.extend_plain(self.lower_unresolved_phis(owner, block)?);
        stmts.append(self.lower_regular_range(
            owner,
            block,
            terminator.instrs.start.index(),
            instr.index(),
        )?);
        Ok(stmts)
    }

    /// 普通块和 loop syntax prefix 共用入口协议：AfterCleanup 先消费计划中的前缀，
    /// 再发射一次 label/phi；BeforeRegion 的 label 仍由 region owner 发射。
    pub(super) fn lower_block_entry(
        &mut self,
        owner: RegionId,
        block: BlockRef,
        start: usize,
        end: usize,
        stmts: &mut PlannedBlock,
    ) -> Result<usize, HirLowerError> {
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
        let remaining_start = match placement {
            Some(LabelPlacement::AfterCleanup(last)) => {
                if last.index() < start || last.index() >= end {
                    return self.invalid_region(
                        owner,
                        "label cleanup placement is outside the regular block prefix",
                    );
                }
                stmts.append(self.lower_regular_range(owner, block, start, last.index() + 1)?);
                self.emit_label(block, LabelPlacement::AfterCleanup(last), stmts)?;
                last.index() + 1
            }
            Some(LabelPlacement::BeforeRegion(_)) => start,
            Some(LabelPlacement::BeforeBlock) | None => {
                self.emit_label(block, LabelPlacement::BeforeBlock, stmts)?;
                start
            }
        };
        stmts.extend_plain(self.lower_unresolved_phis(owner, block)?);
        Ok(remaining_start)
    }

    pub(super) fn lower_regular_range(
        &mut self,
        owner: RegionId,
        block: BlockRef,
        start: usize,
        end: usize,
    ) -> Result<PlannedBlock, HirLowerError> {
        let mut output = PlannedBlock::new();
        let mut index = start;
        while index < end {
            let mut consumed_end = index + 1;
            let stmts = if let Some(protocol) = self
                .lowering
                .global_decls
                .owner(InstrRef(index))
                .filter(|protocol| {
                    protocol.end <= end
                        && !self
                            .lowering
                            .promotion_facts
                            .has_copy_root_boundary(index..protocol.end)
                        && self
                            .index
                            .scope_starts
                            .range(index + 1..protocol.end)
                            .next()
                            .is_none()
                        && self
                            .index
                            .scope_ends
                            .range(index + 1..protocol.end)
                            .next()
                            .is_none()
                }) {
                let stmt = super::super::super::instrs::lower_global_decl_owner(
                    self.lowering,
                    block,
                    InstrRef(index),
                    protocol,
                )
                .ok_or(HirLowerError::InvalidPlanRegion {
                    proto: self.proto.index(),
                    region: owner.index(),
                    detail: "frozen global declaration protocol no longer matches its owner",
                })?;
                consumed_end = protocol.end;
                vec![stmt]
            } else {
                self.lower_planned_regular(owner, block, InstrRef(index))?
            };
            self.emit_scoped_instr(owner, index, stmts, &mut output)?;
            // cleanup 可能已被结构协议消费；交接属于指令边界，仍须在 scope 结束前发射。
            for &(source, holder) in self
                .lowering
                .promotion_facts
                .copy_scope_handoffs(InstrRef(consumed_end - 1))
            {
                output.push(assign_stmt(
                    vec![HirLValue::Temp(holder)],
                    vec![self.lowering.bindings.expr_for_temp(source)],
                ));
            }
            self.end_lexical_scopes(consumed_end, &mut output);
            index = consumed_end;
        }
        Ok(output)
    }

    pub(super) fn emit_scoped_instr(
        &mut self,
        owner: RegionId,
        instr: usize,
        mut stmts: Vec<HirStmt>,
        output: &mut PlannedBlock,
    ) -> Result<(), HirLowerError> {
        if let Some(scopes) = self.index.scope_starts.get(&instr) {
            self.emitted_scope_boundaries += scopes.len();
            for &scope in scopes {
                if let Some(floor) = self.lowering.bindings.lexical_scopes[scope].initial_nil_floor
                {
                    let mut prefix = self.lowering.dataflow.instr_defs[instr]
                        .iter()
                        .filter(|&&def| self.lowering.dataflow.def_reg(def) < floor)
                        .filter_map(|def| {
                            crate::hir::common::HirBinding::from_lvalue(
                                &self.lowering.bindings.lvalue_for_reg_result(
                                    self.lowering.cfg.instr_to_block[instr],
                                    self.lowering.dataflow.def_reg(*def),
                                    self.lowering.bindings.fixed_temps[def.index()],
                                ),
                            )
                        })
                        .collect::<std::collections::BTreeSet<_>>();
                    if instr == 0 {
                        prefix.extend(
                            self.lowering
                                .bindings
                                .entry_local_regs
                                .iter()
                                .filter(|(reg, _)| **reg < floor)
                                .map(|(_, &local)| crate::hir::common::HirBinding::Local(local)),
                        );
                    }
                    let prefix = emission::split_nil_prefix(&mut stmts, &prefix).ok_or(
                        HirLowerError::InvalidPlanRegion {
                            proto: self.proto.index(),
                            region: owner.index(),
                            detail: "split nil scope contains an invalid declaration or write",
                        },
                    )?;
                    output.extend_plain(prefix);
                }
                output.start_scope(scope);
            }
        }
        output.extend_plain(stmts);
        Ok(())
    }

    pub(super) fn end_lexical_scopes(&mut self, instr: usize, output: &mut PlannedBlock) {
        if let Some(scopes) = self.index.scope_ends.get(&instr) {
            self.emitted_scope_boundaries += scopes.len();
            for &scope in scopes.iter().rev() {
                output.end_scope(scope);
            }
        }
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
                CleanupDisposition::LoopTbcBoundary(_) => {
                    // 根交接在原 CLOSE 完成后读取源码 local；发射这段新后缀后，
                    // loop 末尾不再是该 CLOSE 的原位置，必须保留显式 origins，
                    // 由 HIR close-scopes 在交接前恢复内层资源作用域。
                    if self
                        .lowering
                        .promotion_facts
                        .copy_scope_handoffs(instr_ref)
                        .is_empty()
                    {
                        return Ok(Vec::new());
                    }
                }
                CleanupDisposition::IncomingEdges => return Ok(Vec::new()),
                CleanupDisposition::ExplicitTbc | CleanupDisposition::ExplicitClose => {}
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
