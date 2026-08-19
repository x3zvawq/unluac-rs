//! 降低边转移、清理、phi copy 与循环值动作；依赖最终 EdgePlan/requirements，不负责目标标签布局；例如发射 break/continue/goto 前后的动作。

use super::*;

impl<'a, 'b> PlanBodyLowerer<'a, 'b> {
    pub(super) fn lower_edge(
        &self,
        owner: RegionId,
        edge: EdgeRef,
    ) -> Result<HirBlock, HirLowerError> {
        let plan = self.planned_edge(owner, edge)?;
        if plan.actions_before_trailing_cleanup().is_some() {
            return self.invalid_region(
                owner,
                "trailing-cleanup edge actions escaped their source jump",
            );
        }
        let mut stmts = self.lower_edge_effects(owner, edge)?;
        stmts.extend(self.lower_edge_after_effects(owner, edge, plan)?);
        Ok(HirBlock { stmts })
    }

    pub(super) fn planned_edge(
        &self,
        owner: RegionId,
        edge: EdgeRef,
    ) -> Result<&EdgePlan, HirLowerError> {
        let plan = self.lowering.structure.plan().edge_plan(edge).ok_or(
            HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "CFG edge has no final edge plan",
            },
        )?;
        if !self.edge_requirement_matches(edge, plan.transfer) {
            return self.invalid_region(owner, "edge transfer contradicts plan requirements");
        }
        Ok(plan)
    }

    pub(super) fn lower_edge_after_effects(
        &self,
        owner: RegionId,
        edge: EdgeRef,
        plan: &EdgePlan,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let mut stmts = Vec::new();
        if let Some((loop_id, tail)) = self.lowering.structure.plan().loop_exit_tail_for_edge(edge)
        {
            let loop_region = self.lowering.structure.plan().loop_region(loop_id).ok_or(
                HirLowerError::InvalidPlanRegion {
                    proto: self.proto.index(),
                    region: owner.index(),
                    detail: "loop exit tail has no owning loop region",
                },
            )?;
            if !self.loop_contains_region(loop_region, owner)
                || tail.normal_exit != edge
                || plan.transfer != EdgeTransfer::Break(loop_region)
            {
                return self.invalid_region(owner, "loop exit tail edge ownership is stale");
            }
            stmts.extend(self.lower_loop_exit_tail(loop_region, tail.block, tail.range)?);
        }
        match plan.transfer {
            EdgeTransfer::Unreachable => {
                return self.invalid_region(owner, "reachable region uses unreachable edge plan");
            }
            EdgeTransfer::Fallthrough | EdgeTransfer::BranchArm(_) | EdgeTransfer::LoopBack(_) => {}
            EdgeTransfer::Return | EdgeTransfer::TailCall => {
                let cfg_edge = self.lowering.cfg.edges.get(edge.index()).ok_or(
                    HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "terminal transfer references a missing CFG edge",
                    },
                )?;
                if !matches!(cfg_edge.kind, EdgeKind::Return | EdgeKind::TailCall) {
                    let terminator = self.block_terminator(owner, cfg_edge.to)?;
                    let (instr, matches_transfer) = match terminator.kind {
                        BlockTerminatorKind::Return { instr, .. } => {
                            (instr, plan.transfer == EdgeTransfer::Return)
                        }
                        BlockTerminatorKind::TailCall { instr, .. } => {
                            (instr, plan.transfer == EdgeTransfer::TailCall)
                        }
                        _ => {
                            return self.invalid_region(
                                owner,
                                "forwarded terminal target is not terminal",
                            );
                        }
                    };
                    if !matches_transfer || terminator.instrs.start != instr {
                        return self.invalid_region(
                            owner,
                            "forwarded terminal target has a non-empty prefix",
                        );
                    }
                    let Some(low) = self.lowering.proto.instrs.get(instr.index()) else {
                        return self.invalid_region(
                            owner,
                            "forwarded terminal instruction is outside the proto",
                        );
                    };
                    let Some(terminal) =
                        lower_terminal_instr(self.lowering, cfg_edge.to, instr, low)
                    else {
                        return self
                            .invalid_region(owner, "forwarded terminal lowering rejected opcode");
                    };
                    stmts.extend(terminal);
                }
            }
            EdgeTransfer::Break(loop_region) => {
                if !self.break_target_contains_region(loop_region, owner) {
                    return self
                        .invalid_region(owner, "break targets a non-containing lexical region");
                }
                if let Some(guard) = self.normal_tail_guard_for_break(loop_region, edge)? {
                    stmts.push(assign_stmt(
                        vec![HirLValue::Temp(guard)],
                        vec![HirExpr::Boolean(true)],
                    ));
                }
                stmts.push(HirStmt::Break);
            }
            EdgeTransfer::Continue(loop_region) => {
                if !self.loop_contains_region(loop_region, owner) {
                    return self
                        .invalid_region(owner, "continue targets a non-containing loop region");
                }
                stmts.extend(
                    self.lower_loop_value_phase(loop_region, LoopValuePhase::LatchEpilogue)?,
                );
                stmts.extend(self.lower_repeat_normal_stage(loop_region)?);
                stmts.push(HirStmt::Continue);
            }
            EdgeTransfer::Goto(label, _) => {
                let Some(target) = self.lowering.structure.plan().label(label) else {
                    return self.invalid_region(owner, "goto target has no planned label");
                };
                let Some(cfg_edge) = self.lowering.cfg.edges.get(edge.index()) else {
                    return self.invalid_region(owner, "goto transfer references a missing edge");
                };
                if cfg_edge.to != target.block {
                    return self.invalid_region(owner, "goto edge disagrees with planned label");
                }
                stmts.extend(goto_block(HirLabelId(label.index())).stmts);
            }
        }
        Ok(stmts)
    }

    pub(super) fn lower_repeat_normal_stage(
        &self,
        loop_region: RegionId,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let loop_id = match self.lowering.structure.plan().region(loop_region) {
            Some(RegionPlan::Loop { plan, .. }) => *plan,
            _ => return self.invalid_region(loop_region, "continue target is not a loop region"),
        };
        let Some(LoopVmProtocol::Repeat(protocol)) =
            self.lowering.structure.plan().loop_protocol(loop_id)
        else {
            return Ok(Vec::new());
        };
        let temps = self
            .lowering
            .bindings
            .repeat_staged_temps
            .get(loop_id.index())
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: loop_region.index(),
                detail: "repeat staged-result bindings are missing",
            })?;
        if temps.len() != protocol.value_plan.staged_results.len() {
            return self.invalid_region(
                loop_region,
                "repeat staged-result bindings contradict the protocol",
            );
        }
        if temps.is_empty() {
            return Ok(Vec::new());
        }
        let values = protocol
            .value_plan
            .staged_results
            .iter()
            .zip(temps)
            .filter(|(result, temp)| !self.repeat_stage_is_direct(result.target, **temp))
            .map(|(result, _)| self.ssa_expr(loop_region, result.normal_value))
            .collect::<Result<Vec<_>, _>>()?;
        let targets = protocol
            .value_plan
            .staged_results
            .iter()
            .zip(temps)
            .filter(|(result, temp)| !self.repeat_stage_is_direct(result.target, **temp))
            .map(|(_, temp)| HirLValue::Temp(*temp))
            .collect::<Vec<_>>();
        if targets.is_empty() {
            return Ok(Vec::new());
        }
        Ok(vec![assign_stmt(targets, values)])
    }

    pub(super) fn repeat_stage_is_direct(&self, target: PhiId, stage: TempId) -> bool {
        self.lowering.bindings.phi_temps.get(target.index()) == Some(&stage)
    }

    pub(super) fn lower_loop_exit_tail(
        &self,
        owner: RegionId,
        block: BlockRef,
        range: crate::structure::InstrRange,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let block_range = self.block_terminator(owner, block)?.instrs;
        if range.start != block_range.start || range.is_empty() || range.end() >= block_range.end()
        {
            return self.invalid_region(owner, "loop exit tail instruction range is stale");
        }
        let mut stmts = Vec::new();
        for index in range.start.index()..range.end() {
            stmts.extend(self.lower_planned_regular(owner, block, InstrRef(index))?);
        }
        Ok(stmts)
    }

    pub(super) fn normal_tail_guard_for_break(
        &self,
        loop_region: RegionId,
        edge: EdgeRef,
    ) -> Result<Option<TempId>, HirLowerError> {
        if self
            .lowering
            .structure
            .plan()
            .single_pass_for_region(loop_region)
            .is_some()
        {
            return Ok(None);
        }
        if !matches!(
            self.lowering.structure.plan().region(loop_region),
            Some(RegionPlan::Loop { .. })
        ) {
            return self.invalid_region(loop_region, "break target is not a loop region");
        }
        match self
            .index
            .normal_tail_guard_by_edge
            .get(edge.index())
            .copied()
            .flatten()
        {
            None => Ok(None),
            Some((owner, guard)) if owner == loop_region => Ok(Some(guard)),
            Some(_) => self.invalid_region(
                loop_region,
                "normal-tail break has a conflicting loop owner",
            ),
        }
    }

    pub(super) fn break_target_contains_region(&self, target: RegionId, region: RegionId) -> bool {
        let plan = self.lowering.structure.plan();
        (matches!(plan.region(target), Some(RegionPlan::Loop { .. }))
            || plan.single_pass_for_region(target).is_some())
            && plan.region_contains(target, region)
    }

    pub(super) fn lower_edge_effects(
        &self,
        owner: RegionId,
        edge: EdgeRef,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let edge_plan = self.lowering.structure.plan().edge_plan(edge).ok_or(
            HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "CFG edge has no final edge plan",
            },
        )?;
        let direct_copies = if self
            .lowering
            .structure
            .plan()
            .edge_action_is_forwarded_only(edge)
        {
            &[][..]
        } else {
            edge_plan.phi_copies.as_slice()
        };
        let mut stmts = self.lower_edge_copy_set(
            owner,
            edge,
            direct_copies,
            &edge_plan.iteration,
            edge_plan.transfer,
        )?;
        if let Some(route) = edge_plan.forward_route {
            for action_edge in self
                .lowering
                .structure
                .plan()
                .forward_route_action_edges(route)
            {
                let action_plan = self
                    .lowering
                    .structure
                    .plan()
                    .edge_plan(action_edge)
                    .ok_or(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: owner.index(),
                        detail: "forwarded action references a missing edge plan",
                    })?;
                stmts.extend(self.lower_edge_copy_set(
                    owner,
                    action_edge,
                    &action_plan.phi_copies,
                    &[],
                    edge_plan.transfer,
                )?);
            }
        }
        Ok(stmts)
    }

    pub(super) fn lower_edge_copy_set(
        &self,
        owner: RegionId,
        edge: EdgeRef,
        copies: &[crate::structure::PhiEdgeCopy],
        iteration: &[LoopIterationDisposition],
        effective_transfer: EdgeTransfer,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        self.planned_edge(owner, edge)?;
        let source_block = self
            .lowering
            .cfg
            .edges
            .get(edge.index())
            .map(|edge| edge.from)
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "final edge plan references a missing CFG edge",
            })?;
        let mut targets = Vec::new();
        let mut values = Vec::new();
        let elided = self
            .index
            .consumed_loop_copy_targets
            .get(edge.index())
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "edge copy elision index misses a final edge",
            })?;
        for copy in copies {
            if copy.value == crate::structure::SsaValue::Phi(copy.phi_id)
                || elided.binary_search(&copy.phi_id).is_ok()
            {
                continue;
            }
            let phi_target = self
                .lowering
                .bindings
                .phi_temps
                .get(copy.phi_id.index())
                .copied()
                .ok_or(HirLowerError::InvalidPlanRegion {
                    proto: self.proto.index(),
                    region: owner.index(),
                    detail: "edge phi copy target has no HIR temp binding",
                })?;
            let source_reg = self.ssa_reg(owner, copy.value)?;
            let value = if let Some(local) = self
                .lowering
                .bindings
                .local_for_reg_in_block(source_block, source_reg)
            {
                HirExpr::LocalRef(local)
            } else {
                self.edge_copy_expr(owner, source_block, phi_target, copy.value)?
            };
            let staged_target = match effective_transfer {
                EdgeTransfer::Break(loop_region) => self
                    .index
                    .repeat_staged_result_by_phi
                    .get(copy.phi_id.index())
                    .copied()
                    .flatten()
                    .filter(|(owner, _)| *owner == loop_region)
                    .map(|(_, temp)| temp),
                _ => None,
            };
            let target = if let Some(stage) = staged_target {
                HirLValue::Temp(stage)
            } else {
                self.lowering.bindings.lvalue_for_temp(phi_target)
            };
            targets.push(target);
            values.push(value);
        }
        for disposition in iteration {
            let LoopIterationDisposition {
                loop_region,
                target,
                incoming,
                source,
            } = *disposition;
            if !self.loop_contains_region(loop_region, owner) {
                return self
                    .invalid_region(owner, "iteration edge action targets a non-containing loop");
            }
            match self.lowering.structure.plan().region(loop_region) {
                Some(RegionPlan::Loop { .. }) => {}
                _ => {
                    return self
                        .invalid_region(owner, "iteration edge action owner is not a loop region");
                }
            }
            let target = self
                .lowering
                .bindings
                .phi_temps
                .get(target.index())
                .copied()
                .ok_or(HirLowerError::InvalidPlanRegion {
                    proto: self.proto.index(),
                    region: owner.index(),
                    detail: "iteration edge target has no HIR temp binding",
                })?;
            let value = match source {
                LoopValueSource::Ssa(value) if value == incoming => {
                    self.edge_copy_expr(owner, source_block, target, value)?
                }
                LoopValueSource::Ssa(_) => {
                    return self.invalid_region(
                        owner,
                        "iteration edge source changed its canonical SSA identity",
                    );
                }
                source => self.lower_loop_value_source(loop_region, source)?,
            };
            targets.push(self.lowering.bindings.lvalue_for_temp(target));
            values.push(value);
        }
        Ok(copy_assignment_stmt(targets, values).into_iter().collect())
    }

    pub(super) fn edge_requirement_matches(&self, edge: EdgeRef, transfer: EdgeTransfer) -> bool {
        let requirements = self.lowering.structure.plan().requirements();
        let planned = || {
            requirements
                .for_edge(edge)
                .iter()
                .filter_map(|id| requirements.get(*id))
        };
        match transfer {
            EdgeTransfer::Goto(label, reason) => planned().any(|requirement| {
                matches!(
                    requirement,
                    PlanRequirement::Goto {
                        label: planned_label,
                        reason: planned_reason,
                        ..
                    } if *planned_label == label && *planned_reason == reason
                )
            }),
            EdgeTransfer::Continue(loop_region) => planned().any(|requirement| {
                matches!(
                    requirement,
                    PlanRequirement::Continue {
                        loop_region: planned_loop,
                        ..
                    } if *planned_loop == loop_region
                )
            }),
            _ => !planned().any(|requirement| {
                matches!(
                    requirement,
                    PlanRequirement::Goto { .. } | PlanRequirement::Continue { .. }
                )
            }),
        }
    }
}
