//! 按冻结的 VM loop protocol 降低 while/repeat/for；依赖循环分区和边计划，不负责重新识别循环；例如处理 repeat 尾条件与 normal-tail。

use super::*;

impl<'a, 'b> PlanBodyLowerer<'a, 'b> {
    pub(super) fn lower_loop(
        &mut self,
        region: RegionId,
        plan: crate::structure::LoopPlanId,
        parts: PlannedLoopParts,
    ) -> Result<HirBlock, HirLowerError> {
        let PlannedLoopParts {
            preheader,
            control,
            body,
            normal_tail_region,
            normal_tail_body,
        } = parts;
        let payload = self.lowering.structure.plan().loop_(plan).ok_or(
            HirLowerError::MissingPlanPayload {
                proto: self.proto.index(),
                kind: "loop",
                id: plan.index(),
            },
        )?;
        let identity = PlannedLoopIdentity {
            header: payload.header,
            source_bindings: payload.source_bindings,
            preheader_body: payload.control_edges.preheader_body,
            preheader_exit: payload.control_edges.preheader_exit,
            has_normal_tail: payload.normal_tail.is_some(),
        };
        let propagated_break = payload.propagated_break;
        if self.lowering.structure.plan().loop_region(plan) != Some(region) {
            return self.invalid_region(region, "loop payload is bound to another region");
        }
        let normal_tail = match (
            identity.has_normal_tail,
            normal_tail_region,
            normal_tail_body,
        ) {
            (false, None, None) => None,
            (true, Some(_), Some(tail)) if tail.stmts.is_empty() => None,
            (true, Some(_), Some(tail)) => Some((
                tail,
                self.lowering
                    .bindings
                    .loop_guard_temps
                    .get(plan.index())
                    .copied()
                    .flatten()
                    .ok_or(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: region.index(),
                        detail: "normal-tail loop has no guard binding",
                    })?,
            )),
            _ => {
                return self.invalid_region(region, "normal-tail payload and region slot disagree");
            }
        };
        let protocol = self
            .lowering
            .structure
            .plan()
            .loop_protocol(plan)
            .cloned()
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "loop payload has no finalized VM protocol",
            })?;
        let mut lowered = match protocol {
            LoopVmProtocol::While(protocol) => self.lower_while_loop(
                region,
                control,
                body,
                normal_tail,
                propagated_break,
                protocol,
            ),
            LoopVmProtocol::Repeat(protocol) if normal_tail.is_none() => {
                self.lower_repeat_loop(region, plan, control, body, protocol)
            }
            LoopVmProtocol::NumericFor(protocol) => self.lower_numeric_for(
                region,
                identity,
                PlannedForRegions {
                    preheader,
                    control,
                    normal_tail,
                },
                body,
                protocol,
            ),
            LoopVmProtocol::GenericFor(protocol) => self.lower_generic_for(
                region,
                identity,
                PlannedForRegions {
                    preheader,
                    control,
                    normal_tail,
                },
                body,
                protocol,
            ),
            LoopVmProtocol::WhileTrue if normal_tail.is_none() => {
                if preheader.is_some() {
                    return self.invalid_region(region, "plain loop unexpectedly owns a preheader");
                }
                self.lower_while_true_loop(region, control, body)
            }
            _ => self.invalid_region(region, "loop protocol contradicts region slots"),
        }?;
        if let Some(target) = propagated_break {
            if target == region || !self.loop_contains_region(target, region) {
                return self
                    .invalid_region(region, "propagated break does not target a containing loop");
            }
            lowered.stmts.push(HirStmt::Break);
        }
        Ok(lowered)
    }

    pub(super) fn lower_while_loop(
        &mut self,
        region: RegionId,
        control: RegionId,
        mut body: HirBlock,
        normal_tail: Option<(HirBlock, TempId)>,
        propagated_break: Option<RegionId>,
        protocol: LoopConditionProtocol,
    ) -> Result<HirBlock, HirLowerError> {
        let condition = self.lower_loop_condition(region, control, Some(protocol.condition))?;
        let body_edge = protocol.body_edge;
        let exit_edge = protocol.exit_edge;
        let cond = if protocol.body_on_truthy {
            condition.cond.clone()
        } else {
            condition.cond.clone().negate()
        };
        let exit_transfer = self.planned_edge(region, exit_edge)?.transfer;
        let cross_loop_transfer = match exit_transfer {
            EdgeTransfer::LoopBack(target) | EdgeTransfer::Continue(target) if target != region => {
                Some(target)
            }
            EdgeTransfer::Break(target) if target != region && propagated_break != Some(target) => {
                Some(target)
            }
            _ => None,
        };

        let mut stmts = Vec::new();
        if let Some((_, guard)) = &normal_tail {
            stmts.push(assign_stmt(
                vec![HirLValue::Temp(*guard)],
                vec![HirExpr::Boolean(false)],
            ));
        }
        let mut loop_body = condition.prefix;
        let exit = match exit_transfer {
            EdgeTransfer::BranchArm(crate::structure::BranchArm::LoopExit) => {
                let mut exit = self.lower_edge(region, exit_edge)?;
                exit.stmts.push(HirStmt::Break);
                exit
            }
            EdgeTransfer::LoopBack(target) | EdgeTransfer::Continue(target) if target != region => {
                HirBlock {
                    stmts: vec![HirStmt::Break],
                }
            }
            EdgeTransfer::Break(target) if target != region && propagated_break == Some(target) => {
                self.lower_edge(region, exit_edge)?
            }
            EdgeTransfer::Break(target) if target != region => HirBlock {
                stmts: vec![HirStmt::Break],
            },
            EdgeTransfer::Break(target) if target == region => {
                self.lower_edge(region, exit_edge)?
            }
            EdgeTransfer::Goto(..) => self.lower_edge(region, exit_edge)?,
            _ => {
                return self.invalid_region(
                    region,
                    "while condition exit contradicts its final transfer",
                );
            }
        };
        if normal_tail.is_none()
            && loop_body.is_empty()
            && cross_loop_transfer.is_none()
            && matches!(exit.stmts.as_slice(), [HirStmt::Break])
        {
            loop_body.extend(self.lower_edge(region, body_edge)?.stmts);
            loop_body.append(&mut body.stmts);
            stmts.push(HirStmt::While(Box::new(HirWhile {
                cond,
                body: HirBlock { stmts: loop_body },
            })));
            return Ok(HirBlock { stmts });
        }
        loop_body.push(branch_stmt(cond.negate(), exit, None));
        loop_body.extend(self.lower_edge(region, body_edge)?.stmts);
        loop_body.append(&mut body.stmts);
        if normal_tail.is_some()
            && exit_transfer == EdgeTransfer::BranchArm(crate::structure::BranchArm::LoopExit)
        {
            // generalized while 的 normal-tail guard 已把“正常退出”和提前 break
            // 分开；自然 LoopExit 证明这份独占 tail 是 post-tested 词法形状。
            stmts.push(HirStmt::Repeat(Box::new(HirRepeat {
                body: HirBlock { stmts: loop_body },
                cond: HirExpr::Boolean(false),
            })));
        } else {
            stmts.push(HirStmt::While(Box::new(HirWhile {
                cond: HirExpr::Boolean(true),
                body: HirBlock { stmts: loop_body },
            })));
        }
        if let Some(target) = cross_loop_transfer {
            if !self.loop_contains_region(target, region) {
                return self.invalid_region(
                    region,
                    "loop condition exit breaks a non-containing outer loop",
                );
            }
            // control_edges.exit 冻结内层语法退出，edge transfer 冻结退出后继续
            // break 外层；phi actions 只在内层 loop 完成后消费一次。
            stmts.extend(self.lower_edge(region, exit_edge)?.stmts);
        }
        if let Some((tail, guard)) = normal_tail {
            stmts.push(branch_stmt(HirExpr::TempRef(guard).negate(), tail, None));
        }
        Ok(HirBlock { stmts })
    }

    pub(super) fn lower_repeat_loop(
        &mut self,
        region: RegionId,
        plan: crate::structure::LoopPlanId,
        control: RegionId,
        mut body: HirBlock,
        protocol: LoopRepeatProtocol,
    ) -> Result<HirBlock, HirLowerError> {
        let condition =
            self.lower_loop_condition(region, control, Some(protocol.condition.condition))?;
        let backedge = protocol.condition.body_edge;
        let exit = protocol.condition.exit_edge;
        let exit_cond = if protocol.condition.body_on_truthy {
            condition.cond.clone().negate()
        } else {
            condition.cond.clone()
        };
        let exit_plan = self
            .lowering
            .structure
            .plan()
            .edge_plan(exit)
            .cloned()
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "repeat exit has no final edge plan",
            })?;
        let staged_temps = self
            .lowering
            .bindings
            .repeat_staged_temps
            .get(plan.index())
            .cloned()
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "repeat staged-result bindings are missing",
            })?;
        if staged_temps.len() != protocol.value_plan.staged_results.len() {
            return self.invalid_region(
                region,
                "repeat staged-result bindings contradict the protocol",
            );
        }
        let normal_stage = protocol
            .value_plan
            .staged_results
            .iter()
            .zip(&staged_temps)
            .filter(|(result, temp)| !self.repeat_stage_is_direct(result.target, **temp))
            .map(|(result, temp)| Ok((*temp, self.ssa_expr(region, result.normal_value)?)))
            .collect::<Result<Vec<_>, HirLowerError>>()?;
        let final_stage = protocol
            .value_plan
            .staged_results
            .iter()
            .zip(&staged_temps)
            .filter(|(result, temp)| !self.repeat_stage_is_direct(result.target, **temp))
            .map(|(result, temp)| {
                let target = self
                    .lowering
                    .bindings
                    .phi_temps
                    .get(result.target.index())
                    .copied()
                    .ok_or(HirLowerError::InvalidPlanRegion {
                        proto: self.proto.index(),
                        region: region.index(),
                        detail: "repeat staged result has no final phi binding",
                    })?;
                Ok((
                    self.lowering.bindings.lvalue_for_temp(target),
                    HirExpr::TempRef(*temp),
                ))
            })
            .collect::<Result<Vec<_>, HirLowerError>>()?;

        let mut body_stmts = Vec::new();
        if protocol.prefix_placement == crate::structure::LoopConditionPrefixPlacement::BeforeBody {
            body_stmts.extend(condition.prefix.clone());
        }
        body_stmts.append(&mut body.stmts);
        if protocol.prefix_placement == crate::structure::LoopConditionPrefixPlacement::AfterBody {
            body_stmts.extend(condition.prefix);
        }
        if !normal_stage.is_empty() {
            body_stmts.push(assign_stmt(
                normal_stage
                    .iter()
                    .map(|(temp, _)| HirLValue::Temp(*temp))
                    .collect::<Vec<_>>(),
                normal_stage
                    .iter()
                    .map(|(_, value)| value.clone())
                    .collect::<Vec<_>>(),
            ));
        }
        let backedge_stmts = if protocol.value_plan.backedge_copies.is_empty() {
            self.lower_edge(region, backedge)?.stmts
        } else {
            let transfer = self.planned_edge(region, backedge)?.transfer;
            if !matches!(transfer, EdgeTransfer::LoopBack(target) if target == region) {
                return self.invalid_region(
                    region,
                    "repeat native-latch copies contradict the backedge transfer",
                );
            }
            self.lower_edge_copy_set(
                region,
                backedge,
                &protocol.value_plan.backedge_copies,
                &[],
                transfer,
            )?
        };
        if matches!(protocol.form, LoopRepeatForm::Native) {
            let exit_transfer_matches = if protocol.exit_after_loop {
                !matches!(exit_plan.transfer, EdgeTransfer::Break(target) if target == region)
            } else {
                matches!(exit_plan.transfer, EdgeTransfer::Break(target) if target == region)
                    || exit_plan.transfer
                        == EdgeTransfer::BranchArm(crate::structure::BranchArm::LoopExit)
            };
            if !exit_transfer_matches {
                return self.invalid_region(
                    region,
                    "repeat native exit contradicts its staged-result protocol",
                );
            }
            body_stmts.extend(backedge_stmts);
            let mut stmts = vec![HirStmt::Repeat(Box::new(HirRepeat {
                body: HirBlock { stmts: body_stmts },
                cond: exit_cond,
            }))];
            if !final_stage.is_empty() {
                stmts.push(assign_stmt(
                    final_stage
                        .iter()
                        .map(|(target, _)| target.clone())
                        .collect::<Vec<_>>(),
                    final_stage
                        .iter()
                        .map(|(_, value)| value.clone())
                        .collect::<Vec<_>>(),
                ));
            }
            if protocol.exit_after_loop {
                stmts.extend(self.lower_edge(region, exit)?.stmts);
            }
            return Ok(HirBlock { stmts });
        }
        if !protocol.value_plan.staged_results.is_empty() || protocol.exit_after_loop {
            return self.invalid_region(region, "non-native repeat retains native exit actions");
        }
        let exit_stmts = self.lower_edge(region, exit)?.stmts;
        body_stmts.push(branch_stmt(
            exit_cond,
            HirBlock { stmts: exit_stmts },
            Some(HirBlock {
                stmts: backedge_stmts,
            }),
        ));
        // terminal edge 带值动作时仍可保留 repeat 作用域：尾分支只求值一次条件，
        // 两个 arm 分别执行 final plan 冻结的 exit/backedge actions。显式 continue
        // 会直接跳到 repeat 条件，因而不能在这里把真实条件替换成 false。
        if matches!(protocol.form, LoopRepeatForm::TailBranchRepeat) {
            return Ok(HirBlock {
                stmts: vec![HirStmt::Repeat(Box::new(HirRepeat {
                    body: HirBlock { stmts: body_stmts },
                    cond: HirExpr::Boolean(false),
                }))],
            });
        }
        self.invalid_region(region, "repeat protocol has an unknown lowering form")
    }

    pub(super) fn lower_while_true_loop(
        &mut self,
        region: RegionId,
        control: RegionId,
        mut body: HirBlock,
    ) -> Result<HirBlock, HirLowerError> {
        let mut stmts = self.lower_syntax_region_prefix(region, control, None)?;
        stmts.append(&mut body.stmts);
        Ok(HirBlock {
            stmts: vec![HirStmt::While(Box::new(HirWhile {
                cond: HirExpr::Boolean(true),
                body: HirBlock { stmts },
            }))],
        })
    }

    pub(super) fn lower_numeric_for(
        &mut self,
        region: RegionId,
        loop_: PlannedLoopIdentity,
        regions: PlannedForRegions,
        mut body: HirBlock,
        protocol: crate::structure::NumericForProtocol,
    ) -> Result<HirBlock, HirLowerError> {
        let PlannedForRegions {
            preheader,
            control,
            normal_tail,
        } = regions;
        let preheader_region = preheader.ok_or(HirLowerError::InvalidPlanRegion {
            proto: self.proto.index(),
            region: region.index(),
            detail: "numeric for has no planned preheader region",
        })?;
        let preheader = self.single_block_region(preheader_region)?;
        let Some(LowInstr::NumericForInit(init)) =
            self.lowering.proto.instrs.get(protocol.init_instr.index())
        else {
            return self.invalid_region(region, "numeric for plan references a non-init opcode");
        };
        if loop_.preheader_body != Some(protocol.body_edge)
            || loop_.preheader_exit != Some(protocol.exit_edge)
            || init.index != protocol.index
            || init.limit != protocol.limit
            || init.step != protocol.step
            || init.binding != protocol.binding
        {
            return self.invalid_region(region, "numeric for payload contradicts VM control");
        }
        let binding = self
            .lowering
            .bindings
            .numeric_for_locals
            .get(&loop_.header)
            .copied()
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "numeric for has no selected source binding",
            })?;
        let mut stmts = self.lower_syntax_region_prefix(region, preheader_region, None)?;
        stmts.extend(self.lower_loop_value_phase(region, LoopValuePhase::BeforeLoop)?);
        if let Some((_, guard)) = &normal_tail {
            stmts.push(assign_stmt(
                vec![HirLValue::Temp(*guard)],
                vec![HirExpr::Boolean(false)],
            ));
        }

        let start = expr_for_reg_use(
            self.lowering,
            preheader,
            protocol.init_instr,
            protocol.index,
        );
        let limit = expr_for_reg_use(
            self.lowering,
            preheader,
            protocol.init_instr,
            protocol.limit,
        );
        let step = expr_for_reg_use(self.lowering, preheader, protocol.init_instr, protocol.step);
        let mut loop_stmts = self.lower_loop_value_phase(region, LoopValuePhase::BodyPrologue)?;
        loop_stmts.append(&mut body.stmts);
        if protocol.body_completes_normally {
            loop_stmts.extend(self.lower_syntax_region_prefix(region, control, None)?);
            loop_stmts
                .extend(self.lower_loop_value_phase(region, LoopValuePhase::IterationEpilogue)?);
            loop_stmts.extend(self.lower_loop_value_phase(region, LoopValuePhase::LatchEpilogue)?);
        } else {
            self.consume_syntax_region(region, control)?;
        }
        stmts.push(HirStmt::NumericFor(Box::new(HirNumericFor {
            binding,
            start,
            limit,
            step,
            body: HirBlock { stmts: loop_stmts },
        })));
        stmts.extend(self.lower_loop_value_phase(region, LoopValuePhase::AfterLoop)?);
        if let Some((tail, guard)) = normal_tail {
            stmts.push(branch_stmt(HirExpr::TempRef(guard).negate(), tail, None));
        }
        let exit_plan = self.planned_edge(region, protocol.exit_edge)?;
        stmts.extend(self.lower_edge_after_effects(region, protocol.exit_edge, exit_plan)?);
        Ok(HirBlock { stmts })
    }

    pub(super) fn lower_generic_for(
        &mut self,
        region: RegionId,
        loop_: PlannedLoopIdentity,
        regions: PlannedForRegions,
        mut body: HirBlock,
        protocol: crate::structure::GenericForProtocol,
    ) -> Result<HirBlock, HirLowerError> {
        let PlannedForRegions {
            preheader,
            control,
            normal_tail,
        } = regions;
        let preheader_region = preheader.ok_or(HirLowerError::InvalidPlanRegion {
            proto: self.proto.index(),
            region: region.index(),
            detail: "generic for has no planned preheader region",
        })?;
        let preheader = self.single_block_region(preheader_region)?;
        let header = loop_.header;
        let Some(LowInstr::GenericForLoop(_loop_instr)) =
            self.lowering.proto.instrs.get(protocol.loop_instr.index())
        else {
            return self
                .invalid_region(region, "generic for protocol references a non-loop opcode");
        };
        if !matches!(
            loop_.source_bindings,
            Some(crate::structure::LoopSourceBindings::Generic(bindings))
                if bindings == protocol.bindings
        ) {
            return self.invalid_region(region, "generic for payload contradicts VM bindings");
        }
        let bindings = self
            .lowering
            .bindings
            .generic_for_locals
            .get(&header)
            .cloned()
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "generic for has no selected source bindings",
            })?;
        if bindings.len() != protocol.bindings.len {
            return self.invalid_region(region, "generic for binding arity changed after planning");
        }
        let mut stmts =
            self.lower_syntax_region_prefix(region, preheader_region, protocol.prep_instr)?;
        stmts.extend(self.lower_loop_value_phase(region, LoopValuePhase::BeforeLoop)?);
        if let Some((_, guard)) = &normal_tail {
            stmts.push(assign_stmt(
                vec![HirLValue::Temp(*guard)],
                vec![HirExpr::Boolean(false)],
            ));
        }
        let mut loop_stmts = self.lower_loop_value_phase(region, LoopValuePhase::BodyPrologue)?;
        loop_stmts.append(&mut body.stmts);
        self.consume_syntax_region(region, control)?;
        if protocol.body_completes_normally {
            loop_stmts
                .extend(self.lower_loop_value_phase(region, LoopValuePhase::IterationEpilogue)?);
            if protocol.immediate_break {
                loop_stmts.push(HirStmt::Break);
            } else {
                loop_stmts
                    .extend(self.lower_loop_value_phase(region, LoopValuePhase::LatchEpilogue)?);
            }
        }
        stmts.push(HirStmt::GenericFor(Box::new(HirGenericFor {
            bindings,
            iterator: lower_generic_for_iterator(self.lowering, preheader, protocol).into(),
            body: HirBlock { stmts: loop_stmts },
        })));
        stmts.extend(self.lower_loop_value_phase(region, LoopValuePhase::AfterLoop)?);
        if let Some((tail, guard)) = normal_tail {
            stmts.push(branch_stmt(HirExpr::TempRef(guard).negate(), tail, None));
        }
        let exit_plan = self.planned_edge(region, protocol.exit_edge)?;
        stmts.extend(self.lower_edge_after_effects(region, protocol.exit_edge, exit_plan)?);
        Ok(HirBlock { stmts })
    }

    pub(super) fn lower_loop_condition(
        &mut self,
        owner: RegionId,
        control: RegionId,
        selected: Option<crate::structure::ConditionPlanId>,
    ) -> Result<PlannedLoopCondition, HirLowerError> {
        let Some(selected) = selected else {
            return self.invalid_region(owner, "loop payload is missing its frozen condition plan");
        };

        let condition = self
            .lowering
            .structure
            .plan()
            .condition(selected)
            .cloned()
            .ok_or(HirLowerError::MissingPlanPayload {
                proto: self.proto.index(),
                kind: "condition",
                id: selected.index(),
            })?;
        self.verify_condition_plan(owner, &condition)?;
        let decision = build_condition_decision_expr(self.lowering, &condition).ok_or(
            HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "frozen loop condition cannot be materialized",
            },
        )?;
        self.verify_condition_region(owner, control, &condition.blocks)?;
        let header = condition.header().ok_or(HirLowerError::InvalidPlanRegion {
            proto: self.proto.index(),
            region: owner.index(),
            detail: "frozen loop condition has no entry node",
        })?;
        for block in condition
            .blocks
            .iter()
            .copied()
            .filter(|block| *block != header)
        {
            self.consume_syntax_block(owner, block, None)?;
        }
        Ok(PlannedLoopCondition {
            prefix: self.lower_condition_prefix(owner, header)?,
            cond: finalize_condition_decision_expr(
                decision,
                crate::hir::expr_safety::HirExprSafety::for_dialect(self.lowering.target.version),
            ),
        })
    }

    pub(super) fn loop_contains_region(&self, loop_region: RegionId, region: RegionId) -> bool {
        matches!(
            self.lowering.structure.plan().region(loop_region),
            Some(RegionPlan::Loop { .. })
        ) && self
            .lowering
            .structure
            .plan()
            .region_contains(loop_region, region)
    }
}
