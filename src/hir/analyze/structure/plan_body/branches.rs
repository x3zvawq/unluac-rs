//! 将分支、短路条件和值判定区域降低为 HIR；依赖冻结的 condition/value payload，不负责选择候选；例如生成带边动作的 if/else。
//! ValueDecision 的入口 CALL 与前缀在同一事务内交接：只有原覆盖前沿证明后继先覆写结果槽，
//! 才把唯一末尾调用接入测试。例如 `f() and g()` 不应新增跨 g 的 f 结果强根；独立 saved
//! 处于后继调用低槽时没有该证明，仍保留原声明与前缀。

use super::*;

impl<'a, 'b> PlanBodyLowerer<'a, 'b> {
    pub(super) fn lower_branch(
        &mut self,
        region: RegionId,
        plan: crate::structure::BranchPlanId,
        condition: RegionId,
        then_arm: PlannedBlock,
        else_arm: Option<PlannedBlock>,
    ) -> Result<PlannedBlock, HirLowerError> {
        let payload = self.lowering.structure.plan().branch(plan).ok_or(
            HirLowerError::MissingPlanPayload {
                proto: self.proto.index(),
                kind: "branch",
                id: plan.index(),
            },
        )?;
        let (mut stmts, mut cond) =
            self.lower_short_circuit_condition(region, condition, payload.condition)?;
        if payload.condition_inverted {
            cond = cond.negate();
        }

        let mut then_block = PlannedBlock::from(self.lower_edge(region, payload.then_edge)?);
        then_block.append(then_arm);
        let mut else_block = PlannedBlock::from(self.lower_edge(region, payload.else_edge)?);
        if let Some(arm) = else_arm {
            else_block.append(arm);
        }
        let else_block = if else_block.is_empty() {
            None
        } else {
            Some(self.finish_emission(region, else_block)?)
        };
        stmts.push(branch_stmt(
            cond,
            self.finish_emission(region, then_block)?,
            else_block,
        ));
        Ok(stmts)
    }

    pub(super) fn lower_short_circuit_condition(
        &mut self,
        owner: RegionId,
        condition_region: RegionId,
        condition_plan: crate::structure::ConditionPlanId,
    ) -> Result<(PlannedBlock, HirExpr), HirLowerError> {
        let selected = self
            .lowering
            .structure
            .plan()
            .condition(condition_plan)
            .ok_or(HirLowerError::MissingPlanPayload {
                proto: self.proto.index(),
                kind: "condition",
                id: condition_plan.index(),
            })?;
        self.verify_condition_plan(owner, selected)?;
        let decision = build_condition_decision_expr(self.lowering, selected).ok_or(
            HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: owner.index(),
                detail: "frozen short-circuit condition cannot be materialized",
            },
        )?;
        self.verify_condition_region(owner, condition_region, &selected.blocks)?;
        let header = selected.header().ok_or(HirLowerError::InvalidPlanRegion {
            proto: self.proto.index(),
            region: owner.index(),
            detail: "frozen condition has no entry node",
        })?;
        let stmts = self.lower_condition_prefix(owner, header)?;
        #[cfg(debug_assertions)]
        for block in selected.blocks() {
            if block != header {
                self.mark_block_emitted(
                    owner,
                    block,
                    "plan emits one condition block more than once",
                )?;
            }
        }
        Ok((
            stmts,
            finalize_condition_decision_expr(
                decision,
                crate::hir::expr_safety::HirExprSafety::for_dialect(self.lowering.target),
            ),
        ))
    }

    pub(super) fn lower_value_decision(
        &mut self,
        region: RegionId,
        plan: crate::structure::ValueDecisionPlanId,
    ) -> Result<PlannedBlock, HirLowerError> {
        let selected = self.lowering.structure.plan().value_decision(plan).ok_or(
            HirLowerError::MissingPlanPayload {
                proto: self.proto.index(),
                kind: "value-decision",
                id: plan.index(),
            },
        )?;
        self.verify_value_decision_plan(region, selected)?;
        if self.lowering.structure.plan().value_decision_region(plan) != Some(region) {
            return self
                .invalid_region(region, "value decision payload is bound to another region");
        }
        let header = selected.header().ok_or(HirLowerError::InvalidPlanRegion {
            proto: self.proto.index(),
            region: region.index(),
            detail: "value decision has no entry node",
        })?;
        let mut decision = build_value_decision_expr(self.lowering, selected).ok_or(
            HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "frozen value decision cannot be materialized",
            },
        )?;
        let mut stmts = self.lower_condition_prefix(region, header)?;
        self.absorb_value_entry_call(selected, &mut stmts, &mut decision);
        let target = self
            .lowering
            .bindings
            .phi_temps
            .get(selected.result_phi.index())
            .copied()
            .ok_or(HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail: "value decision result phi has no HIR binding",
            })?;
        stmts.push(assign_stmt(
            vec![self.lowering.bindings.lvalue_for_reg_result(
                selected.merge,
                self.ssa_reg(region, crate::structure::SsaValue::Phi(selected.result_phi))?,
                target,
            )],
            vec![finalize_value_decision_expr(
                decision,
                crate::hir::expr_safety::HirExprSafety::for_dialect(self.lowering.target),
                |node| {
                    // 原节点 identity 在本次 lowering 中仍与冻结 plan 一一对应。
                    // 只在此次归约事务消费证明，不把许可挂到可被后续 pass 改写的节点。
                    node.test_source == crate::hir::HirDecisionTestSource::Value
                        && matches!(node.test, HirExpr::Call(_))
                        && super::super::super::exprs::branch_call_result_ending_after_test(
                            self.lowering,
                            selected.nodes[node.id.index()].predicate,
                            &selected.call_root_frontiers,
                        )
                        .is_some()
                },
            )],
        ));
        stmts.extend_plain(self.lower_edge_effects(region, selected.shared_exit_action)?);
        #[cfg(debug_assertions)]
        for block in selected.blocks().filter(|block| *block != header) {
            self.mark_block_emitted(region, block, "plan emits one value block more than once")?;
        }
        Ok(stmts)
    }

    fn absorb_value_entry_call(
        &self,
        selected: &crate::structure::ValueDecisionPlan,
        prefix: &mut PlannedBlock,
        decision: &mut crate::hir::common::HirDecisionExpr,
    ) {
        let node = &mut decision.nodes[decision.entry.index()];
        let HirExpr::TempRef(temp) = node.test else {
            return;
        };
        let predicate = selected.nodes[selected.entry.index()].predicate;
        if node.test_source != crate::hir::HirDecisionTestSource::Value {
            return;
        }
        let Some(def) = super::super::super::exprs::branch_call_result_ending_after_test(
            self.lowering,
            predicate,
            &selected.call_root_frontiers,
        ) else {
            return;
        };
        let reg = self.lowering.dataflow.def_reg(def);
        let source = self.lowering.dataflow.def_instr(def);
        let LowInstr::Call(call) = &self.lowering.proto.instrs[source.index()] else {
            return;
        };
        if call.results
            != crate::transformer::ResultPack::Fixed(crate::transformer::RegRange {
                start: reg,
                len: 1,
            })
            || self.lowering.bindings.fixed_temps[def.index()] != temp
            || !self.lowering.dataflow.def_phi_uses[def.index()].is_empty()
            || self.lowering.dataflow.reg_is_reference_captured(reg)
            || self.lowering.bindings.temp_debug_locals[temp.index()].is_some()
            || self
                .lowering
                .bindings
                .captured_temp_targets
                .contains_key(&temp)
            || self.lowering.bindings.temp_decl_locals.contains_key(&temp)
        {
            return;
        }
        let Some((target, HirExpr::Call(value))) =
            prefix.last().and_then(HirStmt::scalar_temp_assignment)
        else {
            return;
        };
        if target != temp
            || value
                .source_site
                .is_none_or(|site| site.proto != self.lowering.id || site.instr != source)
        {
            return;
        }
        // 最后一条唯一 CALL 移到随后的入口测试；没有跨过任何参数准备或其它求值。
        let Some(HirStmt::Assign(mut assign)) = prefix.pop_trailing_without_scope_boundary() else {
            return;
        };
        node.test = assign
            .values
            .fixed
            .pop()
            .expect("scalar CALL assignment has its fixed result");
    }

    pub(super) fn verify_condition_region(
        &mut self,
        owner: RegionId,
        region: RegionId,
        blocks: &[BlockRef],
    ) -> Result<(), HirLowerError> {
        let Some(expected_count) = self
            .index
            .plain_block_count
            .get(region.index())
            .copied()
            .flatten()
        else {
            return self.invalid_region(
                region,
                "condition region contains a non-condition control region",
            );
        };
        if blocks.len() != expected_count {
            return self.invalid_region(
                owner,
                "condition materialization did not consume the exact planned region",
            );
        }

        self.condition_epoch = self.condition_epoch.wrapping_add(1);
        if self.condition_epoch == 0 {
            self.condition_block_seen_at.fill(0);
            self.condition_epoch = 1;
        }
        for block in blocks {
            let Some(seen_at) = self.condition_block_seen_at.get_mut(block.index()) else {
                return self.invalid_region(owner, "condition block is outside the CFG arena");
            };
            if std::mem::replace(seen_at, self.condition_epoch) == self.condition_epoch {
                return self.invalid_region(owner, "condition plan contains one block twice");
            }
            let Some(block_region) = self.lowering.structure.plan().region_for_block(*block) else {
                return self.invalid_region(owner, "condition block has no containment owner");
            };
            if !self
                .lowering
                .structure
                .plan()
                .region_contains(region, block_region)
            {
                return self.invalid_region(
                    owner,
                    "condition materialization did not consume the exact planned region",
                );
            }
        }
        Ok(())
    }
}
