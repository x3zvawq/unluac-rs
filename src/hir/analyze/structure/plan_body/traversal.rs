//! 迭代遍历区域树并调度子区域 lowering；依赖共享 lowerer 索引，不负责具体分支/循环语法；例如用任务栈降低深层 Sequence。

use super::*;
use crate::hir::promotion::ImplicitRootScopeFence;

impl<'a, 'b> PlanBodyLowerer<'a, 'b> {
    pub(super) fn new(
        proto: HirProtoRef,
        lowering: &'b ProtoLowering<'a>,
    ) -> Result<Self, HirLowerError> {
        let index = PlanLoweringIndex::build(proto, lowering)?;
        Ok(Self {
            proto,
            lowering,
            index,
            emitted_scope_boundaries: 0,
            #[cfg(debug_assertions)]
            emitted_labels: vec![false; lowering.structure.plan().labels().len()],
            #[cfg(debug_assertions)]
            emitted_label_count: 0,
            #[cfg(debug_assertions)]
            emitted_blocks: vec![false; lowering.cfg.blocks.len()],
            #[cfg(debug_assertions)]
            emitted_synthetic_inputs: vec![false; lowering.structure.plan().phis().len()],
            condition_block_seen_at: vec![0; lowering.cfg.blocks.len()],
            condition_epoch: 0,
        })
    }

    pub(super) fn lower_plan_node(&mut self, id: RegionId) -> Result<HirBlock, HirLowerError> {
        let mut tasks = vec![LowerTask::Region(id)];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                LowerTask::Region(region) => {
                    let node = self.lowering.structure.plan().region(region).ok_or(
                        HirLowerError::MissingPlanRegion {
                            proto: self.proto.index(),
                            region: region.index(),
                        },
                    )?;
                    let mut prefix = PlannedBlock::new();
                    self.emit_region_label(region, &mut prefix)?;
                    let mut region_local_decls = local_decl_stmts(
                        self.lowering
                            .bindings
                            .capture_region_local_decls
                            .get(&region)
                            .cloned()
                            .unwrap_or_default(),
                    );
                    let single_pass = self
                        .lowering
                        .structure
                        .plan()
                        .single_pass_for_region(region)
                        .is_some();
                    let outer_prefix = if single_pass {
                        PlannedBlock::from(std::mem::take(&mut region_local_decls))
                    } else {
                        PlannedBlock::new()
                    };
                    prefix.extend_plain(region_local_decls);
                    prefix.extend_plain(self.lower_region_inputs(region)?);
                    match node {
                        RegionPlan::Block { block, .. } => {
                            prefix.append(self.lower_block(region, *block)?);
                            results.push(prefix);
                        }
                        RegionPlan::Sequence { children, .. } => {
                            let result_start = results.len();
                            tasks.push(LowerTask::FinishSequence {
                                region,
                                outer_prefix,
                                prefix,
                                result_start,
                                child_count: children.len(),
                                single_pass,
                            });
                            tasks.extend(children.iter().rev().copied().map(LowerTask::Region));
                        }
                        RegionPlan::Branch {
                            plan,
                            condition,
                            then_arm,
                            else_arm,
                            ..
                        } => {
                            let result_start = results.len();
                            tasks.push(LowerTask::FinishBranch {
                                region,
                                prefix,
                                plan: *plan,
                                condition: *condition,
                                has_else: else_arm.is_some(),
                                result_start,
                            });
                            if let Some(else_arm) = else_arm {
                                tasks.push(LowerTask::Region(*else_arm));
                            }
                            tasks.push(LowerTask::Region(*then_arm));
                        }
                        RegionPlan::ValueDecision { plan, .. } => {
                            prefix.append(self.lower_value_decision(region, *plan)?);
                            results.push(prefix);
                        }
                        RegionPlan::Loop {
                            plan,
                            preheader,
                            control,
                            body,
                            normal_tail,
                            ..
                        } => {
                            let result_start = results.len();
                            tasks.push(LowerTask::FinishLoop {
                                region,
                                prefix,
                                plan: *plan,
                                preheader: *preheader,
                                control: *control,
                                normal_tail: *normal_tail,
                                result_start,
                            });
                            if let Some(normal_tail) = normal_tail {
                                tasks.push(LowerTask::Region(*normal_tail));
                            }
                            tasks.push(LowerTask::Region(*body));
                        }
                        RegionPlan::Unstructured { layout, .. } => {
                            let result_start = results.len();
                            tasks.push(LowerTask::FinishUnstructured {
                                region,
                                outer_prefix,
                                prefix,
                                result_start,
                                item_count: layout.len(),
                                single_pass: false,
                            });
                            tasks.extend(layout.iter().rev().map(|item| match item {
                                UnstructuredLayoutItem::Block(block) => LowerTask::Block {
                                    owner: region,
                                    block: *block,
                                },
                                UnstructuredLayoutItem::Region(child) => LowerTask::Region(*child),
                            }));
                        }
                    }
                }
                LowerTask::Block { owner, block } => {
                    results.push(self.lower_block(owner, block)?);
                }
                LowerTask::FinishSequence {
                    region,
                    mut outer_prefix,
                    mut prefix,
                    result_start,
                    child_count,
                    single_pass,
                } => {
                    let children = self.take_lowered_children(
                        region,
                        &mut results,
                        result_start,
                        child_count,
                    )?;
                    if let Some(fence) = self
                        .lowering
                        .promotion_facts
                        .implicit_root_scope_fence(region)
                    {
                        let Some(RegionPlan::Sequence {
                            children: planned_children,
                            ..
                        }) = self.lowering.structure.plan().region(region)
                        else {
                            return self.invalid_region(
                                region,
                                "implicit root scope fence owner is not a sequence",
                            );
                        };
                        let fenced = match flatten_implicit_root_scope_fence(
                            children,
                            planned_children,
                            fence,
                        ) {
                            Ok(stmts) => stmts,
                            Err(detail) => return self.invalid_region(region, detail),
                        };
                        prefix.append(fenced);
                    } else {
                        for child in children {
                            prefix.append(child);
                        }
                    }
                    if single_pass {
                        let Some((_, fence)) = self
                            .lowering
                            .structure
                            .plan()
                            .single_pass_for_region(region)
                        else {
                            return self.invalid_region(
                                region,
                                "single-pass sequence has no frozen fence payload",
                            );
                        };
                        if fence.region != region {
                            return self.invalid_region(
                                region,
                                "single-pass payload is bound to another region",
                            );
                        }
                        let mut outer = PlannedBlock::new();
                        self.emit_label(
                            fence.entry,
                            LabelPlacement::BeforeRegion(region),
                            &mut outer,
                        )?;
                        outer.append(outer_prefix);
                        outer.push(HirStmt::Repeat(Box::new(HirRepeat {
                            body: self.finish_emission(region, prefix)?,
                            cond: HirExpr::Boolean(true),
                            preserves_condition: false,
                            lifetime: Default::default(),
                        })));
                        prefix = outer;
                    } else {
                        outer_prefix.append(prefix);
                        prefix = outer_prefix;
                    }
                    results.push(prefix);
                }
                LowerTask::FinishUnstructured {
                    region,
                    mut outer_prefix,
                    mut prefix,
                    result_start,
                    item_count: child_count,
                    single_pass,
                } => {
                    for child in
                        self.take_lowered_children(region, &mut results, result_start, child_count)?
                    {
                        prefix.append(child);
                    }
                    if single_pass {
                        let Some((_, fence)) = self
                            .lowering
                            .structure
                            .plan()
                            .single_pass_for_region(region)
                        else {
                            return self.invalid_region(
                                region,
                                "single-pass sequence has no frozen fence payload",
                            );
                        };
                        if fence.region != region {
                            return self.invalid_region(
                                region,
                                "single-pass payload is bound to another region",
                            );
                        }
                        let mut outer = PlannedBlock::new();
                        self.emit_label(
                            fence.entry,
                            LabelPlacement::BeforeRegion(region),
                            &mut outer,
                        )?;
                        outer.append(outer_prefix);
                        outer.push(HirStmt::Repeat(Box::new(HirRepeat {
                            body: self.finish_emission(region, prefix)?,
                            cond: HirExpr::Boolean(true),
                            preserves_condition: false,
                            lifetime: Default::default(),
                        })));
                        prefix = outer;
                    } else {
                        outer_prefix.append(prefix);
                        prefix = outer_prefix;
                    }
                    results.push(prefix);
                }
                LowerTask::FinishBranch {
                    region,
                    mut prefix,
                    plan,
                    condition,
                    has_else,
                    result_start,
                } => {
                    let mut children = self.take_lowered_children(
                        region,
                        &mut results,
                        result_start,
                        usize::from(has_else) + 1,
                    )?;
                    let then_arm = children.remove(0);
                    let else_arm = has_else.then(|| children.remove(0));
                    prefix.append(self.lower_branch(region, plan, condition, then_arm, else_arm)?);
                    results.push(prefix);
                }
                LowerTask::FinishLoop {
                    region,
                    mut prefix,
                    plan,
                    preheader,
                    control,
                    normal_tail,
                    result_start,
                } => {
                    let mut children = self.take_lowered_children(
                        region,
                        &mut results,
                        result_start,
                        usize::from(normal_tail.is_some()) + 1,
                    )?;
                    let body = children.remove(0);
                    let tail = normal_tail.map(|_| children.remove(0));
                    prefix.append(self.lower_loop(
                        region,
                        plan,
                        PlannedLoopParts {
                            preheader,
                            control,
                            body,
                            normal_tail_region: normal_tail,
                            normal_tail_body: tail,
                        },
                    )?);
                    results.push(prefix);
                }
            }
        }
        if results.len() != 1 {
            return self.invalid_region(id, "iterative region lowering left orphaned results");
        }
        self.finish_emission(id, results.pop().expect("exactly one region result"))
    }

    pub(super) fn finish_emission(
        &self,
        region: RegionId,
        output: PlannedBlock,
    ) -> Result<HirBlock, HirLowerError> {
        output
            .finish()
            .map_err(|detail| HirLowerError::InvalidPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
                detail,
            })
    }

    pub(super) fn take_lowered_children(
        &self,
        region: RegionId,
        results: &mut Vec<PlannedBlock>,
        start: usize,
        expected: usize,
    ) -> Result<Vec<PlannedBlock>, HirLowerError> {
        if results.len() != start.saturating_add(expected) {
            return self.invalid_region(region, "region child results contradict containment");
        }
        Ok(results.split_off(start))
    }

    pub(super) fn lower_region_inputs(
        &mut self,
        region: RegionId,
    ) -> Result<Vec<HirStmt>, HirLowerError> {
        let inputs = self.index.region_inputs.get(region.index()).ok_or(
            HirLowerError::MissingPlanRegion {
                proto: self.proto.index(),
                region: region.index(),
            },
        )?;
        let mut assignments = Vec::new();
        for &(phi_id, value) in inputs {
            #[cfg(debug_assertions)]
            if self
                .emitted_synthetic_inputs
                .get_mut(phi_id.index())
                .is_none_or(|emitted| std::mem::replace(emitted, true))
            {
                return self.invalid_region(region, "synthetic region input is emitted twice");
            }
            assignments.push((phi_id, self.ssa_expr(region, value)?));
        }
        self.copy_assignments(region, assignments)
    }
}

fn flatten_implicit_root_scope_fence(
    mut children: Vec<PlannedBlock>,
    planned_children: &[RegionId],
    fence: &ImplicitRootScopeFence,
) -> Result<PlannedBlock, &'static str> {
    let Some(start) = planned_children
        .iter()
        .position(|child| *child == fence.first_child)
    else {
        return Err("implicit root scope fence start is not a direct child");
    };
    let Some(end) = planned_children
        .iter()
        .position(|child| *child == fence.end_before_child)
    else {
        return Err("implicit root scope fence end is not a direct child");
    };
    // ended_roots is retained as a consumer-side certificate sanity check. HIR promotion can
    // merge identities, so this layer must not try to rematch the original TempIds to statements.
    if start >= end || planned_children.len() != children.len() || fence.ended_roots.is_empty() {
        return Err("implicit root scope fence has a stale child interval");
    }

    let trailing = children.split_off(end);
    let scoped_children = children.split_off(start);
    let mut flattened = PlannedBlock::new();
    for child in children {
        flattened.append(child);
    }
    let mut scoped = PlannedBlock::new();
    for child in scoped_children {
        scoped.append(child);
    }
    let mut trailing = trailing.into_iter();
    let Some(mut end_child) = trailing.next() else {
        return Err("implicit root scope fence end child is empty");
    };
    if !matches!(end_child.last(), Some(HirStmt::If(_))) {
        return Err("implicit root scope fence end child has no terminal branch");
    }
    let end_child_tail = end_child.split_off(end_child.len() - 1);
    scoped.append(end_child);
    flattened.push(HirStmt::Block(Box::new(scoped.finish()?)));
    flattened.append(end_child_tail);
    for child in trailing {
        flattened.append(child);
    }
    Ok(flattened)
}
