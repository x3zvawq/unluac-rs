//! 收集 break assignment、推导 carried binding 重写并校验 home slot/capture；依赖 slot ownership，不负责并行赋值拆分；例如拒绝跨捕获槽的别名重写。

use super::*;

pub(super) fn collect_break_assignments(
    block: &HirBlock,
    exits: &mut Vec<ExitValues>,
    reject_untracked_transfers: bool,
) -> bool {
    for (index, stmt) in block.stmts.iter().enumerate() {
        match stmt {
            HirStmt::Break => {
                let Some(previous) = index
                    .checked_sub(1)
                    .and_then(|index| block.stmts.get(index))
                else {
                    // 候选拒绝[ProofIncomplete]：break 前没有可承载 result reaching-def 的语句。
                    return false;
                };
                let mut assignments = Vec::new();
                if !collect_terminal_assignments(previous, &mut assignments) {
                    // 候选拒绝[ProofIncomplete]：break 前的结构化语句存在无尾赋值的
                    // fallthrough 路径；仍需更一般的 reaching-def 证明。
                    return false;
                }
                exits.extend(assignments.into_iter().map(assignment_values));
            }
            HirStmt::If(if_stmt) => {
                if !collect_break_assignments(
                    &if_stmt.then_block,
                    exits,
                    reject_untracked_transfers,
                ) || if_stmt.else_block.as_ref().is_some_and(|block| {
                    !collect_break_assignments(block, exits, reject_untracked_transfers)
                }) {
                    return false;
                }
            }
            HirStmt::Block(block) => {
                if !collect_break_assignments(block, exits, reject_untracked_transfers) {
                    return false;
                }
            }
            HirStmt::Continue | HirStmt::Goto(_) | HirStmt::Label(_)
                if reject_untracked_transfers =>
            {
                // 候选拒绝[SemanticBarrier:ControlFlow]：continue/goto/label 可绕过已收集的 break writeback，出口集合不完整会提交错误 state。
                return false;
            }
            HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::NumericFor(_)
            | HirStmt::GenericFor(_) => {}
            _ => {}
        }
    }
    true
}

fn collect_terminal_assignments<'a>(
    stmt: &'a HirStmt,
    assignments: &mut Vec<&'a HirAssign>,
) -> bool {
    match stmt {
        HirStmt::Assign(assign) => {
            assignments.push(assign);
            true
        }
        HirStmt::Block(block) => block
            .stmts
            .last()
            .is_some_and(|stmt| collect_terminal_assignments(stmt, assignments)),
        HirStmt::If(if_stmt) => {
            let Some(else_block) = &if_stmt.else_block else {
                return false;
            };
            let mut branch_assignments = Vec::new();
            let complete =
                if_stmt.then_block.stmts.last().is_some_and(|stmt| {
                    collect_terminal_assignments(stmt, &mut branch_assignments)
                }) && else_block.stmts.last().is_some_and(|stmt| {
                    collect_terminal_assignments(stmt, &mut branch_assignments)
                });
            if complete {
                assignments.extend(branch_assignments);
            }
            complete
        }
        HirStmt::LocalDecl(_)
        | HirStmt::GlobalDecl(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

pub(super) fn block_may_fall_through(block: &HirBlock) -> bool {
    let Some(last) = block.stmts.last() else {
        return true;
    };
    match last {
        HirStmt::Return(_) | HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_) => false,
        HirStmt::If(if_stmt) => if_stmt.else_block.as_ref().is_none_or(|else_block| {
            block_may_fall_through(&if_stmt.then_block) || block_may_fall_through(else_block)
        }),
        HirStmt::Block(block) => block_may_fall_through(block),
        _ => true,
    }
}

pub(super) fn result_writes_are_standalone_seed_copies(
    stmts: &[HirStmt],
    result: CarryBinding,
    seed: CarryBinding,
    expected_writes: usize,
) -> bool {
    struct CopyWriteCollector {
        result: CarryBinding,
        seed: CarryBinding,
        writes: usize,
        valid: bool,
    }

    impl HirVisitor for CopyWriteCollector {
        fn visit_stmt(&mut self, stmt: &HirStmt) {
            let HirStmt::Assign(assign) = stmt else {
                return;
            };
            let result_writes = assign
                .targets
                .iter()
                .filter(|target| carry_binding_from_lvalue(target) == Some(self.result))
                .count();
            if result_writes == 0 {
                return;
            }
            self.writes += result_writes;
            self.valid &= matches!(
                (assign.targets.as_slice(), assign.values.fixed.as_slice()),
                ([target], [value])
                    if assign.values.tail.is_none()
                        && carry_binding_from_lvalue(target) == Some(self.result)
                        && carry_binding_from_expr(value) == Some(self.seed)
            );
        }
    }

    let mut collector = CopyWriteCollector {
        result,
        seed,
        writes: 0,
        valid: true,
    };
    visit_stmts(stmts, &mut collector);
    collector.valid && collector.writes == expected_writes
}

pub(super) fn infer_rewrites(
    results: &[CarryBinding],
    exits: &[ExitValues],
    region_index: usize,
    result_index: &RegionResultIndex<'_>,
    promotion_facts: &ProtoPromotionFacts,
    require_home_slot: bool,
) -> Option<BTreeMap<CarryBinding, CarryBinding>> {
    let mut rewrites = BTreeMap::new();
    for result in results {
        let candidates = exits
            .iter()
            .filter_map(|exit| exit.get(result))
            .filter_map(ExitValue::exact_binding)
            .filter(|binding| result_index.is_available_before(*binding, region_index))
            .collect::<BTreeSet<_>>();
        let Some(seed) = candidates.iter().copied().find(|seed| {
            *seed != *result
                && !results.contains(seed)
                && result_index.is_private_after(*seed, region_index)
                && (!require_home_slot || bindings_share_home_slot(*result, *seed, promotion_facts))
        }) else {
            // 候选拒绝[SemanticBarrier:Lifetime]：多出口 join owner 若在 region 后仍可观察或与 result 异槽，分支写入会改变其独立 epoch/root。
            // 候选拒绝[ProofIncomplete]：result-to-result seed 链需要先做映射闭包；单层 rewrite map 不能把中间 result 当作稳定 owner。
            return None;
        };
        // 每个出口的 result producer 都在原路径原地改写；因此私有 seed 可直接作为 join slot，
        // 其他出口 seed 会自然变成 `join = path_seed`，不需要额外 phi 表达。
        if !rewritten_result_keeps_exit_values(*result, seed, exits) {
            // 候选拒绝[SemanticBarrier:EvalOrder]：同批 assignment 在 result 后再次写 seed 时，改名后的最后写会覆盖原 result 出口值；反最小见 seed_write_after_result_is_rejected。
            return None;
        }
        if require_home_slot && !bindings_share_home_slot(*result, seed, promotion_facts) {
            // 候选拒绝[SemanticBarrier:Lifetime]：异槽或 compaction 下 result/state 是两个 GC/close 可观察 root，不能只凭值相同合并。
            return None;
        }
        rewrites.insert(*result, seed);
    }
    if !shared_seed_results_are_exact_copies(&rewrites, exits) {
        // 候选拒绝[ProofIncomplete]：共享 seed 的多个 result 若不是每条出口都精确复制该 seed，
        // 并行合并后只能保留一个最后值；尚缺能证明各 result 出口值相等的 value relation。
        return None;
    }
    Some(rewrites)
}

fn shared_seed_results_are_exact_copies(
    rewrites: &BTreeMap<CarryBinding, CarryBinding>,
    exits: &[ExitValues],
) -> bool {
    let mut results_by_seed = BTreeMap::<CarryBinding, Vec<CarryBinding>>::new();
    for (result, seed) in rewrites {
        results_by_seed.entry(*seed).or_default().push(*result);
    }
    results_by_seed.into_iter().all(|(seed, results)| {
        results.len() == 1
            || exits.iter().all(|exit| {
                results
                    .iter()
                    .all(|result| exit.get(result).and_then(ExitValue::exact_binding) == Some(seed))
            })
    })
}

pub(super) fn rewritten_results_keep_exit_values(
    rewrites: &BTreeMap<CarryBinding, CarryBinding>,
    exits: &[ExitValues],
) -> bool {
    rewrites
        .iter()
        .all(|(result, seed)| rewritten_result_keeps_exit_values(*result, *seed, exits))
}

fn rewritten_result_keeps_exit_values(
    result: CarryBinding,
    seed: CarryBinding,
    exits: &[ExitValues],
) -> bool {
    exits.iter().all(|exit| {
        exit.get(&result)
            .zip(exit.get(&seed))
            .is_none_or(|(result, seed)| result.target_index() > seed.target_index())
    })
}

pub(super) fn rewrites_preserve_home_slots(
    rewrites: &BTreeMap<CarryBinding, CarryBinding>,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    rewrites
        .iter()
        .all(|(result, seed)| bindings_share_home_slot(*result, *seed, promotion_facts))
}

pub(super) fn bindings_share_home_slot(
    result: CarryBinding,
    seed: CarryBinding,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    !promotion_facts.compacts_home_slots()
        && binding_home_slot(result, promotion_facts)
            .zip(binding_home_slot(seed, promotion_facts))
            .is_some_and(|(result, seed)| result == seed)
}

pub(super) fn rewrite_is_private_and_uncaptured(
    region_index: usize,
    rewrites: &BTreeMap<CarryBinding, CarryBinding>,
    result_index: &RegionResultIndex<'_>,
) -> bool {
    rewrites
        .values()
        .all(|seed| result_index.is_private_after(*seed, region_index))
}

pub(super) fn apply_rewrites(
    block: &mut HirBlock,
    declarations: std::ops::Range<usize>,
    region_index: usize,
    rewrites: BTreeMap<CarryBinding, CarryBinding>,
    promotion_facts: &mut ProtoPromotionFacts,
) {
    let prunable = rewrites.values().copied().collect::<BTreeSet<_>>();
    let rewritten = rewrite_stmts(
        &mut block.stmts[region_index..],
        &mut BindingClassRewritePass {
            rewrites,
            promotion_facts,
        },
    );
    assert!(
        rewritten,
        "inferred region results must contain at least one planned binding rewrite"
    );
    rewrite_stmts(
        &mut block.stmts[region_index..],
        &mut RedundantSelfAssignPrunePass::for_bindings(prunable.iter().copied()),
    );
    if !declarations.is_empty() {
        block.stmts.drain(declarations);
    }
    prune_empty_assign_stmts(block);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::common::{HirIf, LocalId, ParamId, TempId};
    use crate::hir::promotion::HomeSlotKey;

    fn result_assignment() -> HirStmt {
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Local(LocalId(0))],
            values: HirValuePack::fixed(vec![HirExpr::ParamRef(ParamId(0))]),
        }))
    }

    #[test]
    fn break_collects_every_complete_if_tail_assignment() {
        let block = HirBlock {
            stmts: vec![
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::TempRef(TempId(0)),
                    then_block: HirBlock {
                        stmts: vec![result_assignment()],
                    },
                    else_block: Some(HirBlock {
                        stmts: vec![HirStmt::Block(Box::new(HirBlock {
                            stmts: vec![result_assignment()],
                        }))],
                    }),
                })),
                HirStmt::Break,
            ],
        };
        let mut exits = Vec::new();

        assert!(collect_break_assignments(&block, &mut exits, true));
        assert!(exits.len() == 2);
        assert!(exits.iter().all(|exit| {
            exit.get(&CarryBinding::Local(LocalId(0)))
                .and_then(ExitValue::exact_binding)
                == Some(CarryBinding::Param(ParamId(0)))
        }));
    }

    #[test]
    fn break_rejects_if_tail_with_unassigned_fallthrough_arm() {
        let block = HirBlock {
            stmts: vec![
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::TempRef(TempId(0)),
                    then_block: HirBlock {
                        stmts: vec![result_assignment()],
                    },
                    else_block: None,
                })),
                HirStmt::Break,
            ],
        };
        let mut exits = Vec::new();

        assert!(!collect_break_assignments(&block, &mut exits, true));
        assert!(exits.is_empty());
    }

    #[test]
    fn seed_write_after_result_is_rejected() {
        let result = CarryBinding::Local(LocalId(0));
        let overwritten = HirAssign {
            targets: vec![HirLValue::Local(LocalId(0)), HirLValue::Param(ParamId(0))],
            values: HirValuePack::fixed(vec![HirExpr::ParamRef(ParamId(0)), HirExpr::Integer(7)]),
        };
        let preserved = HirAssign {
            targets: vec![HirLValue::Param(ParamId(0)), HirLValue::Local(LocalId(0))],
            values: HirValuePack::fixed(vec![HirExpr::Integer(7), HirExpr::ParamRef(ParamId(0))]),
        };
        let overwritten = assignment_values(&overwritten);
        let preserved = assignment_values(&preserved);
        let captured = BTreeSet::new();
        let index = RegionResultIndex::new(&[], &captured);

        assert!(
            infer_rewrites(
                &[result],
                &[overwritten],
                0,
                &index,
                &ProtoPromotionFacts::default(),
                false,
            )
            .is_none()
        );
        assert!(
            infer_rewrites(
                &[result],
                &[preserved],
                0,
                &index,
                &ProtoPromotionFacts::default(),
                false,
            )
            .is_some()
        );
    }

    #[test]
    fn multiple_exit_seeds_choose_a_private_join_owner() {
        let result = CarryBinding::Local(LocalId(0));
        let first = CarryBinding::Local(LocalId(1));
        let second = CarryBinding::Local(LocalId(2));
        let exits = [first, second]
            .into_iter()
            .map(|seed| {
                assignment_values(&HirAssign {
                    targets: vec![HirLValue::Local(LocalId(0))],
                    values: HirValuePack::fixed(vec![match seed {
                        CarryBinding::Local(local) => HirExpr::LocalRef(local),
                        CarryBinding::Param(_) | CarryBinding::Temp(_) => unreachable!(),
                    }]),
                })
            })
            .collect::<Vec<_>>();
        let stmts = vec![
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![LocalId(1)],
                values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
            })),
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![LocalId(2)],
                values: HirValuePack::fixed(vec![HirExpr::Integer(2)]),
            })),
        ];
        let captured = BTreeSet::new();
        let index = RegionResultIndex::new(&stmts, &captured);
        let mut facts = ProtoPromotionFacts::default();
        for local in [LocalId(0), LocalId(1), LocalId(2)] {
            facts.record_local_home_slot(local, HomeSlotKey::new(0, 0));
        }

        let rewrites = infer_rewrites(&[result], &exits, 2, &index, &facts, true)
            .expect("a private seed can own the path-sensitive join writes");

        assert!(rewrites == BTreeMap::from([(result, first)]));
    }

    #[test]
    fn multiple_exit_seeds_reject_observable_join_owners() {
        let result = CarryBinding::Local(LocalId(0));
        let exits = [LocalId(1), LocalId(2)]
            .into_iter()
            .map(|seed| {
                assignment_values(&HirAssign {
                    targets: vec![HirLValue::Local(LocalId(0))],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(seed)]),
                })
            })
            .collect::<Vec<_>>();
        let stmts = vec![
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![LocalId(1)],
                values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
            })),
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![LocalId(2)],
                values: HirValuePack::fixed(vec![HirExpr::Integer(2)]),
            })),
            HirStmt::Block(Box::default()),
            HirStmt::Return(Box::new(crate::hir::common::HirReturn {
                values: HirValuePack::fixed(vec![
                    HirExpr::LocalRef(LocalId(1)),
                    HirExpr::LocalRef(LocalId(2)),
                ]),
            })),
        ];
        let captured = BTreeSet::new();
        let index = RegionResultIndex::new(&stmts, &captured);

        assert!(
            infer_rewrites(
                &[result],
                &exits,
                2,
                &index,
                &ProtoPromotionFacts::default(),
                false,
            )
            .is_none()
        );
    }

    #[test]
    fn shared_seed_accepts_results_that_are_exact_copies_on_every_exit() {
        let first = CarryBinding::Local(LocalId(0));
        let second = CarryBinding::Local(LocalId(1));
        let seed = CarryBinding::Param(ParamId(0));
        let exit = assignment_values(&HirAssign {
            targets: vec![HirLValue::Local(LocalId(0)), HirLValue::Local(LocalId(1))],
            values: HirValuePack::fixed(vec![
                HirExpr::ParamRef(ParamId(0)),
                HirExpr::ParamRef(ParamId(0)),
            ]),
        });
        let captured = BTreeSet::new();
        let index = RegionResultIndex::new(&[], &captured);

        let rewrites = infer_rewrites(
            &[first, second],
            &[exit],
            0,
            &index,
            &ProtoPromotionFacts::default(),
            false,
        )
        .expect("parallel exact copies retain the same value after sharing their seed");

        assert!(rewrites == BTreeMap::from([(first, seed), (second, seed)]));
    }

    #[test]
    fn shared_seed_rejects_results_with_distinct_exit_values() {
        let first = CarryBinding::Local(LocalId(0));
        let second = CarryBinding::Local(LocalId(1));
        let exact = assignment_values(&HirAssign {
            targets: vec![HirLValue::Local(LocalId(0)), HirLValue::Local(LocalId(1))],
            values: HirValuePack::fixed(vec![
                HirExpr::ParamRef(ParamId(0)),
                HirExpr::ParamRef(ParamId(0)),
            ]),
        });
        let distinct = assignment_values(&HirAssign {
            targets: vec![HirLValue::Local(LocalId(0)), HirLValue::Local(LocalId(1))],
            values: HirValuePack::fixed(vec![HirExpr::Integer(1), HirExpr::Integer(2)]),
        });
        let captured = BTreeSet::new();
        let index = RegionResultIndex::new(&[], &captured);

        assert!(
            infer_rewrites(
                &[first, second],
                &[exact, distinct],
                0,
                &index,
                &ProtoPromotionFacts::default(),
                false,
            )
            .is_none()
        );
    }
}
