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
                    // 候选拒绝[SemanticBarrier:ControlFlow]：该 break 路径没有定义 result；
                    // 若只收集其它 break，改名会让这条路径错误地观察 seed 的旧值。
                    return false;
                };
                let mut assignments = Vec::new();
                if !collect_terminal_assignments(previous, &mut assignments) {
                    // 候选拒绝[SemanticBarrier:ControlFlow]：break 前结构尾至少有一条
                    // fallthrough 路径未定义 result；合并后该路径会改为观察 seed 旧值。
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
            HirStmt::Continue if reject_untracked_transfers => {
                // 候选拒绝[SemanticBarrier:ControlFlow]：continue 可绕过已收集的 break
                // writeback 并从 repeat condition 退出；self-contained goto/label 已由
                // owner-wide lexical CFG 建边，不再作为整个 body 的 blanket guard。
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
    result_index: &RegionResultIndex,
    promotion_facts: &ProtoPromotionFacts,
    require_home_slot: bool,
) -> Option<BTreeMap<CarryBinding, CarryBinding>> {
    let mut rewrites = BTreeMap::new();
    for result in results {
        let exact_bindings = exits
            .iter()
            .filter_map(|exit| exit.get(result))
            .filter_map(ExitValue::exact_binding)
            .collect::<BTreeSet<_>>();
        if exact_bindings.is_empty() {
            continue;
        }
        let candidates = exact_bindings
            .iter()
            .copied()
            .filter(|binding| result_index.is_available_before(*binding, region_index))
            .collect::<BTreeSet<_>>();
        if candidates.is_empty() {
            // 候选拒绝[SemanticBarrier:Scope]：出口 owner 在 region 前不可用时，直接把
            // result producer 改写为该 owner 会制造声明前写入。
            return None;
        }
        let Some(seed) = candidates.iter().copied().find(|seed| {
            *seed != *result
                && !results.contains(seed)
                && result_index.is_private_after(*seed, region_index)
                && (!require_home_slot || bindings_share_home_slot(*result, *seed, promotion_facts))
        }) else {
            if candidates
                .iter()
                .all(|seed| *seed == *result || results.contains(seed))
            {
                // 候选拒绝[SemanticBarrier:EvalOrder]：result-to-result 出口 RHS 读的是并行
                // 写前的旧 result epoch；将 rewrite map 做闭包会把它换成下游 seed。
            } else {
                // 候选拒绝[SemanticBarrier:Lifetime]：多出口 join owner 若在 region 后仍可
                // 观察或与 result 异槽，分支写入会改变其独立 epoch/root。
            }
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
    retain_compatible_shared_seed_rewrites(&mut rewrites, exits);
    (!rewrites.is_empty()).then_some(rewrites)
}

fn retain_compatible_shared_seed_rewrites(
    rewrites: &mut BTreeMap<CarryBinding, CarryBinding>,
    exits: &[ExitValues],
) {
    let mut results_by_seed = BTreeMap::<CarryBinding, Vec<CarryBinding>>::new();
    for (result, seed) in rewrites.iter() {
        results_by_seed.entry(*seed).or_default().push(*result);
    }
    for results in results_by_seed
        .into_values()
        .filter(|results| results.len() > 1)
    {
        let values_are_equal = exits.iter().all(|exit| {
            let Some(first) = exit.get(&results[0]) else {
                return false;
            };
            results[1..].iter().all(|result| {
                exit.get(result)
                    .is_some_and(|value| exit_values_are_proven_equal(first, value))
            })
        });
        if !values_are_equal {
            // 未证明相等时仍可合并一个 result；其余 result 保留独立 binding，避免把
            // 两个并行出口值压进同一个 seed。这样不需要猜测任意表达式的值关系。
            for result in &results[1..] {
                rewrites.remove(result);
            }
        }
    }
}

fn exit_values_are_proven_equal(left: &ExitValue, right: &ExitValue) -> bool {
    match (left, right) {
        (
            ExitValue::TailProjection {
                projection: left, ..
            },
            ExitValue::TailProjection {
                projection: right, ..
            },
        ) => left == right,
        (ExitValue::Expr { expr: left, .. }, ExitValue::Expr { expr: right, .. }) => {
            carry_binding_from_expr(left)
                .is_some_and(|binding| carry_binding_from_expr(right) == Some(binding))
                || match (left, right) {
                    (HirExpr::Nil, HirExpr::Nil)
                    | (HirExpr::Boolean(false), HirExpr::Boolean(false))
                    | (HirExpr::Boolean(true), HirExpr::Boolean(true)) => true,
                    (HirExpr::Integer(left), HirExpr::Integer(right)) => left == right,
                    (HirExpr::Int64(left), HirExpr::Int64(right)) => left == right,
                    (HirExpr::UInt64(left), HirExpr::UInt64(right)) => left == right,
                    (HirExpr::String(left), HirExpr::String(right)) => left == right,
                    (HirExpr::Vector(left), HirExpr::Vector(right)) => left == right,
                    (
                        HirExpr::Complex {
                            real: left_real,
                            imag: left_imag,
                        },
                        HirExpr::Complex {
                            real: right_real,
                            imag: right_imag,
                        },
                    ) => {
                        left_real.to_bits() == right_real.to_bits()
                            && left_imag.to_bits() == right_imag.to_bits()
                    }
                    (HirExpr::UpvalueRef(left), HirExpr::UpvalueRef(right)) => left == right,
                    (HirExpr::Number(left), HirExpr::Number(right)) => {
                        left.to_bits() == right.to_bits()
                    }
                    _ => false,
                }
        }
        (ExitValue::Expr { .. }, ExitValue::TailProjection { .. })
        | (ExitValue::TailProjection { .. }, ExitValue::Expr { .. }) => false,
    }
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

pub(super) fn rewrite_is_private_after(
    region_index: usize,
    rewrites: &BTreeMap<CarryBinding, CarryBinding>,
    result_index: &RegionResultIndex,
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
    let rewrite_end = block.stmts.len();
    apply_rewrites_in_range(
        block,
        declarations,
        region_index..rewrite_end,
        rewrites,
        promotion_facts,
    );
}

pub(super) fn apply_rewrites_in_range(
    block: &mut HirBlock,
    declarations: std::ops::Range<usize>,
    rewrite_range: std::ops::Range<usize>,
    rewrites: BTreeMap<CarryBinding, CarryBinding>,
    promotion_facts: &mut ProtoPromotionFacts,
) {
    apply_rewrites_with_declarations(
        block,
        declarations.collect(),
        rewrite_range,
        rewrites,
        promotion_facts,
    );
}

pub(super) fn apply_rewrites_with_declarations(
    block: &mut HirBlock,
    mut declarations: Vec<usize>,
    rewrite_range: std::ops::Range<usize>,
    rewrites: BTreeMap<CarryBinding, CarryBinding>,
    promotion_facts: &mut ProtoPromotionFacts,
) {
    let prunable = rewrites.values().copied().collect::<BTreeSet<_>>();
    let rewritten = rewrite_stmts(
        &mut block.stmts[rewrite_range.clone()],
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
        &mut block.stmts[rewrite_range],
        &mut RedundantSelfAssignPrunePass::for_bindings(prunable.iter().copied()),
    );
    declarations.sort_unstable();
    for declaration in declarations.into_iter().rev() {
        block.stmts.remove(declaration);
    }
    prune_empty_assign_stmts(block);
}

pub(super) fn apply_loop_result_rewrites(
    block: &mut HirBlock,
    loop_index: usize,
    rewrite_end: usize,
    rewrites: BTreeMap<CarryBinding, CarryBinding>,
    promotion_facts: &mut ProtoPromotionFacts,
    has_fallthrough_exit: bool,
) {
    let prunable = rewrites.values().copied().collect::<BTreeSet<_>>();
    let boundary = (rewrite_end < block.stmts.len()).then_some(rewrite_end);
    let mut pass = BindingClassRewritePass {
        rewrites,
        promotion_facts,
    };
    let mut rewritten = match &mut block.stmts[loop_index] {
        HirStmt::While(while_stmt) => {
            rewrite_break_exit_assignments(&mut while_stmt.body, &mut pass)
        }
        HirStmt::Repeat(repeat_stmt) => {
            let mut rewritten = rewrite_break_exit_assignments(&mut repeat_stmt.body, &mut pass);
            if has_fallthrough_exit {
                rewritten |= rewrite_terminal_assignments_mut(
                    repeat_stmt
                        .body
                        .stmts
                        .last_mut()
                        .expect("fallthrough result loop has a terminal assignment"),
                    &mut pass,
                );
            }
            rewritten
        }
        _ => unreachable!("loop result rewrite requires while/repeat"),
    };
    rewritten |= rewrite_stmts(&mut block.stmts[loop_index + 1..rewrite_end], &mut pass);
    if let Some(boundary) = boundary {
        rewritten |= rewrite_boundary_assignment_reads(&mut block.stmts[boundary], &mut pass);
    }
    assert!(
        rewritten,
        "inferred loop results must contain at least one planned binding rewrite"
    );
    rewrite_stmts(
        &mut block.stmts[loop_index..rewrite_end],
        &mut RedundantSelfAssignPrunePass::for_bindings(prunable.iter().copied()),
    );
    prune_empty_assign_stmts(block);
}

fn rewrite_break_exit_assignments(
    block: &mut HirBlock,
    pass: &mut BindingClassRewritePass<'_>,
) -> bool {
    let mut rewritten = false;
    for index in 0..block.stmts.len() {
        if matches!(block.stmts[index], HirStmt::Break) {
            rewritten |= rewrite_terminal_assignments_mut(
                block
                    .stmts
                    .get_mut(index - 1)
                    .expect("collected break has a reaching assignment"),
                pass,
            );
            continue;
        }
        match &mut block.stmts[index] {
            HirStmt::If(if_stmt) => {
                rewritten |= rewrite_break_exit_assignments(&mut if_stmt.then_block, pass);
                if let Some(else_block) = &mut if_stmt.else_block {
                    rewritten |= rewrite_break_exit_assignments(else_block, pass);
                }
            }
            HirStmt::Block(block) => rewritten |= rewrite_break_exit_assignments(block, pass),
            HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::NumericFor(_)
            | HirStmt::GenericFor(_)
            | HirStmt::LocalDecl(_)
            | HirStmt::GlobalDecl(_)
            | HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Return(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => {}
        }
    }
    rewritten
}

fn rewrite_terminal_assignments_mut(
    stmt: &mut HirStmt,
    pass: &mut BindingClassRewritePass<'_>,
) -> bool {
    match stmt {
        HirStmt::Assign(_) => rewrite_stmts(std::slice::from_mut(stmt), pass),
        HirStmt::Block(block) => rewrite_terminal_assignments_mut(
            block
                .stmts
                .last_mut()
                .expect("collected terminal block has a tail"),
            pass,
        ),
        HirStmt::If(if_stmt) => {
            let then_rewritten = rewrite_terminal_assignments_mut(
                if_stmt
                    .then_block
                    .stmts
                    .last_mut()
                    .expect("collected terminal if arm has a tail"),
                pass,
            );
            let else_rewritten = rewrite_terminal_assignments_mut(
                if_stmt
                    .else_block
                    .as_mut()
                    .and_then(|block| block.stmts.last_mut())
                    .expect("collected terminal else arm has a tail"),
                pass,
            );
            then_rewritten || else_rewritten
        }
        _ => unreachable!("collected terminal result producer must end in assignments"),
    }
}

fn rewrite_boundary_assignment_reads(
    stmt: &mut HirStmt,
    pass: &mut BindingClassRewritePass<'_>,
) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        unreachable!("loop result epoch boundary is a direct assignment");
    };
    let original_targets = std::mem::take(&mut assign.targets);
    let retained_indices = original_targets
        .iter()
        .enumerate()
        .filter_map(|(index, target)| {
            (!carry_binding_from_lvalue(target)
                .is_some_and(|binding| pass.rewrites.contains_key(&binding)))
            .then_some(index)
        })
        .collect::<Vec<_>>();
    let mut scratch = HirStmt::Assign(Box::new(HirAssign {
        targets: retained_indices
            .iter()
            .map(|index| original_targets[*index].clone())
            .collect(),
        values: assign.values.clone(),
        initializer_merge_transaction: None,
        generic_for_initializer_producer: None,
        method_rewrite_transaction: None,
    }));
    let rewritten = rewrite_stmts(std::slice::from_mut(&mut scratch), pass);
    let HirStmt::Assign(scratch) = scratch else {
        unreachable!();
    };
    assign.values = scratch.values;
    let mut rewritten_targets = scratch.targets.into_iter();
    assign.targets = original_targets
        .into_iter()
        .enumerate()
        .map(|(index, target)| {
            if retained_indices.binary_search(&index).is_ok() {
                rewritten_targets
                    .next()
                    .expect("retained target rewrite preserves arity")
            } else {
                target
            }
        })
        .collect();
    if rewritten {
        assign.generic_for_initializer_producer = None;
    }
    rewritten
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
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
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
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        };
        let preserved = HirAssign {
            targets: vec![HirLValue::Param(ParamId(0)), HirLValue::Local(LocalId(0))],
            values: HirValuePack::fixed(vec![HirExpr::Integer(7), HirExpr::ParamRef(ParamId(0))]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        };
        let overwritten = assignment_values(&overwritten);
        let preserved = assignment_values(&preserved);
        let index = RegionResultIndex::new(&[]);

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
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })
            })
            .collect::<Vec<_>>();
        let stmts = vec![
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![LocalId(1)],
                values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                initializer_merge_transaction: None,
            })),
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![LocalId(2)],
                values: HirValuePack::fixed(vec![HirExpr::Integer(2)]),
                initializer_merge_transaction: None,
            })),
        ];
        let index = RegionResultIndex::new(&stmts);
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
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })
            })
            .collect::<Vec<_>>();
        let stmts = vec![
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![LocalId(1)],
                values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                initializer_merge_transaction: None,
            })),
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![LocalId(2)],
                values: HirValuePack::fixed(vec![HirExpr::Integer(2)]),
                initializer_merge_transaction: None,
            })),
            HirStmt::Block(Box::default()),
            HirStmt::Return(Box::new(crate::hir::common::HirReturn {
                source_instr: None,
                values: HirValuePack::fixed(vec![
                    HirExpr::LocalRef(LocalId(1)),
                    HirExpr::LocalRef(LocalId(2)),
                ]),
            })),
        ];
        let index = RegionResultIndex::new(&stmts);

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
    fn shared_seed_accepts_proven_equal_values_on_every_exit() {
        let first = CarryBinding::Local(LocalId(0));
        let second = CarryBinding::Local(LocalId(1));
        let seed = CarryBinding::Param(ParamId(0));
        let exact = assignment_values(&HirAssign {
            targets: vec![HirLValue::Local(LocalId(0)), HirLValue::Local(LocalId(1))],
            values: HirValuePack::fixed(vec![
                HirExpr::ParamRef(ParamId(0)),
                HirExpr::ParamRef(ParamId(0)),
            ]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        });
        let equal_literals = assignment_values(&HirAssign {
            targets: vec![HirLValue::Local(LocalId(0)), HirLValue::Local(LocalId(1))],
            values: HirValuePack::fixed(vec![HirExpr::Integer(7), HirExpr::Integer(7)]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        });
        let index = RegionResultIndex::new(&[]);

        let rewrites = infer_rewrites(
            &[first, second],
            &[exact, equal_literals],
            0,
            &index,
            &ProtoPromotionFacts::default(),
            false,
        )
        .expect("equal exit values retain one value after sharing their seed");

        assert!(rewrites == BTreeMap::from([(first, seed), (second, seed)]));
    }

    #[test]
    fn shared_seed_keeps_one_result_when_exit_values_differ() {
        let first = CarryBinding::Local(LocalId(0));
        let second = CarryBinding::Local(LocalId(1));
        let exact = assignment_values(&HirAssign {
            targets: vec![HirLValue::Local(LocalId(0)), HirLValue::Local(LocalId(1))],
            values: HirValuePack::fixed(vec![
                HirExpr::ParamRef(ParamId(0)),
                HirExpr::ParamRef(ParamId(0)),
            ]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        });
        let distinct = assignment_values(&HirAssign {
            targets: vec![HirLValue::Local(LocalId(0)), HirLValue::Local(LocalId(1))],
            values: HirValuePack::fixed(vec![HirExpr::Integer(1), HirExpr::Integer(2)]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        });
        let index = RegionResultIndex::new(&[]);

        let rewrites = infer_rewrites(
            &[first, second],
            &[exact, distinct],
            0,
            &index,
            &ProtoPromotionFacts::default(),
            false,
        )
        .expect("one result can still use the seed without merging distinct exit values");

        assert!(rewrites == BTreeMap::from([(first, CarryBinding::Param(ParamId(0)))]));
    }

    #[test]
    fn result_seed_chain_rejects_parallel_old_epoch_read() {
        let first = CarryBinding::Local(LocalId(0));
        let second = CarryBinding::Local(LocalId(1));
        let exit = assignment_values(&HirAssign {
            targets: vec![HirLValue::Local(LocalId(0)), HirLValue::Local(LocalId(1))],
            values: HirValuePack::fixed(vec![
                HirExpr::LocalRef(LocalId(1)),
                HirExpr::ParamRef(ParamId(0)),
            ]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        });
        let index = RegionResultIndex::new(&[]);

        assert!(
            infer_rewrites(
                &[first, second],
                &[exit],
                0,
                &index,
                &ProtoPromotionFacts::default(),
                false,
            )
            .is_none()
        );
    }
}
