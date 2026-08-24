//! 把 generic-for 的 VM 初始化序列收回完整 source value pack。
//!
//! Lua 5.4+ 除 iterator/state/control 外还会物化第 4 个 closing value；前置固定表达式
//! 与最终多返回调用又可能拆成多条赋值。这里优先按 GenericFor 已记录的完整源码 pack
//! 一次接管初始化序列；若 closing value 已经更早求值，则只额外收回紧邻循环头的匿名
//! 单次 `nil` run，不跨语句移动其它表达式。
//!
//! 输入：`t0 = next; t1,t2,t3 = factory()<exact:3>; GenericFor(t0,t1,t2,t3)`
//! 输出：`GenericFor(next, factory()<open>)`
//! 输入：`t1,t2 = nil,nil; GenericFor(t0,t1,t2,t3)`
//! 输出：`GenericFor(t0,nil,nil,t3)`
//! direct closure producer 保留为独立 local function；child proto 的体量无法由 HIR
//! 表达式复杂度概括，不应恢复成 loop head 内的多行匿名函数。

use std::collections::{BTreeMap, VecDeque};

use crate::hir::common::{
    HirBlock, HirExpr, HirGenericFor, HirLValue, HirProto, HirStmt, HirValuePack, TempId,
};
use crate::hir::promotion::ProtoPromotionFacts;

use super::mention::collect_temp_use_counts;
use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn fold_generic_for_iterators_in_proto(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
) -> bool {
    let use_counts = collect_temp_use_counts(proto);
    let debug_temps = proto
        .temp_debug_locals
        .iter()
        .map(Option::is_some)
        .collect();
    rewrite_proto(
        proto,
        &mut GenericForIteratorPass {
            use_counts,
            debug_temps,
            facts,
        },
    )
}

struct GenericForIteratorPass<'a> {
    use_counts: BTreeMap<TempId, usize>,
    debug_temps: Vec<bool>,
    facts: &'a ProtoPromotionFacts,
}

impl HirRewritePass for GenericForIteratorPass<'_> {
    fn rewrite_stmt(&mut self, stmt: &mut HirStmt) -> bool {
        let HirStmt::GenericFor(generic_for) = stmt else {
            return false;
        };
        trim_trailing_nil_iterators(&mut generic_for.iterator)
    }

    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let old_stmts = std::mem::take(&mut block.stmts);
        let mut pending = VecDeque::from(old_stmts);
        let mut new_stmts = Vec::with_capacity(pending.len());
        let mut changed = false;

        while !pending.is_empty() {
            if fold_adjacent_nil_iterators(&mut pending, self, &mut new_stmts) {
                changed = true;
            } else if let Some(plan) = fold_plan(pending.make_contiguous(), self) {
                fold_front(&mut pending, plan, &mut new_stmts);
                changed = true;
            } else {
                new_stmts.push(
                    pending
                        .pop_front()
                        .expect("non-empty generic-for scan queue"),
                );
            }
        }

        block.stmts = new_stmts;
        changed
    }
}

fn trim_trailing_nil_iterators(iterator: &mut HirValuePack) -> bool {
    if iterator.tail.is_some() {
        return false;
    }
    let original_len = iterator.fixed.len();
    while iterator.fixed.len() > 1 && matches!(iterator.fixed.last(), Some(HirExpr::Nil)) {
        iterator.fixed.pop();
    }
    iterator.fixed.len() != original_len
}

fn fold_adjacent_nil_iterators(
    pending: &mut VecDeque<HirStmt>,
    context: &GenericForIteratorPass<'_>,
    new_stmts: &mut Vec<HirStmt>,
) -> bool {
    let (iterator_start, value_count) = {
        let stmts = pending.make_contiguous();
        let (Some(HirStmt::Assign(assign)), Some(HirStmt::GenericFor(generic_for))) =
            (stmts.first(), stmts.get(1))
        else {
            return false;
        };
        let value_count = assign.targets.len();
        // exact-width tail 也能给出目标数，但 fixed 为空；这里只接受逐项可核验的 nil。
        if value_count == 0
            || assign.values.tail.is_some()
            || assign.values.fixed.len() != value_count
        {
            return false;
        }
        let Some(iterator_start) =
            generic_for
                .iterator
                .fixed
                .windows(value_count)
                .position(|window| {
                    window
                        .iter()
                        .zip(&assign.targets)
                        .zip(&assign.values.fixed)
                        .all(|((iterator, target), value)| {
                            matches!(
                                (iterator, target, value),
                                (
                                    HirExpr::TempRef(actual),
                                    HirLValue::Temp(expected),
                                    HirExpr::Nil
                                ) if actual == expected
                                    && context.use_counts.get(expected) == Some(&1)
                                    && !context
                                        .debug_temps
                                        .get(expected.index())
                                        .copied()
                                        .unwrap_or(false)
                            )
                        })
                })
        else {
            return false;
        };
        (iterator_start, value_count)
    };

    let Some(HirStmt::Assign(_)) = pending.pop_front() else {
        unreachable!("validated adjacent generic-for nil assignment");
    };
    let Some(HirStmt::GenericFor(mut generic_for)) = pending.pop_front() else {
        unreachable!("validated adjacent generic-for owner");
    };
    generic_for.iterator.fixed[iterator_start..iterator_start + value_count].fill(HirExpr::Nil);
    trim_trailing_nil_iterators(&mut generic_for.iterator);
    new_stmts.push(HirStmt::GenericFor(generic_for));
    true
}

#[derive(Clone, Copy)]
struct FoldPlan {
    assignment_count: usize,
    gap_count: usize,
}

fn fold_plan(stmts: &[HirStmt], context: &GenericForIteratorPass<'_>) -> Option<FoldPlan> {
    // VM 最多给 generic-for 保留 iterator/state/control/closing 四个 source slots。
    for assignment_count in 1..=4 {
        if !matches!(stmts.get(assignment_count - 1), Some(HirStmt::Assign(_))) {
            return None;
        }
        let assignments = &stmts[..assignment_count];
        if let Some(HirStmt::GenericFor(generic_for)) = stmts.get(assignment_count) {
            return assignments_match_iterator(assignments, generic_for).then_some(FoldPlan {
                assignment_count,
                gap_count: 0,
            });
        }
        if let (Some(gap @ HirStmt::Assign(_)), Some(HirStmt::GenericFor(generic_for))) =
            (stmts.get(assignment_count), stmts.get(assignment_count + 1))
            && assignments_match_iterator(assignments, generic_for)
        {
            return parameter_pack_can_cross_temp_copy(assignments, gap, context).then_some(
                FoldPlan {
                    assignment_count,
                    gap_count: 1,
                },
            );
        }
    }
    None
}

// 跨 gap 比相邻折叠多一次求值重排；这里只接纳 VM 的 parameter+nil pack，
// 并以唯一 use/debug identity/home slot 同时证明被删 temp 与保留 copy 相互独立。
fn parameter_pack_can_cross_temp_copy(
    assignments: &[HirStmt],
    gap: &HirStmt,
    context: &GenericForIteratorPass<'_>,
) -> bool {
    let HirStmt::Assign(gap) = gap else {
        return false;
    };
    let ([HirLValue::Temp(gap_target)], [HirExpr::TempRef(gap_source)], None) = (
        gap.targets.as_slice(),
        gap.values.fixed.as_slice(),
        gap.values.tail.as_ref(),
    ) else {
        return false;
    };
    let (Some(gap_target_slot), Some(gap_source_slot)) = (
        context.facts.trusted_temp_home_slot(*gap_target),
        context.facts.trusted_temp_home_slot(*gap_source),
    ) else {
        return false;
    };

    let mut iterator_target_slots = Vec::new();
    let mut iterator_source_slots = Vec::new();
    for stmt in assignments {
        let HirStmt::Assign(assign) = stmt else {
            return false;
        };
        if assign.values.tail.is_some() {
            return false;
        }
        for target in &assign.targets {
            let HirLValue::Temp(temp) = target else {
                return false;
            };
            let Some(slot) = context.facts.trusted_temp_home_slot(*temp) else {
                return false;
            };
            if context.use_counts.get(temp) != Some(&1)
                || context
                    .debug_temps
                    .get(temp.index())
                    .copied()
                    .unwrap_or(false)
                || iterator_target_slots.contains(&slot)
            {
                return false;
            }
            iterator_target_slots.push(slot);
        }
        for value in &assign.values.fixed {
            match value {
                HirExpr::Nil => {}
                HirExpr::ParamRef(param) => {
                    let Some(slot) = context.facts.trusted_param_home_slot(*param) else {
                        return false;
                    };
                    iterator_source_slots.push(slot);
                }
                _ => return false,
            }
        }
    }

    !iterator_target_slots.contains(&gap_target_slot)
        && !iterator_source_slots.contains(&gap_target_slot)
        && !iterator_target_slots.contains(&gap_source_slot)
        && iterator_source_slots
            .iter()
            .all(|slot| !iterator_target_slots.contains(slot))
}

fn assignments_match_iterator(assignments: &[HirStmt], generic_for: &HirGenericFor) -> bool {
    if generic_for.iterator.tail.is_some() {
        return false;
    }

    let mut expected = generic_for.iterator.fixed.iter();
    for (index, stmt) in assignments.iter().enumerate() {
        let HirStmt::Assign(assign) = stmt else {
            return false;
        };
        if assign.values.exact_result_len() != Some(assign.targets.len())
            || (assign.values.tail.is_some() && index + 1 != assignments.len())
            || assign
                .values
                .fixed
                .iter()
                .any(|value| matches!(value, HirExpr::Closure(_)))
        {
            return false;
        }
        for target in &assign.targets {
            let (HirLValue::Temp(actual), Some(HirExpr::TempRef(expected))) =
                (target, expected.next())
            else {
                return false;
            };
            if actual != expected {
                return false;
            }
        }
    }
    expected.next().is_none()
}

fn fold_front(pending: &mut VecDeque<HirStmt>, plan: FoldPlan, new_stmts: &mut Vec<HirStmt>) {
    let mut iterator = HirValuePack::default();
    for _ in 0..plan.assignment_count {
        let HirStmt::Assign(assign) = pending
            .pop_front()
            .expect("validated generic-for init assignment")
        else {
            unreachable!("fold plan only counts assignments");
        };
        iterator.fixed.extend(assign.values.fixed);
        if let Some(tail) = assign.values.tail {
            iterator.tail = Some(tail.into_open());
        }
    }

    trim_trailing_nil_iterators(&mut iterator);

    for _ in 0..plan.gap_count {
        new_stmts.push(
            pending
                .pop_front()
                .expect("validated generic-for assignment gap"),
        );
    }

    let Some(HirStmt::GenericFor(mut generic_for)) = pending.pop_front() else {
        unreachable!("validated generic-for owner");
    };
    generic_for.iterator = iterator;
    new_stmts.push(HirStmt::GenericFor(generic_for));
}
