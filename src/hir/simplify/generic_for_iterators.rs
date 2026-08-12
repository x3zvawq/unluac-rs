//! 把 generic-for 的 VM 初始化序列收回完整 source value pack。
//!
//! Lua 5.4+ 除 iterator/state/control 外还会物化第 4 个 closing value；前置固定表达式
//! 与最终多返回调用又可能拆成多条赋值。这里按 GenericFor 已记录的完整源码 pack
//! 一次接管初始化序列，不再按 call/nil 形状分别猜测。
//!
//! 输入：`t0 = next; t1,t2,t3 = factory()<exact:3>; GenericFor(t0,t1,t2,t3)`
//! 输出：`GenericFor(next, factory()<open>)`

use std::collections::VecDeque;

use crate::hir::common::{
    HirBlock, HirExpr, HirGenericFor, HirLValue, HirProto, HirStmt, HirValuePack,
};

use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn fold_generic_for_iterators_in_proto(proto: &mut HirProto) -> bool {
    rewrite_proto(proto, &mut GenericForIteratorPass)
}

struct GenericForIteratorPass;

impl HirRewritePass for GenericForIteratorPass {
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
            if let Some(plan) = fold_plan(pending.make_contiguous()) {
                new_stmts.push(fold_front(&mut pending, plan));
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

#[derive(Clone, Copy)]
struct FoldPlan {
    assignment_count: usize,
}

fn fold_plan(stmts: &[HirStmt]) -> Option<FoldPlan> {
    // VM 最多给 generic-for 保留 iterator/state/control/closing 四个 source slots。
    for assignment_count in 1..=4 {
        if !matches!(stmts.get(assignment_count - 1), Some(HirStmt::Assign(_))) {
            return None;
        }
        let Some(HirStmt::GenericFor(generic_for)) = stmts.get(assignment_count) else {
            continue;
        };
        if assignments_match_iterator(&stmts[..assignment_count], generic_for) {
            return Some(FoldPlan { assignment_count });
        }
        return None;
    }
    None
}

fn assignments_match_iterator(assignments: &[HirStmt], generic_for: &HirGenericFor) -> bool {
    if generic_for.iterator.tail.is_some() {
        return false;
    }

    let Some(expected) = generic_for
        .iterator
        .fixed
        .iter()
        .map(|expr| match expr {
            HirExpr::TempRef(temp) => Some(*temp),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    let mut actual = Vec::with_capacity(expected.len());
    for (index, stmt) in assignments.iter().enumerate() {
        let HirStmt::Assign(assign) = stmt else {
            return false;
        };
        if assign.values.exact_result_len() != Some(assign.targets.len())
            || (assign.values.tail.is_some() && index + 1 != assignments.len())
        {
            return false;
        }
        for target in &assign.targets {
            let HirLValue::Temp(temp) = target else {
                return false;
            };
            actual.push(*temp);
        }
    }
    actual == expected
}

fn fold_front(pending: &mut VecDeque<HirStmt>, plan: FoldPlan) -> HirStmt {
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

    let Some(HirStmt::GenericFor(mut generic_for)) = pending.pop_front() else {
        unreachable!("validated generic-for owner");
    };
    generic_for.iterator = iterator;
    HirStmt::GenericFor(generic_for)
}
