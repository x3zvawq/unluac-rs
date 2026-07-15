//! 恢复被临时寄存器拆开的多返回值赋值。
//!
//! Lua 5.1 编译器会把 `a, b = obj:f()` 这类目标不是连续寄存器的赋值拆成：
//! 先用一组 temp 接住调用返回值，再把这些 temp 逐个写回真正目标。HIR 到这里已经
//! 知道这些写回都是全局赋值时，可以把它们重新收成一条多赋值，避免后续 AST
//! 再物化出只转手一次的局部临时变量。

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::hir::common::{HirAssign, HirBlock, HirExpr, HirLValue, HirProto, HirStmt, TempId};

use super::temp_touch::{TempTouchIndex, collect_temp_refs_by_stmt};
use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn collapse_multiret_global_assignments_in_proto(proto: &mut HirProto) -> bool {
    rewrite_proto(proto, &mut MultiretAssignmentPass)
}

struct MultiretAssignmentPass;

impl HirRewritePass for MultiretAssignmentPass {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        collapse_block_multiret_global_assignments(block)
    }
}

fn collapse_block_multiret_global_assignments(block: &mut HirBlock) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let stmt_refs = collect_temp_refs_by_stmt(&old_stmts);
    let touch_index = TempTouchIndex::new(&stmt_refs);
    let mut pending = VecDeque::from(old_stmts);
    let mut new_stmts = Vec::with_capacity(pending.len());
    let mut changed = false;
    let mut index = 0;

    while !pending.is_empty() {
        if let Some(plan) = collapse_plan(pending.make_contiguous(), index, &touch_index) {
            let consumed = plan.consumed;
            new_stmts.push(collapse_front(&mut pending, plan));
            changed = true;
            index += consumed;
            continue;
        }

        new_stmts.push(
            pending
                .pop_front()
                .expect("non-empty multiret assignment scan queue"),
        );
        index += 1;
    }

    block.stmts = new_stmts;
    changed
}

struct CollapsePlan {
    temp_targets: Vec<TempId>,
    consumed: usize,
}

fn collapse_plan(
    stmts: &[HirStmt],
    original_index: usize,
    touch_index: &TempTouchIndex<'_>,
) -> Option<CollapsePlan> {
    let HirStmt::Assign(source_assign) = stmts.first()? else {
        return None;
    };
    let temp_targets = temp_targets_for_multiret_call(source_assign)?;
    let consumed = temp_targets.len() + 1;
    let transfer_stmts = stmts.get(1..consumed)?;

    let temp_set = temp_targets.iter().copied().collect::<BTreeSet<_>>();
    let mut transfers = BTreeSet::new();
    let mut target_names = BTreeSet::new();
    for stmt in transfer_stmts {
        let (temp, target) = global_transfer_assignment(stmt)?;
        let target_name = global_target_name(target)?;
        if !temp_set.contains(&temp) || !transfers.insert(temp) {
            return None;
        }
        if !target_names.insert(target_name) {
            return None;
        }
    }

    if transfers.len() != temp_targets.len()
        || temp_set
            .iter()
            .any(|temp| touch_index.touches_after(original_index + consumed, *temp))
    {
        return None;
    }

    Some(CollapsePlan {
        temp_targets,
        consumed,
    })
}

fn collapse_front(pending: &mut VecDeque<HirStmt>, plan: CollapsePlan) -> HirStmt {
    let Some(HirStmt::Assign(source_assign)) = pending.pop_front() else {
        unreachable!("validated multiret source assignment");
    };
    let mut transfers = BTreeMap::new();
    for _ in 1..plan.consumed {
        let stmt = pending
            .pop_front()
            .expect("validated multiret transfer assignment");
        let (temp, target) = into_global_transfer_assignment(stmt)
            .expect("validated multiret global transfer shape");
        transfers.insert(temp, target);
    }
    let targets = plan
        .temp_targets
        .iter()
        .map(|temp| {
            transfers
                .remove(temp)
                .expect("validated multiret transfer temp")
        })
        .collect();
    HirStmt::Assign(Box::new(HirAssign {
        targets,
        values: source_assign.values,
    }))
}

fn temp_targets_for_multiret_call(assign: &HirAssign) -> Option<Vec<TempId>> {
    if assign.targets.len() < 2 {
        return None;
    }
    let tail = assign.values.tail.as_ref()?;
    let HirExpr::Call(_) = tail.as_expr() else {
        return None;
    };
    if !assign.values.fixed.is_empty() || tail.exact_width() != Some(assign.targets.len()) {
        return None;
    }
    assign
        .targets
        .iter()
        .map(|target| match target {
            HirLValue::Temp(temp) => Some(*temp),
            _ => None,
        })
        .collect()
}

fn global_transfer_assignment(stmt: &HirStmt) -> Option<(TempId, &HirLValue)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let ([target @ HirLValue::Global(_)], [HirExpr::TempRef(temp)]) =
        (assign.targets.as_slice(), assign.values.fixed.as_slice())
    else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
    Some((*temp, target))
}

fn into_global_transfer_assignment(stmt: HirStmt) -> Option<(TempId, HirLValue)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let HirAssign {
        mut targets,
        values,
    } = *assign;
    if targets.len() != 1 || values.tail.is_some() || values.fixed.len() != 1 {
        return None;
    }
    let target = targets.pop()?;
    if !matches!(target, HirLValue::Global(_)) {
        return None;
    }
    let HirExpr::TempRef(temp) = values.fixed.into_iter().next()? else {
        return None;
    };
    Some((temp, target))
}

fn global_target_name(target: &HirLValue) -> Option<&str> {
    let HirLValue::Global(global) = target else {
        return None;
    };
    Some(&global.name)
}
