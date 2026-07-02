//! 恢复被临时寄存器拆开的多返回值赋值。
//!
//! Lua 5.1 编译器会把 `a, b = obj:f()` 这类目标不是连续寄存器的赋值拆成：
//! 先用一组 temp 接住调用返回值，再把这些 temp 逐个写回真正目标。HIR 到这里已经
//! 知道这些写回都是全局赋值时，可以把它们重新收成一条多赋值，避免后续 AST
//! 再物化出只转手一次的局部临时变量。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirAssign, HirBlock, HirExpr, HirLValue, HirProto, HirStmt, TempId};

use super::temp_touch::stmts_touch_any_temp;
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
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while index < old_stmts.len() {
        if let Some(collapse) = try_collapse_multiret_global_assignment(&old_stmts, index) {
            new_stmts.push(HirStmt::Assign(Box::new(collapse.rewritten)));
            changed = true;
            index += collapse.consumed;
            continue;
        }

        new_stmts.push(old_stmts[index].clone());
        index += 1;
    }

    block.stmts = new_stmts;
    changed
}

struct CollapseResult {
    rewritten: HirAssign,
    consumed: usize,
}

fn try_collapse_multiret_global_assignment(
    stmts: &[HirStmt],
    index: usize,
) -> Option<CollapseResult> {
    let HirStmt::Assign(source_assign) = stmts.get(index)? else {
        return None;
    };
    let temp_targets = temp_targets_for_multiret_call(source_assign)?;
    let consumed = temp_targets.len() + 1;
    let transfer_stmts = stmts.get((index + 1)..(index + consumed))?;

    let mut transfers = BTreeMap::new();
    let mut target_names = BTreeSet::new();
    for stmt in transfer_stmts {
        let (temp, target) = global_transfer_assignment(stmt)?;
        let target_name = global_target_name(&target)?;
        if !temp_targets.contains(&temp) || transfers.insert(temp, target).is_some() {
            return None;
        }
        if !target_names.insert(target_name) {
            return None;
        }
    }

    if transfers.len() != temp_targets.len() {
        return None;
    }
    let temp_set = temp_targets.iter().copied().collect();
    if stmts_touch_any_temp(&stmts[(index + consumed)..], &temp_set) {
        return None;
    }

    let targets = temp_targets
        .iter()
        .map(|temp| transfers.get(temp).cloned())
        .collect::<Option<Vec<_>>>()?;

    Some(CollapseResult {
        rewritten: HirAssign {
            targets,
            values: source_assign.values.clone(),
        },
        consumed,
    })
}

fn temp_targets_for_multiret_call(assign: &HirAssign) -> Option<Vec<TempId>> {
    if assign.targets.len() < 2 {
        return None;
    }
    let [HirExpr::Call(call)] = assign.values.as_slice() else {
        return None;
    };
    if !call.multiret {
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

fn global_transfer_assignment(stmt: &HirStmt) -> Option<(TempId, HirLValue)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let ([target @ HirLValue::Global(_)], [HirExpr::TempRef(temp)]) =
        (assign.targets.as_slice(), assign.values.as_slice())
    else {
        return None;
    };
    Some((*temp, target.clone()))
}

fn global_target_name(target: &HirLValue) -> Option<String> {
    let HirLValue::Global(global) = target else {
        return None;
    };
    Some(global.name.clone())
}
