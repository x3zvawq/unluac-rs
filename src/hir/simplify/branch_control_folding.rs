//! branch-control 收敛：把 HIR 中残留的前向 goto 壳恢复成普通条件结构。
//!
//! 这里只消费已经存在的 `If/Goto/Label`，不重新解释 CFG，也不接管同一 lvalue 选值；
//! branch-value 形状仍由 `branch_value_folding` 先处理。每轮先为当前 block 建一次 label
//! 位置和引用计数，再按不交叉区间从右向左改写，避免多个 guard 共用 label 时反复全块
//! 扫描和重建。

use std::collections::BTreeMap;

use crate::hir::common::{HirBlock, HirIf, HirLabelId, HirProto, HirStmt};

use super::label_refs::count_label_references;
use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn fold_branch_control_in_proto(proto: &mut HirProto) -> bool {
    rewrite_proto(proto, &mut BranchControlPass)
}

struct BranchControlPass;

impl HirRewritePass for BranchControlPass {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let terminal_changed = fold_forward_gotos(&mut block.stmts, FoldKind::TerminalElse);
        let guard_changed = fold_forward_gotos(&mut block.stmts, FoldKind::Guard);
        let nop_changed = remove_nop_goto_labels(&mut block.stmts);
        terminal_changed || guard_changed || nop_changed
    }
}

#[derive(Clone, Copy)]
enum FoldKind {
    TerminalElse,
    Guard,
}

struct FoldGroup {
    label: HirLabelId,
    label_index: usize,
    candidates: Vec<FoldCandidate>,
}

#[derive(Clone, Copy)]
struct FoldCandidate {
    if_index: usize,
    invert_cond: bool,
}

fn fold_forward_gotos(stmts: &mut Vec<HirStmt>, kind: FoldKind) -> bool {
    let label_indices = index_top_level_labels(stmts);
    let label_refs = count_label_references(stmts);
    let mut groups = BTreeMap::<usize, FoldGroup>::new();

    for (if_index, stmt) in stmts.iter().enumerate() {
        let Some((target, invert_cond)) = fold_target(stmt, kind) else {
            continue;
        };
        let Some(label_index) = label_indices.get(&target).copied() else {
            continue;
        };
        if label_index <= if_index + 1 {
            continue;
        }
        let body = &stmts[(if_index + 1)..label_index];
        if !can_move_into_branch(body)
            || matches!(kind, FoldKind::TerminalElse)
                && is_branch_value_assignment(stmt, body, invert_cond)
        {
            continue;
        }
        groups
            .entry(label_index)
            .or_insert_with(|| FoldGroup {
                label: target,
                label_index,
                candidates: Vec::new(),
            })
            .candidates
            .push(FoldCandidate {
                if_index,
                invert_cond,
            });
    }

    if groups.is_empty() {
        return false;
    }

    // 可移动区间不含顶层 label，因此不同目标的区间不会交叉。倒序改写可保持更早
    // 区间的原始索引稳定；同一 label 的多个 guard 在一次改写中直接嵌套。
    for group in groups.into_values().rev() {
        let keep_label =
            label_refs.get(&group.label).copied().unwrap_or_default() > group.candidates.len();
        rewrite_fold_group(stmts, group, kind, keep_label);
    }
    true
}

fn rewrite_fold_group(
    stmts: &mut Vec<HirStmt>,
    group: FoldGroup,
    kind: FoldKind,
    keep_label: bool,
) {
    let first = group.candidates[0].if_index;
    let mut next = group.label_index;
    let mut nested = Vec::new();

    for candidate in group.candidates.into_iter().rev() {
        let if_index = candidate.if_index;
        let mut body = stmts[(if_index + 1)..next].to_vec();
        body.append(&mut nested);
        let HirStmt::If(if_stmt) = stmts[if_index].clone() else {
            unreachable!("branch-control fold index must point to an if")
        };
        nested = vec![HirStmt::If(Box::new(rewrite_if(
            *if_stmt,
            body,
            kind,
            candidate.invert_cond,
        )))];
        next = if_index;
    }

    if keep_label {
        nested.push(stmts[group.label_index].clone());
    }
    stmts.splice(first..=group.label_index, nested);
}

fn rewrite_if(mut if_stmt: HirIf, body: Vec<HirStmt>, kind: FoldKind, invert_cond: bool) -> HirIf {
    if invert_cond {
        if_stmt.cond = if_stmt.cond.negate();
        if_stmt.then_block = if_stmt
            .else_block
            .take()
            .expect("inverted fold must have an else block");
    }
    match kind {
        FoldKind::TerminalElse => {
            let popped = if_stmt.then_block.stmts.pop();
            debug_assert!(matches!(popped, Some(HirStmt::Goto(_))));
            if_stmt.else_block = Some(HirBlock { stmts: body });
        }
        FoldKind::Guard => {
            if_stmt.cond = if_stmt.cond.negate();
            if_stmt.then_block = HirBlock { stmts: body };
            if_stmt.else_block = None;
        }
    }
    if_stmt
}

fn fold_target(stmt: &HirStmt, kind: FoldKind) -> Option<(HirLabelId, bool)> {
    let HirStmt::If(if_stmt) = stmt else {
        return None;
    };
    let else_block = if_stmt.else_block.as_ref();
    let (branch, invert_cond) = match else_block {
        Some(else_block) if if_stmt.then_block.stmts.is_empty() => (else_block, true),
        Some(else_block) if else_block.stmts.is_empty() => (&if_stmt.then_block, false),
        None => (&if_stmt.then_block, false),
        Some(_) => return None,
    };
    match kind {
        FoldKind::TerminalElse => {
            if branch.stmts.len() < 2 {
                return None;
            }
            let HirStmt::Goto(goto) = branch.stmts.last()? else {
                return None;
            };
            Some((goto.target, invert_cond))
        }
        FoldKind::Guard => {
            let [HirStmt::Goto(goto)] = branch.stmts.as_slice() else {
                return None;
            };
            Some((goto.target, invert_cond))
        }
    }
}

fn can_move_into_branch(stmts: &[HirStmt]) -> bool {
    stmts.iter().all(|stmt| {
        !matches!(
            stmt,
            HirStmt::LocalDecl(_) | HirStmt::Goto(_) | HirStmt::Label(_)
        )
    })
}

fn is_branch_value_assignment(if_stmt: &HirStmt, else_body: &[HirStmt], invert_cond: bool) -> bool {
    let HirStmt::If(if_stmt) = if_stmt else {
        return false;
    };
    let branch = if invert_cond {
        let Some(else_block) = if_stmt.else_block.as_ref() else {
            return false;
        };
        else_block
    } else {
        &if_stmt.then_block
    };
    let [HirStmt::Assign(then_assign), HirStmt::Goto(_)] = branch.stmts.as_slice() else {
        return false;
    };
    let [HirStmt::Assign(else_assign)] = else_body else {
        return false;
    };
    then_assign.targets == else_assign.targets
}

fn index_top_level_labels(stmts: &[HirStmt]) -> BTreeMap<HirLabelId, usize> {
    stmts
        .iter()
        .enumerate()
        .filter_map(|(index, stmt)| match stmt {
            HirStmt::Label(label) => Some((label.id, index)),
            _ => None,
        })
        .collect()
}

fn remove_nop_goto_labels(stmts: &mut Vec<HirStmt>) -> bool {
    let label_refs = count_label_references(stmts);
    let mut old = std::mem::take(stmts).into_iter().peekable();
    let mut rewritten = Vec::with_capacity(old.len());
    let mut changed = false;

    while let Some(stmt) = old.next() {
        let HirStmt::Goto(goto) = &stmt else {
            rewritten.push(stmt);
            continue;
        };
        let Some(HirStmt::Label(label)) = old.peek() else {
            rewritten.push(stmt);
            continue;
        };
        if goto.target != label.id {
            rewritten.push(stmt);
            continue;
        }

        let label = old.next().expect("peeked label must remain available");
        if label_refs.get(&goto.target).copied().unwrap_or_default() > 1 {
            rewritten.push(label);
        }
        changed = true;
    }

    *stmts = rewritten;
    changed
}
