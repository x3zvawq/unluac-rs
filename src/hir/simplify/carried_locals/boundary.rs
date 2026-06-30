//! fallback 边界快照的 carried binding 等价类收敛。
//!
//! 这个模块只识别显式 `label/goto` mesh 里的边界别名快照，例如多个分支入口都出现
//! `assign tA, tB = sA, sB; goto L` 时，把同一个状态槽位串成等价类并统一到 canonical
//! binding。它依赖 `binding.rs` 的 local/temp 统一表示和 rewrite pass，但不处理普通
//! seed handoff，也不判断更新后交棒；这些由 `handoffs.rs` 负责。
//!
//! 例子：
//! - 输入：`if cond then assign t10, t11 = t0, t1; goto L2 end; ... ::L2:: assign t2 = t10 + 1`
//! - 输出：`if cond then goto L2 end; ... ::L2:: assign t0 = t0 + 1`

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirAssign, HirBlock, HirLabelId, HirStmt};

use super::super::walk::rewrite_stmts;
use super::binding::{
    BindingClassRewritePass, CarryBinding, carry_binding_from_expr, carry_binding_from_lvalue,
};
use super::prune::{collect_prunable_bindings, prune_boundary_snapshot_self_assigns};

pub(super) fn collapse_boundary_alias_classes(block: &mut HirBlock) -> bool {
    if !block
        .stmts
        .iter()
        .any(|stmt| matches!(stmt, HirStmt::Goto(_) | HirStmt::Label(_)))
    {
        return false;
    }

    let boundary_pairs = collect_boundary_alias_pairs(block);
    if boundary_pairs.len() < 2 {
        return false;
    }

    let mut adjacency = BTreeMap::<CarryBinding, BTreeSet<CarryBinding>>::new();
    for pairs in boundary_pairs {
        for (target, source) in pairs {
            adjacency.entry(target).or_default().insert(source);
            adjacency.entry(source).or_default().insert(target);
        }
    }

    let mut visited = BTreeSet::new();
    let mut rewrites = BTreeMap::new();
    for &binding in adjacency.keys() {
        if !visited.insert(binding) {
            continue;
        }

        let mut stack = vec![binding];
        let mut component = BTreeSet::from([binding]);
        while let Some(current) = stack.pop() {
            let Some(neighbors) = adjacency.get(&current) else {
                continue;
            };
            for &neighbor in neighbors {
                if visited.insert(neighbor) {
                    stack.push(neighbor);
                }
                component.insert(neighbor);
            }
        }

        // 这里只吃“已经被多条边界快照串起来”的 mesh 状态类。
        // 单条 `a = b` 本身既可能是 handoff，也可能只是暂时保留的并行值；
        // 至少需要 3 个成员，才能证明这更像同一槽位在多个 label 入口之间来回交棒。
        if component.len() < 3 {
            continue;
        }

        let canonical = component
            .iter()
            .copied()
            .min_by_key(|binding| binding_canonical_key(*binding))
            .expect("component is non-empty");
        for member in component {
            if member != canonical {
                rewrites.insert(member, canonical);
            }
        }
    }

    if rewrites.is_empty() {
        return false;
    }

    let prunable_bindings = collect_prunable_bindings(rewrites.values().copied());
    let mut pass = BindingClassRewritePass { rewrites };
    if !rewrite_stmts(&mut block.stmts, &mut pass) {
        return false;
    }

    prune_boundary_snapshot_self_assigns(block, &prunable_bindings);
    true
}

pub(super) fn next_label_has_prior_goto(stmts: &[HirStmt], index: usize) -> bool {
    let Some(HirStmt::Label(label)) = stmts.get(index + 1) else {
        return false;
    };
    stmts[..index]
        .iter()
        .any(|stmt| stmt_contains_goto_to_label(stmt, label.id))
}

pub(super) fn stmt_contains_goto_to_label(stmt: &HirStmt, target: HirLabelId) -> bool {
    match stmt {
        HirStmt::Goto(goto) => goto.target == target,
        HirStmt::If(if_stmt) => {
            block_contains_goto_to_label(&if_stmt.then_block, target)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|else_block| block_contains_goto_to_label(else_block, target))
        }
        HirStmt::While(while_stmt) => block_contains_goto_to_label(&while_stmt.body, target),
        HirStmt::Repeat(repeat_stmt) => block_contains_goto_to_label(&repeat_stmt.body, target),
        HirStmt::Block(block) => block_contains_goto_to_label(block, target),
        HirStmt::Unstructured(unstructured) => {
            block_contains_goto_to_label(&unstructured.body, target)
        }
        HirStmt::NumericFor(numeric_for) => block_contains_goto_to_label(&numeric_for.body, target),
        HirStmt::GenericFor(generic_for) => block_contains_goto_to_label(&generic_for.body, target),
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Label(_) => false,
    }
}

fn block_contains_goto_to_label(block: &HirBlock, target: HirLabelId) -> bool {
    block
        .stmts
        .iter()
        .any(|stmt| stmt_contains_goto_to_label(stmt, target))
}

fn collect_boundary_alias_pairs(block: &HirBlock) -> Vec<Vec<(CarryBinding, CarryBinding)>> {
    let mut pairs = Vec::new();

    for (index, stmt) in block.stmts.iter().enumerate() {
        if let HirStmt::Assign(assign) = stmt
            && let Some(alias_pairs) =
                top_level_boundary_alias_pairs(assign, block.stmts.get(index + 1))
        {
            pairs.push(alias_pairs);
        }

        let HirStmt::If(if_stmt) = stmt else {
            continue;
        };
        let falls_through_to_label = matches!(block.stmts.get(index + 1), Some(HirStmt::Label(_)));

        if let Some(then_pairs) =
            edge_snapshot_alias_pairs(&if_stmt.then_block, falls_through_to_label)
        {
            pairs.push(then_pairs);
        }
        if let Some(else_block) = &if_stmt.else_block
            && let Some(else_pairs) = edge_snapshot_alias_pairs(else_block, falls_through_to_label)
        {
            pairs.push(else_pairs);
        }
    }

    pairs
}

fn top_level_boundary_alias_pairs(
    assign: &HirAssign,
    next_stmt: Option<&HirStmt>,
) -> Option<Vec<(CarryBinding, CarryBinding)>> {
    match next_stmt {
        Some(HirStmt::Goto(_)) | Some(HirStmt::Label(_)) => pure_alias_pairs(assign),
        _ => None,
    }
}

fn edge_snapshot_alias_pairs(
    block: &HirBlock,
    allow_fallthrough_to_label: bool,
) -> Option<Vec<(CarryBinding, CarryBinding)>> {
    match block.stmts.as_slice() {
        [HirStmt::Assign(assign), HirStmt::Goto(_)] => pure_alias_pairs(assign),
        [HirStmt::Assign(assign)] if allow_fallthrough_to_label => pure_alias_pairs(assign),
        _ => None,
    }
}

fn pure_alias_pairs(assign: &HirAssign) -> Option<Vec<(CarryBinding, CarryBinding)>> {
    if assign.targets.is_empty() || assign.targets.len() != assign.values.len() {
        return None;
    }

    let mut seen_targets = BTreeSet::new();
    let mut seen_sources = BTreeSet::new();
    let mut pairs = Vec::with_capacity(assign.targets.len());

    for (target, value) in assign.targets.iter().zip(&assign.values) {
        let target = carry_binding_from_lvalue(target)?;
        let source = carry_binding_from_expr(value)?;
        if !seen_targets.insert(target) || !seen_sources.insert(source) {
            return None;
        }
        pairs.push((target, source));
    }

    Some(pairs)
}

fn binding_canonical_key(binding: CarryBinding) -> (u8, usize) {
    match binding {
        CarryBinding::Local(local) => (0, local.index()),
        CarryBinding::Temp(temp) => (1, temp.index()),
    }
}
