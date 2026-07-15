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

pub(super) struct LabelJumpIndex {
    gotos_by_label: BTreeMap<HirLabelId, Vec<usize>>,
    nearest_prior_labels: Vec<Option<HirLabelId>>,
}

impl LabelJumpIndex {
    pub(super) fn new(stmts: &[HirStmt]) -> Self {
        let mut gotos_by_label = BTreeMap::<HirLabelId, Vec<usize>>::new();
        let mut nearest_prior_labels = Vec::with_capacity(stmts.len());
        let mut nearest_prior_label = None;

        for (index, stmt) in stmts.iter().enumerate() {
            nearest_prior_labels.push(nearest_prior_label);
            for target in goto_targets(stmt) {
                gotos_by_label.entry(target).or_default().push(index);
            }
            if let HirStmt::Label(label) = stmt {
                nearest_prior_label = Some(label.id);
            }
        }

        Self {
            gotos_by_label,
            nearest_prior_labels,
        }
    }

    pub(super) fn next_label_has_prior_goto(&self, stmts: &[HirStmt], index: usize) -> bool {
        let Some(HirStmt::Label(label)) = stmts.get(index + 1) else {
            return false;
        };
        self.has_goto_before(index, label.id)
    }

    pub(super) fn nearest_prior_label(&self, index: usize) -> Option<HirLabelId> {
        self.nearest_prior_labels.get(index).copied().flatten()
    }

    pub(super) fn has_goto_at_or_after(&self, start: usize, target: HirLabelId) -> bool {
        let Some(indices) = self.gotos_by_label.get(&target) else {
            return false;
        };
        let offset = indices.partition_point(|index| *index < start);
        indices.get(offset).is_some()
    }

    fn has_goto_before(&self, end: usize, target: HirLabelId) -> bool {
        self.gotos_by_label
            .get(&target)
            .is_some_and(|indices| indices.first().is_some_and(|index| *index < end))
    }
}

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

fn goto_targets(stmt: &HirStmt) -> BTreeSet<HirLabelId> {
    let mut targets = BTreeSet::new();
    collect_goto_targets(stmt, &mut targets);
    targets
}

fn collect_goto_targets(stmt: &HirStmt, targets: &mut BTreeSet<HirLabelId>) {
    match stmt {
        HirStmt::Goto(goto) => {
            targets.insert(goto.target);
        }
        HirStmt::If(if_stmt) => {
            collect_block_goto_targets(&if_stmt.then_block, targets);
            if let Some(else_block) = &if_stmt.else_block {
                collect_block_goto_targets(else_block, targets);
            }
        }
        HirStmt::While(while_stmt) => collect_block_goto_targets(&while_stmt.body, targets),
        HirStmt::Repeat(repeat_stmt) => collect_block_goto_targets(&repeat_stmt.body, targets),
        HirStmt::Block(block) => collect_block_goto_targets(block, targets),
        HirStmt::Unstructured(unstructured) => {
            collect_block_goto_targets(&unstructured.body, targets);
        }
        HirStmt::NumericFor(numeric_for) => collect_block_goto_targets(&numeric_for.body, targets),
        HirStmt::GenericFor(generic_for) => collect_block_goto_targets(&generic_for.body, targets),
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
        | HirStmt::Label(_) => {}
    }
}

fn collect_block_goto_targets(block: &HirBlock, targets: &mut BTreeSet<HirLabelId>) {
    for stmt in &block.stmts {
        collect_goto_targets(stmt, targets);
    }
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
    if assign.values.tail.is_some()
        || assign.targets.is_empty()
        || assign.targets.len() != assign.values.fixed.len()
    {
        return None;
    }

    let mut seen_targets = BTreeSet::new();
    let mut seen_sources = BTreeSet::new();
    let mut pairs = Vec::with_capacity(assign.targets.len());

    for (target, value) in assign.targets.iter().zip(&assign.values.fixed) {
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
