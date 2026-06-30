//! 这个 pass 负责收回 AST build hoist 后残留的 carried local 机械拆分。
//!
//! 相邻 `local seed = expr; local carried; ... carried = seed ...` 属于 HIR
//! `carried-locals` 的身份收敛职责。这里只处理 AST build 把空 carried local
//! hoist 到块首后，seed local 留在后面初始化声明串里的残余形状：
//!
//! - `local carried; local a = ...; local i, total = 1, 0; ... carried = next; i, total = ...`
//! - 会收回成：`local a = ...; local i, total = 1, 0; ... total = next; i = ...`
//!   这样后面的 `statement_merge / inline_exprs` 才能继续把分支内的中转 local 收回源码形状。

use super::super::common::{
    AstAssign, AstBindingRef, AstBlock, AstExpr, AstLValue, AstLocalAttr, AstModule, AstStmt,
};
use super::ReadabilityContext;
use super::binding_flow::name_matches_binding;
use super::binding_tree::{
    expr_references_binding, lvalue_references_binding, rewrite_binding_in_stmt,
    stmt_references_or_captures_binding,
};
use super::walk::{self, AstRewritePass, BlockKind};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let _ = context.target;
    walk::rewrite_module(module, &mut LocalCoalescePass)
}

struct LocalCoalescePass;

impl AstRewritePass for LocalCoalescePass {
    fn rewrite_block(&mut self, block: &mut AstBlock, _kind: BlockKind) -> bool {
        let mut changed = false;
        let mut index = 0;
        while index < block.stmts.len() {
            let Some(carried) = single_empty_local_decl(&block.stmts[index]) else {
                index += 1;
                continue;
            };
            let Some((seed_index, seed)) = find_later_seed_local(&block.stmts, index, carried)
            else {
                index += 1;
                continue;
            };

            let mut tail = block.stmts.split_off(seed_index + 1);
            rewrite_carried_binding_in_stmts(&mut tail, carried, seed);
            block.stmts.append(&mut tail);
            block.stmts.remove(index);
            changed = true;
        }

        changed
    }
}

fn initialized_local_decl_bindings(stmt: &AstStmt) -> Vec<AstBindingRef> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return Vec::new();
    };
    local_decl
        .bindings
        .iter()
        .enumerate()
        .filter_map(|(index, binding)| {
            (binding.attr == AstLocalAttr::None && index < local_decl.values.len())
                .then_some(binding.id)
        })
        .collect()
}

fn single_empty_local_decl(stmt: &AstStmt) -> Option<AstBindingRef> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    if !local_decl.values.is_empty() || binding.attr != AstLocalAttr::None {
        return None;
    }
    Some(binding.id)
}

fn find_later_seed_local(
    stmts: &[AstStmt],
    carried_index: usize,
    carried: AstBindingRef,
) -> Option<(usize, AstBindingRef)> {
    let carried_mentions = BindingMentionSpans::new(stmts, carried);
    for seed_index in carried_index + 1..stmts.len() {
        let AstStmt::LocalDecl(_) = &stmts[seed_index] else {
            break;
        };
        if carried_mentions.has_in_range(carried_index + 1, seed_index) {
            return None;
        }
        for seed in initialized_local_decl_bindings(&stmts[seed_index]) {
            if tail_has_structured_carried_writeback(
                stmts,
                seed_index + 1,
                seed,
                carried,
                &carried_mentions,
            ) {
                return Some((seed_index, seed));
            }
        }
    }
    None
}

fn tail_has_structured_carried_writeback(
    stmts: &[AstStmt],
    tail_start: usize,
    seed: AstBindingRef,
    carried: AstBindingRef,
    carried_mentions: &BindingMentionSpans,
) -> bool {
    if stmts.len().saturating_sub(tail_start) < 2 {
        return false;
    }

    for index in tail_start..stmts.len().saturating_sub(1) {
        let AstStmt::If(if_stmt) = &stmts[index] else {
            continue;
        };
        let AstStmt::Assign(writeback) = &stmts[index + 1] else {
            continue;
        };
        if !is_supported_seed_writeback_assign(writeback, seed, carried)
            || carried_mentions.has_in_range(tail_start, index)
            || carried_mentions.has_from(index + 2)
            || !if_branches_end_with_carried_assign(if_stmt, carried)
        {
            continue;
        }
        return true;
    }
    false
}

struct BindingMentionSpans {
    prefix_counts: Vec<usize>,
}

impl BindingMentionSpans {
    fn new(stmts: &[AstStmt], binding: AstBindingRef) -> Self {
        let mut prefix_counts = Vec::with_capacity(stmts.len() + 1);
        prefix_counts.push(0);
        for stmt in stmts {
            let count = usize::from(stmt_references_or_captures_binding(stmt, binding));
            let previous = prefix_counts.last().copied().unwrap_or(0);
            prefix_counts.push(previous + count);
        }

        Self { prefix_counts }
    }

    fn has_in_range(&self, start: usize, end: usize) -> bool {
        if start >= end {
            return false;
        }
        self.prefix_counts[end] > self.prefix_counts[start]
    }

    fn has_from(&self, index: usize) -> bool {
        self.prefix_counts.last().copied().unwrap_or(0) > self.prefix_counts[index]
    }
}

fn if_branches_end_with_carried_assign(
    if_stmt: &super::super::common::AstIf,
    carried: AstBindingRef,
) -> bool {
    block_ends_with_carried_assign(&if_stmt.then_block, carried)
        && if_stmt
            .else_block
            .as_ref()
            .is_some_and(|block| block_ends_with_carried_assign(block, carried))
}

fn block_ends_with_carried_assign(block: &AstBlock, carried: AstBindingRef) -> bool {
    let Some((last, _)) = block.stmts.split_last() else {
        return false;
    };
    !BindingMentionSpans::new(&block.stmts, carried).has_in_range(0, block.stmts.len() - 1)
        && matches!(last, AstStmt::Assign(assign) if is_direct_carried_store(assign, carried))
}

fn is_direct_carried_store(assign: &AstAssign, carried: AstBindingRef) -> bool {
    let [AstLValue::Name(target)] = assign.targets.as_slice() else {
        return false;
    };
    let [value] = assign.values.as_slice() else {
        return false;
    };
    name_matches_binding(target, carried) && !expr_references_binding(value, carried)
}

fn is_supported_seed_writeback_assign(
    assign: &AstAssign,
    seed: AstBindingRef,
    carried: AstBindingRef,
) -> bool {
    if assign.targets.len() != assign.values.len() || assign.targets.is_empty() {
        return false;
    }

    let mut saw_writeback = false;
    for (target, value) in assign.targets.iter().zip(&assign.values) {
        let is_writeback = matches!(
            (target, value),
            (AstLValue::Name(target), AstExpr::Var(value))
                if name_matches_binding(target, seed) && name_matches_binding(value, carried)
        );
        if is_writeback {
            saw_writeback = true;
            continue;
        }
        if lvalue_references_binding(target, seed) || expr_references_binding(value, seed) {
            return false;
        }
    }

    saw_writeback
}

fn rewrite_carried_binding_in_stmts(
    stmts: &mut Vec<AstStmt>,
    carried: AstBindingRef,
    seed: AstBindingRef,
) {
    let mut prune_pass = RedundantSeedCopyPrunePass { carried, seed };
    for stmt in stmts.iter_mut() {
        rewrite_binding_in_stmt(stmt, carried, seed);
        walk::rewrite_stmt(stmt, &mut prune_pass);
    }
    prune_redundant_seed_copy_stmts(stmts, carried, seed);
}

struct RedundantSeedCopyPrunePass {
    carried: AstBindingRef,
    seed: AstBindingRef,
}

impl AstRewritePass for RedundantSeedCopyPrunePass {
    fn rewrite_block(&mut self, block: &mut AstBlock, _kind: BlockKind) -> bool {
        prune_redundant_seed_copy_stmts(&mut block.stmts, self.carried, self.seed)
    }

    fn rewrite_stmt(&mut self, stmt: &mut AstStmt) -> bool {
        prune_redundant_self_assign_components(stmt, self.seed)
    }
}

fn prune_redundant_seed_copy_stmts(
    stmts: &mut Vec<AstStmt>,
    carried: AstBindingRef,
    seed: AstBindingRef,
) -> bool {
    let original_len = stmts.len();
    stmts.retain(|stmt| {
        !is_exact_copy_stmt(stmt, carried, seed)
            && !is_redundant_self_assign(stmt, seed)
            && !is_empty_assign_stmt(stmt)
    });
    stmts.len() != original_len
}

fn prune_redundant_self_assign_components(stmt: &mut AstStmt, binding: AstBindingRef) -> bool {
    let AstStmt::Assign(assign) = stmt else {
        return false;
    };

    let mut rewritten = Vec::with_capacity(assign.targets.len());
    for (target, value) in assign
        .targets
        .iter()
        .cloned()
        .zip(assign.values.iter().cloned())
    {
        if !matches_redundant_self_assign_component(&target, &value, binding) {
            rewritten.push((target, value));
        }
    }
    if rewritten.len() == assign.targets.len() {
        return false;
    }

    assign.targets = rewritten.iter().map(|(target, _)| target.clone()).collect();
    assign.values = rewritten.into_iter().map(|(_, value)| value).collect();
    true
}

fn matches_redundant_self_assign_component(
    target: &AstLValue,
    value: &AstExpr,
    binding: AstBindingRef,
) -> bool {
    let AstLValue::Name(target) = target else {
        return false;
    };
    let AstExpr::Var(value) = value else {
        return false;
    };
    name_matches_binding(target, binding) && name_matches_binding(value, binding)
}

fn is_exact_copy_stmt(stmt: &AstStmt, carried: AstBindingRef, seed: AstBindingRef) -> bool {
    let AstStmt::Assign(assign) = stmt else {
        return false;
    };
    is_exact_seed_copy_assign(assign, carried, seed)
}

fn is_empty_assign_stmt(stmt: &AstStmt) -> bool {
    matches!(stmt, AstStmt::Assign(assign) if assign.targets.is_empty())
}

fn is_redundant_self_assign(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    let AstStmt::Assign(assign) = stmt else {
        return false;
    };
    let [AstLValue::Name(target)] = assign.targets.as_slice() else {
        return false;
    };
    let [AstExpr::Var(value)] = assign.values.as_slice() else {
        return false;
    };
    name_matches_binding(target, binding) && name_matches_binding(value, binding)
}

fn is_exact_seed_copy_assign(
    assign: &AstAssign,
    carried: AstBindingRef,
    seed: AstBindingRef,
) -> bool {
    let [AstLValue::Name(target)] = assign.targets.as_slice() else {
        return false;
    };
    let [AstExpr::Var(value)] = assign.values.as_slice() else {
        return false;
    };
    name_matches_binding(target, carried) && name_matches_binding(value, seed)
}
