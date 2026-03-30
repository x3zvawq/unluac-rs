//! 这个 pass 负责收回“seed local + carried local”这一类机械拆分。
//!
//! 在一些 branch-carried / loop-carried 结构里，前层为了保持 SSA 风格，会先落成：
//! `local seed = expr; local carried; ... carried = seed ...`
//! 但如果 `seed` 之后唯一的职责只是给 `carried` 提供初值，那么源码层更自然的形状
//! 往往就是只保留一个最外层 local，并在各个分支里直接更新它。
//!
//! 除了相邻的 `local seed = ...; local carried` 之外，这里也会处理 “hoisted 空 carried
//! local 在前，真正的 seed local 还在后面的初始化声明串里” 这一类形状：
//! - `local carried; local a = ...; local i, total = 1, 0; ... carried = next; i, total = ...`
//! - 会收回成：`local a = ...; local i, total = 1, 0; ... total = next; i = ...`
//!   这样后面的 `statement_merge / inline_exprs` 才能继续把分支内的中转 local 收回源码形状。

use super::super::common::{
    AstAssign, AstBindingRef, AstBlock, AstExpr, AstLValue, AstLocalAttr, AstModule, AstStmt,
};
use super::ReadabilityContext;
use super::binding_flow::name_matches_binding;
use super::binding_tree::{
    call_references_binding, expr_references_binding, lvalue_references_binding,
    rewrite_binding_in_stmt,
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
            if index + 1 < block.stmts.len()
                && let Some(seed) = single_initialized_local_decl(&block.stmts[index])
                && let Some(carried) = single_empty_local_decl(&block.stmts[index + 1])
                && seed_can_absorb_carried(&block.stmts[(index + 2)..], seed, carried)
            {
                let mut tail = block.stmts.split_off(index + 2);
                rewrite_carried_binding_in_stmts(&mut tail, carried, seed);
                block.stmts.append(&mut tail);
                block.stmts.remove(index + 1);
                changed = true;
                continue;
            }

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

fn single_initialized_local_decl(stmt: &AstStmt) -> Option<AstBindingRef> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [_value] = local_decl.values.as_slice() else {
        return None;
    };
    (binding.attr == AstLocalAttr::None).then_some(binding.id)
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
    for seed_index in carried_index + 1..stmts.len() {
        let AstStmt::LocalDecl(_) = &stmts[seed_index] else {
            break;
        };
        if stmts[(carried_index + 1)..seed_index]
            .iter()
            .any(|stmt| stmt_mentions_binding(stmt, carried))
        {
            return None;
        }
        for seed in initialized_local_decl_bindings(&stmts[seed_index]) {
            let tail = &stmts[(seed_index + 1)..];
            if tail_has_structured_carried_writeback(tail, seed, carried) {
                return Some((seed_index, seed));
            }
        }
    }
    None
}

fn tail_has_structured_carried_writeback(
    stmts: &[AstStmt],
    seed: AstBindingRef,
    carried: AstBindingRef,
) -> bool {
    for index in 0..stmts.len().saturating_sub(1) {
        let AstStmt::If(if_stmt) = &stmts[index] else {
            continue;
        };
        let AstStmt::Assign(writeback) = &stmts[index + 1] else {
            continue;
        };
        if !is_supported_seed_writeback_assign(writeback, seed, carried)
            || stmts[..index]
                .iter()
                .any(|stmt| stmt_mentions_binding(stmt, carried))
            || stmts[(index + 2)..]
                .iter()
                .any(|stmt| stmt_mentions_binding(stmt, carried))
            || !if_branches_end_with_carried_assign(if_stmt, carried)
        {
            continue;
        }
        return true;
    }
    false
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
    let Some((last, prefix)) = block.stmts.split_last() else {
        return false;
    };
    prefix
        .iter()
        .all(|stmt| !stmt_mentions_binding(stmt, carried))
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

fn seed_can_absorb_carried(stmts: &[AstStmt], seed: AstBindingRef, carried: AstBindingRef) -> bool {
    stmts
        .iter()
        .all(|stmt| stmt_allows_seed_to_absorb_carried(stmt, seed, carried))
}

fn stmt_allows_seed_to_absorb_carried(
    stmt: &AstStmt,
    seed: AstBindingRef,
    carried: AstBindingRef,
) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            local_decl
                .bindings
                .iter()
                .all(|binding| binding.id != seed && binding.id != carried)
                && local_decl
                    .values
                    .iter()
                    .all(|value| !expr_references_binding(value, seed))
        }
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .all(|value| !expr_references_binding(value, seed)),
        AstStmt::Assign(assign) => {
            if is_exact_seed_copy_assign(assign, carried, seed)
                || is_supported_seed_writeback_assign(assign, seed, carried)
            {
                true
            } else {
                !assign_targets_binding(assign, seed)
                    && assign
                        .targets
                        .iter()
                        .all(|target| !lvalue_references_binding(target, seed))
                    && assign
                        .values
                        .iter()
                        .all(|value| !expr_references_binding(value, seed))
            }
        }
        AstStmt::CallStmt(call_stmt) => !call_references_binding(&call_stmt.call, seed),
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .all(|value| !expr_references_binding(value, seed)),
        AstStmt::If(if_stmt) => {
            !expr_references_binding(&if_stmt.cond, seed)
                && seed_can_absorb_carried(&if_stmt.then_block.stmts, seed, carried)
                && if_stmt
                    .else_block
                    .as_ref()
                    .is_none_or(|block| seed_can_absorb_carried(&block.stmts, seed, carried))
        }
        AstStmt::While(while_stmt) => {
            !expr_references_binding(&while_stmt.cond, seed)
                && seed_can_absorb_carried(&while_stmt.body.stmts, seed, carried)
        }
        AstStmt::Repeat(repeat_stmt) => {
            seed_can_absorb_carried(&repeat_stmt.body.stmts, seed, carried)
                && !expr_references_binding(&repeat_stmt.cond, seed)
        }
        AstStmt::NumericFor(numeric_for) => {
            numeric_for.binding != seed
                && numeric_for.binding != carried
                && !expr_references_binding(&numeric_for.start, seed)
                && !expr_references_binding(&numeric_for.limit, seed)
                && !expr_references_binding(&numeric_for.step, seed)
                && seed_can_absorb_carried(&numeric_for.body.stmts, seed, carried)
        }
        AstStmt::GenericFor(generic_for) => {
            !generic_for
                .bindings
                .iter()
                .any(|binding| *binding == seed || *binding == carried)
                && generic_for
                    .iterator
                    .iter()
                    .all(|expr| !expr_references_binding(expr, seed))
                && seed_can_absorb_carried(&generic_for.body.stmts, seed, carried)
        }
        AstStmt::DoBlock(block) => seed_can_absorb_carried(&block.stmts, seed, carried),
        AstStmt::FunctionDecl(function_decl) => {
            !function_name_references_binding(&function_decl.target, seed)
        }
        AstStmt::LocalFunctionDecl(function_decl) => function_decl.name != seed,
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => true,
    }
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

fn stmt_mentions_binding(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .any(|value| expr_references_binding(value, binding)),
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .any(|value| expr_references_binding(value, binding)),
        AstStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .any(|target| lvalue_references_binding(target, binding))
                || assign
                    .values
                    .iter()
                    .any(|value| expr_references_binding(value, binding))
        }
        AstStmt::CallStmt(call_stmt) => call_references_binding(&call_stmt.call, binding),
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .any(|value| expr_references_binding(value, binding)),
        AstStmt::If(if_stmt) => {
            expr_references_binding(&if_stmt.cond, binding)
                || if_stmt
                    .then_block
                    .stmts
                    .iter()
                    .any(|stmt| stmt_mentions_binding(stmt, binding))
                || if_stmt.else_block.as_ref().is_some_and(|block| {
                    block
                        .stmts
                        .iter()
                        .any(|stmt| stmt_mentions_binding(stmt, binding))
                })
        }
        AstStmt::While(while_stmt) => {
            expr_references_binding(&while_stmt.cond, binding)
                || while_stmt
                    .body
                    .stmts
                    .iter()
                    .any(|stmt| stmt_mentions_binding(stmt, binding))
        }
        AstStmt::Repeat(repeat_stmt) => {
            repeat_stmt
                .body
                .stmts
                .iter()
                .any(|stmt| stmt_mentions_binding(stmt, binding))
                || expr_references_binding(&repeat_stmt.cond, binding)
        }
        AstStmt::NumericFor(numeric_for) => {
            expr_references_binding(&numeric_for.start, binding)
                || expr_references_binding(&numeric_for.limit, binding)
                || expr_references_binding(&numeric_for.step, binding)
                || numeric_for
                    .body
                    .stmts
                    .iter()
                    .any(|stmt| stmt_mentions_binding(stmt, binding))
        }
        AstStmt::GenericFor(generic_for) => {
            generic_for
                .iterator
                .iter()
                .any(|expr| expr_references_binding(expr, binding))
                || generic_for
                    .body
                    .stmts
                    .iter()
                    .any(|stmt| stmt_mentions_binding(stmt, binding))
        }
        AstStmt::DoBlock(block) => block
            .stmts
            .iter()
            .any(|stmt| stmt_mentions_binding(stmt, binding)),
        AstStmt::FunctionDecl(_) | AstStmt::LocalFunctionDecl(_) => false,
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => false,
    }
}

fn assign_targets_binding(assign: &AstAssign, binding: AstBindingRef) -> bool {
    assign.targets.iter().any(|target| match target {
        AstLValue::Name(name) => name_matches_binding(name, binding),
        AstLValue::FieldAccess(_) | AstLValue::IndexAccess(_) => false,
    })
}

fn function_name_references_binding(
    target: &super::super::common::AstFunctionName,
    binding: AstBindingRef,
) -> bool {
    let path = match target {
        super::super::common::AstFunctionName::Plain(path) => path,
        super::super::common::AstFunctionName::Method(path, _) => path,
    };
    name_matches_binding(&path.root, binding)
}

#[cfg(test)]
mod tests;
