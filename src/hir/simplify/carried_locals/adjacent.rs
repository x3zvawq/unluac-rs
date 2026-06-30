//! 相邻 seed/carried local handoff 收敛。
//!
//! 这个规则只处理结构化后暴露出的窄形状：
//! `local state = init; local next; ... next = state ...`。主模块负责调度不同
//! handoff owner；这里只在 seed 不再可观察、carried 没有闭包捕获、且后续写回形状
//! 明确时，把 carried 的使用点认回 seed。

use std::collections::BTreeMap;

use crate::hir::common::{HirAssign, HirBlock, HirCallExpr, HirExpr, HirLValue, HirStmt, LocalId};

use super::super::local_shapes::{
    empty_single_local_decl_binding, initialized_single_local_decl_binding,
};
use super::super::mention::{expr_mentions_local, stmt_captures_local, stmts_mention_local};
use super::super::walk::rewrite_stmts;
use super::binding::{BindingClassRewritePass, CarryBinding};
use super::prune::{
    collect_prunable_bindings, prune_empty_assign_stmts, prune_redundant_self_assigns_in_stmts,
};

pub(super) fn try_collapse_adjacent_local_seed_handoff(block: &mut HirBlock, index: usize) -> bool {
    let Some(seed) = initialized_single_local_decl_binding(&block.stmts[index]) else {
        return false;
    };
    let Some(carried) = block
        .stmts
        .get(index + 1)
        .and_then(empty_single_local_decl_binding)
    else {
        return false;
    };

    let tail = &block.stmts[index + 2..];
    if tail.is_empty()
        || !stmts_mention_local(tail, carried)
        || tail.iter().any(|stmt| {
            stmt_captures_local(stmt, seed)
                || stmt_captures_local(stmt, carried)
                || !stmt_allows_seed_to_absorb_carried(stmt, seed, carried)
        })
    {
        return false;
    }

    let mut tail = block.stmts.split_off(index + 2);
    rewrite_carried_local_in_stmts(&mut tail, carried, seed);
    block.stmts.append(&mut tail);
    block.stmts.remove(index + 1);
    prune_empty_assign_stmts(block);
    true
}

fn rewrite_carried_local_in_stmts(stmts: &mut [HirStmt], carried: LocalId, seed: LocalId) {
    let mut rewrites = BTreeMap::new();
    rewrites.insert(CarryBinding::Local(carried), CarryBinding::Local(seed));
    let mut pass = BindingClassRewritePass { rewrites };
    rewrite_stmts(stmts, &mut pass);
    prune_redundant_self_assigns_in_stmts(
        stmts,
        collect_prunable_bindings([CarryBinding::Local(seed)]),
    );
}

fn stmt_allows_seed_to_absorb_carried(stmt: &HirStmt, seed: LocalId, carried: LocalId) -> bool {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            local_decl
                .bindings
                .iter()
                .all(|binding| *binding != seed && *binding != carried)
                && local_decl
                    .values
                    .iter()
                    .all(|value| !expr_mentions_local(value, seed))
        }
        HirStmt::Assign(assign) => {
            if is_exact_local_copy_assign(assign, carried, seed)
                || is_supported_local_writeback_assign(assign, seed, carried)
            {
                true
            } else {
                !assign_targets_local(assign, seed)
                    && assign
                        .targets
                        .iter()
                        .all(|target| !lvalue_mentions_local(target, seed))
                    && assign
                        .values
                        .iter()
                        .all(|value| !expr_mentions_local(value, seed))
            }
        }
        HirStmt::TableSetList(set_list) => {
            !expr_mentions_local(&set_list.base, seed)
                && set_list
                    .values
                    .iter()
                    .all(|value| !expr_mentions_local(value, seed))
                && set_list
                    .trailing_multivalue
                    .as_ref()
                    .is_none_or(|value| !expr_mentions_local(value, seed))
        }
        HirStmt::ErrNil(err_nil) => !expr_mentions_local(&err_nil.value, seed),
        HirStmt::ToBeClosed(to_be_closed) => !expr_mentions_local(&to_be_closed.value, seed),
        HirStmt::CallStmt(call_stmt) => !call_mentions_local(&call_stmt.call, seed),
        HirStmt::Return(ret) => ret
            .values
            .iter()
            .all(|value| !expr_mentions_local(value, seed)),
        HirStmt::If(if_stmt) => {
            !expr_mentions_local(&if_stmt.cond, seed)
                && stmts_allow_seed_to_absorb_carried(&if_stmt.then_block.stmts, seed, carried)
                && if_stmt.else_block.as_ref().is_none_or(|else_block| {
                    stmts_allow_seed_to_absorb_carried(&else_block.stmts, seed, carried)
                })
        }
        HirStmt::While(while_stmt) => {
            !expr_mentions_local(&while_stmt.cond, seed)
                && stmts_allow_seed_to_absorb_carried(&while_stmt.body.stmts, seed, carried)
        }
        HirStmt::Repeat(repeat_stmt) => {
            stmts_allow_seed_to_absorb_carried(&repeat_stmt.body.stmts, seed, carried)
                && !expr_mentions_local(&repeat_stmt.cond, seed)
        }
        HirStmt::NumericFor(numeric_for) => {
            numeric_for.binding != seed
                && numeric_for.binding != carried
                && !expr_mentions_local(&numeric_for.start, seed)
                && !expr_mentions_local(&numeric_for.limit, seed)
                && !expr_mentions_local(&numeric_for.step, seed)
                && stmts_allow_seed_to_absorb_carried(&numeric_for.body.stmts, seed, carried)
        }
        HirStmt::GenericFor(generic_for) => {
            !generic_for
                .bindings
                .iter()
                .any(|binding| *binding == seed || *binding == carried)
                && generic_for
                    .iterator
                    .iter()
                    .all(|value| !expr_mentions_local(value, seed))
                && stmts_allow_seed_to_absorb_carried(&generic_for.body.stmts, seed, carried)
        }
        HirStmt::Block(block) => stmts_allow_seed_to_absorb_carried(&block.stmts, seed, carried),
        HirStmt::Unstructured(unstructured) => {
            stmts_allow_seed_to_absorb_carried(&unstructured.body.stmts, seed, carried)
        }
        HirStmt::Close(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => true,
    }
}

fn stmts_allow_seed_to_absorb_carried(stmts: &[HirStmt], seed: LocalId, carried: LocalId) -> bool {
    stmts
        .iter()
        .all(|stmt| stmt_allows_seed_to_absorb_carried(stmt, seed, carried))
}

fn is_exact_local_copy_assign(assign: &HirAssign, carried: LocalId, seed: LocalId) -> bool {
    let [HirLValue::Local(target)] = assign.targets.as_slice() else {
        return false;
    };
    let [HirExpr::LocalRef(value)] = assign.values.as_slice() else {
        return false;
    };
    *target == carried && *value == seed
}

fn is_supported_local_writeback_assign(
    assign: &HirAssign,
    seed: LocalId,
    carried: LocalId,
) -> bool {
    if assign.targets.len() != assign.values.len() || assign.targets.is_empty() {
        return false;
    }

    let mut saw_writeback = false;
    for (target, value) in assign.targets.iter().zip(&assign.values) {
        let is_writeback = matches!(
            (target, value),
            (HirLValue::Local(target), HirExpr::LocalRef(value))
                if *target == seed && *value == carried
        );
        if is_writeback {
            saw_writeback = true;
            continue;
        }
        if lvalue_mentions_local(target, seed) || expr_mentions_local(value, seed) {
            return false;
        }
    }

    saw_writeback
}

fn assign_targets_local(assign: &HirAssign, local: LocalId) -> bool {
    assign
        .targets
        .iter()
        .any(|target| matches!(target, HirLValue::Local(target) if *target == local))
}

fn lvalue_mentions_local(lvalue: &HirLValue, local: LocalId) -> bool {
    match lvalue {
        HirLValue::Local(target) => *target == local,
        HirLValue::TableAccess(access) => {
            expr_mentions_local(&access.base, local) || expr_mentions_local(&access.key, local)
        }
        HirLValue::Param(_) | HirLValue::Temp(_) | HirLValue::Upvalue(_) | HirLValue::Global(_) => {
            false
        }
    }
}

fn call_mentions_local(call: &HirCallExpr, local: LocalId) -> bool {
    expr_mentions_local(&call.callee, local)
        || call.args.iter().any(|arg| expr_mentions_local(arg, local))
}
