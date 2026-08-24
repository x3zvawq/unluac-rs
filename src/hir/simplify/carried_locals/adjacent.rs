//! 相邻 seed/carried local handoff 收敛。
//!
//! 这个规则只处理结构化后暴露出的窄形状：
//! `local state = init; local next; ... next = state ...`。主模块负责调度不同
//! handoff owner；这里只在 seed 不再可观察、carried 没有闭包捕获、且后续写回形状
//! 明确时，把 carried 的使用点认回 seed。相邻 owner 只接受单目标 `carried = seed`
//! 复制；`seed = carried` 尤其是多目标并行写回会保守保留两个 binding。
//! capture/TBC direct 身份及 raw-home may-alias 由父模块统一保护，不在这里改写资源 cell。

use std::collections::BTreeMap;

use crate::hir::common::{HirAssign, HirBlock, HirCallExpr, HirExpr, HirLValue, HirStmt, LocalId};
use crate::hir::promotion::ProtoPromotionFacts;

use super::super::local_shapes::{
    empty_single_local_decl_binding, initialized_single_local_decl_binding,
};
use super::super::mention::{expr_mentions_local, stmt_captures_local, stmts_mention_local};
use super::super::walk::rewrite_stmts;
use super::HandoffIdentityFacts;
use super::binding::{
    BindingClassRewritePass, BindingProtection, CarryBinding, bindings_share_exact_home_slot,
};
use super::prune::{
    collect_prunable_bindings, prune_empty_assign_stmts, prune_redundant_self_assigns_in_stmts,
};
use super::reads::{collect_binding_mentions_by_stmt, collect_binding_mentions_in_expr};

pub(super) fn try_collapse_guarded_local_update(
    block: &mut HirBlock,
    index: usize,
    outer_bindings: &dyn BindingProtection,
    captured_bindings: &std::collections::BTreeSet<CarryBinding>,
    promotion_facts: &mut ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
) -> bool {
    let Some((next, value)) = block.stmts.get(index).and_then(initialized_local) else {
        return false;
    };
    let next_binding = CarryBinding::Local(next);
    let Some(HirStmt::If(if_stmt)) = block.stmts.get(index + 1) else {
        return false;
    };
    if if_stmt.cond != HirExpr::LocalRef(next) {
        return false;
    }
    let Some(state) = exact_binding_copy(&if_stmt.then_block.stmts, next) else {
        return false;
    };
    if !matches!(state, CarryBinding::Param(_) | CarryBinding::Local(_))
        || state == next_binding
        || matches!(state, CarryBinding::Local(_)) && outer_bindings.contains(&state)
        || captured_bindings.contains(&state)
        || captured_bindings.contains(&next_binding)
        || !identity_facts.binding_merge_preserves_identity(next_binding, state, promotion_facts)
        || collect_binding_mentions_in_expr(value).contains(&next_binding)
    {
        return false;
    }
    let Some(else_block) = if_stmt.else_block.as_ref() else {
        return false;
    };
    if !matches!(else_block.stmts.as_slice(), [HirStmt::Return(_)])
        || collect_binding_mentions_by_stmt(&else_block.stmts)[0]
            .iter()
            .any(|binding| *binding == state || *binding == next_binding)
        || collect_binding_mentions_by_stmt(&block.stmts[index + 2..])
            .iter()
            .any(|mentions| mentions.contains(&next_binding))
    {
        return false;
    }

    let values = match &mut block.stmts[index] {
        HirStmt::LocalDecl(local_decl) => std::mem::take(&mut local_decl.values),
        _ => return false,
    };
    block.stmts[index] = HirStmt::Assign(Box::new(HirAssign {
        targets: vec![binding_lvalue(state)],
        values,
    }));

    let mut rewrites = BTreeMap::new();
    rewrites.insert(next_binding, state);
    rewrite_stmts(
        &mut block.stmts[index + 1..index + 2],
        &mut BindingClassRewritePass {
            rewrites,
            promotion_facts,
        },
    );
    prune_redundant_self_assigns_in_stmts(
        &mut block.stmts[index + 1..index + 2],
        collect_prunable_bindings([state]),
    );
    true
}

pub(super) fn try_collapse_adjacent_local_seed_handoff(
    block: &mut HirBlock,
    index: usize,
    promotion_facts: &mut ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
) -> bool {
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
    if promotion_facts.compacts_home_slots()
        || !bindings_share_exact_home_slot(
            CarryBinding::Local(carried),
            CarryBinding::Local(seed),
            promotion_facts,
        )
        || !identity_facts.binding_merge_preserves_identity(
            CarryBinding::Local(carried),
            CarryBinding::Local(seed),
            promotion_facts,
        )
        || tail.is_empty()
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
    rewrite_carried_local_in_stmts(&mut tail, carried, seed, promotion_facts);
    block.stmts.append(&mut tail);
    block.stmts.remove(index + 1);
    prune_empty_assign_stmts(block);
    true
}

fn rewrite_carried_local_in_stmts(
    stmts: &mut [HirStmt],
    carried: LocalId,
    seed: LocalId,
    promotion_facts: &mut ProtoPromotionFacts,
) {
    let mut rewrites = BTreeMap::new();
    rewrites.insert(CarryBinding::Local(carried), CarryBinding::Local(seed));
    let mut pass = BindingClassRewritePass {
        rewrites,
        promotion_facts,
    };
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
            if is_exact_local_copy_assign(assign, carried, seed) {
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
    let [HirExpr::LocalRef(value)] = assign.values.fixed.as_slice() else {
        return false;
    };
    if assign.values.tail.is_some() {
        return false;
    }
    *target == carried && *value == seed
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

fn initialized_local(stmt: &HirStmt) -> Option<(LocalId, &HirExpr)> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [value] = local_decl.values.fixed.as_slice() else {
        return None;
    };
    local_decl
        .values
        .tail
        .is_none()
        .then_some((*binding, value))
}

fn exact_binding_copy(stmts: &[HirStmt], value: LocalId) -> Option<CarryBinding> {
    let [HirStmt::Assign(assign)] = stmts else {
        return None;
    };
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [HirExpr::LocalRef(source)] = assign.values.fixed.as_slice() else {
        return None;
    };
    (assign.values.tail.is_none() && *source == value)
        .then(|| super::binding::carry_binding_from_lvalue(target))
        .flatten()
}

fn binding_lvalue(binding: CarryBinding) -> HirLValue {
    match binding {
        CarryBinding::Param(param) => HirLValue::Param(param),
        CarryBinding::Local(local) => HirLValue::Local(local),
        CarryBinding::Temp(temp) => HirLValue::Temp(temp),
    }
}
