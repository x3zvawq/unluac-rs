//! 循环内 `next -> carried` 写回的窄化折叠。
//!
//! 结构计划会保留 SSA 中“本轮新值”和“下轮 carried 值”的独立身份。局部提升后，
//! 若循环中途 `break`/`return`，这种身份边界通常表现为
//! `local next = f(carried)`，并在循环尾写回 `carried = next`。当 local 身份在循环外
//! 已死时可以直接复用 carried；repeat 的 next-value 若只是唯一的尾部 temp，则还可在
//! 所有路径必经写回、后缀无状态改写与词法跳转的前提下，把条件和 live-out 一并归回
//! carried。两种折叠都不跨越 capture、提前退出或 label barrier。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirAssign, HirBlock, HirExpr, HirLValue, HirStmt, LocalId, TempId};

use super::super::mention::{stmts_captured_locals, stmts_mention_local};
use super::super::visit::{HirVisitor, visit_stmts};
use super::super::walk::{rewrite_expr, rewrite_stmts};
use super::binding::{BindingClassRewritePass, CarryBinding, carry_binding_from_lvalue};
use super::prune::RedundantSelfAssignPrunePass;
use super::reads::BindingReadCollector;

#[derive(Clone, Copy)]
struct LoopUpdateFold {
    seed_index: usize,
    carried: LocalId,
    next: LocalId,
}

pub(super) fn collapse_dead_loop_update_handoffs(
    block: &mut HirBlock,
    stmt_mentions: &[BTreeSet<CarryBinding>],
) -> bool {
    let captured_locals = stmts_captured_locals(&block.stmts);
    if collapse_repeat_tail_temp_updates(block, stmt_mentions, &captured_locals) {
        return true;
    }

    let last_mentions = last_local_mentions(stmt_mentions);
    let mut changed = false;

    for index in 0..block.stmts.len() {
        let Some(fold) = find_fold(&block.stmts[index], index, &last_mentions, &captured_locals)
        else {
            continue;
        };
        apply_fold(&mut block.stmts[index], fold);
        changed = true;
    }

    changed
}

fn collapse_repeat_tail_temp_updates(
    block: &mut HirBlock,
    stmt_mentions: &[BTreeSet<CarryBinding>],
    captured_locals: &BTreeSet<LocalId>,
) -> bool {
    let mut first_mentions = BTreeMap::new();
    let mut last_mentions = BTreeMap::new();
    for (index, mentions) in stmt_mentions.iter().enumerate() {
        for binding in mentions {
            first_mentions.entry(*binding).or_insert(index);
            last_mentions.insert(*binding, index);
        }
    }
    let writes = collect_top_level_write_facts(&block.stmts);
    let mut control_prefix = Vec::with_capacity(block.stmts.len() + 1);
    control_prefix.push(0usize);
    for stmt in &block.stmts {
        control_prefix.push(
            control_prefix.last().copied().unwrap_or_default()
                + usize::from(stmt_has_label_or_goto(stmt)),
        );
    }

    let mut rewrites = BTreeMap::new();
    let mut carried = BTreeSet::new();
    for (index, stmt) in block.stmts.iter().enumerate() {
        let HirStmt::Repeat(repeat_stmt) = stmt else {
            continue;
        };
        let Some((next, state, value, prefix)) = repeat_tail_temp_update(&repeat_stmt.body) else {
            continue;
        };
        let next_binding = CarryBinding::Temp(next);
        let state_binding = CarryBinding::Local(state);
        let mut reads = BindingReadCollector::default();
        reads.collect_expr(value);
        let last_next_mention = last_mentions.get(&next_binding).copied().unwrap_or(index);
        if reads.single_read() != Some(state_binding)
            || captured_locals.contains(&state)
            || first_mentions.get(&next_binding).copied() != Some(index)
            || writes.counts.get(&next_binding).copied() != Some(1)
            || writes.last_stmt.get(&state_binding).copied() != Some(index)
            || !super::reads::collect_binding_mentions_in_expr(&repeat_stmt.cond)
                .contains(&next_binding)
            || prefix.iter().any(stmt_has_early_control)
            || prefix
                .iter()
                .any(|stmt| stmt_writes_binding(stmt, state_binding))
            || super::reads::collect_binding_mentions_by_stmt(prefix)
                .iter()
                .any(|mentions| mentions.contains(&next_binding))
            || control_prefix[last_next_mention + 1] != control_prefix[index]
            || rewrites.insert(next_binding, state_binding).is_some()
        {
            continue;
        }
        carried.insert(state_binding);
    }
    if rewrites.is_empty() {
        return false;
    }

    rewrite_stmts(&mut block.stmts, &mut BindingClassRewritePass { rewrites });
    rewrite_stmts(
        &mut block.stmts,
        &mut RedundantSelfAssignPrunePass::for_bindings(carried),
    );
    true
}

fn repeat_tail_temp_update(body: &HirBlock) -> Option<(TempId, LocalId, &HirExpr, &[HirStmt])> {
    let [
        prefix @ ..,
        HirStmt::Assign(seed),
        HirStmt::Assign(writeback),
    ] = body.stmts.as_slice()
    else {
        return None;
    };
    let [HirLValue::Temp(next)] = seed.targets.as_slice() else {
        return None;
    };
    let [value] = seed.values.fixed.as_slice() else {
        return None;
    };
    let [HirLValue::Local(state)] = writeback.targets.as_slice() else {
        return None;
    };
    let [HirExpr::TempRef(source)] = writeback.values.fixed.as_slice() else {
        return None;
    };
    (seed.values.tail.is_none() && writeback.values.tail.is_none() && next == source)
        .then_some((*next, *state, value, prefix))
}

#[derive(Default)]
struct TopLevelWriteFacts {
    counts: BTreeMap<CarryBinding, usize>,
    last_stmt: BTreeMap<CarryBinding, usize>,
}

fn collect_top_level_write_facts(stmts: &[HirStmt]) -> TopLevelWriteFacts {
    let mut facts = TopLevelWriteFacts::default();
    for (index, stmt) in stmts.iter().enumerate() {
        let mut writes = BindingWriteCollector::default();
        visit_stmts(std::slice::from_ref(stmt), &mut writes);
        for (binding, count) in writes.counts {
            *facts.counts.entry(binding).or_default() += count;
            facts.last_stmt.insert(binding, index);
        }
    }
    facts
}

#[derive(Default)]
struct BindingWriteCollector {
    counts: BTreeMap<CarryBinding, usize>,
}

impl HirVisitor for BindingWriteCollector {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let Some(binding) = carry_binding_from_lvalue(lvalue) {
            *self.counts.entry(binding).or_default() += 1;
        }
    }
}

fn stmt_writes_binding(stmt: &HirStmt, binding: CarryBinding) -> bool {
    let mut writes = BindingWriteCollector::default();
    visit_stmts(std::slice::from_ref(stmt), &mut writes);
    writes.counts.contains_key(&binding)
}

fn stmt_has_early_control(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_) => true,
        HirStmt::If(if_stmt) => {
            if_stmt.then_block.stmts.iter().any(stmt_has_early_control)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| block.stmts.iter().any(stmt_has_early_control))
        }
        HirStmt::Block(block) => block.stmts.iter().any(stmt_has_early_control),
        _ => false,
    }
}

fn stmt_has_label_or_goto(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::Goto(_) | HirStmt::Label(_) => true,
        HirStmt::If(if_stmt) => {
            if_stmt.then_block.stmts.iter().any(stmt_has_label_or_goto)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| block.stmts.iter().any(stmt_has_label_or_goto))
        }
        HirStmt::While(while_stmt) => while_stmt.body.stmts.iter().any(stmt_has_label_or_goto),
        HirStmt::Repeat(repeat_stmt) => repeat_stmt.body.stmts.iter().any(stmt_has_label_or_goto),
        HirStmt::NumericFor(numeric_for) => {
            numeric_for.body.stmts.iter().any(stmt_has_label_or_goto)
        }
        HirStmt::GenericFor(generic_for) => {
            generic_for.body.stmts.iter().any(stmt_has_label_or_goto)
        }
        HirStmt::Block(block) => block.stmts.iter().any(stmt_has_label_or_goto),
        _ => false,
    }
}

fn last_local_mentions(stmt_mentions: &[BTreeSet<CarryBinding>]) -> BTreeMap<LocalId, usize> {
    let mut last_mentions = BTreeMap::new();
    for (index, mentions) in stmt_mentions.iter().enumerate() {
        for binding in mentions {
            if let CarryBinding::Local(local) = binding {
                last_mentions.insert(*local, index);
            }
        }
    }
    last_mentions
}

fn find_fold(
    stmt: &HirStmt,
    stmt_index: usize,
    last_mentions: &BTreeMap<LocalId, usize>,
    captured_locals: &BTreeSet<LocalId>,
) -> Option<LoopUpdateFold> {
    let body = loop_body(stmt)?;
    let (writeback, prefix) = body.stmts.split_last()?;
    let (carried, next) = exact_local_writeback(writeback)?;
    if carried == next
        || last_mentions.get(&carried).copied() != Some(stmt_index)
        || last_mentions.get(&next).copied() != Some(stmt_index)
        || captured_locals.contains(&carried)
        || captured_locals.contains(&next)
        || !stmts_allow_dead_update_fold(prefix)
    {
        return None;
    }

    for (seed_index, seed) in prefix.iter().enumerate() {
        let Some((seed_binding, value)) = initialized_local(seed) else {
            continue;
        };
        if seed_binding != next
            || stmts_mention_local(&prefix[..seed_index], next)
            || stmts_mention_local(&prefix[seed_index + 1..], carried)
            || !stmts_contain_terminal_exit(&prefix[seed_index + 1..])
        {
            continue;
        }
        let mut reads = BindingReadCollector::default();
        reads.collect_expr(value);
        if reads.single_read() == Some(CarryBinding::Local(carried)) {
            return Some(LoopUpdateFold {
                seed_index,
                carried,
                next,
            });
        }
    }
    None
}

fn loop_body(stmt: &HirStmt) -> Option<&HirBlock> {
    match stmt {
        HirStmt::While(while_stmt) => Some(&while_stmt.body),
        HirStmt::Repeat(repeat_stmt) => Some(&repeat_stmt.body),
        _ => None,
    }
}

fn loop_body_mut(stmt: &mut HirStmt) -> Option<(&mut HirBlock, Option<&mut HirExpr>)> {
    match stmt {
        HirStmt::While(while_stmt) => Some((&mut while_stmt.body, None)),
        HirStmt::Repeat(repeat_stmt) => Some((&mut repeat_stmt.body, Some(&mut repeat_stmt.cond))),
        _ => None,
    }
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

fn exact_local_writeback(stmt: &HirStmt) -> Option<(LocalId, LocalId)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Local(target)] = assign.targets.as_slice() else {
        return None;
    };
    let [HirExpr::LocalRef(value)] = assign.values.fixed.as_slice() else {
        return None;
    };
    assign.values.tail.is_none().then_some((*target, *value))
}

fn stmts_allow_dead_update_fold(stmts: &[HirStmt]) -> bool {
    stmts.iter().all(stmt_allows_dead_update_fold)
}

fn stmt_allows_dead_update_fold(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::If(if_stmt) => {
            stmts_allow_dead_update_fold(&if_stmt.then_block.stmts)
                && if_stmt
                    .else_block
                    .as_ref()
                    .is_none_or(|block| stmts_allow_dead_update_fold(&block.stmts))
        }
        HirStmt::Block(block) => stmts_allow_dead_update_fold(&block.stmts),
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break => true,
        HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn stmts_contain_terminal_exit(stmts: &[HirStmt]) -> bool {
    stmts.iter().any(stmt_contains_terminal_exit)
}

fn stmt_contains_terminal_exit(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::Break | HirStmt::Return(_) => true,
        HirStmt::If(if_stmt) => {
            stmts_contain_terminal_exit(&if_stmt.then_block.stmts)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| stmts_contain_terminal_exit(&block.stmts))
        }
        HirStmt::Block(block) => stmts_contain_terminal_exit(&block.stmts),
        _ => false,
    }
}

fn apply_fold(stmt: &mut HirStmt, fold: LoopUpdateFold) {
    let Some((body, repeat_cond)) = loop_body_mut(stmt) else {
        return;
    };
    let values = match &mut body.stmts[fold.seed_index] {
        HirStmt::LocalDecl(local_decl) => std::mem::take(&mut local_decl.values),
        _ => return,
    };
    body.stmts[fold.seed_index] = HirStmt::Assign(Box::new(HirAssign {
        targets: vec![HirLValue::Local(fold.carried)],
        values,
    }));
    body.stmts.pop();

    let mut rewrites = BTreeMap::new();
    rewrites.insert(
        CarryBinding::Local(fold.next),
        CarryBinding::Local(fold.carried),
    );
    let mut pass = BindingClassRewritePass { rewrites };
    rewrite_stmts(&mut body.stmts[fold.seed_index + 1..], &mut pass);
    if let Some(cond) = repeat_cond {
        rewrite_expr(cond, &mut pass);
    }
}
