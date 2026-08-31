//! 收回 repeat 尾部只为承接最终状态而生成的临时快照。
//!
//! 只处理一条可证明的局部形状：body 末尾先计算 `temp = repeatable(local)`，紧接着
//! `local = temp`，循环后的唯一消费者是 `return temp`。中间没有 break/continue/goto，
//! 因而把第一条赋值直接改成 `local = repeatable(local)` 不会改变任何可观察求值点；
//! 捕获、`<close>` 和 debug temp 也会阻断该规则。

use std::collections::{BTreeMap, BTreeSet};

use super::super::mention::{
    collect_temp_use_counts, collect_temp_write_counts, stmts_protected_locals,
    stmts_reference_captured_bindings, stmts_to_be_closed_temps, stmts_value_captured_bindings,
};
use super::super::temp_touch::collect_temp_refs_in_expr;
use super::super::walk::for_each_nested_block_mut;
use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirLValue, HirProto, HirStmt, LocalId, TempId,
};

pub(super) fn coalesce_repeat_terminal_snapshots(proto: &mut HirProto) -> bool {
    let use_counts = collect_temp_use_counts(proto);
    let reference_captured = stmts_reference_captured_bindings(&proto.body.stmts);
    let value_captured = stmts_value_captured_bindings(&proto.body.stmts);
    let mut captured_locals = reference_captured.locals;
    captured_locals.extend(value_captured.locals);
    let mut captured_temps = reference_captured.temps;
    captured_temps.extend(value_captured.temps);
    let closed_temps = stmts_to_be_closed_temps(&proto.body.stmts);
    let protected_locals = stmts_protected_locals(&proto.body.stmts);
    let write_counts = collect_temp_write_counts(proto);
    let facts = RepeatSnapshotFacts {
        use_counts: &use_counts,
        captured_locals: &captured_locals,
        protected_locals: &protected_locals,
        captured_temps: &captured_temps,
        closed_temps: &closed_temps,
        write_counts: &write_counts,
        debug_temps: &proto.temp_debug_locals,
    };
    rewrite_block(&mut proto.body, &facts)
}

struct RepeatSnapshotFacts<'a> {
    use_counts: &'a BTreeMap<TempId, usize>,
    captured_locals: &'a BTreeSet<LocalId>,
    protected_locals: &'a BTreeSet<LocalId>,
    captured_temps: &'a BTreeSet<TempId>,
    closed_temps: &'a BTreeSet<TempId>,
    write_counts: &'a BTreeMap<TempId, usize>,
    debug_temps: &'a [Option<String>],
}

fn rewrite_block(block: &mut HirBlock, facts: &RepeatSnapshotFacts<'_>) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        for_each_nested_block_mut(stmt, &mut |nested| {
            changed |= rewrite_block(nested, facts);
        });
    }

    let mut index = 0;
    while index + 1 < block.stmts.len() {
        let Some(return_temp) = immediate_return_temp(&block.stmts[index + 1]) else {
            index += 1;
            continue;
        };
        let HirStmt::Repeat(repeat) = &mut block.stmts[index] else {
            index += 1;
            continue;
        };
        let Some(local) = try_rewrite_repeat(repeat, return_temp, facts) else {
            index += 1;
            continue;
        };
        if let HirStmt::Return(ret) = &mut block.stmts[index + 1] {
            ret.values.fixed[0] = HirExpr::LocalRef(local);
            changed = true;
        }
        index += 1;
    }
    changed
}

fn immediate_return_temp(stmt: &HirStmt) -> Option<TempId> {
    let HirStmt::Return(ret) = stmt else {
        return None;
    };
    if ret.values.tail.is_some() || ret.values.fixed.len() != 1 {
        return None;
    }
    match &ret.values.fixed[0] {
        HirExpr::TempRef(temp) => Some(*temp),
        _ => None,
    }
}

fn try_rewrite_repeat(
    repeat: &mut crate::hir::common::HirRepeat,
    return_temp: TempId,
    facts: &RepeatSnapshotFacts<'_>,
) -> Option<LocalId> {
    // 候选拒绝[SemanticBarrier:ControlFlow]：break/continue/return/goto 可绕过尾 copy；删除 temp 会改变对应出口的 live-out。
    // 候选拒绝[ProofIncomplete]：嵌套 loop 被同一 control 检查 blanket 拒绝；需区分内层自有 transfer 并证明其写集合。
    // 候选拒绝[SemanticBarrier:Capture]：捕获 return temp 时，删除其唯一写会让 closure 观察旧值。
    // 候选拒绝[SemanticBarrier:Lifetime]：TBC temp 或非唯一 use/write 仍有额外 epoch/close 观察者。
    // 候选拒绝[LayerBoundary]：debug temp 的源码身份由 locals owner 保留。
    if repeat.body.stmts.len() < 2
        || stmt_contains_loop_exit(&repeat.body)
        || facts.captured_temps.contains(&return_temp)
        || facts.closed_temps.contains(&return_temp)
        || facts
            .debug_temps
            .get(return_temp.index())
            .is_some_and(Option::is_some)
        || facts.use_counts.get(&return_temp).copied() != Some(2)
        || facts.write_counts.get(&return_temp).copied() != Some(1)
    {
        return None;
    }
    let copy_index = repeat.body.stmts.len() - 1;
    let producer_index = copy_index - 1;
    let (temp, value) = match &repeat.body.stmts[producer_index] {
        HirStmt::Assign(assign) => match assign_shape(assign) {
            Some((HirLValue::Temp(temp), value)) => (*temp, value.clone()),
            _ => return None,
        },
        _ => return None,
    };
    // 候选拒绝[ProofIncomplete]：producer 自读 temp 已被全局 use-count 间接排除；应由统一 def-use epoch 证明取代重复形状门。
    if temp != return_temp
        || value_mentions_temp(&value, temp)
        || !matches!(
            &repeat.body.stmts[copy_index],
            HirStmt::Assign(assign)
                if matches!(assign_shape(assign), Some((HirLValue::Local(_), HirExpr::TempRef(t))) if *t == temp)
        )
    {
        return None;
    }
    let local = match &repeat.body.stmts[copy_index] {
        HirStmt::Assign(assign) => match assign_shape(assign) {
            Some((HirLValue::Local(local), HirExpr::TempRef(_))) => *local,
            _ => return None,
        },
        _ => return None,
    };
    // 候选拒绝[LayerBoundary]：captured/protected local 的 cell/resource identity 不由 snapshot owner 合并。
    if facts.captured_locals.contains(&local) || facts.protected_locals.contains(&local) {
        return None;
    }
    let HirStmt::Assign(producer) = &mut repeat.body.stmts[producer_index] else {
        return None;
    };
    producer.targets[0] = HirLValue::Local(local);
    producer.values.fixed[0] = value;
    repeat.body.stmts.remove(copy_index);
    Some(local)
}

fn assign_shape(assign: &HirAssign) -> Option<(&HirLValue, &HirExpr)> {
    (assign.targets.len() == 1 && assign.values.tail.is_none() && assign.values.fixed.len() == 1)
        .then(|| (&assign.targets[0], &assign.values.fixed[0]))
}

fn value_mentions_temp(value: &HirExpr, temp: crate::hir::common::TempId) -> bool {
    collect_temp_refs_in_expr(value).contains(&temp)
}

fn stmt_contains_loop_exit(block: &HirBlock) -> bool {
    block.stmts.iter().any(stmt_contains_unsafe_control)
}

/// A nested loop can consume `break`/`continue` without leaving the repeat, but it also
/// introduces another state machine whose writes are not covered by this local two-statement
/// proof.  Reject the whole nested control subtree; this keeps the rewrite structural instead
/// of trying to infer path coverage from HIR alone.
fn stmt_contains_unsafe_control(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Return(_)
        | HirStmt::Goto(_)
        | HirStmt::Label(_)
        | HirStmt::Close(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_) => true,
        HirStmt::If(if_stmt) => {
            block_contains_unsafe_control(&if_stmt.then_block)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(block_contains_unsafe_control)
        }
        HirStmt::Block(block) => block_contains_unsafe_control(block),
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::CallStmt(_) => false,
    }
}

fn block_contains_unsafe_control(block: &HirBlock) -> bool {
    block.stmts.iter().any(stmt_contains_unsafe_control)
}
