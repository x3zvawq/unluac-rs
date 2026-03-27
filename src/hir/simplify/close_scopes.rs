//! 这个文件负责把 `<close>` 相关的显式 cleanup 重新物化成词法块。
//!
//! Lua 5.4 在 low-IR 里会保留 `tbc rX` / `close from rX` 这类 VM 级语义。结构层能在
//! 一部分 case 里直接把它们吸收进 `while/if/do`，但像 `goto` 反复重入同一块时，
//! HIR 仍可能留下“声明已经恢复、cleanup 还没变回词法边界”的中间形状。这里不去 AST
//! 末端兜底，而是在 HIR 里基于 `<close>` 绑定和对应寄存器槽位，把它们重新收成
//! `HirStmt::Block`，让后面的 AST lowering 自然落成 `do ... end`。

use crate::hir::common::{
    HirBlock, HirCallExpr, HirExpr, HirLValue, HirProto, HirStmt, LocalId, TempId,
};

#[cfg(test)]
mod tests;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ScopeInterval {
    start: usize,
    end: usize,
    reg_index: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScopeBinding {
    Local(LocalId),
    Temp(TempId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ScopeStart {
    start: usize,
    reg_index: usize,
    binding: ScopeBinding,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct ScopeActivity {
    mentions_binding: bool,
    closes_scope: bool,
}

impl ScopeActivity {
    fn any(self) -> bool {
        self.mentions_binding || self.closes_scope
    }

    fn merge(&mut self, other: ScopeActivity) {
        self.mentions_binding |= other.mentions_binding;
        self.closes_scope |= other.closes_scope;
    }
}

pub(super) fn materialize_tbc_close_scopes_in_proto(proto: &mut HirProto) -> bool {
    materialize_block(&mut proto.body)
}

fn materialize_block(block: &mut HirBlock) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        changed |= materialize_stmt(stmt);
    }

    let rewritten = rewrite_stmt_slice(&block.stmts);
    if rewritten != block.stmts {
        block.stmts = rewritten;
        changed = true;
    }

    changed
}

fn materialize_stmt(stmt: &mut HirStmt) -> bool {
    match stmt {
        HirStmt::If(if_stmt) => {
            let mut changed = materialize_block(&mut if_stmt.then_block);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= materialize_block(else_block);
            }
            changed
        }
        HirStmt::While(while_stmt) => materialize_block(&mut while_stmt.body),
        HirStmt::Repeat(repeat_stmt) => materialize_block(&mut repeat_stmt.body),
        HirStmt::NumericFor(numeric_for) => materialize_block(&mut numeric_for.body),
        HirStmt::GenericFor(generic_for) => materialize_block(&mut generic_for.body),
        HirStmt::Block(block) => materialize_block(block),
        HirStmt::Unstructured(unstructured) => materialize_block(&mut unstructured.body),
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
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn rewrite_stmt_slice(stmts: &[HirStmt]) -> Vec<HirStmt> {
    let intervals = collect_scope_intervals(stmts);
    if intervals.is_empty() {
        return stmts
            .iter()
            .filter(|stmt| !matches!(stmt, HirStmt::Close(close) if close.from_reg == 0))
            .cloned()
            .collect();
    }

    let mut cursor = 0;
    rebuild_slice(stmts, 0, stmts.len(), &intervals, &mut cursor, None)
}

fn collect_scope_intervals(stmts: &[HirStmt]) -> Vec<ScopeInterval> {
    let mut intervals = Vec::new();
    for index in 0..stmts.len() {
        let Some(scope_start) = scope_start(stmts, index) else {
            continue;
        };
        let Some(end) = find_scope_end(
            stmts,
            scope_start.start + 2,
            scope_start.binding,
            scope_start.reg_index,
        ) else {
            continue;
        };
        if scope_start.start < end {
            intervals.push(ScopeInterval {
                start: scope_start.start,
                end,
                reg_index: scope_start.reg_index,
            });
        }
    }

    intervals.sort_by_key(|interval| (interval.start, interval.end));

    well_nested_scope_intervals(&intervals)
        .then_some(intervals)
        .unwrap_or_default()
}

fn scope_start(stmts: &[HirStmt], index: usize) -> Option<ScopeStart> {
    match (stmts.get(index), stmts.get(index + 1)) {
        (
            Some(HirStmt::LocalDecl(_) | HirStmt::Assign(_)),
            Some(HirStmt::ToBeClosed(to_be_closed)),
        ) => binding_from_expr(&to_be_closed.value).map(|binding| ScopeStart {
            start: index,
            reg_index: to_be_closed.reg_index,
            binding,
        }),
        _ => None,
    }
}

fn binding_from_expr(expr: &HirExpr) -> Option<ScopeBinding> {
    match expr {
        HirExpr::LocalRef(local) => Some(ScopeBinding::Local(*local)),
        HirExpr::TempRef(temp) => Some(ScopeBinding::Temp(*temp)),
        _ => None,
    }
}

fn find_scope_end(
    stmts: &[HirStmt],
    start_index: usize,
    binding: ScopeBinding,
    reg_index: usize,
) -> Option<usize> {
    let mut saw_close = false;
    let mut last_activity = None;

    for (index, stmt) in stmts.iter().enumerate().skip(start_index) {
        let activity = scope_activity_in_stmt(stmt, binding, reg_index);
        if activity.any() {
            last_activity = Some(index + 1);
        }
        saw_close |= activity.closes_scope;
    }

    if saw_close { last_activity } else { None }
}

fn well_nested_scope_intervals(intervals: &[ScopeInterval]) -> bool {
    let mut stack = Vec::<ScopeInterval>::new();

    for interval in intervals {
        while let Some(top) = stack.last() {
            if interval.start >= top.end {
                stack.pop();
            } else {
                break;
            }
        }

        if let Some(parent) = stack.last()
            && interval.end > parent.end
        {
            return false;
        }

        stack.push(*interval);
    }

    true
}

fn rebuild_slice(
    stmts: &[HirStmt],
    start: usize,
    end: usize,
    intervals: &[ScopeInterval],
    cursor: &mut usize,
    active_scope_reg: Option<usize>,
) -> Vec<HirStmt> {
    let mut rewritten = Vec::new();
    let mut index = start;

    while index < end {
        while *cursor < intervals.len() && intervals[*cursor].end <= index {
            *cursor += 1;
        }

        if *cursor < intervals.len() {
            let interval = intervals[*cursor];
            if interval.start == index && interval.end <= end {
                *cursor += 1;
                let inner = rebuild_slice(
                    stmts,
                    interval.start,
                    interval.end,
                    intervals,
                    cursor,
                    Some(interval.reg_index),
                );
                let mut block_stmt = HirStmt::Block(Box::new(HirBlock { stmts: inner }));
                strip_matching_close_from_stmt(&mut block_stmt, active_scope_reg);
                rewritten.push(block_stmt);
                index = interval.end;
                continue;
            }
        }

        let mut cloned = stmts[index].clone();
        if strip_matching_close_from_stmt(&mut cloned, active_scope_reg) {
            rewritten.push(cloned);
        }
        index += 1;
    }

    rewritten
}

fn strip_matching_close_from_stmt(stmt: &mut HirStmt, active_scope_reg: Option<usize>) -> bool {
    match stmt {
        HirStmt::Close(close) => close.from_reg != 0 && active_scope_reg != Some(close.from_reg),
        HirStmt::If(if_stmt) => {
            strip_matching_close_from_block(&mut if_stmt.then_block, active_scope_reg);
            if let Some(else_block) = &mut if_stmt.else_block {
                strip_matching_close_from_block(else_block, active_scope_reg);
            }
            true
        }
        HirStmt::While(while_stmt) => {
            strip_matching_close_from_block(&mut while_stmt.body, active_scope_reg);
            true
        }
        HirStmt::Repeat(repeat_stmt) => {
            strip_matching_close_from_block(&mut repeat_stmt.body, active_scope_reg);
            true
        }
        HirStmt::NumericFor(numeric_for) => {
            strip_matching_close_from_block(&mut numeric_for.body, active_scope_reg);
            true
        }
        HirStmt::GenericFor(generic_for) => {
            strip_matching_close_from_block(&mut generic_for.body, active_scope_reg);
            true
        }
        HirStmt::Block(block) => {
            strip_matching_close_from_block(block, active_scope_reg);
            true
        }
        HirStmt::Unstructured(unstructured) => {
            strip_matching_close_from_block(&mut unstructured.body, active_scope_reg);
            true
        }
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => true,
    }
}

fn strip_matching_close_from_block(block: &mut HirBlock, active_scope_reg: Option<usize>) {
    block
        .stmts
        .retain_mut(|stmt| strip_matching_close_from_stmt(stmt, active_scope_reg));
}

fn scope_activity_in_stmt(
    stmt: &HirStmt,
    binding: ScopeBinding,
    reg_index: usize,
) -> ScopeActivity {
    match stmt {
        HirStmt::LocalDecl(local_decl) => ScopeActivity {
            mentions_binding: local_decl
                .bindings
                .iter()
                .copied()
                .any(|local| binding == ScopeBinding::Local(local))
                || local_decl
                    .values
                    .iter()
                    .any(|value| expr_mentions_binding(value, binding)),
            closes_scope: false,
        },
        HirStmt::Assign(assign) => ScopeActivity {
            mentions_binding: assign
                .targets
                .iter()
                .any(|target| lvalue_mentions_binding(target, binding))
                || assign
                    .values
                    .iter()
                    .any(|value| expr_mentions_binding(value, binding)),
            closes_scope: false,
        },
        HirStmt::TableSetList(set_list) => ScopeActivity {
            mentions_binding: expr_mentions_binding(&set_list.base, binding)
                || set_list
                    .values
                    .iter()
                    .any(|value| expr_mentions_binding(value, binding))
                || set_list
                    .trailing_multivalue
                    .as_ref()
                    .is_some_and(|value| expr_mentions_binding(value, binding)),
            closes_scope: false,
        },
        HirStmt::ErrNil(err_nil) => ScopeActivity {
            mentions_binding: expr_mentions_binding(&err_nil.value, binding),
            closes_scope: false,
        },
        HirStmt::ToBeClosed(to_be_closed) => ScopeActivity {
            mentions_binding: expr_mentions_binding(&to_be_closed.value, binding),
            closes_scope: false,
        },
        HirStmt::Close(close) => ScopeActivity {
            mentions_binding: false,
            closes_scope: close.from_reg == reg_index,
        },
        HirStmt::CallStmt(call_stmt) => scope_activity_in_call(&call_stmt.call, binding),
        HirStmt::Return(ret) => ScopeActivity {
            mentions_binding: ret
                .values
                .iter()
                .any(|value| expr_mentions_binding(value, binding)),
            closes_scope: false,
        },
        HirStmt::If(if_stmt) => {
            let mut activity = ScopeActivity {
                mentions_binding: expr_mentions_binding(&if_stmt.cond, binding),
                closes_scope: false,
            };
            activity.merge(scope_activity_in_block(
                &if_stmt.then_block,
                binding,
                reg_index,
            ));
            if let Some(else_block) = &if_stmt.else_block {
                activity.merge(scope_activity_in_block(else_block, binding, reg_index));
            }
            activity
        }
        HirStmt::While(while_stmt) => {
            let mut activity = ScopeActivity {
                mentions_binding: expr_mentions_binding(&while_stmt.cond, binding),
                closes_scope: false,
            };
            activity.merge(scope_activity_in_block(
                &while_stmt.body,
                binding,
                reg_index,
            ));
            activity
        }
        HirStmt::Repeat(repeat_stmt) => {
            let mut activity = scope_activity_in_block(&repeat_stmt.body, binding, reg_index);
            activity.mentions_binding |= expr_mentions_binding(&repeat_stmt.cond, binding);
            activity
        }
        HirStmt::NumericFor(numeric_for) => {
            let mut activity = ScopeActivity {
                mentions_binding: binding == ScopeBinding::Local(numeric_for.binding)
                    || expr_mentions_binding(&numeric_for.start, binding)
                    || expr_mentions_binding(&numeric_for.limit, binding)
                    || expr_mentions_binding(&numeric_for.step, binding),
                closes_scope: false,
            };
            activity.merge(scope_activity_in_block(
                &numeric_for.body,
                binding,
                reg_index,
            ));
            activity
        }
        HirStmt::GenericFor(generic_for) => {
            let mut activity = ScopeActivity {
                mentions_binding: generic_for
                    .bindings
                    .iter()
                    .copied()
                    .any(|local| binding == ScopeBinding::Local(local))
                    || generic_for
                        .iterator
                        .iter()
                        .any(|expr| expr_mentions_binding(expr, binding)),
                closes_scope: false,
            };
            activity.merge(scope_activity_in_block(
                &generic_for.body,
                binding,
                reg_index,
            ));
            activity
        }
        HirStmt::Block(block) => scope_activity_in_block(block, binding, reg_index),
        HirStmt::Unstructured(unstructured) => {
            scope_activity_in_block(&unstructured.body, binding, reg_index)
        }
        HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_) | HirStmt::Label(_) => {
            ScopeActivity::default()
        }
    }
}

fn scope_activity_in_block(
    block: &HirBlock,
    binding: ScopeBinding,
    reg_index: usize,
) -> ScopeActivity {
    let mut activity = ScopeActivity::default();
    for stmt in &block.stmts {
        activity.merge(scope_activity_in_stmt(stmt, binding, reg_index));
    }
    activity
}

fn scope_activity_in_call(call: &HirCallExpr, binding: ScopeBinding) -> ScopeActivity {
    ScopeActivity {
        mentions_binding: expr_mentions_binding(&call.callee, binding)
            || call
                .args
                .iter()
                .any(|arg| expr_mentions_binding(arg, binding)),
        closes_scope: false,
    }
}

fn lvalue_mentions_binding(target: &HirLValue, binding: ScopeBinding) -> bool {
    match target {
        HirLValue::Temp(temp) => binding == ScopeBinding::Temp(*temp),
        HirLValue::Local(local) => binding == ScopeBinding::Local(*local),
        HirLValue::Upvalue(_) | HirLValue::Global(_) => false,
        HirLValue::TableAccess(access) => {
            expr_mentions_binding(&access.base, binding)
                || expr_mentions_binding(&access.key, binding)
        }
    }
}

fn expr_mentions_binding(expr: &HirExpr, binding: ScopeBinding) -> bool {
    match expr {
        HirExpr::LocalRef(local) => binding == ScopeBinding::Local(*local),
        HirExpr::TempRef(temp) => binding == ScopeBinding::Temp(*temp),
        HirExpr::TableAccess(access) => {
            expr_mentions_binding(&access.base, binding)
                || expr_mentions_binding(&access.key, binding)
        }
        HirExpr::Unary(unary) => expr_mentions_binding(&unary.expr, binding),
        HirExpr::Binary(binary) => {
            expr_mentions_binding(&binary.lhs, binding)
                || expr_mentions_binding(&binary.rhs, binding)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_mentions_binding(&logical.lhs, binding)
                || expr_mentions_binding(&logical.rhs, binding)
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_mentions_binding(&node.test, binding)
                || decision_target_mentions_binding(&node.truthy, binding)
                || decision_target_mentions_binding(&node.falsy, binding)
        }),
        HirExpr::Call(call) => scope_activity_in_call(call, binding).mentions_binding,
        HirExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                crate::hir::common::HirTableField::Array(value) => {
                    expr_mentions_binding(value, binding)
                }
                crate::hir::common::HirTableField::Record(record) => {
                    record_key_mentions_binding(&record.key, binding)
                        || expr_mentions_binding(&record.value, binding)
                }
            }) || table
                .trailing_multivalue
                .as_ref()
                .is_some_and(|value| expr_mentions_binding(value, binding))
        }
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_mentions_binding(&capture.value, binding)),
        HirExpr::Unresolved(_)
        | HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::ParamRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg => false,
    }
}

fn decision_target_mentions_binding(
    target: &crate::hir::common::HirDecisionTarget,
    binding: ScopeBinding,
) -> bool {
    match target {
        crate::hir::common::HirDecisionTarget::Node(_) => false,
        crate::hir::common::HirDecisionTarget::CurrentValue => false,
        crate::hir::common::HirDecisionTarget::Expr(expr) => expr_mentions_binding(expr, binding),
    }
}

fn record_key_mentions_binding(
    key: &crate::hir::common::HirTableKey,
    binding: ScopeBinding,
) -> bool {
    match key {
        crate::hir::common::HirTableKey::Name(_) => false,
        crate::hir::common::HirTableKey::Expr(expr) => expr_mentions_binding(expr, binding),
    }
}
