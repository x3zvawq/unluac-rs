//! 这个文件负责把残留在最终 HIR 输出前的 `Decision` 彻底线性化掉。
//!
//! `Decision` 适合作为 HIR 内部恢复共享短路子图时的过渡表示，但不应该继续流到 AST。
//! 这里的策略不是再去赌某个 case 能不能被局部规则折平，而是提供一条更通用的
//! “值表达式物化”通道：
//! 1. 能直接保持成普通表达式的子树继续保持；
//! 2. 带共享/短路语义的值子树会被物化成 `local + if + assign`；
//! 3. 最终 HIR 不再暴露 `Decision`，AST 只需要面对常规结构化节点。

use std::mem;

use crate::hir::common::{
    HirAssign, HirBinaryExpr, HirBlock, HirCallExpr, HirCallStmt, HirClosureExpr, HirDecisionExpr,
    HirDecisionNode, HirDecisionTarget, HirExpr, HirGenericFor, HirIf, HirLValue, HirLocalDecl,
    HirLogicalExpr, HirNumericFor, HirProto, HirRecordField, HirReturn, HirStmt, HirTableAccess,
    HirTableConstructor, HirTableField, HirTableKey, HirTableSetList, HirToBeClosed, HirUnaryExpr,
    LocalId,
};

use super::super::visit::{HirVisitor, visit_expr};
use super::super::walk::rewrite_nested_blocks_in_stmt;

pub(super) fn eliminate_remaining_decisions_in_proto(proto: &mut HirProto) -> bool {
    let mut next_local_index = proto.locals.len();
    let mut new_locals = Vec::new();
    let mut new_local_debug_hints = Vec::new();
    let changed = eliminate_block(
        &mut proto.body,
        &mut next_local_index,
        &mut new_locals,
        &mut new_local_debug_hints,
    );
    proto.locals.extend(new_locals);
    proto.local_debug_hints.extend(new_local_debug_hints);
    changed
}

fn eliminate_block(
    block: &mut HirBlock,
    next_local_index: &mut usize,
    new_locals: &mut Vec<LocalId>,
    new_local_debug_hints: &mut Vec<Option<String>>,
) -> bool {
    let mut changed = false;
    let mut rewritten = Vec::with_capacity(block.stmts.len());
    let original = mem::take(&mut block.stmts);
    let mut state = EliminationState {
        next_local_index,
        new_locals,
        new_local_debug_hints,
    };

    for stmt in original {
        let (mut lowered, stmt_changed) = eliminate_stmt(stmt, &mut state);
        changed |= stmt_changed;
        rewritten.append(&mut lowered);
    }

    block.stmts = rewritten;
    changed
}

struct EliminationState<'a> {
    next_local_index: &'a mut usize,
    new_locals: &'a mut Vec<LocalId>,
    new_local_debug_hints: &'a mut Vec<Option<String>>,
}

impl EliminationState<'_> {
    fn alloc_local(&mut self) -> LocalId {
        let local = LocalId(*self.next_local_index);
        *self.next_local_index += 1;
        self.new_locals.push(local);
        self.new_local_debug_hints.push(None);
        local
    }
}

fn eliminate_stmt(stmt: HirStmt, state: &mut EliminationState<'_>) -> (Vec<HirStmt>, bool) {
    match stmt {
        HirStmt::LocalDecl(local_decl)
            if local_decl.bindings.len() == 1
                && local_decl.values.len() == 1
                && expr_contains_eliminable_decision(&local_decl.values[0]) =>
        {
            let binding = local_decl.bindings[0];
            let value = local_decl
                .values
                .into_iter()
                .next()
                .expect("single-value local decl should stay non-empty");
            let mut stmts = vec![empty_local_decl(binding)];
            stmts.extend(materialize_expr_into_target(
                value,
                HirLValue::Local(binding),
                state,
            ));
            (stmts, true)
        }
        HirStmt::Assign(assign)
            if assign.targets.len() == 1
                && assign.values.len() == 1
                && assign_target_supports_direct_materialization(&assign.targets[0])
                && expr_contains_eliminable_decision(&assign.values[0]) =>
        {
            let target = assign
                .targets
                .into_iter()
                .next()
                .expect("single-target assign should stay non-empty");
            let value = assign
                .values
                .into_iter()
                .next()
                .expect("single-value assign should stay non-empty");
            (materialize_expr_into_target(value, target, state), true)
        }
        HirStmt::LocalDecl(local_decl) => {
            let (mut prefix, values, changed) = extract_value_exprs(local_decl.values, state);
            prefix.push(HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: local_decl.bindings,
                values,
            })));
            (prefix, changed)
        }
        HirStmt::Assign(assign) => {
            let (mut prefix, values, values_changed) = extract_value_exprs(assign.values, state);
            prefix.push(HirStmt::Assign(Box::new(HirAssign {
                targets: assign.targets,
                values,
            })));
            (prefix, values_changed)
        }
        HirStmt::TableSetList(set_list) => {
            let (mut prefix, base, base_changed) = extract_value_expr(set_list.base, state);
            let (value_prefix, values, values_changed) =
                extract_value_exprs(set_list.values, state);
            prefix.extend(value_prefix);
            let (trailing_prefix, trailing_multivalue, trailing_changed) = set_list
                .trailing_multivalue
                .map(|expr| extract_value_expr(expr, state))
                .map_or((Vec::new(), None, false), |(prefix, expr, changed)| {
                    (prefix, Some(expr), changed)
                });
            prefix.extend(trailing_prefix);
            prefix.push(HirStmt::TableSetList(Box::new(HirTableSetList {
                base,
                start_index: set_list.start_index,
                values,
                trailing_multivalue,
            })));
            (prefix, base_changed || values_changed || trailing_changed)
        }
        HirStmt::ErrNil(err_nil) => {
            let (mut prefix, value, changed) = extract_value_expr(err_nil.value, state);
            prefix.push(HirStmt::ErrNil(Box::new(crate::hir::common::HirErrNil {
                value,
                name: err_nil.name,
            })));
            (prefix, changed)
        }
        HirStmt::ToBeClosed(to_be_closed) => {
            let (mut prefix, value, changed) = extract_value_expr(to_be_closed.value, state);
            prefix.push(HirStmt::ToBeClosed(Box::new(HirToBeClosed {
                reg_index: to_be_closed.reg_index,
                value,
            })));
            (prefix, changed)
        }
        HirStmt::CallStmt(call_stmt) => {
            let (mut prefix, call, changed) = extract_call_expr(call_stmt.call, state);
            prefix.push(HirStmt::CallStmt(Box::new(HirCallStmt { call })));
            (prefix, changed)
        }
        HirStmt::Return(ret) => {
            let (mut prefix, values, changed) = extract_value_exprs(ret.values, state);
            prefix.push(HirStmt::Return(Box::new(HirReturn { values })));
            (prefix, changed)
        }
        HirStmt::If(mut if_stmt) => {
            let cond_changed = eliminate_condition_expr(&mut if_stmt.cond);
            let mut stmt = HirStmt::If(if_stmt);
            let nested_changed = eliminate_nested_blocks_in_stmt(&mut stmt, state);
            (vec![stmt], cond_changed || nested_changed)
        }
        HirStmt::While(mut while_stmt) => {
            let cond_changed = eliminate_condition_expr(&mut while_stmt.cond);
            let mut stmt = HirStmt::While(while_stmt);
            let nested_changed = eliminate_nested_blocks_in_stmt(&mut stmt, state);
            (vec![stmt], cond_changed || nested_changed)
        }
        HirStmt::Repeat(mut repeat_stmt) => {
            let cond_changed = eliminate_condition_expr(&mut repeat_stmt.cond);
            let mut stmt = HirStmt::Repeat(repeat_stmt);
            let nested_changed = eliminate_nested_blocks_in_stmt(&mut stmt, state);
            (vec![stmt], nested_changed || cond_changed)
        }
        HirStmt::NumericFor(numeric_for) => {
            let (mut prefix, numeric_for, changed) = extract_numeric_for(numeric_for, state);
            let mut stmt = HirStmt::NumericFor(numeric_for);
            let nested_changed = eliminate_nested_blocks_in_stmt(&mut stmt, state);
            prefix.push(stmt);
            (prefix, changed || nested_changed)
        }
        HirStmt::GenericFor(generic_for) => {
            let (mut prefix, generic_for, changed) = extract_generic_for(generic_for, state);
            let mut stmt = HirStmt::GenericFor(generic_for);
            let nested_changed = eliminate_nested_blocks_in_stmt(&mut stmt, state);
            prefix.push(stmt);
            (prefix, changed || nested_changed)
        }
        HirStmt::Block(block) => {
            let mut stmt = HirStmt::Block(block);
            let changed = eliminate_nested_blocks_in_stmt(&mut stmt, state);
            (vec![stmt], changed)
        }
        HirStmt::Unstructured(unstructured) => {
            let mut stmt = HirStmt::Unstructured(unstructured);
            let changed = eliminate_nested_blocks_in_stmt(&mut stmt, state);
            (vec![stmt], changed)
        }
        HirStmt::Break
        | HirStmt::Close(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => (vec![stmt], false),
    }
}

fn eliminate_nested_blocks_in_stmt(stmt: &mut HirStmt, state: &mut EliminationState<'_>) -> bool {
    rewrite_nested_blocks_in_stmt(stmt, &mut |block| {
        eliminate_block(
            block,
            state.next_local_index,
            state.new_locals,
            state.new_local_debug_hints,
        )
    })
}

fn assign_target_supports_direct_materialization(target: &HirLValue) -> bool {
    matches!(
        target,
        HirLValue::Temp(_) | HirLValue::Local(_) | HirLValue::Upvalue(_) | HirLValue::Global(_)
    )
}

fn extract_numeric_for(
    mut numeric_for: Box<HirNumericFor>,
    state: &mut EliminationState<'_>,
) -> (Vec<HirStmt>, Box<HirNumericFor>, bool) {
    let (prefix, mut exprs, exprs_changed) = extract_value_exprs(
        vec![numeric_for.start, numeric_for.limit, numeric_for.step],
        state,
    );
    numeric_for.start = exprs.remove(0);
    numeric_for.limit = exprs.remove(0);
    numeric_for.step = exprs.remove(0);
    (prefix, numeric_for, exprs_changed)
}

fn extract_generic_for(
    mut generic_for: Box<HirGenericFor>,
    state: &mut EliminationState<'_>,
) -> (Vec<HirStmt>, Box<HirGenericFor>, bool) {
    let (prefix, iterator, iterator_changed) = extract_value_exprs(generic_for.iterator, state);
    generic_for.iterator = iterator;
    (prefix, generic_for, iterator_changed)
}

fn extract_call_expr(
    call: HirCallExpr,
    state: &mut EliminationState<'_>,
) -> (Vec<HirStmt>, HirCallExpr, bool) {
    let (mut prefix, callee, callee_changed) = extract_value_expr(call.callee, state);
    let (arg_prefix, args, args_changed) = extract_value_exprs(call.args, state);
    prefix.extend(arg_prefix);
    (
        prefix,
        HirCallExpr {
            callee,
            args,
            multiret: call.multiret,
            method: call.method,
            method_name: call.method_name,
        },
        callee_changed || args_changed,
    )
}

fn extract_value_exprs(
    exprs: Vec<HirExpr>,
    state: &mut EliminationState<'_>,
) -> (Vec<HirStmt>, Vec<HirExpr>, bool) {
    let mut prefix = Vec::new();
    let mut rewritten = Vec::with_capacity(exprs.len());
    let mut changed = false;

    for expr in exprs {
        let (expr_prefix, expr, expr_changed) = extract_value_expr(expr, state);
        prefix.extend(expr_prefix);
        rewritten.push(expr);
        changed |= expr_changed;
    }

    (prefix, rewritten, changed)
}

fn extract_value_expr(
    expr: HirExpr,
    state: &mut EliminationState<'_>,
) -> (Vec<HirStmt>, HirExpr, bool) {
    if !expr_contains_eliminable_decision(&expr) {
        return (Vec::new(), expr, false);
    }
    if let Some(collapsed) = collapse_expr_to_pure(expr.clone()) {
        return (Vec::new(), collapsed, true);
    }

    let local = state.alloc_local();
    let mut prefix = vec![empty_local_decl(local)];
    prefix.extend(materialize_expr_into_target(
        expr,
        HirLValue::Local(local),
        state,
    ));
    (prefix, HirExpr::LocalRef(local), true)
}

fn materialize_expr_into_target(
    expr: HirExpr,
    target: HirLValue,
    state: &mut EliminationState<'_>,
) -> Vec<HirStmt> {
    match expr {
        HirExpr::Decision(decision) => materialize_decision_into_target(*decision, target, state),
        HirExpr::LogicalAnd(logical) => {
            materialize_logical_expr_into_target(true, *logical, target, state)
        }
        HirExpr::LogicalOr(logical) => {
            materialize_logical_expr_into_target(false, *logical, target, state)
        }
        expr => {
            let (mut prefix, expr) = prepare_pure_expr(expr, state);
            prefix.push(assign_stmt(target, expr));
            prefix
        }
    }
}

fn materialize_logical_expr_into_target(
    is_and: bool,
    logical: HirLogicalExpr,
    target: HirLValue,
    state: &mut EliminationState<'_>,
) -> Vec<HirStmt> {
    if let Some(lhs_truthy) = super::expr_truthiness(&logical.lhs) {
        return if is_and {
            if lhs_truthy {
                materialize_expr_into_target(logical.rhs, target, state)
            } else {
                materialize_expr_into_target(logical.lhs, target, state)
            }
        } else if lhs_truthy {
            materialize_expr_into_target(logical.lhs, target, state)
        } else {
            materialize_expr_into_target(logical.rhs, target, state)
        };
    }

    let lhs_local = state.alloc_local();
    let mut stmts = vec![empty_local_decl(lhs_local)];
    stmts.extend(materialize_expr_into_target(
        logical.lhs,
        HirLValue::Local(lhs_local),
        state,
    ));
    stmts.push(assign_stmt(target.clone(), HirExpr::LocalRef(lhs_local)));

    let guard = if is_and {
        HirExpr::LocalRef(lhs_local)
    } else {
        super::negate_expr(HirExpr::LocalRef(lhs_local))
    };
    let then_block = HirBlock {
        stmts: materialize_expr_into_target(logical.rhs, target, state),
    };
    stmts.push(HirStmt::If(Box::new(HirIf {
        cond: guard,
        then_block,
        else_block: None,
    })));
    stmts
}

fn materialize_decision_into_target(
    decision: HirDecisionExpr,
    target: HirLValue,
    state: &mut EliminationState<'_>,
) -> Vec<HirStmt> {
    if let Some(expr) = super::collapse_value_decision_expr(&decision) {
        return materialize_expr_into_target(expr, target, state);
    }

    materialize_decision_node(&decision, decision.entry.index(), target, state)
}

fn materialize_decision_node(
    decision: &HirDecisionExpr,
    node_index: usize,
    target: HirLValue,
    state: &mut EliminationState<'_>,
) -> Vec<HirStmt> {
    let node = &decision.nodes[node_index];
    let captures_current = matches!(node.truthy, HirDecisionTarget::CurrentValue)
        || matches!(node.falsy, HirDecisionTarget::CurrentValue);
    let (mut prefix, prepared_test) = prepare_pure_expr(node.test.clone(), state);
    let (cond, current_value) = if captures_current {
        let current_local = state.alloc_local();
        prefix.push(local_decl_with_value(current_local, prepared_test));
        (
            HirExpr::LocalRef(current_local),
            Some(HirExpr::LocalRef(current_local)),
        )
    } else {
        (prepared_test, None)
    };

    let then_block = HirBlock {
        stmts: materialize_decision_target(
            decision,
            node,
            &node.truthy,
            current_value.as_ref(),
            target.clone(),
            state,
        ),
    };
    let else_stmts = materialize_decision_target(
        decision,
        node,
        &node.falsy,
        current_value.as_ref(),
        target,
        state,
    );

    if then_block.stmts == else_stmts {
        prefix.extend(then_block.stmts);
        return prefix;
    }

    if let Some(cond_truthy) = super::expr_truthiness(&cond) {
        prefix.extend(if cond_truthy {
            then_block.stmts
        } else {
            else_stmts
        });
        return prefix;
    }

    if then_block.stmts.is_empty() && else_stmts.is_empty() {
        return prefix;
    }

    let (cond, then_block, else_block) = if then_block.stmts.is_empty() {
        (
            super::negate_expr(cond),
            HirBlock { stmts: else_stmts },
            None,
        )
    } else if else_stmts.is_empty() {
        (cond, then_block, None)
    } else {
        (cond, then_block, Some(HirBlock { stmts: else_stmts }))
    };

    prefix.push(HirStmt::If(Box::new(HirIf {
        cond,
        then_block,
        else_block,
    })));
    prefix
}

fn materialize_decision_target(
    decision: &HirDecisionExpr,
    node: &HirDecisionNode,
    target_branch: &HirDecisionTarget,
    current_value: Option<&HirExpr>,
    target: HirLValue,
    state: &mut EliminationState<'_>,
) -> Vec<HirStmt> {
    match target_branch {
        HirDecisionTarget::Node(next_ref) => {
            materialize_decision_node(decision, next_ref.index(), target, state)
        }
        HirDecisionTarget::CurrentValue => vec![assign_stmt(
            target,
            current_value.cloned().unwrap_or_else(|| node.test.clone()),
        )],
        HirDecisionTarget::Expr(expr) => materialize_expr_into_target(expr.clone(), target, state),
    }
}

fn prepare_pure_expr(expr: HirExpr, state: &mut EliminationState<'_>) -> (Vec<HirStmt>, HirExpr) {
    if expr_contains_eliminable_decision(&expr)
        && let Some(collapsed) = collapse_expr_to_pure(expr.clone())
    {
        return prepare_pure_expr(collapsed, state);
    }

    match expr {
        HirExpr::Decision(_) | HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)
            if expr_contains_eliminable_decision(&expr) =>
        {
            let local = state.alloc_local();
            let mut prefix = vec![empty_local_decl(local)];
            prefix.extend(materialize_expr_into_target(
                expr,
                HirLValue::Local(local),
                state,
            ));
            (prefix, HirExpr::LocalRef(local))
        }
        HirExpr::TableAccess(access) => {
            let (mut prefix, base) = prepare_pure_expr(access.base, state);
            let (key_prefix, key) = prepare_pure_expr(access.key, state);
            prefix.extend(key_prefix);
            (
                prefix,
                HirExpr::TableAccess(Box::new(HirTableAccess { base, key })),
            )
        }
        HirExpr::Unary(unary) => {
            let (prefix, expr) = prepare_pure_expr(unary.expr, state);
            (
                prefix,
                HirExpr::Unary(Box::new(HirUnaryExpr { op: unary.op, expr })),
            )
        }
        HirExpr::Binary(binary) => {
            let (mut prefix, lhs) = prepare_pure_expr(binary.lhs, state);
            let (rhs_prefix, rhs) = prepare_pure_expr(binary.rhs, state);
            prefix.extend(rhs_prefix);
            (
                prefix,
                HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: binary.op,
                    lhs,
                    rhs,
                })),
            )
        }
        HirExpr::LogicalAnd(logical) => {
            let (mut prefix, lhs) = prepare_pure_expr(logical.lhs, state);
            let (rhs_prefix, rhs) = prepare_pure_expr(logical.rhs, state);
            prefix.extend(rhs_prefix);
            (
                prefix,
                HirExpr::LogicalAnd(Box::new(HirLogicalExpr { lhs, rhs })),
            )
        }
        HirExpr::LogicalOr(logical) => {
            let (mut prefix, lhs) = prepare_pure_expr(logical.lhs, state);
            let (rhs_prefix, rhs) = prepare_pure_expr(logical.rhs, state);
            prefix.extend(rhs_prefix);
            (
                prefix,
                HirExpr::LogicalOr(Box::new(HirLogicalExpr { lhs, rhs })),
            )
        }
        HirExpr::Call(call) => {
            let (prefix, call, _) = extract_call_expr(*call, state);
            (prefix, HirExpr::Call(Box::new(call)))
        }
        HirExpr::TableConstructor(table) => {
            let (prefix, table) = prepare_table_constructor(*table, state);
            (prefix, HirExpr::TableConstructor(Box::new(table)))
        }
        HirExpr::Closure(closure) => {
            let (prefix, closure) = prepare_closure(*closure, state);
            (prefix, HirExpr::Closure(Box::new(closure)))
        }
        expr => (Vec::new(), expr),
    }
}

fn collapse_expr_to_pure(expr: HirExpr) -> Option<HirExpr> {
    match expr {
        HirExpr::Decision(decision) => super::collapse_value_decision_expr(&decision),
        HirExpr::TableAccess(access) => Some(HirExpr::TableAccess(Box::new(HirTableAccess {
            base: collapse_expr_to_pure(access.base)?,
            key: collapse_expr_to_pure(access.key)?,
        }))),
        HirExpr::Unary(unary) => Some(HirExpr::Unary(Box::new(HirUnaryExpr {
            op: unary.op,
            expr: collapse_expr_to_pure(unary.expr)?,
        }))),
        HirExpr::Binary(binary) => Some(HirExpr::Binary(Box::new(HirBinaryExpr {
            op: binary.op,
            lhs: collapse_expr_to_pure(binary.lhs)?,
            rhs: collapse_expr_to_pure(binary.rhs)?,
        }))),
        HirExpr::LogicalAnd(logical) => {
            let lhs = collapse_expr_to_pure(logical.lhs)?;
            let rhs = collapse_expr_to_pure(logical.rhs)?;
            let expr = HirExpr::LogicalAnd(Box::new(HirLogicalExpr { lhs, rhs }));
            Some(super::simplify_lua_logical_shape(&expr).unwrap_or(expr))
        }
        HirExpr::LogicalOr(logical) => {
            let lhs = collapse_expr_to_pure(logical.lhs)?;
            let rhs = collapse_expr_to_pure(logical.rhs)?;
            let expr = HirExpr::LogicalOr(Box::new(HirLogicalExpr { lhs, rhs }));
            Some(super::simplify_lua_logical_shape(&expr).unwrap_or(expr))
        }
        HirExpr::Call(call) => {
            let callee = collapse_expr_to_pure(call.callee)?;
            let args = call
                .args
                .into_iter()
                .map(collapse_expr_to_pure)
                .collect::<Option<Vec<_>>>()?;
            Some(HirExpr::Call(Box::new(HirCallExpr {
                callee,
                args,
                multiret: call.multiret,
                method: call.method,
                method_name: call.method_name,
            })))
        }
        HirExpr::TableConstructor(table) => {
            let mut fields = Vec::with_capacity(table.fields.len());
            for field in table.fields {
                match field {
                    HirTableField::Array(expr) => {
                        fields.push(HirTableField::Array(collapse_expr_to_pure(expr)?));
                    }
                    HirTableField::Record(field) => {
                        let key = match field.key {
                            HirTableKey::Name(name) => HirTableKey::Name(name),
                            HirTableKey::Expr(expr) => {
                                HirTableKey::Expr(collapse_expr_to_pure(expr)?)
                            }
                        };
                        fields.push(HirTableField::Record(crate::hir::common::HirRecordField {
                            key,
                            value: collapse_expr_to_pure(field.value)?,
                        }));
                    }
                }
            }
            let trailing_multivalue = match table.trailing_multivalue {
                Some(expr) => Some(collapse_expr_to_pure(expr)?),
                None => None,
            };
            Some(HirExpr::TableConstructor(Box::new(HirTableConstructor {
                fields,
                trailing_multivalue,
            })))
        }
        HirExpr::Closure(closure) => {
            let mut closure = *closure;
            for capture in &mut closure.captures {
                capture.value = collapse_expr_to_pure(capture.value.clone())?;
            }
            Some(HirExpr::Closure(Box::new(closure)))
        }
        expr => Some(expr),
    }
}

fn prepare_table_constructor(
    table: HirTableConstructor,
    state: &mut EliminationState<'_>,
) -> (Vec<HirStmt>, HirTableConstructor) {
    let mut prefix = Vec::new();
    let mut fields = Vec::with_capacity(table.fields.len());

    for field in table.fields {
        match field {
            HirTableField::Array(expr) => {
                let (expr_prefix, expr) = prepare_pure_expr(expr, state);
                prefix.extend(expr_prefix);
                fields.push(HirTableField::Array(expr));
            }
            HirTableField::Record(HirRecordField { key, value }) => {
                let (key_prefix, key) = match key {
                    HirTableKey::Name(name) => (Vec::new(), HirTableKey::Name(name)),
                    HirTableKey::Expr(expr) => {
                        let (prefix, expr) = prepare_pure_expr(expr, state);
                        (prefix, HirTableKey::Expr(expr))
                    }
                };
                prefix.extend(key_prefix);
                let (value_prefix, value) = prepare_pure_expr(value, state);
                prefix.extend(value_prefix);
                fields.push(HirTableField::Record(HirRecordField { key, value }));
            }
        }
    }

    let (trailing_prefix, trailing_multivalue) = table
        .trailing_multivalue
        .map(|expr| {
            let (prefix, expr) = prepare_pure_expr(expr, state);
            (prefix, Some(expr))
        })
        .unwrap_or_default();
    prefix.extend(trailing_prefix);

    (
        prefix,
        HirTableConstructor {
            fields,
            trailing_multivalue,
        },
    )
}

fn prepare_closure(
    mut closure: HirClosureExpr,
    state: &mut EliminationState<'_>,
) -> (Vec<HirStmt>, HirClosureExpr) {
    let mut prefix = Vec::new();
    for capture in &mut closure.captures {
        let (capture_prefix, value) = prepare_pure_expr(capture.value.clone(), state);
        prefix.extend(capture_prefix);
        capture.value = value;
    }
    (prefix, closure)
}

fn eliminate_condition_expr(expr: &mut HirExpr) -> bool {
    let mut changed = match expr {
        HirExpr::TableAccess(access) => {
            eliminate_condition_expr(&mut access.base) || eliminate_condition_expr(&mut access.key)
        }
        HirExpr::Unary(unary) => eliminate_condition_expr(&mut unary.expr),
        HirExpr::Binary(binary) => {
            eliminate_condition_expr(&mut binary.lhs) || eliminate_condition_expr(&mut binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            eliminate_condition_expr(&mut logical.lhs) || eliminate_condition_expr(&mut logical.rhs)
        }
        HirExpr::Decision(decision) => {
            if let Some(replacement) = super::collapse_condition_decision_expr(decision) {
                *expr = replacement;
                true
            } else {
                false
            }
        }
        HirExpr::Call(call) => {
            eliminate_condition_expr(&mut call.callee)
                || call.args.iter_mut().any(eliminate_condition_expr)
        }
        HirExpr::TableConstructor(table) => {
            table.fields.iter_mut().any(|field| match field {
                HirTableField::Array(expr) => eliminate_condition_expr(expr),
                HirTableField::Record(field) => {
                    let key_changed = match &mut field.key {
                        HirTableKey::Name(_) => false,
                        HirTableKey::Expr(expr) => eliminate_condition_expr(expr),
                    };
                    key_changed || eliminate_condition_expr(&mut field.value)
                }
            }) || table
                .trailing_multivalue
                .as_mut()
                .is_some_and(eliminate_condition_expr)
        }
        HirExpr::Closure(closure) => closure
            .captures
            .iter_mut()
            .any(|capture| eliminate_condition_expr(&mut capture.value)),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
    };

    if let Some(replacement) = super::simplify_lua_logical_shape(expr) {
        *expr = replacement;
        changed = true;
    }
    if let Some(replacement) = super::simplify_condition_truthiness_shape(expr) {
        *expr = replacement;
        changed = true;
    }

    changed
}

fn expr_contains_eliminable_decision(expr: &HirExpr) -> bool {
    let mut collector = EliminableDecisionCollector { found: false };
    visit_expr(expr, &mut collector);
    collector.found
}

struct EliminableDecisionCollector {
    found: bool,
}

impl HirVisitor for EliminableDecisionCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.found |=
            matches!(expr, HirExpr::Decision(decision) if !super::decision_has_cycles(decision));
    }
}

fn empty_local_decl(local: LocalId) -> HirStmt {
    HirStmt::LocalDecl(Box::new(HirLocalDecl {
        bindings: vec![local],
        values: Vec::new(),
    }))
}

fn local_decl_with_value(local: LocalId, value: HirExpr) -> HirStmt {
    HirStmt::LocalDecl(Box::new(HirLocalDecl {
        bindings: vec![local],
        values: vec![value],
    }))
}

fn assign_stmt(target: HirLValue, value: HirExpr) -> HirStmt {
    HirStmt::Assign(Box::new(HirAssign {
        targets: vec![target],
        values: vec![value],
    }))
}
