//! 残余 `Decision` 线性化 pass 的 block / stmt 遍历入口。
//!
//! `Decision` 适合作为 HIR 内部恢复共享短路子图时的过渡表示，但不应该继续流到 AST。
//! 这个文件只负责按语句顺序遍历 block，并把表达式抽取、值物化和条件消除委托给
//! `eliminate_materialize.rs`；它不重新识别 Decision DAG，也不在 statement 层补 case
//! 特判。
//!
//! 例子：
//! - 输入：`local x = Decision(...)`
//! - 输出：`local x; if ... then x = ... else x = ... end`

use std::mem;

use crate::hir::common::{
    HirAssign, HirBlock, HirCallStmt, HirErrNil, HirLValue, HirLocalDecl, HirProto, HirReturn,
    HirStmt, HirTableSetList, HirToBeClosed, LocalId,
};

use super::super::walk::rewrite_nested_blocks_in_stmt;
use super::eliminate_materialize::{
    assign_target_supports_direct_materialization, eliminate_condition_expr, empty_local_decl,
    expr_contains_eliminable_decision, extract_call_expr, extract_generic_for, extract_numeric_for,
    extract_value_expr, extract_value_exprs, materialize_expr_into_target,
};
use super::eliminate_state::EliminationState;

pub(crate) fn eliminate_remaining_decisions_in_proto(proto: &mut HirProto) -> bool {
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
            prefix.push(HirStmt::ErrNil(Box::new(HirErrNil {
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
            prefix.push(HirStmt::Return(Box::new(HirReturn {
                values,
                trailing_multiret: ret.trailing_multiret,
            })));
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
