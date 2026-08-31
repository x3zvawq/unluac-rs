//! 这个子模块负责 temp-inline pass 的实际替换动作。
//!
//! 它依赖 `site` 已确认的内联位置和上层给好的 replacement，只做语法树内的定点替换，
//! 不会在这里重新判断这个 temp 应不应该内联。
//! 例如：`local r0 = print; r0(1)` 选定站点后，会在这里把 `r0` 改成 `print`。

use super::*;
pub(super) use crate::hir::rewrite::replace_temp_in_expr;
use crate::hir::rewrite::{
    replace_temp_in_call as replace_temp_in_call_expr, replace_temp_in_value_pack,
    replace_temps_in_call, replace_temps_in_expr, replace_temps_in_value_pack,
};
use std::collections::BTreeMap;

pub(super) fn replace_temp_in_stmt(stmt: &mut HirStmt, temp: TempId, replacement: &HirExpr) {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            replace_temp_in_value_pack(&mut local_decl.values, temp, replacement);
        }
        HirStmt::GlobalDecl(global_decl) => {
            replace_temp_in_value_pack(&mut global_decl.values, temp, replacement);
        }
        HirStmt::Assign(assign) => {
            for target in &mut assign.targets {
                replace_temp_in_lvalue(target, temp, replacement);
            }
            replace_temp_in_value_pack(&mut assign.values, temp, replacement);
        }
        HirStmt::TableSetList(set_list) => {
            replace_temp_in_expr(&mut set_list.base, temp, replacement);
            replace_temp_in_value_pack(&mut set_list.values, temp, replacement);
        }
        HirStmt::ErrNil(err_nil) => {
            replace_temp_in_expr(&mut err_nil.value, temp, replacement);
        }
        HirStmt::ToBeClosed(to_be_closed) => {
            replace_temp_in_expr(&mut to_be_closed.value, temp, replacement);
        }
        HirStmt::CallStmt(call_stmt) => {
            replace_temp_in_call_expr(&mut call_stmt.call, temp, replacement);
        }
        HirStmt::Return(ret) => {
            replace_temp_in_value_pack(&mut ret.values, temp, replacement);
        }
        HirStmt::If(if_stmt) => {
            replace_temp_in_expr(&mut if_stmt.cond, temp, replacement);
            replace_temp_in_block(&mut if_stmt.then_block, temp, replacement);
            if let Some(else_block) = &mut if_stmt.else_block {
                replace_temp_in_block(else_block, temp, replacement);
            }
        }
        HirStmt::While(while_stmt) => {
            replace_temp_in_expr(&mut while_stmt.cond, temp, replacement);
            replace_temp_in_block(&mut while_stmt.body, temp, replacement);
        }
        HirStmt::Repeat(repeat_stmt) => {
            replace_temp_in_block(&mut repeat_stmt.body, temp, replacement);
            replace_temp_in_expr(&mut repeat_stmt.cond, temp, replacement);
        }
        HirStmt::NumericFor(numeric_for) => {
            replace_temp_in_expr(&mut numeric_for.start, temp, replacement);
            replace_temp_in_expr(&mut numeric_for.limit, temp, replacement);
            replace_temp_in_expr(&mut numeric_for.step, temp, replacement);
            replace_temp_in_block(&mut numeric_for.body, temp, replacement);
        }
        HirStmt::GenericFor(generic_for) => {
            replace_temp_in_value_pack(&mut generic_for.iterator, temp, replacement);
            replace_temp_in_block(&mut generic_for.body, temp, replacement);
        }
        HirStmt::Close(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
        HirStmt::Block(block) => replace_temp_in_block(block, temp, replacement),
    }
}

pub(super) fn replace_temps_in_stmt(
    stmt: &mut HirStmt,
    replacements: &BTreeMap<TempId, HirExpr>,
) -> usize {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            replace_temps_in_value_pack(&mut local_decl.values, replacements)
        }
        HirStmt::GlobalDecl(global_decl) => {
            replace_temps_in_value_pack(&mut global_decl.values, replacements)
        }
        HirStmt::Assign(assign) => {
            let targets = assign
                .targets
                .iter_mut()
                .map(|target| replace_temps_in_lvalue(target, replacements))
                .sum::<usize>();
            targets + replace_temps_in_value_pack(&mut assign.values, replacements)
        }
        HirStmt::TableSetList(set_list) => {
            replace_temps_in_expr(&mut set_list.base, replacements)
                + replace_temps_in_value_pack(&mut set_list.values, replacements)
        }
        HirStmt::ErrNil(err_nil) => replace_temps_in_expr(&mut err_nil.value, replacements),
        HirStmt::ToBeClosed(to_be_closed) => {
            replace_temps_in_expr(&mut to_be_closed.value, replacements)
        }
        HirStmt::CallStmt(call_stmt) => replace_temps_in_call(&mut call_stmt.call, replacements),
        HirStmt::Return(ret) => replace_temps_in_value_pack(&mut ret.values, replacements),
        HirStmt::If(if_stmt) => {
            let then_count = replace_temps_in_expr(&mut if_stmt.cond, replacements)
                + replace_temps_in_block(&mut if_stmt.then_block, replacements);
            then_count
                + if_stmt
                    .else_block
                    .as_mut()
                    .map_or(0, |block| replace_temps_in_block(block, replacements))
        }
        HirStmt::While(while_stmt) => {
            replace_temps_in_expr(&mut while_stmt.cond, replacements)
                + replace_temps_in_block(&mut while_stmt.body, replacements)
        }
        HirStmt::Repeat(repeat_stmt) => {
            replace_temps_in_block(&mut repeat_stmt.body, replacements)
                + replace_temps_in_expr(&mut repeat_stmt.cond, replacements)
        }
        HirStmt::NumericFor(numeric_for) => {
            replace_temps_in_expr(&mut numeric_for.start, replacements)
                + replace_temps_in_expr(&mut numeric_for.limit, replacements)
                + replace_temps_in_expr(&mut numeric_for.step, replacements)
                + replace_temps_in_block(&mut numeric_for.body, replacements)
        }
        HirStmt::GenericFor(generic_for) => {
            replace_temps_in_value_pack(&mut generic_for.iterator, replacements)
                + replace_temps_in_block(&mut generic_for.body, replacements)
        }
        HirStmt::Block(block) => replace_temps_in_block(block, replacements),
        HirStmt::Close(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => 0,
    }
}

fn replace_temps_in_block(block: &mut HirBlock, replacements: &BTreeMap<TempId, HirExpr>) -> usize {
    block
        .stmts
        .iter_mut()
        .map(|stmt| replace_temps_in_stmt(stmt, replacements))
        .sum()
}

fn replace_temp_in_block(block: &mut HirBlock, temp: TempId, replacement: &HirExpr) {
    for stmt in &mut block.stmts {
        replace_temp_in_stmt(stmt, temp, replacement);
    }
}

fn replace_temp_in_lvalue(lvalue: &mut HirLValue, temp: TempId, replacement: &HirExpr) {
    if let HirLValue::TableAccess(access) = lvalue {
        replace_temp_in_expr(&mut access.base, temp, replacement);
        replace_temp_in_expr(&mut access.key, temp, replacement);
    }
}

fn replace_temps_in_lvalue(
    lvalue: &mut HirLValue,
    replacements: &BTreeMap<TempId, HirExpr>,
) -> usize {
    if let HirLValue::TableAccess(access) = lvalue {
        replace_temps_in_expr(&mut access.base, replacements)
            + replace_temps_in_expr(&mut access.key, replacements)
    } else {
        0
    }
}
