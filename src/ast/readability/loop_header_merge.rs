//! 这个 pass 负责把“紧邻 loop header 的机械 local alias run”收回控制头。
//!
//! 常见形状是：
//! `local start = 1; local limit = #list; local step = 1; for i = start, limit, step do`
//! 这些 local 往往只是前层为了保持单值边界而提前物化的中间 binding。
//! 当它们只在 loop header 被读取时，把它们重新折回控制头会更接近源码。

use crate::readability::ReadabilityOptions;

use super::super::common::{
    AstBlock, AstExpr, AstLocalAttr, AstLocalOrigin, AstModule, AstNameRef, AstStmt,
};
use super::ReadabilityContext;
use super::binding_flow::{count_binding_uses_in_stmt, count_binding_uses_in_stmts};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    rewrite_block(&mut module.body, context.options)
}

fn rewrite_block(block: &mut AstBlock, options: ReadabilityOptions) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        changed |= rewrite_nested(stmt, options);
    }

    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut index = 0;
    while index < old_stmts.len() {
        let mut run_end = index;
        while run_end < old_stmts.len() && loop_header_candidate(&old_stmts[run_end]).is_some() {
            run_end += 1;
        }

        if run_end == index || run_end >= old_stmts.len() {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        }

        let mut rewritten_loop = old_stmts[run_end].clone();
        let mut removed = vec![false; run_end - index];
        let mut collapsed_count = 0usize;

        for candidate_index in (index..run_end).rev() {
            let Some((binding, value)) = loop_header_candidate(&old_stmts[candidate_index]) else {
                continue;
            };
            if !is_loop_header_inline_expr(value, options) {
                continue;
            }
            if count_binding_uses_in_stmts(
                &old_stmts[(candidate_index + 1)..(run_end + 1)],
                binding.id,
            ) != 1
            {
                continue;
            }
            if count_binding_uses_in_stmts(&old_stmts[(run_end + 1)..], binding.id) != 0 {
                continue;
            }
            if count_binding_uses_in_stmts(&old_stmts[(candidate_index + 1)..run_end], binding.id)
                != 0
            {
                continue;
            }
            if !header_uses_binding_exactly_once(&rewritten_loop, binding.id) {
                continue;
            }

            let mut trial_loop = rewritten_loop.clone();
            if rewrite_loop_header_binding(&mut trial_loop, binding.id, value) {
                rewritten_loop = trial_loop;
                removed[candidate_index - index] = true;
                collapsed_count += 1;
            }
        }

        if collapsed_count >= 2 {
            changed = true;
            for (offset, stmt) in old_stmts[index..run_end].iter().enumerate() {
                if !removed[offset] {
                    new_stmts.push(stmt.clone());
                }
            }
            new_stmts.push(rewritten_loop);
            index = run_end + 1;
            continue;
        }

        new_stmts.push(old_stmts[index].clone());
        index += 1;
    }

    block.stmts = new_stmts;
    changed
}

fn rewrite_nested(stmt: &mut AstStmt, options: ReadabilityOptions) -> bool {
    match stmt {
        AstStmt::If(if_stmt) => {
            let mut changed = rewrite_block(&mut if_stmt.then_block, options);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= rewrite_block(else_block, options);
            }
            rewrite_nested_functions_in_expr(&mut if_stmt.cond, options) | changed
        }
        AstStmt::While(while_stmt) => {
            rewrite_nested_functions_in_expr(&mut while_stmt.cond, options)
                | rewrite_block(&mut while_stmt.body, options)
        }
        AstStmt::Repeat(repeat_stmt) => {
            rewrite_block(&mut repeat_stmt.body, options)
                | rewrite_nested_functions_in_expr(&mut repeat_stmt.cond, options)
        }
        AstStmt::NumericFor(numeric_for) => {
            let mut changed = rewrite_nested_functions_in_expr(&mut numeric_for.start, options);
            changed |= rewrite_nested_functions_in_expr(&mut numeric_for.limit, options);
            changed |= rewrite_nested_functions_in_expr(&mut numeric_for.step, options);
            changed | rewrite_block(&mut numeric_for.body, options)
        }
        AstStmt::GenericFor(generic_for) => {
            let mut changed = false;
            for expr in &mut generic_for.iterator {
                changed |= rewrite_nested_functions_in_expr(expr, options);
            }
            changed | rewrite_block(&mut generic_for.body, options)
        }
        AstStmt::DoBlock(block) => rewrite_block(block, options),
        AstStmt::FunctionDecl(function_decl) => {
            rewrite_block(&mut function_decl.func.body, options)
        }
        AstStmt::LocalFunctionDecl(function_decl) => {
            rewrite_block(&mut function_decl.func.body, options)
        }
        AstStmt::LocalDecl(local_decl) => {
            local_decl.values.iter_mut().fold(false, |changed, expr| {
                rewrite_nested_functions_in_expr(expr, options) | changed
            })
        }
        AstStmt::GlobalDecl(global_decl) => {
            global_decl.values.iter_mut().fold(false, |changed, expr| {
                rewrite_nested_functions_in_expr(expr, options) | changed
            })
        }
        AstStmt::Assign(assign) => {
            let mut changed = false;
            for target in &mut assign.targets {
                changed |= rewrite_nested_functions_in_lvalue(target, options);
            }
            for value in &mut assign.values {
                changed |= rewrite_nested_functions_in_expr(value, options);
            }
            changed
        }
        AstStmt::CallStmt(call_stmt) => {
            rewrite_nested_functions_in_call(&mut call_stmt.call, options)
        }
        AstStmt::Return(ret) => ret.values.iter_mut().fold(false, |changed, expr| {
            rewrite_nested_functions_in_expr(expr, options) | changed
        }),
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => false,
    }
}

fn rewrite_nested_functions_in_call(
    call: &mut super::super::common::AstCallKind,
    options: ReadabilityOptions,
) -> bool {
    match call {
        super::super::common::AstCallKind::Call(call) => {
            let mut changed = rewrite_nested_functions_in_expr(&mut call.callee, options);
            for arg in &mut call.args {
                changed |= rewrite_nested_functions_in_expr(arg, options);
            }
            changed
        }
        super::super::common::AstCallKind::MethodCall(call) => {
            let mut changed = rewrite_nested_functions_in_expr(&mut call.receiver, options);
            for arg in &mut call.args {
                changed |= rewrite_nested_functions_in_expr(arg, options);
            }
            changed
        }
    }
}

fn rewrite_nested_functions_in_lvalue(
    lvalue: &mut super::super::common::AstLValue,
    options: ReadabilityOptions,
) -> bool {
    match lvalue {
        super::super::common::AstLValue::Name(_) => false,
        super::super::common::AstLValue::FieldAccess(access) => {
            rewrite_nested_functions_in_expr(&mut access.base, options)
        }
        super::super::common::AstLValue::IndexAccess(access) => {
            rewrite_nested_functions_in_expr(&mut access.base, options)
                | rewrite_nested_functions_in_expr(&mut access.index, options)
        }
    }
}

fn rewrite_nested_functions_in_expr(expr: &mut AstExpr, options: ReadabilityOptions) -> bool {
    match expr {
        AstExpr::FieldAccess(access) => rewrite_nested_functions_in_expr(&mut access.base, options),
        AstExpr::IndexAccess(access) => {
            rewrite_nested_functions_in_expr(&mut access.base, options)
                | rewrite_nested_functions_in_expr(&mut access.index, options)
        }
        AstExpr::Unary(unary) => rewrite_nested_functions_in_expr(&mut unary.expr, options),
        AstExpr::Binary(binary) => {
            rewrite_nested_functions_in_expr(&mut binary.lhs, options)
                | rewrite_nested_functions_in_expr(&mut binary.rhs, options)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            rewrite_nested_functions_in_expr(&mut logical.lhs, options)
                | rewrite_nested_functions_in_expr(&mut logical.rhs, options)
        }
        AstExpr::Call(call) => {
            let mut changed = rewrite_nested_functions_in_expr(&mut call.callee, options);
            for arg in &mut call.args {
                changed |= rewrite_nested_functions_in_expr(arg, options);
            }
            changed
        }
        AstExpr::MethodCall(call) => {
            let mut changed = rewrite_nested_functions_in_expr(&mut call.receiver, options);
            for arg in &mut call.args {
                changed |= rewrite_nested_functions_in_expr(arg, options);
            }
            changed
        }
        AstExpr::TableConstructor(table) => {
            let mut changed = false;
            for field in &mut table.fields {
                changed |= match field {
                    super::super::common::AstTableField::Array(value) => {
                        rewrite_nested_functions_in_expr(value, options)
                    }
                    super::super::common::AstTableField::Record(record) => {
                        let key_changed = match &mut record.key {
                            super::super::common::AstTableKey::Name(_) => false,
                            super::super::common::AstTableKey::Expr(key) => {
                                rewrite_nested_functions_in_expr(key, options)
                            }
                        };
                        key_changed | rewrite_nested_functions_in_expr(&mut record.value, options)
                    }
                };
            }
            changed
        }
        AstExpr::FunctionExpr(function) => rewrite_block(&mut function.body, options),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => false,
    }
}

fn loop_header_candidate(
    stmt: &AstStmt,
) -> Option<(&super::super::common::AstLocalBinding, &AstExpr)> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [value] = local_decl.values.as_slice() else {
        return None;
    };
    if binding.attr != AstLocalAttr::None || binding.origin != AstLocalOrigin::Recovered {
        return None;
    }
    Some((binding, value))
}

fn is_loop_header_inline_expr(expr: &AstExpr, options: ReadabilityOptions) -> bool {
    expr_complexity(expr) <= options.return_inline_max_complexity
        && !matches!(
            expr,
            AstExpr::VarArg | AstExpr::TableConstructor(_) | AstExpr::FunctionExpr(_)
        )
}

fn header_uses_binding_exactly_once(
    stmt: &AstStmt,
    binding: super::super::common::AstBindingRef,
) -> bool {
    count_binding_uses_in_loop_header(stmt, binding) == 1
        && count_binding_uses_in_stmt(stmt, binding) == 1
}

fn rewrite_loop_header_binding(
    stmt: &mut AstStmt,
    binding: super::super::common::AstBindingRef,
    replacement: &AstExpr,
) -> bool {
    match stmt {
        AstStmt::NumericFor(numeric_for) => {
            let mut changed = replace_exact_name_expr(&mut numeric_for.start, binding, replacement);
            changed |= replace_exact_name_expr(&mut numeric_for.limit, binding, replacement);
            changed |= replace_exact_name_expr(&mut numeric_for.step, binding, replacement);
            changed
        }
        AstStmt::GenericFor(generic_for) => generic_for
            .iterator
            .iter_mut()
            .fold(false, |changed, expr| {
                replace_exact_name_expr(expr, binding, replacement) || changed
            }),
        _ => false,
    }
}

fn count_binding_uses_in_loop_header(
    stmt: &AstStmt,
    binding: super::super::common::AstBindingRef,
) -> usize {
    match stmt {
        AstStmt::NumericFor(numeric_for) => {
            count_name_expr_uses(&numeric_for.start, binding)
                + count_name_expr_uses(&numeric_for.limit, binding)
                + count_name_expr_uses(&numeric_for.step, binding)
        }
        AstStmt::GenericFor(generic_for) => generic_for
            .iterator
            .iter()
            .map(|expr| count_name_expr_uses(expr, binding))
            .sum(),
        _ => 0,
    }
}

fn replace_exact_name_expr(
    expr: &mut AstExpr,
    binding: super::super::common::AstBindingRef,
    replacement: &AstExpr,
) -> bool {
    if matches!(expr, AstExpr::Var(name) if name_matches_binding(name, binding)) {
        *expr = replacement.clone();
        true
    } else {
        false
    }
}

fn count_name_expr_uses(expr: &AstExpr, binding: super::super::common::AstBindingRef) -> usize {
    match expr {
        AstExpr::Var(name) if name_matches_binding(name, binding) => 1,
        _ => 0,
    }
}

fn expr_complexity(expr: &AstExpr) -> usize {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => 1,
        AstExpr::Unary(unary) => 1 + expr_complexity(&unary.expr),
        AstExpr::Binary(binary) => 1 + expr_complexity(&binary.lhs) + expr_complexity(&binary.rhs),
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            1 + expr_complexity(&logical.lhs) + expr_complexity(&logical.rhs)
        }
        AstExpr::FieldAccess(access) => 1 + expr_complexity(&access.base),
        AstExpr::IndexAccess(access) => {
            1 + expr_complexity(&access.base) + expr_complexity(&access.index)
        }
        AstExpr::Call(call) => {
            1 + expr_complexity(&call.callee) + call.args.iter().map(expr_complexity).sum::<usize>()
        }
        AstExpr::MethodCall(call) => {
            1 + expr_complexity(&call.receiver)
                + call.args.iter().map(expr_complexity).sum::<usize>()
        }
        AstExpr::TableConstructor(table) => {
            1 + table
                .fields
                .iter()
                .map(|field| match field {
                    super::super::common::AstTableField::Array(value) => expr_complexity(value),
                    super::super::common::AstTableField::Record(record) => {
                        let key_cost = match &record.key {
                            super::super::common::AstTableKey::Name(_) => 1,
                            super::super::common::AstTableKey::Expr(key) => expr_complexity(key),
                        };
                        key_cost + expr_complexity(&record.value)
                    }
                })
                .sum::<usize>()
        }
        AstExpr::FunctionExpr(function) => 1 + function.body.stmts.len(),
    }
}

fn name_matches_binding(name: &AstNameRef, binding: super::super::common::AstBindingRef) -> bool {
    match (binding, name) {
        (super::super::common::AstBindingRef::Local(local), AstNameRef::Local(target)) => {
            local == *target
        }
        (super::super::common::AstBindingRef::Temp(temp), AstNameRef::Temp(target)) => {
            temp == *target
        }
        (
            super::super::common::AstBindingRef::SyntheticLocal(local),
            AstNameRef::SyntheticLocal(target),
        ) => local == *target,
        _ => false,
    }
}

#[cfg(test)]
mod tests;
