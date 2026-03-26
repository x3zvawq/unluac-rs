//! 受阈值约束的保守表达式内联。
//!
//! 这里只处理非常窄的一类模式：
//! - 单值 temp 赋值
//! - 后续只使用一次
//! - 使用点出现在 return / 调用参数 / 索引位
//! - 被内联表达式必须是我们能证明“纯且无元方法副作用”的安全子集

use crate::hir::TempId;
use crate::readability::ReadabilityOptions;

use super::super::common::{
    AstAssign, AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstGlobalDecl,
    AstLValue, AstLocalAttr, AstLocalDecl, AstModule, AstNameRef, AstStmt, AstTableField,
    AstTableKey,
};
use super::ReadabilityContext;

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let _ = context.target;
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
        let Some(next_stmt) = old_stmts.get(index + 1) else {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        };

        let Some((binding, value)) = inline_candidate(&old_stmts[index]) else {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        };
        if !is_inline_candidate_expr(value) {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        }
        if count_temp_uses_in_stmts(&old_stmts[(index + 1)..], binding) != 1 {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        }

        let mut rewritten_next = next_stmt.clone();
        if !rewrite_stmt_use_sites(&mut rewritten_next, binding, value, options) {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        }

        new_stmts.push(rewritten_next);
        changed = true;
        index += 2;
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
            changed
        }
        AstStmt::While(while_stmt) => rewrite_block(&mut while_stmt.body, options),
        AstStmt::Repeat(repeat_stmt) => rewrite_block(&mut repeat_stmt.body, options),
        AstStmt::NumericFor(numeric_for) => rewrite_block(&mut numeric_for.body, options),
        AstStmt::GenericFor(generic_for) => rewrite_block(&mut generic_for.body, options),
        AstStmt::DoBlock(block) => rewrite_block(block, options),
        AstStmt::FunctionDecl(function_decl) => rewrite_function(&mut function_decl.func, options),
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            rewrite_function(&mut local_function_decl.func, options)
        }
        AstStmt::LocalDecl(_)
        | AstStmt::GlobalDecl(_)
        | AstStmt::Assign(_)
        | AstStmt::CallStmt(_)
        | AstStmt::Return(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_) => false,
    }
}

fn rewrite_function(function: &mut AstFunctionExpr, options: ReadabilityOptions) -> bool {
    rewrite_block(&mut function.body, options)
}

fn inline_candidate(stmt: &AstStmt) -> Option<(TempId, &AstExpr)> {
    match stmt {
        AstStmt::Assign(assign) => inline_candidate_from_assign(assign),
        AstStmt::LocalDecl(local_decl) => inline_candidate_from_local_decl(local_decl),
        _ => None,
    }
}

fn inline_candidate_from_assign(assign: &AstAssign) -> Option<(TempId, &AstExpr)> {
    let [AstLValue::Name(AstNameRef::Temp(temp))] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.as_slice() else {
        return None;
    };
    Some((*temp, value))
}

fn inline_candidate_from_local_decl(local_decl: &AstLocalDecl) -> Option<(TempId, &AstExpr)> {
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [value] = local_decl.values.as_slice() else {
        return None;
    };
    if binding.attr != AstLocalAttr::None {
        return None;
    }
    let AstBindingRef::Temp(temp) = binding.id else {
        return None;
    };
    Some((temp, value))
}

fn rewrite_stmt_use_sites(
    stmt: &mut AstStmt,
    binding: TempId,
    replacement: &AstExpr,
    options: ReadabilityOptions,
) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => rewrite_expr_list_context(
            &mut local_decl.values,
            binding,
            replacement,
            InlineSite::Neutral,
            options,
        ),
        AstStmt::GlobalDecl(global_decl) => {
            rewrite_global_decl_use_sites(global_decl, binding, replacement, options)
        }
        AstStmt::Assign(assign) => {
            let mut changed = false;
            for target in &mut assign.targets {
                changed |= rewrite_lvalue_use_sites(target, binding, replacement, options);
            }
            changed |= rewrite_expr_list_context(
                &mut assign.values,
                binding,
                replacement,
                InlineSite::Neutral,
                options,
            );
            changed
        }
        AstStmt::CallStmt(call_stmt) => {
            rewrite_call_use_sites(&mut call_stmt.call, binding, replacement, options)
        }
        AstStmt::Return(ret) => rewrite_expr_list_context(
            &mut ret.values,
            binding,
            replacement,
            InlineSite::ReturnValue,
            options,
        ),
        AstStmt::If(if_stmt) => rewrite_expr_use_sites(
            &mut if_stmt.cond,
            binding,
            replacement,
            InlineSite::Neutral,
            options,
        ),
        AstStmt::While(while_stmt) => rewrite_expr_use_sites(
            &mut while_stmt.cond,
            binding,
            replacement,
            InlineSite::Neutral,
            options,
        ),
        AstStmt::Repeat(repeat_stmt) => rewrite_expr_use_sites(
            &mut repeat_stmt.cond,
            binding,
            replacement,
            InlineSite::Neutral,
            options,
        ),
        AstStmt::NumericFor(numeric_for) => {
            let mut changed = rewrite_expr_use_sites(
                &mut numeric_for.start,
                binding,
                replacement,
                InlineSite::Neutral,
                options,
            );
            changed |= rewrite_expr_use_sites(
                &mut numeric_for.limit,
                binding,
                replacement,
                InlineSite::Neutral,
                options,
            );
            changed |= rewrite_expr_use_sites(
                &mut numeric_for.step,
                binding,
                replacement,
                InlineSite::Neutral,
                options,
            );
            changed
        }
        AstStmt::GenericFor(generic_for) => rewrite_expr_list_context(
            &mut generic_for.iterator,
            binding,
            replacement,
            InlineSite::Neutral,
            options,
        ),
        AstStmt::DoBlock(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_) => false,
    }
}

fn rewrite_global_decl_use_sites(
    global_decl: &mut AstGlobalDecl,
    binding: TempId,
    replacement: &AstExpr,
    options: ReadabilityOptions,
) -> bool {
    rewrite_expr_list_context(
        &mut global_decl.values,
        binding,
        replacement,
        InlineSite::Neutral,
        options,
    )
}

fn rewrite_expr_list_context(
    exprs: &mut [AstExpr],
    binding: TempId,
    replacement: &AstExpr,
    site: InlineSite,
    options: ReadabilityOptions,
) -> bool {
    let mut changed = false;
    for expr in exprs {
        changed |= rewrite_expr_use_sites(expr, binding, replacement, site, options);
    }
    changed
}

fn rewrite_lvalue_use_sites(
    lvalue: &mut AstLValue,
    binding: TempId,
    replacement: &AstExpr,
    options: ReadabilityOptions,
) -> bool {
    match lvalue {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => rewrite_expr_use_sites(
            &mut access.base,
            binding,
            replacement,
            InlineSite::Neutral.descend_access_base(),
            options,
        ),
        AstLValue::IndexAccess(access) => {
            let mut changed = rewrite_expr_use_sites(
                &mut access.base,
                binding,
                replacement,
                InlineSite::Neutral.descend_access_base(),
                options,
            );
            changed |= rewrite_expr_use_sites(
                &mut access.index,
                binding,
                replacement,
                InlineSite::Index,
                options,
            );
            changed
        }
    }
}

fn rewrite_call_use_sites(
    call: &mut AstCallKind,
    binding: TempId,
    replacement: &AstExpr,
    options: ReadabilityOptions,
) -> bool {
    match call {
        AstCallKind::Call(call) => {
            let mut changed = rewrite_expr_use_sites(
                &mut call.callee,
                binding,
                replacement,
                InlineSite::Neutral,
                options,
            );
            changed |= rewrite_expr_list_context(
                &mut call.args,
                binding,
                replacement,
                InlineSite::CallArg,
                options,
            );
            changed
        }
        AstCallKind::MethodCall(call) => {
            let mut changed = rewrite_expr_use_sites(
                &mut call.receiver,
                binding,
                replacement,
                InlineSite::Neutral,
                options,
            );
            changed |= rewrite_expr_list_context(
                &mut call.args,
                binding,
                replacement,
                InlineSite::CallArg,
                options,
            );
            changed
        }
    }
}

fn rewrite_expr_use_sites(
    expr: &mut AstExpr,
    binding: TempId,
    replacement: &AstExpr,
    site: InlineSite,
    options: ReadabilityOptions,
) -> bool {
    if site.allows(binding, expr, replacement, options) {
        *expr = replacement.clone();
        return true;
    }

    match expr {
        AstExpr::FieldAccess(access) => rewrite_expr_use_sites(
            &mut access.base,
            binding,
            replacement,
            site.descend_access_base(),
            options,
        ),
        AstExpr::IndexAccess(access) => {
            let mut changed = rewrite_expr_use_sites(
                &mut access.base,
                binding,
                replacement,
                site.descend_access_base(),
                options,
            );
            changed |= rewrite_expr_use_sites(
                &mut access.index,
                binding,
                replacement,
                InlineSite::Index,
                options,
            );
            changed
        }
        AstExpr::Unary(unary) => rewrite_expr_use_sites(
            &mut unary.expr,
            binding,
            replacement,
            InlineSite::Neutral,
            options,
        ),
        AstExpr::Binary(binary) => {
            let mut changed = rewrite_expr_use_sites(
                &mut binary.lhs,
                binding,
                replacement,
                InlineSite::Neutral,
                options,
            );
            changed |= rewrite_expr_use_sites(
                &mut binary.rhs,
                binding,
                replacement,
                InlineSite::Neutral,
                options,
            );
            changed
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            let mut changed = rewrite_expr_use_sites(
                &mut logical.lhs,
                binding,
                replacement,
                InlineSite::Neutral,
                options,
            );
            changed |= rewrite_expr_use_sites(
                &mut logical.rhs,
                binding,
                replacement,
                InlineSite::Neutral,
                options,
            );
            changed
        }
        AstExpr::Call(call) => {
            let mut changed = rewrite_expr_use_sites(
                &mut call.callee,
                binding,
                replacement,
                InlineSite::Neutral,
                options,
            );
            changed |= rewrite_expr_list_context(
                &mut call.args,
                binding,
                replacement,
                InlineSite::CallArg,
                options,
            );
            changed
        }
        AstExpr::MethodCall(call) => {
            let mut changed = rewrite_expr_use_sites(
                &mut call.receiver,
                binding,
                replacement,
                InlineSite::Neutral,
                options,
            );
            changed |= rewrite_expr_list_context(
                &mut call.args,
                binding,
                replacement,
                InlineSite::CallArg,
                options,
            );
            changed
        }
        AstExpr::TableConstructor(table) => {
            let mut changed = false;
            for field in &mut table.fields {
                match field {
                    AstTableField::Array(value) => {
                        changed |= rewrite_expr_use_sites(
                            value,
                            binding,
                            replacement,
                            InlineSite::Neutral,
                            options,
                        );
                    }
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &mut record.key {
                            changed |= rewrite_expr_use_sites(
                                key,
                                binding,
                                replacement,
                                InlineSite::Index,
                                options,
                            );
                        }
                        changed |= rewrite_expr_use_sites(
                            &mut record.value,
                            binding,
                            replacement,
                            InlineSite::Neutral,
                            options,
                        );
                    }
                }
            }
            changed
        }
        AstExpr::FunctionExpr(_)
        | AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => false,
    }
}

fn count_temp_uses_in_stmts(stmts: &[AstStmt], binding: TempId) -> usize {
    stmts
        .iter()
        .map(|stmt| count_temp_uses_in_stmt(stmt, binding))
        .sum()
}

fn count_temp_uses_in_stmt(stmt: &AstStmt, binding: TempId) -> usize {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .map(|value| count_temp_uses_in_expr(value, binding))
            .sum(),
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .map(|value| count_temp_uses_in_expr(value, binding))
            .sum(),
        AstStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .map(|target| count_temp_uses_in_lvalue(target, binding))
                .sum::<usize>()
                + assign
                    .values
                    .iter()
                    .map(|value| count_temp_uses_in_expr(value, binding))
                    .sum::<usize>()
        }
        AstStmt::CallStmt(call_stmt) => count_temp_uses_in_call(&call_stmt.call, binding),
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .map(|value| count_temp_uses_in_expr(value, binding))
            .sum(),
        AstStmt::If(if_stmt) => {
            count_temp_uses_in_expr(&if_stmt.cond, binding)
                + count_temp_uses_in_block(&if_stmt.then_block, binding)
                + if_stmt
                    .else_block
                    .as_ref()
                    .map(|else_block| count_temp_uses_in_block(else_block, binding))
                    .unwrap_or(0)
        }
        AstStmt::While(while_stmt) => {
            count_temp_uses_in_expr(&while_stmt.cond, binding)
                + count_temp_uses_in_block(&while_stmt.body, binding)
        }
        AstStmt::Repeat(repeat_stmt) => {
            count_temp_uses_in_block(&repeat_stmt.body, binding)
                + count_temp_uses_in_expr(&repeat_stmt.cond, binding)
        }
        AstStmt::NumericFor(numeric_for) => {
            count_temp_uses_in_expr(&numeric_for.start, binding)
                + count_temp_uses_in_expr(&numeric_for.limit, binding)
                + count_temp_uses_in_expr(&numeric_for.step, binding)
                + count_temp_uses_in_block(&numeric_for.body, binding)
        }
        AstStmt::GenericFor(generic_for) => {
            generic_for
                .iterator
                .iter()
                .map(|expr| count_temp_uses_in_expr(expr, binding))
                .sum::<usize>()
                + count_temp_uses_in_block(&generic_for.body, binding)
        }
        AstStmt::DoBlock(block) => count_temp_uses_in_block(block, binding),
        AstStmt::FunctionDecl(function_decl) => {
            count_temp_uses_in_block(&function_decl.func.body, binding)
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            count_temp_uses_in_block(&local_function_decl.func.body, binding)
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => 0,
    }
}

fn count_temp_uses_in_block(block: &AstBlock, binding: TempId) -> usize {
    block
        .stmts
        .iter()
        .map(|stmt| count_temp_uses_in_stmt(stmt, binding))
        .sum()
}

fn count_temp_uses_in_call(call: &AstCallKind, binding: TempId) -> usize {
    match call {
        AstCallKind::Call(call) => {
            count_temp_uses_in_expr(&call.callee, binding)
                + call
                    .args
                    .iter()
                    .map(|arg| count_temp_uses_in_expr(arg, binding))
                    .sum::<usize>()
        }
        AstCallKind::MethodCall(call) => {
            count_temp_uses_in_expr(&call.receiver, binding)
                + call
                    .args
                    .iter()
                    .map(|arg| count_temp_uses_in_expr(arg, binding))
                    .sum::<usize>()
        }
    }
}

fn count_temp_uses_in_lvalue(target: &AstLValue, binding: TempId) -> usize {
    match target {
        AstLValue::Name(_) => 0,
        AstLValue::FieldAccess(access) => count_temp_uses_in_expr(&access.base, binding),
        AstLValue::IndexAccess(access) => {
            count_temp_uses_in_expr(&access.base, binding)
                + count_temp_uses_in_expr(&access.index, binding)
        }
    }
}

fn count_temp_uses_in_expr(expr: &AstExpr, binding: TempId) -> usize {
    match expr {
        AstExpr::Var(AstNameRef::Temp(temp)) if *temp == binding => 1,
        AstExpr::FieldAccess(access) => count_temp_uses_in_expr(&access.base, binding),
        AstExpr::IndexAccess(access) => {
            count_temp_uses_in_expr(&access.base, binding)
                + count_temp_uses_in_expr(&access.index, binding)
        }
        AstExpr::Unary(unary) => count_temp_uses_in_expr(&unary.expr, binding),
        AstExpr::Binary(binary) => {
            count_temp_uses_in_expr(&binary.lhs, binding)
                + count_temp_uses_in_expr(&binary.rhs, binding)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            count_temp_uses_in_expr(&logical.lhs, binding)
                + count_temp_uses_in_expr(&logical.rhs, binding)
        }
        AstExpr::Call(call) => count_temp_uses_in_call(&AstCallKind::Call(call.clone()), binding),
        AstExpr::MethodCall(call) => {
            count_temp_uses_in_call(&AstCallKind::MethodCall(call.clone()), binding)
        }
        AstExpr::TableConstructor(table) => table
            .fields
            .iter()
            .map(|field| match field {
                AstTableField::Array(value) => count_temp_uses_in_expr(value, binding),
                AstTableField::Record(record) => {
                    let key_count = match &record.key {
                        AstTableKey::Name(_) => 0,
                        AstTableKey::Expr(key) => count_temp_uses_in_expr(key, binding),
                    };
                    key_count + count_temp_uses_in_expr(&record.value, binding)
                }
            })
            .sum(),
        AstExpr::FunctionExpr(function) => count_temp_uses_in_block(&function.body, binding),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => 0,
    }
}

fn is_inline_candidate_expr(expr: &AstExpr) -> bool {
    is_context_safe_expr(expr) || is_access_base_inline_expr(expr)
}

fn is_context_safe_expr(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_) => true,
        AstExpr::Var(
            AstNameRef::Param(_)
            | AstNameRef::Local(_)
            | AstNameRef::Temp(_)
            | AstNameRef::Upvalue(_),
        ) => true,
        AstExpr::Unary(unary) => {
            matches!(unary.op, super::super::common::AstUnaryOpKind::Not)
                && is_context_safe_expr(&unary.expr)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            is_context_safe_expr(&logical.lhs) && is_context_safe_expr(&logical.rhs)
        }
        AstExpr::Var(AstNameRef::Global(_))
        | AstExpr::FieldAccess(_)
        | AstExpr::IndexAccess(_)
        | AstExpr::Binary(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_) => false,
    }
}

fn is_access_base_inline_expr(expr: &AstExpr) -> bool {
    is_atomic_access_base_expr(expr) || is_named_field_chain_expr(expr)
}

fn is_named_field_chain_expr(expr: &AstExpr) -> bool {
    let AstExpr::FieldAccess(access) = expr else {
        return false;
    };
    is_atomic_access_base_expr(&access.base) || is_named_field_chain_expr(&access.base)
}

fn is_atomic_access_base_expr(expr: &AstExpr) -> bool {
    matches!(
        expr,
        AstExpr::Nil
            | AstExpr::Boolean(_)
            | AstExpr::Integer(_)
            | AstExpr::Number(_)
            | AstExpr::String(_)
            | AstExpr::Var(_)
    )
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
                    AstTableField::Array(value) => expr_complexity(value),
                    AstTableField::Record(record) => {
                        let key_cost = match &record.key {
                            AstTableKey::Name(_) => 1,
                            AstTableKey::Expr(key) => expr_complexity(key),
                        };
                        key_cost + expr_complexity(&record.value)
                    }
                })
                .sum::<usize>()
        }
        AstExpr::FunctionExpr(function) => 1 + function.body.stmts.len(),
    }
}

#[derive(Clone, Copy)]
enum InlineSite {
    Neutral,
    ReturnValue,
    Index,
    CallArg,
    AccessBase,
}

impl InlineSite {
    fn allows(
        self,
        binding: TempId,
        use_expr: &AstExpr,
        replacement: &AstExpr,
        options: ReadabilityOptions,
    ) -> bool {
        matches!(use_expr, AstExpr::Var(AstNameRef::Temp(temp)) if *temp == binding)
            && self
                .complexity_limit(options)
                .is_some_and(|limit| expr_complexity(replacement) <= limit)
            && (!matches!(self, Self::AccessBase) || is_access_base_inline_expr(replacement))
    }

    fn complexity_limit(self, options: ReadabilityOptions) -> Option<usize> {
        match self {
            Self::Neutral => None,
            Self::ReturnValue => Some(options.return_inline_max_complexity),
            Self::Index => Some(options.index_inline_max_complexity),
            Self::CallArg => Some(options.args_inline_max_complexity),
            Self::AccessBase => Some(options.access_base_inline_max_complexity),
        }
    }

    fn descend_access_base(self) -> Self {
        match self {
            Self::Neutral => Self::AccessBase,
            Self::ReturnValue | Self::Index | Self::CallArg | Self::AccessBase => Self::Neutral,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::common::{
        AstCallExpr, AstFieldAccess, AstIndexAccess, AstLocalBinding, AstMethodCallExpr, AstReturn,
    };
    use crate::ast::{
        AstBinaryExpr, AstBinaryOpKind, AstCallKind, AstExpr, AstLValue, AstLocalAttr, AstModule,
        AstNameRef, AstStmt, AstTargetDialect, AstUnaryExpr, AstUnaryOpKind,
    };
    use crate::hir::{LocalId, TempId};

    use crate::readability::ReadabilityOptions;

    use super::{ReadabilityContext, apply};

    #[test]
    fn inlines_safe_expr_into_single_return_within_threshold() {
        let temp = TempId(0);
        let local = LocalId(0);
        let module = AstModule {
            body: crate::ast::AstBlock {
                stmts: vec![
                    AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: crate::ast::AstBindingRef::Temp(temp),
                            attr: AstLocalAttr::None,
                        }],
                        values: Vec::new(),
                    })),
                    AstStmt::Assign(Box::new(crate::ast::AstAssign {
                        targets: vec![AstLValue::Name(AstNameRef::Temp(temp))],
                        values: vec![AstExpr::Unary(Box::new(AstUnaryExpr {
                            op: AstUnaryOpKind::Not,
                            expr: AstExpr::Var(AstNameRef::Local(local)),
                        }))],
                    })),
                    AstStmt::Return(Box::new(AstReturn {
                        values: vec![AstExpr::Var(AstNameRef::Temp(temp))],
                    })),
                ],
            },
        };

        let module = crate::ast::make_readable_with_options(
            &module,
            AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            ReadabilityOptions::default(),
        );
        assert_eq!(
            module.body.stmts,
            vec![AstStmt::Return(Box::new(AstReturn {
                values: vec![AstExpr::Unary(Box::new(AstUnaryExpr {
                    op: AstUnaryOpKind::Not,
                    expr: AstExpr::Var(AstNameRef::Local(local)),
                }))],
            }))]
        );
    }

    #[test]
    fn does_not_inline_call_arg_when_expr_exceeds_arg_threshold() {
        let temp = TempId(0);
        let lhs = LocalId(0);
        let rhs = LocalId(1);
        let mut module = AstModule {
            body: crate::ast::AstBlock {
                stmts: vec![
                    AstStmt::Assign(Box::new(crate::ast::AstAssign {
                        targets: vec![AstLValue::Name(AstNameRef::Temp(temp))],
                        values: vec![AstExpr::LogicalAnd(Box::new(crate::ast::AstLogicalExpr {
                            lhs: AstExpr::Unary(Box::new(AstUnaryExpr {
                                op: AstUnaryOpKind::Not,
                                expr: AstExpr::Var(AstNameRef::Local(lhs)),
                            })),
                            rhs: AstExpr::Unary(Box::new(AstUnaryExpr {
                                op: AstUnaryOpKind::Not,
                                expr: AstExpr::Var(AstNameRef::Local(rhs)),
                            })),
                        }))],
                    })),
                    AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                        call: AstCallKind::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Var(AstNameRef::Local(LocalId(2))),
                            args: vec![AstExpr::Var(AstNameRef::Temp(temp))],
                        })),
                    })),
                ],
            },
        };

        assert!(!apply(
            &mut module,
            ReadabilityContext {
                target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
                options: ReadabilityOptions {
                    args_inline_max_complexity: 3,
                    ..ReadabilityOptions::default()
                },
            }
        ));
    }

    #[test]
    fn inlines_temp_into_index_slot_with_custom_threshold() {
        let temp = TempId(0);
        let base = LocalId(0);
        let lhs = LocalId(1);
        let rhs = LocalId(2);
        let mut module = AstModule {
            body: crate::ast::AstBlock {
                stmts: vec![
                    AstStmt::Assign(Box::new(crate::ast::AstAssign {
                        targets: vec![AstLValue::Name(AstNameRef::Temp(temp))],
                        values: vec![AstExpr::LogicalOr(Box::new(crate::ast::AstLogicalExpr {
                            lhs: AstExpr::Unary(Box::new(AstUnaryExpr {
                                op: AstUnaryOpKind::Not,
                                expr: AstExpr::Var(AstNameRef::Local(lhs)),
                            })),
                            rhs: AstExpr::Var(AstNameRef::Local(rhs)),
                        }))],
                    })),
                    AstStmt::Return(Box::new(AstReturn {
                        values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                            base: AstExpr::Var(AstNameRef::Local(base)),
                            index: AstExpr::Var(AstNameRef::Temp(temp)),
                        }))],
                    })),
                ],
            },
        };

        assert!(apply(
            &mut module,
            ReadabilityContext {
                target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
                options: ReadabilityOptions {
                    index_inline_max_complexity: 4,
                    ..ReadabilityOptions::default()
                },
            }
        ));
        assert_eq!(
            module.body.stmts,
            vec![AstStmt::Return(Box::new(AstReturn {
                values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                    base: AstExpr::Var(AstNameRef::Local(base)),
                    index: AstExpr::LogicalOr(Box::new(crate::ast::AstLogicalExpr {
                        lhs: AstExpr::Unary(Box::new(AstUnaryExpr {
                            op: AstUnaryOpKind::Not,
                            expr: AstExpr::Var(AstNameRef::Local(lhs)),
                        })),
                        rhs: AstExpr::Var(AstNameRef::Local(rhs)),
                    })),
                }))],
            }))]
        );
    }

    #[test]
    fn does_not_inline_expr_with_potential_runtime_behavior_changes() {
        let temp = TempId(0);
        let mut module = AstModule {
            body: crate::ast::AstBlock {
                stmts: vec![
                    AstStmt::Assign(Box::new(crate::ast::AstAssign {
                        targets: vec![AstLValue::Name(AstNameRef::Temp(temp))],
                        values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                            op: AstBinaryOpKind::Add,
                            lhs: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                            rhs: AstExpr::Integer(1),
                        }))],
                    })),
                    AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                        call: AstCallKind::MethodCall(Box::new(AstMethodCallExpr {
                            receiver: AstExpr::Var(AstNameRef::Local(LocalId(1))),
                            method: "push".to_owned(),
                            args: vec![AstExpr::Var(AstNameRef::Temp(temp))],
                        })),
                    })),
                ],
            },
        };

        assert!(!apply(
            &mut module,
            ReadabilityContext {
                target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
                options: ReadabilityOptions {
                    args_inline_max_complexity: usize::MAX,
                    ..ReadabilityOptions::default()
                },
            }
        ));
    }

    #[test]
    fn inlines_named_field_access_base_into_adjacent_index_assign() {
        let root = LocalId(0);
        let first = TempId(0);
        let second = TempId(1);
        let mut module = AstModule {
            body: crate::ast::AstBlock {
                stmts: vec![
                    AstStmt::Assign(Box::new(crate::ast::AstAssign {
                        targets: vec![AstLValue::Name(AstNameRef::Temp(first))],
                        values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                            base: AstExpr::Var(AstNameRef::Local(root)),
                            field: "branches".to_owned(),
                        }))],
                    })),
                    AstStmt::Assign(Box::new(crate::ast::AstAssign {
                        targets: vec![AstLValue::Name(AstNameRef::Temp(second))],
                        values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                            base: AstExpr::Var(AstNameRef::Temp(first)),
                            index: AstExpr::String("picked".to_owned()),
                        }))],
                    })),
                    AstStmt::Return(Box::new(AstReturn {
                        values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                            base: AstExpr::Var(AstNameRef::Temp(second)),
                            field: "value".to_owned(),
                        }))],
                    })),
                ],
            },
        };

        assert!(apply(
            &mut module,
            ReadabilityContext {
                target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
                options: ReadabilityOptions {
                    access_base_inline_max_complexity: 5,
                    ..ReadabilityOptions::default()
                },
            }
        ));
        assert_eq!(
            module.body.stmts,
            vec![
                AstStmt::Assign(Box::new(crate::ast::AstAssign {
                    targets: vec![AstLValue::Name(AstNameRef::Temp(second))],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                            base: AstExpr::Var(AstNameRef::Local(root)),
                            field: "branches".to_owned(),
                        })),
                        index: AstExpr::String("picked".to_owned()),
                    }))],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Temp(second)),
                        field: "value".to_owned(),
                    }))],
                })),
            ]
        );
    }
}
