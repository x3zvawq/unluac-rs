//! 受阈值约束的保守表达式内联。
//!
//! 这里只处理非常窄的一类模式：
//! - 单值 temp / local 别名
//! - 后续只使用一次
//! - 使用点出现在 return / 调用参数 / 索引位 / 调用目标
//! - 被内联表达式必须是我们能证明“纯且无元方法副作用”的安全子集

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

        let Some((candidate, value)) = inline_candidate(&old_stmts[index]) else {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        };
        if !candidate.allows_expr(value) {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        }
        if count_binding_uses_in_stmts(&old_stmts[(index + 1)..], candidate.binding()) != 1 {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        }

        let mut rewritten_next = next_stmt.clone();
        if !rewrite_stmt_use_sites(&mut rewritten_next, candidate, value, options) {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        }

        new_stmts.push(rewritten_next);
        changed = true;
        index += 2;
    }

    block.stmts = new_stmts;
    changed |= collapse_adjacent_call_alias_runs(block, options);
    changed
}

fn collapse_adjacent_call_alias_runs(block: &mut AstBlock, options: ReadabilityOptions) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while index < old_stmts.len() {
        let mut run_end = index;
        while run_end < old_stmts.len() && inline_candidate(&old_stmts[run_end]).is_some() {
            run_end += 1;
        }

        if run_end == index
            || run_end >= old_stmts.len()
            || !matches!(old_stmts[run_end], AstStmt::CallStmt(_))
        {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        }

        let mut rewritten_sink = old_stmts[run_end].clone();
        let mut removed = vec![false; run_end - index];
        let mut collapsed_count = 0usize;

        for candidate_index in (index..run_end).rev() {
            let Some((candidate, value)) = inline_candidate(&old_stmts[candidate_index]) else {
                continue;
            };
            if !matches!(candidate, InlineCandidate::LocalAlias(_)) {
                continue;
            }
            if count_binding_uses_in_stmts(
                &old_stmts[(candidate_index + 1)..(run_end + 1)],
                candidate.binding(),
            ) != 1
            {
                continue;
            }
            if count_binding_uses_in_stmts(
                &old_stmts[(candidate_index + 1)..run_end],
                candidate.binding(),
            ) != 0
            {
                continue;
            }

            let mut trial_sink = rewritten_sink.clone();
            if rewrite_stmt_use_sites_with_policy(
                &mut trial_sink,
                candidate,
                value,
                options,
                InlinePolicy::ExtendedCallChain,
            ) {
                rewritten_sink = trial_sink;
                removed[candidate_index - index] = true;
                collapsed_count += 1;
            }
        }

        // 这里只折叠真正的“局部别名包”：
        // 至少一次收回两层相邻别名，才能证明我们是在还原机械展开的调用准备序列，
        // 而不是把源码里本来就有阶段语义的 local（例如 stage1 / stage2）继续吞掉。
        if collapsed_count >= 2 {
            changed = true;
            for (offset, stmt) in old_stmts[index..run_end].iter().enumerate() {
                if !removed[offset] {
                    new_stmts.push(stmt.clone());
                }
            }
            new_stmts.push(rewritten_sink);
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
            let mut changed = rewrite_nested_functions_in_expr(&mut if_stmt.cond, options);
            changed |= rewrite_block(&mut if_stmt.then_block, options);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= rewrite_block(else_block, options);
            }
            changed
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
            changed |= rewrite_block(&mut numeric_for.body, options);
            changed
        }
        AstStmt::GenericFor(generic_for) => {
            let mut changed = false;
            for expr in &mut generic_for.iterator {
                changed |= rewrite_nested_functions_in_expr(expr, options);
            }
            changed |= rewrite_block(&mut generic_for.body, options);
            changed
        }
        AstStmt::DoBlock(block) => rewrite_block(block, options),
        AstStmt::FunctionDecl(function_decl) => rewrite_function(&mut function_decl.func, options),
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            rewrite_function(&mut local_function_decl.func, options)
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

fn rewrite_function(function: &mut AstFunctionExpr, options: ReadabilityOptions) -> bool {
    rewrite_block(&mut function.body, options)
}

fn rewrite_nested_functions_in_call(call: &mut AstCallKind, options: ReadabilityOptions) -> bool {
    match call {
        AstCallKind::Call(call) => {
            let mut changed = rewrite_nested_functions_in_expr(&mut call.callee, options);
            for arg in &mut call.args {
                changed |= rewrite_nested_functions_in_expr(arg, options);
            }
            changed
        }
        AstCallKind::MethodCall(call) => {
            let mut changed = rewrite_nested_functions_in_expr(&mut call.receiver, options);
            for arg in &mut call.args {
                changed |= rewrite_nested_functions_in_expr(arg, options);
            }
            changed
        }
    }
}

fn rewrite_nested_functions_in_lvalue(lvalue: &mut AstLValue, options: ReadabilityOptions) -> bool {
    match lvalue {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => {
            rewrite_nested_functions_in_expr(&mut access.base, options)
        }
        AstLValue::IndexAccess(access) => {
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
                match field {
                    AstTableField::Array(value) => {
                        changed |= rewrite_nested_functions_in_expr(value, options);
                    }
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &mut record.key {
                            changed |= rewrite_nested_functions_in_expr(key, options);
                        }
                        changed |= rewrite_nested_functions_in_expr(&mut record.value, options);
                    }
                }
            }
            changed
        }
        // 这里必须显式钻进函数表达式体：
        // expr-inline 阶段早于 function-sugar，很多源码里的 `local function`
        // 这时仍是 `local x = function() ... end`，如果不进这里，整个函数体都会错过内联。
        AstExpr::FunctionExpr(function) => rewrite_function(function, options),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => false,
    }
}

fn inline_candidate(stmt: &AstStmt) -> Option<(InlineCandidate, &AstExpr)> {
    match stmt {
        AstStmt::Assign(assign) => inline_candidate_from_assign(assign),
        AstStmt::LocalDecl(local_decl) => inline_candidate_from_local_decl(local_decl),
        _ => None,
    }
}

fn inline_candidate_from_assign(assign: &AstAssign) -> Option<(InlineCandidate, &AstExpr)> {
    let [AstLValue::Name(AstNameRef::Temp(temp))] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.as_slice() else {
        return None;
    };
    Some((InlineCandidate::TempLike(AstBindingRef::Temp(*temp)), value))
}

fn inline_candidate_from_local_decl(
    local_decl: &AstLocalDecl,
) -> Option<(InlineCandidate, &AstExpr)> {
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [value] = local_decl.values.as_slice() else {
        return None;
    };
    if binding.attr != AstLocalAttr::None {
        return None;
    }
    let candidate = match binding.id {
        AstBindingRef::Temp(_) => InlineCandidate::TempLike(binding.id),
        AstBindingRef::Local(_) | AstBindingRef::SyntheticLocal(_) => {
            InlineCandidate::LocalAlias(binding.id)
        }
    };
    Some((candidate, value))
}

fn rewrite_stmt_use_sites(
    stmt: &mut AstStmt,
    candidate: InlineCandidate,
    replacement: &AstExpr,
    options: ReadabilityOptions,
) -> bool {
    rewrite_stmt_use_sites_with_policy(
        stmt,
        candidate,
        replacement,
        options,
        InlinePolicy::Conservative,
    )
}

fn rewrite_stmt_use_sites_with_policy(
    stmt: &mut AstStmt,
    candidate: InlineCandidate,
    replacement: &AstExpr,
    options: ReadabilityOptions,
    policy: InlinePolicy,
) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => rewrite_expr_list_context(
            &mut local_decl.values,
            candidate,
            replacement,
            InlineSite::Neutral,
            options,
            policy,
        ),
        AstStmt::GlobalDecl(global_decl) => {
            rewrite_global_decl_use_sites(global_decl, candidate, replacement, options, policy)
        }
        AstStmt::Assign(assign) => {
            let mut changed = false;
            for target in &mut assign.targets {
                changed |=
                    rewrite_lvalue_use_sites(target, candidate, replacement, options, policy);
            }
            changed |= rewrite_expr_list_context(
                &mut assign.values,
                candidate,
                replacement,
                InlineSite::Neutral,
                options,
                policy,
            );
            changed
        }
        AstStmt::CallStmt(call_stmt) => {
            rewrite_call_use_sites(&mut call_stmt.call, candidate, replacement, options, policy)
        }
        AstStmt::Return(ret) => rewrite_expr_list_context(
            &mut ret.values,
            candidate,
            replacement,
            InlineSite::ReturnValue,
            options,
            policy,
        ),
        AstStmt::If(if_stmt) => rewrite_expr_use_sites(
            &mut if_stmt.cond,
            candidate,
            replacement,
            InlineSite::Neutral,
            options,
            policy,
        ),
        AstStmt::While(while_stmt) => rewrite_expr_use_sites(
            &mut while_stmt.cond,
            candidate,
            replacement,
            InlineSite::Neutral,
            options,
            policy,
        ),
        AstStmt::Repeat(repeat_stmt) => rewrite_expr_use_sites(
            &mut repeat_stmt.cond,
            candidate,
            replacement,
            InlineSite::Neutral,
            options,
            policy,
        ),
        AstStmt::NumericFor(numeric_for) => {
            let mut changed = rewrite_expr_use_sites(
                &mut numeric_for.start,
                candidate,
                replacement,
                InlineSite::Neutral,
                options,
                policy,
            );
            changed |= rewrite_expr_use_sites(
                &mut numeric_for.limit,
                candidate,
                replacement,
                InlineSite::Neutral,
                options,
                policy,
            );
            changed |= rewrite_expr_use_sites(
                &mut numeric_for.step,
                candidate,
                replacement,
                InlineSite::Neutral,
                options,
                policy,
            );
            changed
        }
        AstStmt::GenericFor(generic_for) => rewrite_expr_list_context(
            &mut generic_for.iterator,
            candidate,
            replacement,
            InlineSite::Neutral,
            options,
            policy,
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
    candidate: InlineCandidate,
    replacement: &AstExpr,
    options: ReadabilityOptions,
    policy: InlinePolicy,
) -> bool {
    rewrite_expr_list_context(
        &mut global_decl.values,
        candidate,
        replacement,
        InlineSite::Neutral,
        options,
        policy,
    )
}

fn rewrite_expr_list_context(
    exprs: &mut [AstExpr],
    candidate: InlineCandidate,
    replacement: &AstExpr,
    site: InlineSite,
    options: ReadabilityOptions,
    policy: InlinePolicy,
) -> bool {
    let mut changed = false;
    for expr in exprs {
        changed |= rewrite_expr_use_sites(expr, candidate, replacement, site, options, policy);
    }
    changed
}

fn rewrite_lvalue_use_sites(
    lvalue: &mut AstLValue,
    candidate: InlineCandidate,
    replacement: &AstExpr,
    options: ReadabilityOptions,
    policy: InlinePolicy,
) -> bool {
    match lvalue {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => rewrite_expr_use_sites(
            &mut access.base,
            candidate,
            replacement,
            InlineSite::Neutral.descend_access_base(),
            options,
            policy,
        ),
        AstLValue::IndexAccess(access) => {
            let mut changed = rewrite_expr_use_sites(
                &mut access.base,
                candidate,
                replacement,
                InlineSite::Neutral.descend_access_base(),
                options,
                policy,
            );
            changed |= rewrite_expr_use_sites(
                &mut access.index,
                candidate,
                replacement,
                InlineSite::Index,
                options,
                policy,
            );
            changed
        }
    }
}

fn rewrite_call_use_sites(
    call: &mut AstCallKind,
    candidate: InlineCandidate,
    replacement: &AstExpr,
    options: ReadabilityOptions,
    policy: InlinePolicy,
) -> bool {
    match call {
        AstCallKind::Call(call) => {
            let mut changed = rewrite_expr_use_sites(
                &mut call.callee,
                candidate,
                replacement,
                InlineSite::CallCallee,
                options,
                policy,
            );
            changed |= rewrite_expr_list_context(
                &mut call.args,
                candidate,
                replacement,
                InlineSite::CallArg,
                options,
                policy,
            );
            changed
        }
        AstCallKind::MethodCall(call) => {
            let mut changed = rewrite_expr_use_sites(
                &mut call.receiver,
                candidate,
                replacement,
                InlineSite::Neutral,
                options,
                policy,
            );
            changed |= rewrite_expr_list_context(
                &mut call.args,
                candidate,
                replacement,
                InlineSite::CallArg,
                options,
                policy,
            );
            changed
        }
    }
}

fn rewrite_expr_use_sites(
    expr: &mut AstExpr,
    candidate: InlineCandidate,
    replacement: &AstExpr,
    site: InlineSite,
    options: ReadabilityOptions,
    policy: InlinePolicy,
) -> bool {
    if site.allows(candidate, expr, replacement, options, policy) {
        *expr = replacement.clone();
        return true;
    }

    match expr {
        AstExpr::FieldAccess(access) => rewrite_expr_use_sites(
            &mut access.base,
            candidate,
            replacement,
            site.descend_access_base(),
            options,
            policy,
        ),
        AstExpr::IndexAccess(access) => {
            let mut changed = rewrite_expr_use_sites(
                &mut access.base,
                candidate,
                replacement,
                site.descend_access_base(),
                options,
                policy,
            );
            changed |= rewrite_expr_use_sites(
                &mut access.index,
                candidate,
                replacement,
                InlineSite::Index,
                options,
                policy,
            );
            changed
        }
        AstExpr::Unary(unary) => rewrite_expr_use_sites(
            &mut unary.expr,
            candidate,
            replacement,
            InlineSite::Neutral,
            options,
            policy,
        ),
        AstExpr::Binary(binary) => {
            let mut changed = rewrite_expr_use_sites(
                &mut binary.lhs,
                candidate,
                replacement,
                InlineSite::Neutral,
                options,
                policy,
            );
            changed |= rewrite_expr_use_sites(
                &mut binary.rhs,
                candidate,
                replacement,
                InlineSite::Neutral,
                options,
                policy,
            );
            changed
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            let mut changed = rewrite_expr_use_sites(
                &mut logical.lhs,
                candidate,
                replacement,
                InlineSite::Neutral,
                options,
                policy,
            );
            changed |= rewrite_expr_use_sites(
                &mut logical.rhs,
                candidate,
                replacement,
                InlineSite::Neutral,
                options,
                policy,
            );
            changed
        }
        AstExpr::Call(call) => {
            let mut changed = rewrite_expr_use_sites(
                &mut call.callee,
                candidate,
                replacement,
                InlineSite::CallCallee,
                options,
                policy,
            );
            changed |= rewrite_expr_list_context(
                &mut call.args,
                candidate,
                replacement,
                InlineSite::CallArg,
                options,
                policy,
            );
            changed
        }
        AstExpr::MethodCall(call) => {
            let mut changed = rewrite_expr_use_sites(
                &mut call.receiver,
                candidate,
                replacement,
                InlineSite::Neutral,
                options,
                policy,
            );
            changed |= rewrite_expr_list_context(
                &mut call.args,
                candidate,
                replacement,
                InlineSite::CallArg,
                options,
                policy,
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
                            candidate,
                            replacement,
                            InlineSite::Neutral,
                            options,
                            policy,
                        );
                    }
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &mut record.key {
                            changed |= rewrite_expr_use_sites(
                                key,
                                candidate,
                                replacement,
                                InlineSite::Index,
                                options,
                                policy,
                            );
                        }
                        changed |= rewrite_expr_use_sites(
                            &mut record.value,
                            candidate,
                            replacement,
                            InlineSite::Neutral,
                            options,
                            policy,
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

fn count_binding_uses_in_stmts(stmts: &[AstStmt], binding: AstBindingRef) -> usize {
    stmts
        .iter()
        .map(|stmt| count_binding_uses_in_stmt(stmt, binding))
        .sum()
}

fn count_binding_uses_in_stmt(stmt: &AstStmt, binding: AstBindingRef) -> usize {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .map(|value| count_binding_uses_in_expr(value, binding))
            .sum(),
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .map(|value| count_binding_uses_in_expr(value, binding))
            .sum(),
        AstStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .map(|target| count_binding_uses_in_lvalue(target, binding))
                .sum::<usize>()
                + assign
                    .values
                    .iter()
                    .map(|value| count_binding_uses_in_expr(value, binding))
                    .sum::<usize>()
        }
        AstStmt::CallStmt(call_stmt) => count_binding_uses_in_call(&call_stmt.call, binding),
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .map(|value| count_binding_uses_in_expr(value, binding))
            .sum(),
        AstStmt::If(if_stmt) => {
            count_binding_uses_in_expr(&if_stmt.cond, binding)
                + count_binding_uses_in_block(&if_stmt.then_block, binding)
                + if_stmt
                    .else_block
                    .as_ref()
                    .map(|else_block| count_binding_uses_in_block(else_block, binding))
                    .unwrap_or(0)
        }
        AstStmt::While(while_stmt) => {
            count_binding_uses_in_expr(&while_stmt.cond, binding)
                + count_binding_uses_in_block(&while_stmt.body, binding)
        }
        AstStmt::Repeat(repeat_stmt) => {
            count_binding_uses_in_block(&repeat_stmt.body, binding)
                + count_binding_uses_in_expr(&repeat_stmt.cond, binding)
        }
        AstStmt::NumericFor(numeric_for) => {
            count_binding_uses_in_expr(&numeric_for.start, binding)
                + count_binding_uses_in_expr(&numeric_for.limit, binding)
                + count_binding_uses_in_expr(&numeric_for.step, binding)
                + count_binding_uses_in_block(&numeric_for.body, binding)
        }
        AstStmt::GenericFor(generic_for) => {
            generic_for
                .iterator
                .iter()
                .map(|expr| count_binding_uses_in_expr(expr, binding))
                .sum::<usize>()
                + count_binding_uses_in_block(&generic_for.body, binding)
        }
        AstStmt::DoBlock(block) => count_binding_uses_in_block(block, binding),
        AstStmt::FunctionDecl(function_decl) => {
            count_binding_uses_in_block(&function_decl.func.body, binding)
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            count_binding_uses_in_block(&local_function_decl.func.body, binding)
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => 0,
    }
}

fn count_binding_uses_in_block(block: &AstBlock, binding: AstBindingRef) -> usize {
    block
        .stmts
        .iter()
        .map(|stmt| count_binding_uses_in_stmt(stmt, binding))
        .sum()
}

fn count_binding_uses_in_call(call: &AstCallKind, binding: AstBindingRef) -> usize {
    match call {
        AstCallKind::Call(call) => {
            count_binding_uses_in_expr(&call.callee, binding)
                + call
                    .args
                    .iter()
                    .map(|arg| count_binding_uses_in_expr(arg, binding))
                    .sum::<usize>()
        }
        AstCallKind::MethodCall(call) => {
            count_binding_uses_in_expr(&call.receiver, binding)
                + call
                    .args
                    .iter()
                    .map(|arg| count_binding_uses_in_expr(arg, binding))
                    .sum::<usize>()
        }
    }
}

fn count_binding_uses_in_lvalue(target: &AstLValue, binding: AstBindingRef) -> usize {
    match target {
        AstLValue::Name(_) => 0,
        AstLValue::FieldAccess(access) => count_binding_uses_in_expr(&access.base, binding),
        AstLValue::IndexAccess(access) => {
            count_binding_uses_in_expr(&access.base, binding)
                + count_binding_uses_in_expr(&access.index, binding)
        }
    }
}

fn count_binding_uses_in_expr(expr: &AstExpr, binding: AstBindingRef) -> usize {
    match expr {
        AstExpr::Var(name) if name_matches_binding(name, binding) => 1,
        AstExpr::FieldAccess(access) => count_binding_uses_in_expr(&access.base, binding),
        AstExpr::IndexAccess(access) => {
            count_binding_uses_in_expr(&access.base, binding)
                + count_binding_uses_in_expr(&access.index, binding)
        }
        AstExpr::Unary(unary) => count_binding_uses_in_expr(&unary.expr, binding),
        AstExpr::Binary(binary) => {
            count_binding_uses_in_expr(&binary.lhs, binding)
                + count_binding_uses_in_expr(&binary.rhs, binding)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            count_binding_uses_in_expr(&logical.lhs, binding)
                + count_binding_uses_in_expr(&logical.rhs, binding)
        }
        AstExpr::Call(call) => {
            count_binding_uses_in_call(&AstCallKind::Call(call.clone()), binding)
        }
        AstExpr::MethodCall(call) => {
            count_binding_uses_in_call(&AstCallKind::MethodCall(call.clone()), binding)
        }
        AstExpr::TableConstructor(table) => table
            .fields
            .iter()
            .map(|field| match field {
                AstTableField::Array(value) => count_binding_uses_in_expr(value, binding),
                AstTableField::Record(record) => {
                    let key_count = match &record.key {
                        AstTableKey::Name(_) => 0,
                        AstTableKey::Expr(key) => count_binding_uses_in_expr(key, binding),
                    };
                    key_count + count_binding_uses_in_expr(&record.value, binding)
                }
            })
            .sum(),
        AstExpr::FunctionExpr(function) => count_binding_uses_in_block(&function.body, binding),
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
            | AstNameRef::SyntheticLocal(_)
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
enum InlineCandidate {
    TempLike(AstBindingRef),
    LocalAlias(AstBindingRef),
}

impl InlineCandidate {
    fn binding(self) -> AstBindingRef {
        match self {
            Self::TempLike(binding) | Self::LocalAlias(binding) => binding,
        }
    }

    fn allows_expr(self, expr: &AstExpr) -> bool {
        match self {
            Self::TempLike(_) => is_inline_candidate_expr(expr),
            // 这里故意不把普通 local 别名放宽到所有上下文：
            // 没有 debug 证据时，我们不能把用户可能主动写出来的局部语义名随手吞掉。
            // 目前只允许它们作为“前缀表达式别名”收回去，例如 `local concat = table.concat`。
            Self::LocalAlias(_) => is_access_base_inline_expr(expr),
        }
    }
}

#[derive(Clone, Copy)]
enum InlineSite {
    Neutral,
    ReturnValue,
    Index,
    CallArg,
    CallCallee,
    AccessBase,
}

#[derive(Clone, Copy)]
enum InlinePolicy {
    Conservative,
    ExtendedCallChain,
}

impl InlineSite {
    fn allows(
        self,
        candidate: InlineCandidate,
        use_expr: &AstExpr,
        replacement: &AstExpr,
        options: ReadabilityOptions,
        policy: InlinePolicy,
    ) -> bool {
        if !matches!(use_expr, AstExpr::Var(name) if name_matches_binding(name, candidate.binding()))
        {
            return false;
        }

        let Some(limit) = self.complexity_limit(options) else {
            return false;
        };
        if expr_complexity(replacement) > limit {
            return false;
        }

        match candidate {
            InlineCandidate::TempLike(_) => {
                !matches!(self, Self::AccessBase | Self::CallCallee)
                    || is_access_base_inline_expr(replacement)
            }
            InlineCandidate::LocalAlias(_) => match policy {
                InlinePolicy::Conservative => {
                    matches!(self, Self::CallCallee | Self::AccessBase)
                        && is_access_base_inline_expr(replacement)
                }
                InlinePolicy::ExtendedCallChain => self.allows_extended_local_alias(replacement),
            },
        }
    }

    fn complexity_limit(self, options: ReadabilityOptions) -> Option<usize> {
        match self {
            Self::Neutral => None,
            Self::ReturnValue => Some(options.return_inline_max_complexity),
            Self::Index => Some(options.index_inline_max_complexity),
            Self::CallArg => Some(options.args_inline_max_complexity),
            // 这里刻意复用 access-base 的阈值：
            // `table.concat(tbl)` 这类“把别名还原回前缀表达式”的可读性取舍，
            // 本质上和 `obj[key]` 里的 base 折叠是同一种源码形状决策。
            Self::CallCallee => Some(options.access_base_inline_max_complexity),
            Self::AccessBase => Some(options.access_base_inline_max_complexity),
        }
    }

    fn descend_access_base(self) -> Self {
        match self {
            Self::Neutral => Self::AccessBase,
            Self::ReturnValue
            | Self::Index
            | Self::CallArg
            | Self::CallCallee
            | Self::AccessBase => Self::Neutral,
        }
    }

    fn allows_extended_local_alias(self, replacement: &AstExpr) -> bool {
        match self {
            Self::CallCallee => {
                is_access_base_inline_expr(replacement) || is_recallable_inline_expr(replacement)
            }
            Self::CallArg => is_context_safe_expr(replacement),
            Self::AccessBase => is_access_base_inline_expr(replacement),
            Self::Neutral | Self::ReturnValue | Self::Index => false,
        }
    }
}

fn is_recallable_inline_expr(expr: &AstExpr) -> bool {
    matches!(expr, AstExpr::Call(_) | AstExpr::MethodCall(_))
}

fn name_matches_binding(name: &AstNameRef, binding: AstBindingRef) -> bool {
    match (binding, name) {
        (AstBindingRef::Local(local), AstNameRef::Local(name_local)) => local == *name_local,
        (AstBindingRef::Temp(temp), AstNameRef::Temp(name_temp)) => temp == *name_temp,
        (AstBindingRef::SyntheticLocal(local), AstNameRef::SyntheticLocal(name_local)) => {
            local == *name_local
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::common::{
        AstCallExpr, AstFieldAccess, AstGlobalName, AstIndexAccess, AstLocalBinding,
        AstMethodCallExpr, AstReturn,
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
            entry_function: Default::default(),
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
            entry_function: Default::default(),
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
            entry_function: Default::default(),
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
            entry_function: Default::default(),
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
            entry_function: Default::default(),
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

    #[test]
    fn inlines_single_use_local_alias_into_call_callee_with_access_base_threshold() {
        let alias = LocalId(0);
        let table_arg = LocalId(1);
        let mut module = AstModule {
            entry_function: Default::default(),
            body: crate::ast::AstBlock {
                stmts: vec![
                    AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: crate::ast::AstBindingRef::Local(alias),
                            attr: AstLocalAttr::None,
                        }],
                        values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                            base: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                                text: "table".to_owned(),
                            })),
                            field: "concat".to_owned(),
                        }))],
                    })),
                    AstStmt::Return(Box::new(AstReturn {
                        values: vec![AstExpr::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Var(AstNameRef::Local(alias)),
                            args: vec![
                                AstExpr::Var(AstNameRef::Local(table_arg)),
                                AstExpr::String(",".to_owned()),
                            ],
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
            vec![AstStmt::Return(Box::new(AstReturn {
                values: vec![AstExpr::Call(Box::new(AstCallExpr {
                    callee: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "table".to_owned(),
                        })),
                        field: "concat".to_owned(),
                    })),
                    args: vec![
                        AstExpr::Var(AstNameRef::Local(table_arg)),
                        AstExpr::String(",".to_owned()),
                    ],
                }))],
            }))]
        );
    }

    #[test]
    fn does_not_inline_local_alias_into_plain_return_value() {
        let alias = LocalId(0);
        let mut module = AstModule {
            entry_function: Default::default(),
            body: crate::ast::AstBlock {
                stmts: vec![
                    AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: crate::ast::AstBindingRef::Local(alias),
                            attr: AstLocalAttr::None,
                        }],
                        values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                            base: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                                text: "table".to_owned(),
                            })),
                            field: "concat".to_owned(),
                        }))],
                    })),
                    AstStmt::Return(Box::new(AstReturn {
                        values: vec![AstExpr::Var(AstNameRef::Local(alias))],
                    })),
                ],
            },
        };

        assert!(!apply(
            &mut module,
            ReadabilityContext {
                target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
                options: ReadabilityOptions {
                    access_base_inline_max_complexity: 5,
                    return_inline_max_complexity: usize::MAX,
                    ..ReadabilityOptions::default()
                },
            }
        ));
    }

    #[test]
    fn collapses_adjacent_local_alias_run_into_final_call_stmt() {
        let print_alias = LocalId(0);
        let label_alias = LocalId(1);
        let stage_alias = LocalId(2);
        let mut module = AstModule {
            entry_function: Default::default(),
            body: crate::ast::AstBlock {
                stmts: vec![
                    AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: crate::ast::AstBindingRef::Local(print_alias),
                            attr: AstLocalAttr::None,
                        }],
                        values: vec![AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "print".to_owned(),
                        }))],
                    })),
                    AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: crate::ast::AstBindingRef::Local(label_alias),
                            attr: AstLocalAttr::None,
                        }],
                        values: vec![AstExpr::String("nested-closure".to_owned())],
                    })),
                    AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: crate::ast::AstBindingRef::Local(stage_alias),
                            attr: AstLocalAttr::None,
                        }],
                        values: vec![AstExpr::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Var(AstNameRef::Local(LocalId(3))),
                            args: vec![AstExpr::Integer(1)],
                        }))],
                    })),
                    AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                        call: AstCallKind::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Var(AstNameRef::Local(print_alias)),
                            args: vec![
                                AstExpr::Var(AstNameRef::Local(label_alias)),
                                AstExpr::Call(Box::new(AstCallExpr {
                                    callee: AstExpr::Var(AstNameRef::Local(stage_alias)),
                                    args: vec![AstExpr::Integer(2)],
                                })),
                            ],
                        })),
                    })),
                ],
            },
        };

        assert!(apply(
            &mut module,
            ReadabilityContext {
                target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
                options: ReadabilityOptions::default(),
            }
        ));
        assert_eq!(
            module.body.stmts,
            vec![AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                call: AstCallKind::Call(Box::new(AstCallExpr {
                    callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                        text: "print".to_owned(),
                    })),
                    args: vec![
                        AstExpr::String("nested-closure".to_owned()),
                        AstExpr::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Call(Box::new(AstCallExpr {
                                callee: AstExpr::Var(AstNameRef::Local(LocalId(3))),
                                args: vec![AstExpr::Integer(1)],
                            })),
                            args: vec![AstExpr::Integer(2)],
                        })),
                    ],
                })),
            }))]
        );
    }

    #[test]
    fn does_not_collapse_single_call_chain_alias_before_final_call_stmt() {
        let stage1 = LocalId(0);
        let stage2 = LocalId(1);
        let mut module = AstModule {
            entry_function: Default::default(),
            body: crate::ast::AstBlock {
                stmts: vec![
                    AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: crate::ast::AstBindingRef::Local(stage1),
                            attr: AstLocalAttr::None,
                        }],
                        values: vec![AstExpr::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Var(AstNameRef::Local(LocalId(2))),
                            args: vec![AstExpr::Integer(2)],
                        }))],
                    })),
                    AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: crate::ast::AstBindingRef::Local(stage2),
                            attr: AstLocalAttr::None,
                        }],
                        values: vec![AstExpr::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Var(AstNameRef::Local(stage1)),
                            args: vec![AstExpr::Integer(3)],
                        }))],
                    })),
                    AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                        call: AstCallKind::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                                text: "print".to_owned(),
                            })),
                            args: vec![
                                AstExpr::String("nested-closure".to_owned()),
                                AstExpr::Call(Box::new(AstCallExpr {
                                    callee: AstExpr::Var(AstNameRef::Local(stage2)),
                                    args: vec![AstExpr::Integer(4)],
                                })),
                            ],
                        })),
                    })),
                ],
            },
        };

        let before = module.clone();
        assert!(!apply(
            &mut module,
            ReadabilityContext {
                target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
                options: ReadabilityOptions::default(),
            }
        ));
        assert_eq!(module.body.stmts, before.body.stmts);
    }

    #[test]
    fn inlines_local_alias_inside_function_body_after_other_locals() {
        let func = crate::hir::HirProtoRef(1);
        let table_local = LocalId(0);
        let helper = LocalId(1);
        let ok = LocalId(2);
        let concat = LocalId(3);
        let mut module = AstModule {
            entry_function: Default::default(),
            body: crate::ast::AstBlock {
                stmts: vec![AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(LocalId(10)),
                        attr: AstLocalAttr::None,
                    }],
                    values: vec![AstExpr::FunctionExpr(Box::new(
                        crate::ast::AstFunctionExpr {
                            function: func,
                            params: vec![crate::hir::ParamId(0), crate::hir::ParamId(1)],
                            is_vararg: false,
                            body: crate::ast::AstBlock {
                                stmts: vec![
                                    AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                                        bindings: vec![AstLocalBinding {
                                            id: crate::ast::AstBindingRef::Local(table_local),
                                            attr: AstLocalAttr::None,
                                        }],
                                        values: vec![AstExpr::TableConstructor(Box::new(
                                            crate::ast::AstTableConstructor { fields: vec![] },
                                        ))],
                                    })),
                                    AstStmt::LocalFunctionDecl(Box::new(
                                        crate::ast::AstLocalFunctionDecl {
                                            name: crate::ast::AstBindingRef::Local(helper),
                                            func: crate::ast::AstFunctionExpr {
                                                function: crate::hir::HirProtoRef(2),
                                                params: vec![
                                                    crate::hir::ParamId(0),
                                                    crate::hir::ParamId(1),
                                                ],
                                                is_vararg: false,
                                                body: crate::ast::AstBlock {
                                                    stmts: vec![AstStmt::Return(Box::new(
                                                        AstReturn {
                                                            values: vec![AstExpr::Var(
                                                                AstNameRef::Param(
                                                                    crate::hir::ParamId(1),
                                                                ),
                                                            )],
                                                        },
                                                    ))],
                                                },
                                            },
                                        },
                                    )),
                                    AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                                        bindings: vec![AstLocalBinding {
                                            id: crate::ast::AstBindingRef::Local(ok),
                                            attr: AstLocalAttr::None,
                                        }],
                                        values: vec![AstExpr::Boolean(true)],
                                    })),
                                    AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                                        bindings: vec![AstLocalBinding {
                                            id: crate::ast::AstBindingRef::Local(concat),
                                            attr: AstLocalAttr::None,
                                        }],
                                        values: vec![AstExpr::FieldAccess(Box::new(
                                            AstFieldAccess {
                                                base: AstExpr::Var(AstNameRef::Global(
                                                    AstGlobalName {
                                                        text: "table".to_owned(),
                                                    },
                                                )),
                                                field: "concat".to_owned(),
                                            },
                                        ))],
                                    })),
                                    AstStmt::Return(Box::new(AstReturn {
                                        values: vec![
                                            AstExpr::Var(AstNameRef::Local(ok)),
                                            AstExpr::Call(Box::new(AstCallExpr {
                                                callee: AstExpr::Var(AstNameRef::Local(concat)),
                                                args: vec![
                                                    AstExpr::Var(AstNameRef::Local(table_local)),
                                                    AstExpr::String(",".to_owned()),
                                                ],
                                            })),
                                        ],
                                    })),
                                ],
                            },
                        },
                    ))],
                }))],
            },
        };

        assert!(apply(
            &mut module,
            ReadabilityContext {
                target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
                options: ReadabilityOptions::default(),
            }
        ));

        let AstStmt::LocalDecl(local_decl) = &module.body.stmts[0] else {
            panic!("expected function wrapper local");
        };
        let AstExpr::FunctionExpr(function) = &local_decl.values[0] else {
            panic!("expected function expr");
        };
        assert!(matches!(
            function.body.stmts.as_slice(),
            [
                _,
                _,
                _,
                AstStmt::Return(ret)
            ] if matches!(
                ret.values.as_slice(),
                [
                    AstExpr::Var(AstNameRef::Local(ok_name)),
                    AstExpr::Call(call)
                ] if *ok_name == ok && matches!(&call.callee, AstExpr::FieldAccess(_))
            )
        ));
    }
}
