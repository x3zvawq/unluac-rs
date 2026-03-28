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
    AstLValue, AstLocalAttr, AstLocalDecl, AstLocalOrigin, AstModule, AstNameRef, AstStmt,
    AstTableField, AstTableKey,
};
use super::ReadabilityContext;
use super::binding_flow::{count_binding_uses_in_stmt, count_binding_uses_in_stmts};
use super::expr_analysis::{
    expr_complexity, is_access_base_inline_expr, is_context_safe_expr, is_lookup_inline_expr,
    is_mechanical_run_inline_expr,
};

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
        let policy = if matches!(candidate, InlineCandidate::LocalAlias { .. })
            && stmt_is_alias_initializer_sink(next_stmt)
        {
            InlinePolicy::AliasInitializerChain
        } else if matches!(candidate, InlineCandidate::LocalAlias { .. })
            && stmt_is_adjacent_call_result_sink(next_stmt)
        {
            InlinePolicy::AdjacentCallResultCallee
        } else {
            InlinePolicy::Conservative
        };
        if !candidate.allows_expr_with_policy(value, policy) {
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
        if !rewrite_stmt_use_sites_with_policy(
            &mut rewritten_next,
            candidate,
            value,
            options,
            policy,
        ) {
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
    changed |= collapse_adjacent_mechanical_alias_runs(block, options);
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
            if !matches!(candidate, InlineCandidate::LocalAlias { .. }) {
                continue;
            }
            if count_binding_uses_in_stmts(
                &old_stmts[(candidate_index + 1)..(run_end + 1)],
                candidate.binding(),
            ) != 1
            {
                continue;
            }
            let intermediate_uses = if is_lookup_inline_expr(value) {
                count_binding_uses_in_remaining_run(
                    &old_stmts[(candidate_index + 1)..run_end],
                    &removed[(candidate_index + 1 - index)..],
                    candidate.binding(),
                )
            } else {
                count_binding_uses_in_stmts(
                    &old_stmts[(candidate_index + 1)..run_end],
                    candidate.binding(),
                )
            };
            if intermediate_uses != 0 {
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

fn collapse_adjacent_mechanical_alias_runs(
    block: &mut AstBlock,
    options: ReadabilityOptions,
) -> bool {
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
            || !stmt_can_absorb_mechanical_run(&old_stmts[run_end])
        {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        }

        let mut rewritten_sink = old_stmts[run_end].clone();
        let mut removed = vec![false; run_end - index];
        let mut collapsed_count = 0usize;
        let mut has_non_lookup_piece = false;

        for candidate_index in (index..run_end).rev() {
            let Some((candidate, value)) = inline_candidate(&old_stmts[candidate_index]) else {
                continue;
            };
            if !candidate.allows_expr_with_policy(value, InlinePolicy::MechanicalRun) {
                continue;
            }
            if count_binding_uses_in_stmts(
                &old_stmts[(candidate_index + 1)..(run_end + 1)],
                candidate.binding(),
            ) != 1
            {
                continue;
            }
            if count_binding_uses_in_stmts(&old_stmts[(run_end + 1)..], candidate.binding()) != 0 {
                continue;
            }
            if count_binding_uses_in_remaining_run(
                &old_stmts[(candidate_index + 1)..run_end],
                &removed[(candidate_index + 1 - index)..],
                candidate.binding(),
            ) != 0
            {
                continue;
            }
            if !stmt_has_nested_binding_use(&rewritten_sink, candidate.binding()) {
                continue;
            }

            let mut trial_sink = rewritten_sink.clone();
            if rewrite_stmt_use_sites_with_policy(
                &mut trial_sink,
                candidate,
                value,
                options,
                InlinePolicy::MechanicalRun,
            ) {
                rewritten_sink = trial_sink;
                removed[candidate_index - index] = true;
                collapsed_count += 1;
                has_non_lookup_piece |= !is_lookup_inline_expr(value);
            }
        }

        if collapsed_count >= 2 && has_non_lookup_piece {
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
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
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
        AstBindingRef::Local(_) | AstBindingRef::SyntheticLocal(_) => InlineCandidate::LocalAlias {
            binding: binding.id,
            origin: binding.origin,
        },
    };
    Some((candidate, value))
}

fn stmt_is_alias_initializer_sink(stmt: &AstStmt) -> bool {
    matches!(
        inline_candidate(stmt),
        Some((InlineCandidate::LocalAlias { .. }, _))
    )
}

fn stmt_is_adjacent_call_result_sink(stmt: &AstStmt) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .any(expr_contains_direct_call_callee_var),
        AstStmt::Assign(assign) => assign
            .values
            .iter()
            .any(expr_contains_direct_call_callee_var),
        AstStmt::Return(ret) => ret.values.iter().any(expr_contains_direct_call_callee_var),
        AstStmt::GlobalDecl(_)
        | AstStmt::CallStmt(_)
        | AstStmt::If(_)
        | AstStmt::While(_)
        | AstStmt::Repeat(_)
        | AstStmt::NumericFor(_)
        | AstStmt::GenericFor(_)
        | AstStmt::DoBlock(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_) => false,
    }
}

fn expr_contains_direct_call_callee_var(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Call(call) => matches!(call.callee, AstExpr::Var(_)),
        AstExpr::MethodCall(_) => false,
        AstExpr::FieldAccess(access) => expr_contains_direct_call_callee_var(&access.base),
        AstExpr::IndexAccess(access) => {
            expr_contains_direct_call_callee_var(&access.base)
                || expr_contains_direct_call_callee_var(&access.index)
        }
        AstExpr::Unary(unary) => expr_contains_direct_call_callee_var(&unary.expr),
        AstExpr::Binary(binary) => {
            expr_contains_direct_call_callee_var(&binary.lhs)
                || expr_contains_direct_call_callee_var(&binary.rhs)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_contains_direct_call_callee_var(&logical.lhs)
                || expr_contains_direct_call_callee_var(&logical.rhs)
        }
        AstExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            AstTableField::Array(value) => expr_contains_direct_call_callee_var(value),
            AstTableField::Record(record) => {
                let key_has_call = match &record.key {
                    AstTableKey::Name(_) => false,
                    AstTableKey::Expr(key) => expr_contains_direct_call_callee_var(key),
                };
                key_has_call || expr_contains_direct_call_callee_var(&record.value)
            }
        }),
        AstExpr::FunctionExpr(_)
        | AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::VarArg => false,
    }
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
            let args_len = call.args.len();
            for (index, arg) in call.args.iter_mut().enumerate() {
                changed |= rewrite_expr_use_sites(
                    arg,
                    candidate,
                    replacement,
                    call_arg_site(index, args_len),
                    options,
                    policy,
                );
            }
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
            let args_len = call.args.len();
            for (index, arg) in call.args.iter_mut().enumerate() {
                changed |= rewrite_expr_use_sites(
                    arg,
                    candidate,
                    replacement,
                    call_arg_site(index, args_len),
                    options,
                    policy,
                );
            }
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
            site.descend_value_expr(),
            options,
            policy,
        ),
        AstExpr::Binary(binary) => {
            let operand_site = match binary.op {
                super::super::common::AstBinaryOpKind::Eq
                | super::super::common::AstBinaryOpKind::Lt
                | super::super::common::AstBinaryOpKind::Le => InlineSite::ComparisonOperand,
                _ => site.descend_value_expr(),
            };
            let mut changed = rewrite_expr_use_sites(
                &mut binary.lhs,
                candidate,
                replacement,
                operand_site,
                options,
                policy,
            );
            changed |= rewrite_expr_use_sites(
                &mut binary.rhs,
                candidate,
                replacement,
                operand_site,
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
                site.descend_value_expr(),
                options,
                policy,
            );
            changed |= rewrite_expr_use_sites(
                &mut logical.rhs,
                candidate,
                replacement,
                site.descend_value_expr(),
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
            let args_len = call.args.len();
            for (index, arg) in call.args.iter_mut().enumerate() {
                changed |= rewrite_expr_use_sites(
                    arg,
                    candidate,
                    replacement,
                    call_arg_site(index, args_len),
                    options,
                    policy,
                );
            }
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
            let args_len = call.args.len();
            for (index, arg) in call.args.iter_mut().enumerate() {
                changed |= rewrite_expr_use_sites(
                    arg,
                    candidate,
                    replacement,
                    call_arg_site(index, args_len),
                    options,
                    policy,
                );
            }
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
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::VarArg => false,
    }
}

fn stmt_can_absorb_mechanical_run(stmt: &AstStmt) -> bool {
    matches!(
        stmt,
        AstStmt::Assign(_)
            | AstStmt::CallStmt(_)
            | AstStmt::Return(_)
            | AstStmt::If(_)
            | AstStmt::While(_)
            | AstStmt::Repeat(_)
            | AstStmt::NumericFor(_)
            | AstStmt::GenericFor(_)
    )
}

fn stmt_has_nested_binding_use(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .any(|value| expr_has_nested_binding_use(value, binding, false)),
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .any(|value| expr_has_nested_binding_use(value, binding, false)),
        AstStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .any(|target| lvalue_has_nested_binding_use(target, binding))
                || assign
                    .values
                    .iter()
                    .any(|value| expr_has_nested_binding_use(value, binding, false))
        }
        AstStmt::CallStmt(call_stmt) => call_has_nested_binding_use(&call_stmt.call, binding),
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .any(|value| expr_has_nested_binding_use(value, binding, false)),
        AstStmt::If(if_stmt) => expr_has_nested_binding_use(&if_stmt.cond, binding, false),
        AstStmt::While(while_stmt) => expr_has_nested_binding_use(&while_stmt.cond, binding, false),
        AstStmt::Repeat(repeat_stmt) => {
            expr_has_nested_binding_use(&repeat_stmt.cond, binding, false)
        }
        AstStmt::NumericFor(numeric_for) => {
            expr_has_nested_binding_use(&numeric_for.start, binding, false)
                || expr_has_nested_binding_use(&numeric_for.limit, binding, false)
                || expr_has_nested_binding_use(&numeric_for.step, binding, false)
        }
        AstStmt::GenericFor(generic_for) => generic_for
            .iterator
            .iter()
            .any(|expr| expr_has_nested_binding_use(expr, binding, false)),
        AstStmt::DoBlock(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_) => false,
    }
}

fn call_has_nested_binding_use(call: &AstCallKind, binding: AstBindingRef) -> bool {
    match call {
        AstCallKind::Call(call) => {
            expr_has_nested_binding_use(&call.callee, binding, false)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_has_nested_binding_use(arg, binding, false))
        }
        AstCallKind::MethodCall(call) => {
            expr_has_nested_binding_use(&call.receiver, binding, false)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_has_nested_binding_use(arg, binding, false))
        }
    }
}

fn lvalue_has_nested_binding_use(target: &AstLValue, binding: AstBindingRef) -> bool {
    match target {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => expr_has_nested_binding_use(&access.base, binding, true),
        AstLValue::IndexAccess(access) => {
            expr_has_nested_binding_use(&access.base, binding, true)
                || expr_has_nested_binding_use(&access.index, binding, true)
        }
    }
}

fn expr_has_nested_binding_use(expr: &AstExpr, binding: AstBindingRef, nested: bool) -> bool {
    match expr {
        AstExpr::Var(name) if name_matches_binding(name, binding) => nested,
        AstExpr::FieldAccess(access) => expr_has_nested_binding_use(&access.base, binding, true),
        AstExpr::IndexAccess(access) => {
            expr_has_nested_binding_use(&access.base, binding, true)
                || expr_has_nested_binding_use(&access.index, binding, true)
        }
        AstExpr::Unary(unary) => expr_has_nested_binding_use(&unary.expr, binding, true),
        AstExpr::Binary(binary) => {
            expr_has_nested_binding_use(&binary.lhs, binding, true)
                || expr_has_nested_binding_use(&binary.rhs, binding, true)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_has_nested_binding_use(&logical.lhs, binding, true)
                || expr_has_nested_binding_use(&logical.rhs, binding, true)
        }
        AstExpr::Call(call) => {
            expr_has_nested_binding_use(&call.callee, binding, true)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_has_nested_binding_use(arg, binding, true))
        }
        AstExpr::MethodCall(call) => {
            expr_has_nested_binding_use(&call.receiver, binding, true)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_has_nested_binding_use(arg, binding, true))
        }
        AstExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            AstTableField::Array(value) => expr_has_nested_binding_use(value, binding, true),
            AstTableField::Record(record) => {
                let key_matches = match &record.key {
                    AstTableKey::Name(_) => false,
                    AstTableKey::Expr(key) => expr_has_nested_binding_use(key, binding, true),
                };
                key_matches || expr_has_nested_binding_use(&record.value, binding, true)
            }
        }),
        AstExpr::FunctionExpr(_)
        | AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::VarArg => false,
    }
}

fn count_binding_uses_in_remaining_run(
    stmts: &[AstStmt],
    removed: &[bool],
    binding: AstBindingRef,
) -> usize {
    stmts
        .iter()
        .zip(removed.iter())
        .filter(|(_, removed)| !**removed)
        .map(|(stmt, _)| count_binding_uses_in_stmt(stmt, binding))
        .sum()
}

fn is_inline_candidate_expr(expr: &AstExpr) -> bool {
    is_context_safe_expr(expr) || is_access_base_inline_expr(expr)
}

fn is_call_callee_inline_expr(expr: &AstExpr) -> bool {
    is_access_base_inline_expr(expr)
        || is_lookup_inline_expr(expr)
        || is_recallable_inline_expr(expr)
}

fn is_extended_neutral_local_alias_expr(expr: &AstExpr) -> bool {
    is_context_safe_expr(expr) || is_lookup_inline_expr(expr)
}

fn is_extended_call_arg_local_alias_expr(expr: &AstExpr) -> bool {
    is_context_safe_expr(expr) || is_lookup_inline_expr(expr)
}

#[derive(Clone, Copy)]
enum InlineCandidate {
    TempLike(AstBindingRef),
    LocalAlias {
        binding: AstBindingRef,
        origin: AstLocalOrigin,
    },
}

impl InlineCandidate {
    fn binding(self) -> AstBindingRef {
        match self {
            Self::TempLike(binding) => binding,
            Self::LocalAlias { binding, .. } => binding,
        }
    }

    fn allows_expr_with_policy(self, expr: &AstExpr, policy: InlinePolicy) -> bool {
        match self {
            Self::TempLike(_) => match policy {
                InlinePolicy::MechanicalRun => is_mechanical_run_inline_expr(expr),
                _ => is_inline_candidate_expr(expr),
            },
            // 这里故意不把普通 local 别名放宽到所有上下文：
            // 没有 debug 证据时，我们不能把用户可能主动写出来的局部语义名随手吞掉。
            // 目前只允许它们作为“前缀表达式别名”收回去，例如 `local concat = table.concat`。
            Self::LocalAlias {
                origin: AstLocalOrigin::DebugHinted,
                ..
            } => is_access_base_inline_expr(expr),
            Self::LocalAlias {
                origin: AstLocalOrigin::Recovered,
                ..
            } => match policy {
                InlinePolicy::MechanicalRun => is_mechanical_run_inline_expr(expr),
                InlinePolicy::AdjacentCallResultCallee => is_lookup_inline_expr(expr),
                _ => is_access_base_inline_expr(expr) || is_recallable_inline_expr(expr),
            },
        }
    }
}

#[derive(Clone, Copy)]
enum InlineSite {
    Neutral,
    ComparisonOperand,
    ReturnValue,
    ReturnNestedValue,
    Index,
    CallArgNonFinal,
    CallArgFinal,
    CallCallee,
    AccessBase,
}

#[derive(Clone, Copy)]
enum InlinePolicy {
    Conservative,
    ExtendedCallChain,
    AliasInitializerChain,
    AdjacentCallResultCallee,
    MechanicalRun,
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

        let Some(limit) = self.complexity_limit(options, policy) else {
            return false;
        };
        if expr_complexity(replacement) > limit {
            return false;
        }

        match candidate {
            InlineCandidate::TempLike(_) => match policy {
                InlinePolicy::MechanicalRun => self.allows_mechanical_run_expr(replacement),
                _ => {
                    !matches!(self, Self::AccessBase | Self::CallCallee)
                        || is_access_base_inline_expr(replacement)
                }
            },
            InlineCandidate::LocalAlias { origin, .. } => match policy {
                InlinePolicy::Conservative => match origin {
                    AstLocalOrigin::DebugHinted => {
                        matches!(self, Self::CallCallee | Self::AccessBase)
                            && is_access_base_inline_expr(replacement)
                    }
                    AstLocalOrigin::Recovered => match self {
                        Self::CallCallee | Self::AccessBase => {
                            is_access_base_inline_expr(replacement)
                        }
                        Self::ComparisonOperand => {
                            is_access_base_inline_expr(replacement)
                                || is_recallable_inline_expr(replacement)
                        }
                        Self::ReturnNestedValue => is_recallable_inline_expr(replacement),
                        _ => false,
                    },
                },
                InlinePolicy::ExtendedCallChain => self.allows_extended_local_alias(replacement),
                InlinePolicy::AliasInitializerChain => {
                    self.allows_alias_initializer_local_alias(replacement)
                }
                InlinePolicy::AdjacentCallResultCallee => {
                    self.allows_adjacent_call_result_local_alias(replacement)
                }
                InlinePolicy::MechanicalRun => match origin {
                    AstLocalOrigin::DebugHinted => false,
                    AstLocalOrigin::Recovered => self.allows_mechanical_run_expr(replacement),
                },
            },
        }
    }

    fn complexity_limit(self, options: ReadabilityOptions, policy: InlinePolicy) -> Option<usize> {
        match self {
            Self::Neutral => match policy {
                InlinePolicy::AliasInitializerChain => {
                    Some(options.access_base_inline_max_complexity)
                }
                InlinePolicy::AdjacentCallResultCallee => None,
                InlinePolicy::Conservative => None,
                InlinePolicy::ExtendedCallChain => Some(options.access_base_inline_max_complexity),
                InlinePolicy::MechanicalRun => Some(options.return_inline_max_complexity),
            },
            Self::ComparisonOperand => Some(options.args_inline_max_complexity),
            Self::ReturnValue => Some(options.return_inline_max_complexity),
            Self::ReturnNestedValue => Some(options.return_inline_max_complexity),
            Self::Index => Some(options.index_inline_max_complexity),
            Self::CallArgNonFinal | Self::CallArgFinal => Some(options.args_inline_max_complexity),
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
            Self::ComparisonOperand => Self::ComparisonOperand,
            Self::ReturnValue => Self::ReturnNestedValue,
            Self::ReturnNestedValue => Self::ReturnNestedValue,
            Self::Index
            | Self::CallArgNonFinal
            | Self::CallArgFinal
            | Self::CallCallee
            | Self::AccessBase => Self::Neutral,
        }
    }

    fn descend_value_expr(self) -> Self {
        match self {
            Self::ReturnValue | Self::ReturnNestedValue => Self::ReturnNestedValue,
            Self::ComparisonOperand => Self::ComparisonOperand,
            Self::Neutral
            | Self::Index
            | Self::CallArgNonFinal
            | Self::CallArgFinal
            | Self::CallCallee
            | Self::AccessBase => Self::Neutral,
        }
    }

    fn allows_extended_local_alias(self, replacement: &AstExpr) -> bool {
        match self {
            Self::Neutral => is_extended_neutral_local_alias_expr(replacement),
            Self::ComparisonOperand => {
                is_extended_neutral_local_alias_expr(replacement)
                    || is_recallable_inline_expr(replacement)
            }
            Self::ReturnNestedValue => is_recallable_inline_expr(replacement),
            Self::CallCallee => is_call_callee_inline_expr(replacement),
            Self::CallArgNonFinal => {
                is_extended_call_arg_local_alias_expr(replacement)
                    || is_recallable_inline_expr(replacement)
            }
            // 这里只有在“局部别名包折回最终调用”时，才允许把纯 lookup 收回参数位。
            // 这能把 `local x = t[1]; local y = t.a; print(x, y)` 这类机械展开收回去，
            // 同时仍然不放宽到任意调用结果，避免把阶段 local 继续吞掉。
            Self::CallArgFinal => is_extended_call_arg_local_alias_expr(replacement),
            Self::AccessBase => is_access_base_inline_expr(replacement),
            Self::ReturnValue | Self::Index => false,
        }
    }

    fn allows_alias_initializer_local_alias(self, replacement: &AstExpr) -> bool {
        match self {
            // 这里专门服务“局部别名链初始化”：
            // `local unpack = table.unpack; local fn = unpack or _G.unpack`
            // 这种形状本质上还是在组装一个后续调用会消费的前缀表达式别名。
            // 允许它在紧邻的下一条 local alias 初始化式里收回，能把机械拆分重新压回
            // 更接近源码的单条声明，而不会放宽到普通 return/if/赋值上下文。
            Self::Neutral | Self::ComparisonOperand | Self::AccessBase | Self::CallCallee => {
                is_access_base_inline_expr(replacement)
            }
            Self::ReturnValue
            | Self::ReturnNestedValue
            | Self::Index
            | Self::CallArgNonFinal
            | Self::CallArgFinal => false,
        }
    }

    fn allows_adjacent_call_result_local_alias(self, replacement: &AstExpr) -> bool {
        matches!(self, Self::CallCallee) && is_lookup_inline_expr(replacement)
    }

    fn allows_mechanical_run_expr(self, replacement: &AstExpr) -> bool {
        match self {
            Self::Neutral | Self::ComparisonOperand | Self::ReturnNestedValue | Self::Index => {
                is_mechanical_run_inline_expr(replacement)
            }
            Self::CallCallee => is_call_callee_inline_expr(replacement),
            Self::AccessBase => {
                is_access_base_inline_expr(replacement) || is_lookup_inline_expr(replacement)
            }
            Self::ReturnValue | Self::CallArgNonFinal | Self::CallArgFinal => false,
        }
    }
}

fn is_recallable_inline_expr(expr: &AstExpr) -> bool {
    matches!(expr, AstExpr::Call(_) | AstExpr::MethodCall(_))
}

fn call_arg_site(index: usize, len: usize) -> InlineSite {
    if index + 1 == len {
        InlineSite::CallArgFinal
    } else {
        InlineSite::CallArgNonFinal
    }
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
mod tests;
