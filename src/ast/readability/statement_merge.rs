//! 把显然属于同一次源码声明的相邻语句重新合并。

use super::super::common::{
    AstBindingRef, AstBlock, AstFunctionExpr, AstLValue, AstLocalAttr, AstLocalDecl, AstModule,
    AstNameRef, AstStmt,
};
use super::ReadabilityContext;

const ADJACENT_LOCAL_VALUE_COMPLEXITY_LIMIT: usize = 4;

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let _ = context.target;
    rewrite_block(&mut module.body)
}

fn rewrite_block(block: &mut AstBlock) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        changed |= rewrite_nested(stmt);
    }

    changed |= sink_hoisted_temp_decls(block);

    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut index = 0;
    while index < old_stmts.len() {
        let Some(next_stmt) = old_stmts.get(index + 1) else {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        };

        if let Some(merged) = try_merge_local_decl_with_assign(&old_stmts[index], next_stmt) {
            new_stmts.push(AstStmt::LocalDecl(Box::new(merged)));
            changed = true;
            index += 2;
            continue;
        }

        new_stmts.push(old_stmts[index].clone());
        index += 1;
    }

    block.stmts = new_stmts;
    changed |= merge_adjacent_single_value_local_decls(block);
    changed
}

fn merge_adjacent_single_value_local_decls(block: &mut AstBlock) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while index < old_stmts.len() {
        let Some((binding, value)) = single_value_local_decl(&old_stmts[index]) else {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        };
        if !is_mergeable_adjacent_local_value(value) {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        }

        let mut bindings = vec![binding.clone()];
        let mut values = vec![value.clone()];
        let mut lookahead = index + 1;
        while let Some((next_binding, next_value)) =
            old_stmts.get(lookahead).and_then(single_value_local_decl)
        {
            // 这里故意只收“连续复制/lookup”式的 local：
            // 目标是把 `local a = x; local b = y; local c = t[k]` 这类明显属于同一段
            // 源码声明的机械拆分重新压回去，而不是把有阶段语义的复杂 local 都并成一行。
            if !is_mergeable_adjacent_local_value(next_value)
                || expr_references_any_binding(next_value, &bindings)
            {
                break;
            }
            bindings.push(next_binding.clone());
            values.push(next_value.clone());
            lookahead += 1;
        }

        let has_multi_use_binding = bindings
            .iter()
            .any(|binding| count_binding_uses_in_stmts(&old_stmts[lookahead..], binding.id) > 1);

        // 这里只合并真正有“阶段 local”味道的连续声明：
        // 如果整组 binding 都只在后缀里被读一次，那往往只是调用前的机械 alias 准备序列，
        // 更适合交给 inline_exprs 去收回，而不是在这里抢先并成一条 multi-local。
        if bindings.len() >= 2 && has_multi_use_binding {
            new_stmts.push(AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings,
                values,
            })));
            changed = true;
            index = lookahead;
            continue;
        }

        new_stmts.push(old_stmts[index].clone());
        index += 1;
    }

    block.stmts = new_stmts;
    changed
}

fn sink_hoisted_temp_decls(block: &mut AstBlock) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index < block.stmts.len() {
        let Some(pending_bindings) = hoisted_temp_bindings(&block.stmts[index]) else {
            index += 1;
            continue;
        };

        let mut remaining = pending_bindings;
        let mut sink_changed = false;
        let mut lookahead = index + 1;
        while lookahead < block.stmts.len() && !remaining.is_empty() {
            if let Some(merged) =
                try_sink_hoisted_decl_into_stmt(&remaining, &block.stmts[lookahead])
            {
                let consumed = merged.bindings.len();
                block.stmts[lookahead] = AstStmt::LocalDecl(Box::new(merged));
                remaining.drain(..consumed);
                sink_changed = true;
                lookahead += 1;
                continue;
            }
            if stmt_references_any_binding(&block.stmts[lookahead], &remaining) {
                break;
            }
            lookahead += 1;
        }

        if !sink_changed {
            index += 1;
            continue;
        }

        changed = true;
        if remaining.is_empty() {
            block.stmts.remove(index);
            continue;
        }

        let AstStmt::LocalDecl(local_decl) = &mut block.stmts[index] else {
            unreachable!("hoisted temp decl scan must point at local decl");
        };
        local_decl.bindings = remaining;
        index += 1;
    }
    changed
}

fn rewrite_nested(stmt: &mut AstStmt) -> bool {
    match stmt {
        AstStmt::If(if_stmt) => {
            let mut changed = rewrite_nested_functions_in_expr(&mut if_stmt.cond);
            changed |= rewrite_block(&mut if_stmt.then_block);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= rewrite_block(else_block);
            }
            changed
        }
        AstStmt::While(while_stmt) => {
            rewrite_nested_functions_in_expr(&mut while_stmt.cond)
                | rewrite_block(&mut while_stmt.body)
        }
        AstStmt::Repeat(repeat_stmt) => {
            rewrite_block(&mut repeat_stmt.body)
                | rewrite_nested_functions_in_expr(&mut repeat_stmt.cond)
        }
        AstStmt::NumericFor(numeric_for) => {
            let mut changed = rewrite_nested_functions_in_expr(&mut numeric_for.start);
            changed |= rewrite_nested_functions_in_expr(&mut numeric_for.limit);
            changed |= rewrite_nested_functions_in_expr(&mut numeric_for.step);
            changed |= rewrite_block(&mut numeric_for.body);
            changed
        }
        AstStmt::GenericFor(generic_for) => {
            let mut changed = false;
            for expr in &mut generic_for.iterator {
                changed |= rewrite_nested_functions_in_expr(expr);
            }
            changed |= rewrite_block(&mut generic_for.body);
            changed
        }
        AstStmt::DoBlock(block) => rewrite_block(block),
        AstStmt::FunctionDecl(function_decl) => rewrite_function(&mut function_decl.func),
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            rewrite_function(&mut local_function_decl.func)
        }
        AstStmt::LocalDecl(local_decl) => {
            local_decl.values.iter_mut().fold(false, |changed, expr| {
                rewrite_nested_functions_in_expr(expr) | changed
            })
        }
        AstStmt::GlobalDecl(global_decl) => {
            global_decl.values.iter_mut().fold(false, |changed, expr| {
                rewrite_nested_functions_in_expr(expr) | changed
            })
        }
        AstStmt::Assign(assign) => {
            let mut changed = false;
            for target in &mut assign.targets {
                changed |= rewrite_nested_functions_in_lvalue(target);
            }
            for value in &mut assign.values {
                changed |= rewrite_nested_functions_in_expr(value);
            }
            changed
        }
        AstStmt::CallStmt(call_stmt) => rewrite_nested_functions_in_call(&mut call_stmt.call),
        AstStmt::Return(ret) => ret.values.iter_mut().fold(false, |changed, expr| {
            rewrite_nested_functions_in_expr(expr) | changed
        }),
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => false,
    }
}

fn rewrite_function(function: &mut AstFunctionExpr) -> bool {
    rewrite_block(&mut function.body)
}

fn rewrite_nested_functions_in_call(call: &mut super::super::common::AstCallKind) -> bool {
    match call {
        super::super::common::AstCallKind::Call(call) => {
            let mut changed = rewrite_nested_functions_in_expr(&mut call.callee);
            for arg in &mut call.args {
                changed |= rewrite_nested_functions_in_expr(arg);
            }
            changed
        }
        super::super::common::AstCallKind::MethodCall(call) => {
            let mut changed = rewrite_nested_functions_in_expr(&mut call.receiver);
            for arg in &mut call.args {
                changed |= rewrite_nested_functions_in_expr(arg);
            }
            changed
        }
    }
}

fn rewrite_nested_functions_in_lvalue(target: &mut AstLValue) -> bool {
    match target {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => rewrite_nested_functions_in_expr(&mut access.base),
        AstLValue::IndexAccess(access) => {
            rewrite_nested_functions_in_expr(&mut access.base)
                | rewrite_nested_functions_in_expr(&mut access.index)
        }
    }
}

fn rewrite_nested_functions_in_expr(expr: &mut super::super::common::AstExpr) -> bool {
    match expr {
        super::super::common::AstExpr::FieldAccess(access) => {
            rewrite_nested_functions_in_expr(&mut access.base)
        }
        super::super::common::AstExpr::IndexAccess(access) => {
            rewrite_nested_functions_in_expr(&mut access.base)
                | rewrite_nested_functions_in_expr(&mut access.index)
        }
        super::super::common::AstExpr::Unary(unary) => {
            rewrite_nested_functions_in_expr(&mut unary.expr)
        }
        super::super::common::AstExpr::Binary(binary) => {
            rewrite_nested_functions_in_expr(&mut binary.lhs)
                | rewrite_nested_functions_in_expr(&mut binary.rhs)
        }
        super::super::common::AstExpr::LogicalAnd(logical)
        | super::super::common::AstExpr::LogicalOr(logical) => {
            rewrite_nested_functions_in_expr(&mut logical.lhs)
                | rewrite_nested_functions_in_expr(&mut logical.rhs)
        }
        super::super::common::AstExpr::Call(call) => {
            let mut changed = rewrite_nested_functions_in_expr(&mut call.callee);
            for arg in &mut call.args {
                changed |= rewrite_nested_functions_in_expr(arg);
            }
            changed
        }
        super::super::common::AstExpr::MethodCall(call) => {
            let mut changed = rewrite_nested_functions_in_expr(&mut call.receiver);
            for arg in &mut call.args {
                changed |= rewrite_nested_functions_in_expr(arg);
            }
            changed
        }
        super::super::common::AstExpr::TableConstructor(table) => {
            let mut changed = false;
            for field in &mut table.fields {
                changed |= match field {
                    super::super::common::AstTableField::Array(value) => {
                        rewrite_nested_functions_in_expr(value)
                    }
                    super::super::common::AstTableField::Record(record) => {
                        let key_changed = match &mut record.key {
                            super::super::common::AstTableKey::Name(_) => false,
                            super::super::common::AstTableKey::Expr(key) => {
                                rewrite_nested_functions_in_expr(key)
                            }
                        };
                        key_changed | rewrite_nested_functions_in_expr(&mut record.value)
                    }
                };
            }
            changed
        }
        super::super::common::AstExpr::FunctionExpr(function) => rewrite_function(function),
        super::super::common::AstExpr::Nil
        | super::super::common::AstExpr::Boolean(_)
        | super::super::common::AstExpr::Integer(_)
        | super::super::common::AstExpr::Number(_)
        | super::super::common::AstExpr::String(_)
        | super::super::common::AstExpr::Var(_)
        | super::super::common::AstExpr::VarArg => false,
    }
}

fn single_value_local_decl(
    stmt: &AstStmt,
) -> Option<(
    &super::super::common::AstLocalBinding,
    &super::super::common::AstExpr,
)> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [value] = local_decl.values.as_slice() else {
        return None;
    };
    (binding.attr == AstLocalAttr::None).then_some((binding, value))
}

fn try_merge_local_decl_with_assign(current: &AstStmt, next: &AstStmt) -> Option<AstLocalDecl> {
    let AstStmt::LocalDecl(local_decl) = current else {
        return None;
    };
    let AstStmt::Assign(assign) = next else {
        return None;
    };
    if !local_decl.values.is_empty() || local_decl.bindings.is_empty() {
        return None;
    }
    if local_decl
        .bindings
        .iter()
        .any(|binding| binding.attr != AstLocalAttr::None)
    {
        return None;
    }
    if local_decl.bindings.len() != assign.targets.len() || assign.values.is_empty() {
        return None;
    }
    if !local_decl
        .bindings
        .iter()
        .zip(assign.targets.iter())
        .all(|(binding, target)| local_binding_matches_target(binding.id, target))
    {
        return None;
    }

    Some(AstLocalDecl {
        bindings: local_decl.bindings.clone(),
        values: assign.values.clone(),
    })
}

fn hoisted_temp_bindings(stmt: &AstStmt) -> Option<Vec<super::super::common::AstLocalBinding>> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    if !local_decl.values.is_empty() || local_decl.bindings.is_empty() {
        return None;
    }
    if local_decl
        .bindings
        .iter()
        .any(|binding| binding.attr != AstLocalAttr::None || !is_temp_like_binding(binding.id))
    {
        return None;
    }
    Some(local_decl.bindings.clone())
}

fn try_sink_hoisted_decl_into_stmt(
    pending: &[super::super::common::AstLocalBinding],
    stmt: &AstStmt,
) -> Option<AstLocalDecl> {
    let AstStmt::Assign(assign) = stmt else {
        return None;
    };
    if assign.values.is_empty() || assign.targets.is_empty() || assign.targets.len() > pending.len()
    {
        return None;
    }
    let candidate = &pending[..assign.targets.len()];
    if !candidate
        .iter()
        .zip(assign.targets.iter())
        .all(|(binding, target)| local_binding_matches_target(binding.id, target))
    {
        return None;
    }
    if stmt_references_any_binding_in_assign(assign, &pending[assign.targets.len()..]) {
        return None;
    }
    Some(AstLocalDecl {
        bindings: candidate.to_vec(),
        values: assign.values.clone(),
    })
}

fn is_temp_like_binding(binding: AstBindingRef) -> bool {
    matches!(
        binding,
        AstBindingRef::Temp(_) | AstBindingRef::SyntheticLocal(_)
    )
}

fn stmt_references_any_binding(
    stmt: &AstStmt,
    bindings: &[super::super::common::AstLocalBinding],
) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            local_decl
                .bindings
                .iter()
                .any(|binding| bindings.iter().any(|pending| pending.id == binding.id))
                || local_decl
                    .values
                    .iter()
                    .any(|value| expr_references_any_binding(value, bindings))
        }
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .any(|value| expr_references_any_binding(value, bindings)),
        AstStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .any(|target| lvalue_references_any_binding(target, bindings))
                || assign
                    .values
                    .iter()
                    .any(|value| expr_references_any_binding(value, bindings))
        }
        AstStmt::CallStmt(call_stmt) => call_references_any_binding(&call_stmt.call, bindings),
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .any(|value| expr_references_any_binding(value, bindings)),
        AstStmt::If(if_stmt) => {
            expr_references_any_binding(&if_stmt.cond, bindings)
                || block_references_any_binding(&if_stmt.then_block, bindings)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| block_references_any_binding(block, bindings))
        }
        AstStmt::While(while_stmt) => {
            expr_references_any_binding(&while_stmt.cond, bindings)
                || block_references_any_binding(&while_stmt.body, bindings)
        }
        AstStmt::Repeat(repeat_stmt) => {
            block_references_any_binding(&repeat_stmt.body, bindings)
                || expr_references_any_binding(&repeat_stmt.cond, bindings)
        }
        AstStmt::NumericFor(numeric_for) => {
            bindings
                .iter()
                .any(|binding| binding.id == numeric_for.binding)
                || expr_references_any_binding(&numeric_for.start, bindings)
                || expr_references_any_binding(&numeric_for.limit, bindings)
                || expr_references_any_binding(&numeric_for.step, bindings)
                || block_references_any_binding(&numeric_for.body, bindings)
        }
        AstStmt::GenericFor(generic_for) => {
            generic_for
                .bindings
                .iter()
                .any(|binding| bindings.iter().any(|pending| pending.id == *binding))
                || generic_for
                    .iterator
                    .iter()
                    .any(|expr| expr_references_any_binding(expr, bindings))
                || block_references_any_binding(&generic_for.body, bindings)
        }
        AstStmt::DoBlock(block) => block_references_any_binding(block, bindings),
        AstStmt::FunctionDecl(function_decl) => {
            function_name_references_any_binding(&function_decl.target, bindings)
                || block_references_any_binding(&function_decl.func.body, bindings)
        }
        AstStmt::LocalFunctionDecl(function_decl) => {
            bindings
                .iter()
                .any(|binding| binding.id == function_decl.name)
                || block_references_any_binding(&function_decl.func.body, bindings)
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => false,
    }
}

fn stmt_references_any_binding_in_assign(
    assign: &super::super::common::AstAssign,
    bindings: &[super::super::common::AstLocalBinding],
) -> bool {
    assign
        .values
        .iter()
        .any(|value| expr_references_any_binding(value, bindings))
}

fn block_references_any_binding(
    block: &AstBlock,
    bindings: &[super::super::common::AstLocalBinding],
) -> bool {
    block
        .stmts
        .iter()
        .any(|stmt| stmt_references_any_binding(stmt, bindings))
}

fn call_references_any_binding(
    call: &super::super::common::AstCallKind,
    bindings: &[super::super::common::AstLocalBinding],
) -> bool {
    match call {
        super::super::common::AstCallKind::Call(call) => {
            expr_references_any_binding(&call.callee, bindings)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_any_binding(arg, bindings))
        }
        super::super::common::AstCallKind::MethodCall(call) => {
            expr_references_any_binding(&call.receiver, bindings)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_any_binding(arg, bindings))
        }
    }
}

fn function_name_references_any_binding(
    target: &super::super::common::AstFunctionName,
    bindings: &[super::super::common::AstLocalBinding],
) -> bool {
    let path = match target {
        super::super::common::AstFunctionName::Plain(path) => path,
        super::super::common::AstFunctionName::Method(path, _) => path,
    };
    name_ref_matches_any_binding(&path.root, bindings)
}

fn lvalue_references_any_binding(
    target: &AstLValue,
    bindings: &[super::super::common::AstLocalBinding],
) -> bool {
    match target {
        AstLValue::Name(name) => name_ref_matches_any_binding(name, bindings),
        AstLValue::FieldAccess(access) => expr_references_any_binding(&access.base, bindings),
        AstLValue::IndexAccess(access) => {
            expr_references_any_binding(&access.base, bindings)
                || expr_references_any_binding(&access.index, bindings)
        }
    }
}

fn expr_references_any_binding(
    expr: &super::super::common::AstExpr,
    bindings: &[super::super::common::AstLocalBinding],
) -> bool {
    match expr {
        super::super::common::AstExpr::Var(name) => name_ref_matches_any_binding(name, bindings),
        super::super::common::AstExpr::FieldAccess(access) => {
            expr_references_any_binding(&access.base, bindings)
        }
        super::super::common::AstExpr::IndexAccess(access) => {
            expr_references_any_binding(&access.base, bindings)
                || expr_references_any_binding(&access.index, bindings)
        }
        super::super::common::AstExpr::Unary(unary) => {
            expr_references_any_binding(&unary.expr, bindings)
        }
        super::super::common::AstExpr::Binary(binary) => {
            expr_references_any_binding(&binary.lhs, bindings)
                || expr_references_any_binding(&binary.rhs, bindings)
        }
        super::super::common::AstExpr::LogicalAnd(logical)
        | super::super::common::AstExpr::LogicalOr(logical) => {
            expr_references_any_binding(&logical.lhs, bindings)
                || expr_references_any_binding(&logical.rhs, bindings)
        }
        super::super::common::AstExpr::Call(call) => {
            expr_references_any_binding(&call.callee, bindings)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_any_binding(arg, bindings))
        }
        super::super::common::AstExpr::MethodCall(call) => {
            expr_references_any_binding(&call.receiver, bindings)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_any_binding(arg, bindings))
        }
        super::super::common::AstExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                super::super::common::AstTableField::Array(value) => {
                    expr_references_any_binding(value, bindings)
                }
                super::super::common::AstTableField::Record(record) => {
                    let key_references_binding = match &record.key {
                        super::super::common::AstTableKey::Name(_) => false,
                        super::super::common::AstTableKey::Expr(expr) => {
                            expr_references_any_binding(expr, bindings)
                        }
                    };
                    key_references_binding || expr_references_any_binding(&record.value, bindings)
                }
            })
        }
        super::super::common::AstExpr::FunctionExpr(function) => {
            block_references_any_binding(&function.body, bindings)
        }
        super::super::common::AstExpr::Nil
        | super::super::common::AstExpr::Boolean(_)
        | super::super::common::AstExpr::Integer(_)
        | super::super::common::AstExpr::Number(_)
        | super::super::common::AstExpr::String(_)
        | super::super::common::AstExpr::VarArg => false,
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
        AstStmt::FunctionDecl(_) | AstStmt::LocalFunctionDecl(_) => 0,
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

fn count_binding_uses_in_call(
    call: &super::super::common::AstCallKind,
    binding: AstBindingRef,
) -> usize {
    match call {
        super::super::common::AstCallKind::Call(call) => {
            count_binding_uses_in_expr(&call.callee, binding)
                + call
                    .args
                    .iter()
                    .map(|arg| count_binding_uses_in_expr(arg, binding))
                    .sum::<usize>()
        }
        super::super::common::AstCallKind::MethodCall(call) => {
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

fn count_binding_uses_in_expr(
    expr: &super::super::common::AstExpr,
    binding: AstBindingRef,
) -> usize {
    match expr {
        super::super::common::AstExpr::Var(name) if name_ref_matches_binding(name, binding) => 1,
        super::super::common::AstExpr::FieldAccess(access) => {
            count_binding_uses_in_expr(&access.base, binding)
        }
        super::super::common::AstExpr::IndexAccess(access) => {
            count_binding_uses_in_expr(&access.base, binding)
                + count_binding_uses_in_expr(&access.index, binding)
        }
        super::super::common::AstExpr::Unary(unary) => {
            count_binding_uses_in_expr(&unary.expr, binding)
        }
        super::super::common::AstExpr::Binary(binary) => {
            count_binding_uses_in_expr(&binary.lhs, binding)
                + count_binding_uses_in_expr(&binary.rhs, binding)
        }
        super::super::common::AstExpr::LogicalAnd(logical)
        | super::super::common::AstExpr::LogicalOr(logical) => {
            count_binding_uses_in_expr(&logical.lhs, binding)
                + count_binding_uses_in_expr(&logical.rhs, binding)
        }
        super::super::common::AstExpr::Call(call) => count_binding_uses_in_call(
            &super::super::common::AstCallKind::Call(call.clone()),
            binding,
        ),
        super::super::common::AstExpr::MethodCall(call) => count_binding_uses_in_call(
            &super::super::common::AstCallKind::MethodCall(call.clone()),
            binding,
        ),
        super::super::common::AstExpr::TableConstructor(table) => table
            .fields
            .iter()
            .map(|field| match field {
                super::super::common::AstTableField::Array(value) => {
                    count_binding_uses_in_expr(value, binding)
                }
                super::super::common::AstTableField::Record(record) => {
                    let key_count = match &record.key {
                        super::super::common::AstTableKey::Name(_) => 0,
                        super::super::common::AstTableKey::Expr(key) => {
                            count_binding_uses_in_expr(key, binding)
                        }
                    };
                    key_count + count_binding_uses_in_expr(&record.value, binding)
                }
            })
            .sum(),
        super::super::common::AstExpr::FunctionExpr(_) => 0,
        super::super::common::AstExpr::Nil
        | super::super::common::AstExpr::Boolean(_)
        | super::super::common::AstExpr::Integer(_)
        | super::super::common::AstExpr::Number(_)
        | super::super::common::AstExpr::String(_)
        | super::super::common::AstExpr::Var(_)
        | super::super::common::AstExpr::VarArg => 0,
    }
}

fn is_mergeable_adjacent_local_value(expr: &super::super::common::AstExpr) -> bool {
    adjacent_local_value_complexity(expr) <= ADJACENT_LOCAL_VALUE_COMPLEXITY_LIMIT
        && is_copy_like_adjacent_local_value(expr)
}

fn is_copy_like_adjacent_local_value(expr: &super::super::common::AstExpr) -> bool {
    match expr {
        super::super::common::AstExpr::Nil
        | super::super::common::AstExpr::Boolean(_)
        | super::super::common::AstExpr::Integer(_)
        | super::super::common::AstExpr::Number(_)
        | super::super::common::AstExpr::String(_)
        | super::super::common::AstExpr::Var(_) => true,
        super::super::common::AstExpr::FieldAccess(access) => {
            is_copy_like_adjacent_local_value(&access.base)
        }
        super::super::common::AstExpr::IndexAccess(access) => {
            is_copy_like_adjacent_local_value(&access.base)
                && is_copy_like_adjacent_local_value(&access.index)
        }
        super::super::common::AstExpr::Unary(_)
        | super::super::common::AstExpr::Binary(_)
        | super::super::common::AstExpr::LogicalAnd(_)
        | super::super::common::AstExpr::LogicalOr(_)
        | super::super::common::AstExpr::Call(_)
        | super::super::common::AstExpr::MethodCall(_)
        | super::super::common::AstExpr::VarArg
        | super::super::common::AstExpr::TableConstructor(_)
        | super::super::common::AstExpr::FunctionExpr(_) => false,
    }
}

fn adjacent_local_value_complexity(expr: &super::super::common::AstExpr) -> usize {
    match expr {
        super::super::common::AstExpr::Nil
        | super::super::common::AstExpr::Boolean(_)
        | super::super::common::AstExpr::Integer(_)
        | super::super::common::AstExpr::Number(_)
        | super::super::common::AstExpr::String(_)
        | super::super::common::AstExpr::Var(_)
        | super::super::common::AstExpr::VarArg => 1,
        super::super::common::AstExpr::FieldAccess(access) => {
            1 + adjacent_local_value_complexity(&access.base)
        }
        super::super::common::AstExpr::IndexAccess(access) => {
            1 + adjacent_local_value_complexity(&access.base)
                + adjacent_local_value_complexity(&access.index)
        }
        super::super::common::AstExpr::Unary(unary) => {
            1 + adjacent_local_value_complexity(&unary.expr)
        }
        super::super::common::AstExpr::Binary(binary) => {
            1 + adjacent_local_value_complexity(&binary.lhs)
                + adjacent_local_value_complexity(&binary.rhs)
        }
        super::super::common::AstExpr::LogicalAnd(logical)
        | super::super::common::AstExpr::LogicalOr(logical) => {
            1 + adjacent_local_value_complexity(&logical.lhs)
                + adjacent_local_value_complexity(&logical.rhs)
        }
        super::super::common::AstExpr::Call(call) => {
            1 + adjacent_local_value_complexity(&call.callee)
                + call
                    .args
                    .iter()
                    .map(adjacent_local_value_complexity)
                    .sum::<usize>()
        }
        super::super::common::AstExpr::MethodCall(call) => {
            1 + adjacent_local_value_complexity(&call.receiver)
                + call
                    .args
                    .iter()
                    .map(adjacent_local_value_complexity)
                    .sum::<usize>()
        }
        super::super::common::AstExpr::TableConstructor(table) => {
            1 + table
                .fields
                .iter()
                .map(|field| match field {
                    super::super::common::AstTableField::Array(value) => {
                        adjacent_local_value_complexity(value)
                    }
                    super::super::common::AstTableField::Record(record) => {
                        let key_cost = match &record.key {
                            super::super::common::AstTableKey::Name(_) => 1,
                            super::super::common::AstTableKey::Expr(key) => {
                                adjacent_local_value_complexity(key)
                            }
                        };
                        key_cost + adjacent_local_value_complexity(&record.value)
                    }
                })
                .sum::<usize>()
        }
        super::super::common::AstExpr::FunctionExpr(function) => 1 + function.body.stmts.len(),
    }
}

fn name_ref_matches_any_binding(
    name: &AstNameRef,
    bindings: &[super::super::common::AstLocalBinding],
) -> bool {
    bindings.iter().any(|binding| match (binding.id, name) {
        (AstBindingRef::Local(local), AstNameRef::Local(target)) => local == *target,
        (AstBindingRef::SyntheticLocal(local), AstNameRef::SyntheticLocal(target)) => {
            local == *target
        }
        (AstBindingRef::Temp(temp), AstNameRef::Temp(target)) => temp == *target,
        _ => false,
    })
}

fn name_ref_matches_binding(name: &AstNameRef, binding: AstBindingRef) -> bool {
    match (binding, name) {
        (AstBindingRef::Local(local), AstNameRef::Local(target)) => local == *target,
        (AstBindingRef::SyntheticLocal(local), AstNameRef::SyntheticLocal(target)) => {
            local == *target
        }
        (AstBindingRef::Temp(temp), AstNameRef::Temp(target)) => temp == *target,
        _ => false,
    }
}

fn local_binding_matches_target(binding: AstBindingRef, target: &AstLValue) -> bool {
    match (binding, target) {
        (AstBindingRef::Local(local), AstLValue::Name(AstNameRef::Local(target_local))) => {
            local == *target_local
        }
        (
            AstBindingRef::SyntheticLocal(local),
            AstLValue::Name(AstNameRef::SyntheticLocal(target_local)),
        ) => local == *target_local,
        (AstBindingRef::Temp(temp), AstLValue::Name(AstNameRef::Temp(target_temp))) => {
            temp == *target_temp
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests;
