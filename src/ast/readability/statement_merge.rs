//! 把显然属于同一次源码声明的相邻语句重新合并。

use super::super::common::{
    AstBindingRef, AstBlock, AstFunctionExpr, AstLValue, AstLocalAttr, AstLocalDecl, AstModule,
    AstNameRef, AstStmt,
};
use super::ReadabilityContext;
use super::binding_flow::{
    block_references_any_binding, count_binding_uses_in_stmts, expr_references_any_binding,
    stmt_references_any_binding,
};
use super::expr_analysis::{expr_complexity, is_copy_like_expr};

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
            if let Some((rewritten, consumed)) = try_sink_hoisted_decl_into_nested_stmt(
                &remaining,
                &block.stmts[lookahead],
                &block.stmts[(lookahead + 1)..],
            ) {
                block.stmts[lookahead] = rewritten;
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

fn try_sink_hoisted_decl_into_nested_stmt(
    pending: &[super::super::common::AstLocalBinding],
    stmt: &AstStmt,
    suffix: &[AstStmt],
) -> Option<(AstStmt, usize)> {
    let sinkable_len = pending
        .iter()
        .take_while(|binding| count_binding_uses_in_stmts(suffix, binding.id) == 0)
        .count();
    if sinkable_len == 0 {
        return None;
    }
    let sinkable = &pending[..sinkable_len];

    match stmt {
        AstStmt::If(if_stmt) => {
            if expr_references_any_binding(&if_stmt.cond, sinkable) {
                return None;
            }
            let then_refs = block_references_any_binding(&if_stmt.then_block, sinkable);
            let else_refs = if_stmt
                .else_block
                .as_ref()
                .is_some_and(|block| block_references_any_binding(block, sinkable));
            if then_refs == else_refs {
                return None;
            }

            let mut rewritten = stmt.clone();
            let target_block = match &mut rewritten {
                AstStmt::If(if_stmt) if then_refs => &mut if_stmt.then_block,
                AstStmt::If(if_stmt) => if_stmt
                    .else_block
                    .as_mut()
                    .expect("else refs imply else block"),
                _ => unreachable!("rewritten stmt must remain if"),
            };
            let consumed = sink_pending_bindings_into_block(target_block, sinkable);
            (consumed > 0).then_some((rewritten, consumed))
        }
        AstStmt::While(while_stmt) => {
            if expr_references_any_binding(&while_stmt.cond, sinkable) {
                return None;
            }
            let mut rewritten = stmt.clone();
            let AstStmt::While(while_stmt) = &mut rewritten else {
                unreachable!("rewritten stmt must remain while");
            };
            let consumed = sink_pending_bindings_into_block(&mut while_stmt.body, sinkable);
            (consumed > 0).then_some((rewritten, consumed))
        }
        AstStmt::Repeat(repeat_stmt) => {
            if expr_references_any_binding(&repeat_stmt.cond, sinkable) {
                return None;
            }
            let mut rewritten = stmt.clone();
            let AstStmt::Repeat(repeat_stmt) = &mut rewritten else {
                unreachable!("rewritten stmt must remain repeat");
            };
            let consumed = sink_pending_bindings_into_block(&mut repeat_stmt.body, sinkable);
            (consumed > 0).then_some((rewritten, consumed))
        }
        AstStmt::NumericFor(numeric_for) => {
            if expr_references_any_binding(&numeric_for.start, sinkable)
                || expr_references_any_binding(&numeric_for.limit, sinkable)
                || expr_references_any_binding(&numeric_for.step, sinkable)
            {
                return None;
            }
            let mut rewritten = stmt.clone();
            let AstStmt::NumericFor(numeric_for) = &mut rewritten else {
                unreachable!("rewritten stmt must remain numeric-for");
            };
            let consumed = sink_pending_bindings_into_block(&mut numeric_for.body, sinkable);
            (consumed > 0).then_some((rewritten, consumed))
        }
        AstStmt::GenericFor(generic_for) => {
            if generic_for
                .iterator
                .iter()
                .any(|expr| expr_references_any_binding(expr, sinkable))
            {
                return None;
            }
            let mut rewritten = stmt.clone();
            let AstStmt::GenericFor(generic_for) = &mut rewritten else {
                unreachable!("rewritten stmt must remain generic-for");
            };
            let consumed = sink_pending_bindings_into_block(&mut generic_for.body, sinkable);
            (consumed > 0).then_some((rewritten, consumed))
        }
        AstStmt::DoBlock(inner) => {
            let mut rewritten = AstBlock {
                stmts: inner.stmts.clone(),
            };
            let consumed = sink_pending_bindings_into_block(&mut rewritten, sinkable);
            (consumed > 0).then_some((AstStmt::DoBlock(Box::new(rewritten)), consumed))
        }
        AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::LocalDecl(_)
        | AstStmt::GlobalDecl(_)
        | AstStmt::Assign(_)
        | AstStmt::CallStmt(_)
        | AstStmt::Return(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_) => None,
    }
}

fn sink_pending_bindings_into_block(
    block: &mut AstBlock,
    pending: &[super::super::common::AstLocalBinding],
) -> usize {
    let mut consumed = 0usize;
    let mut index = 0usize;
    while index < block.stmts.len() && consumed < pending.len() {
        let remaining = &pending[consumed..];
        if let Some(merged) = try_sink_hoisted_decl_into_stmt(remaining, &block.stmts[index]) {
            let merged_len = merged.bindings.len();
            block.stmts[index] = AstStmt::LocalDecl(Box::new(merged));
            consumed += merged_len;
            index += 1;
            continue;
        }
        if let Some((rewritten, nested_consumed)) = try_sink_hoisted_decl_into_nested_stmt(
            remaining,
            &block.stmts[index],
            &block.stmts[(index + 1)..],
        ) {
            block.stmts[index] = rewritten;
            consumed += nested_consumed;
            index += 1;
            continue;
        }
        if stmt_references_any_binding(&block.stmts[index], remaining) {
            break;
        }
        index += 1;
    }
    consumed
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

fn stmt_references_any_binding_in_assign(
    assign: &super::super::common::AstAssign,
    bindings: &[super::super::common::AstLocalBinding],
) -> bool {
    assign
        .values
        .iter()
        .any(|value| expr_references_any_binding(value, bindings))
}

fn is_mergeable_adjacent_local_value(expr: &super::super::common::AstExpr) -> bool {
    expr_complexity(expr) <= ADJACENT_LOCAL_VALUE_COMPLEXITY_LIMIT && is_copy_like_expr(expr)
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
