//! 这个 pass 负责收回“seed local + carried local”这一类机械拆分。
//!
//! 在一些 branch-carried / loop-carried 结构里，前层为了保持 SSA 风格，会先落成：
//! `local seed = expr; local carried; ... carried = seed ...`
//! 但如果 `seed` 之后唯一的职责只是给 `carried` 提供初值，那么源码层更自然的形状
//! 往往就是只保留一个最外层 local，并在各个分支里直接更新它。

use super::super::common::{
    AstAssign, AstBindingRef, AstBlock, AstCallKind, AstExpr, AstLValue, AstLocalAttr, AstModule,
    AstNameRef, AstStmt,
};
use super::ReadabilityContext;

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let _ = context.target;
    rewrite_block(&mut module.body)
}

fn rewrite_block(block: &mut AstBlock) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        changed |= rewrite_nested(stmt);
    }

    let mut index = 0;
    while index + 1 < block.stmts.len() {
        let Some(seed) = single_initialized_local_decl(&block.stmts[index]) else {
            index += 1;
            continue;
        };
        let Some(carried) = single_empty_local_decl(&block.stmts[index + 1]) else {
            index += 1;
            continue;
        };
        if !seed_can_absorb_carried(&block.stmts[(index + 2)..], seed, carried) {
            index += 1;
            continue;
        }

        let mut tail = block.stmts.split_off(index + 2);
        rewrite_carried_binding_in_stmts(&mut tail, carried, seed);
        block.stmts.append(&mut tail);
        block.stmts.remove(index + 1);
        changed = true;
    }

    changed
}

fn rewrite_nested(stmt: &mut AstStmt) -> bool {
    match stmt {
        AstStmt::If(if_stmt) => {
            let mut changed = rewrite_block(&mut if_stmt.then_block);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= rewrite_block(else_block);
            }
            rewrite_nested_functions_in_expr(&mut if_stmt.cond) | changed
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
            changed | rewrite_block(&mut numeric_for.body)
        }
        AstStmt::GenericFor(generic_for) => {
            let mut changed = false;
            for expr in &mut generic_for.iterator {
                changed |= rewrite_nested_functions_in_expr(expr);
            }
            changed | rewrite_block(&mut generic_for.body)
        }
        AstStmt::DoBlock(block) => rewrite_block(block),
        AstStmt::FunctionDecl(function_decl) => rewrite_block(&mut function_decl.func.body),
        AstStmt::LocalFunctionDecl(function_decl) => rewrite_block(&mut function_decl.func.body),
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

fn rewrite_nested_functions_in_call(call: &mut AstCallKind) -> bool {
    match call {
        AstCallKind::Call(call) => {
            let mut changed = rewrite_nested_functions_in_expr(&mut call.callee);
            for arg in &mut call.args {
                changed |= rewrite_nested_functions_in_expr(arg);
            }
            changed
        }
        AstCallKind::MethodCall(call) => {
            let mut changed = rewrite_nested_functions_in_expr(&mut call.receiver);
            for arg in &mut call.args {
                changed |= rewrite_nested_functions_in_expr(arg);
            }
            changed
        }
    }
}

fn rewrite_nested_functions_in_lvalue(lvalue: &mut AstLValue) -> bool {
    match lvalue {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => rewrite_nested_functions_in_expr(&mut access.base),
        AstLValue::IndexAccess(access) => {
            rewrite_nested_functions_in_expr(&mut access.base)
                | rewrite_nested_functions_in_expr(&mut access.index)
        }
    }
}

fn rewrite_nested_functions_in_expr(expr: &mut AstExpr) -> bool {
    match expr {
        AstExpr::FieldAccess(access) => rewrite_nested_functions_in_expr(&mut access.base),
        AstExpr::IndexAccess(access) => {
            rewrite_nested_functions_in_expr(&mut access.base)
                | rewrite_nested_functions_in_expr(&mut access.index)
        }
        AstExpr::Unary(unary) => rewrite_nested_functions_in_expr(&mut unary.expr),
        AstExpr::Binary(binary) => {
            rewrite_nested_functions_in_expr(&mut binary.lhs)
                | rewrite_nested_functions_in_expr(&mut binary.rhs)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            rewrite_nested_functions_in_expr(&mut logical.lhs)
                | rewrite_nested_functions_in_expr(&mut logical.rhs)
        }
        AstExpr::Call(call) => {
            let mut changed = rewrite_nested_functions_in_expr(&mut call.callee);
            for arg in &mut call.args {
                changed |= rewrite_nested_functions_in_expr(arg);
            }
            changed
        }
        AstExpr::MethodCall(call) => {
            let mut changed = rewrite_nested_functions_in_expr(&mut call.receiver);
            for arg in &mut call.args {
                changed |= rewrite_nested_functions_in_expr(arg);
            }
            changed
        }
        AstExpr::TableConstructor(table) => {
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
        AstExpr::FunctionExpr(function) => rewrite_block(&mut function.body),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => false,
    }
}

fn single_initialized_local_decl(stmt: &AstStmt) -> Option<AstBindingRef> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [_value] = local_decl.values.as_slice() else {
        return None;
    };
    (binding.attr == AstLocalAttr::None).then_some(binding.id)
}

fn single_empty_local_decl(stmt: &AstStmt) -> Option<AstBindingRef> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    if !local_decl.values.is_empty() || binding.attr != AstLocalAttr::None {
        return None;
    }
    Some(binding.id)
}

fn seed_can_absorb_carried(stmts: &[AstStmt], seed: AstBindingRef, carried: AstBindingRef) -> bool {
    stmts
        .iter()
        .all(|stmt| stmt_allows_seed_to_absorb_carried(stmt, seed, carried))
}

fn stmt_allows_seed_to_absorb_carried(
    stmt: &AstStmt,
    seed: AstBindingRef,
    carried: AstBindingRef,
) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            local_decl
                .bindings
                .iter()
                .all(|binding| binding.id != seed && binding.id != carried)
                && local_decl
                    .values
                    .iter()
                    .all(|value| !expr_references_binding(value, seed))
        }
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .all(|value| !expr_references_binding(value, seed)),
        AstStmt::Assign(assign) => {
            if is_exact_seed_copy_assign(assign, carried, seed) {
                true
            } else {
                !assign_targets_binding(assign, seed)
                    && assign
                        .targets
                        .iter()
                        .all(|target| !lvalue_references_binding(target, seed))
                    && assign
                        .values
                        .iter()
                        .all(|value| !expr_references_binding(value, seed))
            }
        }
        AstStmt::CallStmt(call_stmt) => !call_references_binding(&call_stmt.call, seed),
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .all(|value| !expr_references_binding(value, seed)),
        AstStmt::If(if_stmt) => {
            !expr_references_binding(&if_stmt.cond, seed)
                && seed_can_absorb_carried(&if_stmt.then_block.stmts, seed, carried)
                && if_stmt
                    .else_block
                    .as_ref()
                    .is_none_or(|block| seed_can_absorb_carried(&block.stmts, seed, carried))
        }
        AstStmt::While(while_stmt) => {
            !expr_references_binding(&while_stmt.cond, seed)
                && seed_can_absorb_carried(&while_stmt.body.stmts, seed, carried)
        }
        AstStmt::Repeat(repeat_stmt) => {
            seed_can_absorb_carried(&repeat_stmt.body.stmts, seed, carried)
                && !expr_references_binding(&repeat_stmt.cond, seed)
        }
        AstStmt::NumericFor(numeric_for) => {
            numeric_for.binding != seed
                && numeric_for.binding != carried
                && !expr_references_binding(&numeric_for.start, seed)
                && !expr_references_binding(&numeric_for.limit, seed)
                && !expr_references_binding(&numeric_for.step, seed)
                && seed_can_absorb_carried(&numeric_for.body.stmts, seed, carried)
        }
        AstStmt::GenericFor(generic_for) => {
            !generic_for
                .bindings
                .iter()
                .any(|binding| *binding == seed || *binding == carried)
                && generic_for
                    .iterator
                    .iter()
                    .all(|expr| !expr_references_binding(expr, seed))
                && seed_can_absorb_carried(&generic_for.body.stmts, seed, carried)
        }
        AstStmt::DoBlock(block) => seed_can_absorb_carried(&block.stmts, seed, carried),
        AstStmt::FunctionDecl(function_decl) => {
            !function_name_references_binding(&function_decl.target, seed)
        }
        AstStmt::LocalFunctionDecl(function_decl) => function_decl.name != seed,
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => true,
    }
}

fn rewrite_carried_binding_in_stmts(
    stmts: &mut Vec<AstStmt>,
    carried: AstBindingRef,
    seed: AstBindingRef,
) {
    for stmt in stmts.iter_mut() {
        rewrite_carried_binding_in_stmt(stmt, carried, seed);
    }
    stmts.retain(|stmt| {
        !is_exact_copy_stmt(stmt, carried, seed) && !is_redundant_self_assign(stmt, seed)
    });
}

fn rewrite_carried_binding_in_stmt(
    stmt: &mut AstStmt,
    carried: AstBindingRef,
    seed: AstBindingRef,
) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for value in &mut local_decl.values {
                rewrite_binding_in_expr(value, carried, seed);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &mut global_decl.values {
                rewrite_binding_in_expr(value, carried, seed);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &mut assign.targets {
                rewrite_binding_in_lvalue(target, carried, seed);
            }
            for value in &mut assign.values {
                rewrite_binding_in_expr(value, carried, seed);
            }
        }
        AstStmt::CallStmt(call_stmt) => rewrite_binding_in_call(&mut call_stmt.call, carried, seed),
        AstStmt::Return(ret) => {
            for value in &mut ret.values {
                rewrite_binding_in_expr(value, carried, seed);
            }
        }
        AstStmt::If(if_stmt) => {
            rewrite_binding_in_expr(&mut if_stmt.cond, carried, seed);
            rewrite_carried_binding_in_stmts(&mut if_stmt.then_block.stmts, carried, seed);
            if let Some(else_block) = &mut if_stmt.else_block {
                rewrite_carried_binding_in_stmts(&mut else_block.stmts, carried, seed);
            }
        }
        AstStmt::While(while_stmt) => {
            rewrite_binding_in_expr(&mut while_stmt.cond, carried, seed);
            rewrite_carried_binding_in_stmts(&mut while_stmt.body.stmts, carried, seed);
        }
        AstStmt::Repeat(repeat_stmt) => {
            rewrite_carried_binding_in_stmts(&mut repeat_stmt.body.stmts, carried, seed);
            rewrite_binding_in_expr(&mut repeat_stmt.cond, carried, seed);
        }
        AstStmt::NumericFor(numeric_for) => {
            rewrite_binding_in_expr(&mut numeric_for.start, carried, seed);
            rewrite_binding_in_expr(&mut numeric_for.limit, carried, seed);
            rewrite_binding_in_expr(&mut numeric_for.step, carried, seed);
            rewrite_carried_binding_in_stmts(&mut numeric_for.body.stmts, carried, seed);
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &mut generic_for.iterator {
                rewrite_binding_in_expr(expr, carried, seed);
            }
            rewrite_carried_binding_in_stmts(&mut generic_for.body.stmts, carried, seed);
        }
        AstStmt::DoBlock(block) => {
            rewrite_carried_binding_in_stmts(&mut block.stmts, carried, seed)
        }
        AstStmt::FunctionDecl(_) | AstStmt::LocalFunctionDecl(_) => {}
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => {}
    }
}

fn rewrite_binding_in_call(call: &mut AstCallKind, carried: AstBindingRef, seed: AstBindingRef) {
    match call {
        AstCallKind::Call(call) => {
            rewrite_binding_in_expr(&mut call.callee, carried, seed);
            for arg in &mut call.args {
                rewrite_binding_in_expr(arg, carried, seed);
            }
        }
        AstCallKind::MethodCall(call) => {
            rewrite_binding_in_expr(&mut call.receiver, carried, seed);
            for arg in &mut call.args {
                rewrite_binding_in_expr(arg, carried, seed);
            }
        }
    }
}

fn rewrite_binding_in_lvalue(target: &mut AstLValue, carried: AstBindingRef, seed: AstBindingRef) {
    match target {
        AstLValue::Name(name) => rewrite_binding_in_name(name, carried, seed),
        AstLValue::FieldAccess(access) => rewrite_binding_in_expr(&mut access.base, carried, seed),
        AstLValue::IndexAccess(access) => {
            rewrite_binding_in_expr(&mut access.base, carried, seed);
            rewrite_binding_in_expr(&mut access.index, carried, seed);
        }
    }
}

fn rewrite_binding_in_expr(expr: &mut AstExpr, carried: AstBindingRef, seed: AstBindingRef) {
    match expr {
        AstExpr::Var(name) => rewrite_binding_in_name(name, carried, seed),
        AstExpr::FieldAccess(access) => rewrite_binding_in_expr(&mut access.base, carried, seed),
        AstExpr::IndexAccess(access) => {
            rewrite_binding_in_expr(&mut access.base, carried, seed);
            rewrite_binding_in_expr(&mut access.index, carried, seed);
        }
        AstExpr::Unary(unary) => rewrite_binding_in_expr(&mut unary.expr, carried, seed),
        AstExpr::Binary(binary) => {
            rewrite_binding_in_expr(&mut binary.lhs, carried, seed);
            rewrite_binding_in_expr(&mut binary.rhs, carried, seed);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            rewrite_binding_in_expr(&mut logical.lhs, carried, seed);
            rewrite_binding_in_expr(&mut logical.rhs, carried, seed);
        }
        AstExpr::Call(call) => {
            rewrite_binding_in_expr(&mut call.callee, carried, seed);
            for arg in &mut call.args {
                rewrite_binding_in_expr(arg, carried, seed);
            }
        }
        AstExpr::MethodCall(call) => {
            rewrite_binding_in_expr(&mut call.receiver, carried, seed);
            for arg in &mut call.args {
                rewrite_binding_in_expr(arg, carried, seed);
            }
        }
        AstExpr::TableConstructor(table) => {
            for field in &mut table.fields {
                match field {
                    super::super::common::AstTableField::Array(value) => {
                        rewrite_binding_in_expr(value, carried, seed);
                    }
                    super::super::common::AstTableField::Record(record) => {
                        if let super::super::common::AstTableKey::Expr(key) = &mut record.key {
                            rewrite_binding_in_expr(key, carried, seed);
                        }
                        rewrite_binding_in_expr(&mut record.value, carried, seed);
                    }
                }
            }
        }
        AstExpr::FunctionExpr(_) => {}
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::VarArg => {}
    }
}

fn rewrite_binding_in_name(name: &mut AstNameRef, carried: AstBindingRef, seed: AstBindingRef) {
    if name_matches_binding(name, carried) {
        *name = binding_to_name(seed);
    }
}

fn is_exact_copy_stmt(stmt: &AstStmt, carried: AstBindingRef, seed: AstBindingRef) -> bool {
    let AstStmt::Assign(assign) = stmt else {
        return false;
    };
    is_exact_seed_copy_assign(assign, carried, seed)
}

fn is_redundant_self_assign(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    let AstStmt::Assign(assign) = stmt else {
        return false;
    };
    let [AstLValue::Name(target)] = assign.targets.as_slice() else {
        return false;
    };
    let [AstExpr::Var(value)] = assign.values.as_slice() else {
        return false;
    };
    name_matches_binding(target, binding) && name_matches_binding(value, binding)
}

fn is_exact_seed_copy_assign(
    assign: &AstAssign,
    carried: AstBindingRef,
    seed: AstBindingRef,
) -> bool {
    let [AstLValue::Name(target)] = assign.targets.as_slice() else {
        return false;
    };
    let [AstExpr::Var(value)] = assign.values.as_slice() else {
        return false;
    };
    name_matches_binding(target, carried) && name_matches_binding(value, seed)
}

fn assign_targets_binding(assign: &AstAssign, binding: AstBindingRef) -> bool {
    assign.targets.iter().any(|target| match target {
        AstLValue::Name(name) => name_matches_binding(name, binding),
        AstLValue::FieldAccess(_) | AstLValue::IndexAccess(_) => false,
    })
}

fn function_name_references_binding(
    target: &super::super::common::AstFunctionName,
    binding: AstBindingRef,
) -> bool {
    let path = match target {
        super::super::common::AstFunctionName::Plain(path) => path,
        super::super::common::AstFunctionName::Method(path, _) => path,
    };
    name_matches_binding(&path.root, binding)
}

fn call_references_binding(call: &AstCallKind, binding: AstBindingRef) -> bool {
    match call {
        AstCallKind::Call(call) => {
            expr_references_binding(&call.callee, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_binding(arg, binding))
        }
        AstCallKind::MethodCall(call) => {
            expr_references_binding(&call.receiver, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_binding(arg, binding))
        }
    }
}

fn lvalue_references_binding(target: &AstLValue, binding: AstBindingRef) -> bool {
    match target {
        AstLValue::Name(name) => name_matches_binding(name, binding),
        AstLValue::FieldAccess(access) => expr_references_binding(&access.base, binding),
        AstLValue::IndexAccess(access) => {
            expr_references_binding(&access.base, binding)
                || expr_references_binding(&access.index, binding)
        }
    }
}

fn expr_references_binding(expr: &AstExpr, binding: AstBindingRef) -> bool {
    match expr {
        AstExpr::Var(name) => name_matches_binding(name, binding),
        AstExpr::FieldAccess(access) => expr_references_binding(&access.base, binding),
        AstExpr::IndexAccess(access) => {
            expr_references_binding(&access.base, binding)
                || expr_references_binding(&access.index, binding)
        }
        AstExpr::Unary(unary) => expr_references_binding(&unary.expr, binding),
        AstExpr::Binary(binary) => {
            expr_references_binding(&binary.lhs, binding)
                || expr_references_binding(&binary.rhs, binding)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_references_binding(&logical.lhs, binding)
                || expr_references_binding(&logical.rhs, binding)
        }
        AstExpr::Call(call) => {
            expr_references_binding(&call.callee, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_binding(arg, binding))
        }
        AstExpr::MethodCall(call) => {
            expr_references_binding(&call.receiver, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_binding(arg, binding))
        }
        AstExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            super::super::common::AstTableField::Array(value) => {
                expr_references_binding(value, binding)
            }
            super::super::common::AstTableField::Record(record) => {
                let key_references = match &record.key {
                    super::super::common::AstTableKey::Name(_) => false,
                    super::super::common::AstTableKey::Expr(key) => {
                        expr_references_binding(key, binding)
                    }
                };
                key_references || expr_references_binding(&record.value, binding)
            }
        }),
        AstExpr::FunctionExpr(_) => false,
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::VarArg => false,
    }
}

fn binding_to_name(binding: AstBindingRef) -> AstNameRef {
    match binding {
        AstBindingRef::Local(local) => AstNameRef::Local(local),
        AstBindingRef::Temp(temp) => AstNameRef::Temp(temp),
        AstBindingRef::SyntheticLocal(local) => AstNameRef::SyntheticLocal(local),
    }
}

fn name_matches_binding(name: &AstNameRef, binding: AstBindingRef) -> bool {
    match (binding, name) {
        (AstBindingRef::Local(local), AstNameRef::Local(target)) => local == *target,
        (AstBindingRef::Temp(temp), AstNameRef::Temp(target)) => temp == *target,
        (AstBindingRef::SyntheticLocal(local), AstNameRef::SyntheticLocal(target)) => {
            local == *target
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests;
