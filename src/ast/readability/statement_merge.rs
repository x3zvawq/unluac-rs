//! 把显然属于同一次源码声明的相邻语句重新合并。

use super::super::common::{
    AstBindingRef, AstBlock, AstFunctionExpr, AstLValue, AstLocalAttr, AstLocalDecl, AstModule,
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
            let mut changed = rewrite_block(&mut if_stmt.then_block);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= rewrite_block(else_block);
            }
            changed
        }
        AstStmt::While(while_stmt) => rewrite_block(&mut while_stmt.body),
        AstStmt::Repeat(repeat_stmt) => rewrite_block(&mut repeat_stmt.body),
        AstStmt::NumericFor(numeric_for) => rewrite_block(&mut numeric_for.body),
        AstStmt::GenericFor(generic_for) => rewrite_block(&mut generic_for.body),
        AstStmt::DoBlock(block) => rewrite_block(block),
        AstStmt::FunctionDecl(function_decl) => rewrite_function(&mut function_decl.func),
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            rewrite_function(&mut local_function_decl.func)
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

fn rewrite_function(function: &mut AstFunctionExpr) -> bool {
    rewrite_block(&mut function.body)
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
mod tests {
    use crate::ast::common::{AstCallExpr, AstCallKind, AstLocalBinding};
    use crate::ast::{
        AstExpr, AstLValue, AstLocalAttr, AstLocalDecl, AstModule, AstNameRef, AstStmt,
        AstTargetDialect, make_readable_with_options,
    };
    use crate::hir::{LocalId, TempId};

    #[test]
    fn merges_empty_local_decl_followed_by_matching_assign() {
        let temp = TempId(0);
        let module = AstModule {
            entry_function: Default::default(),
            body: crate::ast::AstBlock {
                stmts: vec![
                    AstStmt::LocalDecl(Box::new(AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: crate::ast::AstBindingRef::Temp(temp),
                            attr: AstLocalAttr::None,
                        }],
                        values: Vec::new(),
                    })),
                    AstStmt::Assign(Box::new(crate::ast::AstAssign {
                        targets: vec![AstLValue::Name(AstNameRef::Temp(temp))],
                        values: vec![AstExpr::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                            args: vec![AstExpr::Integer(1)],
                        }))],
                    })),
                ],
            },
        };

        let module = make_readable_with_options(
            &module,
            AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            Default::default(),
        );
        assert_eq!(
            module.body.stmts,
            vec![AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings: vec![AstLocalBinding {
                    id: crate::ast::AstBindingRef::SyntheticLocal(crate::ast::AstSyntheticLocalId(
                        temp,
                    )),
                    attr: AstLocalAttr::None,
                }],
                values: vec![AstExpr::Call(Box::new(AstCallExpr {
                    callee: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                    args: vec![AstExpr::Integer(1)],
                }))],
            }))]
        );
    }

    #[test]
    fn does_not_merge_when_assign_targets_do_not_match_decl_bindings() {
        let module = AstModule {
            entry_function: Default::default(),
            body: crate::ast::AstBlock {
                stmts: vec![
                    AstStmt::LocalDecl(Box::new(AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: crate::ast::AstBindingRef::Local(LocalId(0)),
                            attr: AstLocalAttr::None,
                        }],
                        values: Vec::new(),
                    })),
                    AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                        call: AstCallKind::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Var(AstNameRef::Local(LocalId(1))),
                            args: vec![AstExpr::Integer(1)],
                        })),
                    })),
                ],
            },
        };

        let module = make_readable_with_options(
            &module,
            AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            Default::default(),
        );
        assert_eq!(module.body.stmts.len(), 2);
    }
}
