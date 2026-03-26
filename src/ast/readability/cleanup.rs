//! 结构安全的 AST cleanup。

use std::collections::BTreeMap;

use crate::hir::TempId;

use super::super::common::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstModule, AstStmt,
};
use super::ReadabilityContext;

pub(super) fn apply(module: &mut AstModule, _context: ReadabilityContext) -> bool {
    cleanup_block(&mut module.body, true)
}

fn cleanup_block(block: &mut AstBlock, allow_trailing_empty_return_elision: bool) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        changed |= cleanup_stmt(stmt);
    }

    let temp_uses = collect_temp_uses_in_block(block);
    for stmt in &mut block.stmts {
        let AstStmt::LocalDecl(local_decl) = stmt else {
            continue;
        };
        if !local_decl.values.is_empty() {
            continue;
        }
        let original_len = local_decl.bindings.len();
        local_decl.bindings.retain(|binding| match binding.id {
            AstBindingRef::Temp(temp) => temp_uses.get(&temp).copied().unwrap_or(0) > 0,
            AstBindingRef::Local(_) | AstBindingRef::SyntheticLocal(_) => true,
        });
        changed |= local_decl.bindings.len() != original_len;
    }

    let original_len = block.stmts.len();
    block.stmts.retain(|stmt| match stmt {
        AstStmt::LocalDecl(local_decl) => {
            !(local_decl.bindings.is_empty() && local_decl.values.is_empty())
        }
        _ => true,
    });
    changed |= block.stmts.len() != original_len;

    if allow_trailing_empty_return_elision
        && matches!(
            block.stmts.last(),
            Some(AstStmt::Return(ret)) if ret.values.is_empty()
        )
    {
        // 尾部无值 return 只是 VM 的函数/chunk 结束痕迹，不是值得保留到源码层的语句。
        block.stmts.pop();
        changed = true;
    }

    changed
}

fn cleanup_stmt(stmt: &mut AstStmt) -> bool {
    match stmt {
        AstStmt::If(if_stmt) => {
            let mut changed = cleanup_block(&mut if_stmt.then_block, false);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= cleanup_block(else_block, false);
            }
            cleanup_function_exprs_in_expr(&mut if_stmt.cond) || changed
        }
        AstStmt::While(while_stmt) => {
            cleanup_function_exprs_in_expr(&mut while_stmt.cond)
                | cleanup_block(&mut while_stmt.body, false)
        }
        AstStmt::Repeat(repeat_stmt) => {
            cleanup_block(&mut repeat_stmt.body, false)
                | cleanup_function_exprs_in_expr(&mut repeat_stmt.cond)
        }
        AstStmt::NumericFor(numeric_for) => {
            let mut changed = cleanup_function_exprs_in_expr(&mut numeric_for.start);
            changed |= cleanup_function_exprs_in_expr(&mut numeric_for.limit);
            changed |= cleanup_function_exprs_in_expr(&mut numeric_for.step);
            changed | cleanup_block(&mut numeric_for.body, false)
        }
        AstStmt::GenericFor(generic_for) => {
            let mut changed = false;
            for expr in &mut generic_for.iterator {
                changed |= cleanup_function_exprs_in_expr(expr);
            }
            changed | cleanup_block(&mut generic_for.body, false)
        }
        AstStmt::DoBlock(block) => cleanup_block(block, false),
        AstStmt::FunctionDecl(function_decl) => cleanup_function_expr(&mut function_decl.func),
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            cleanup_function_expr(&mut local_function_decl.func)
        }
        AstStmt::LocalDecl(local_decl) => {
            let mut changed = false;
            for value in &mut local_decl.values {
                changed |= cleanup_function_exprs_in_expr(value);
            }
            changed
        }
        AstStmt::GlobalDecl(global_decl) => {
            let mut changed = false;
            for value in &mut global_decl.values {
                changed |= cleanup_function_exprs_in_expr(value);
            }
            changed
        }
        AstStmt::Assign(assign) => {
            let mut changed = false;
            for target in &mut assign.targets {
                changed |= cleanup_function_exprs_in_lvalue(target);
            }
            for value in &mut assign.values {
                changed |= cleanup_function_exprs_in_expr(value);
            }
            changed
        }
        AstStmt::CallStmt(call_stmt) => cleanup_function_exprs_in_call(&mut call_stmt.call),
        AstStmt::Return(ret) => {
            let mut changed = false;
            for value in &mut ret.values {
                changed |= cleanup_function_exprs_in_expr(value);
            }
            changed
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => false,
    }
}

fn cleanup_function_expr(function: &mut AstFunctionExpr) -> bool {
    cleanup_block(&mut function.body, true)
}

fn cleanup_function_exprs_in_call(call: &mut AstCallKind) -> bool {
    match call {
        AstCallKind::Call(call) => {
            let mut changed = cleanup_function_exprs_in_expr(&mut call.callee);
            for arg in &mut call.args {
                changed |= cleanup_function_exprs_in_expr(arg);
            }
            changed
        }
        AstCallKind::MethodCall(call) => {
            let mut changed = cleanup_function_exprs_in_expr(&mut call.receiver);
            for arg in &mut call.args {
                changed |= cleanup_function_exprs_in_expr(arg);
            }
            changed
        }
    }
}

fn cleanup_function_exprs_in_lvalue(target: &mut AstLValue) -> bool {
    match target {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => cleanup_function_exprs_in_expr(&mut access.base),
        AstLValue::IndexAccess(access) => {
            cleanup_function_exprs_in_expr(&mut access.base)
                | cleanup_function_exprs_in_expr(&mut access.index)
        }
    }
}

fn cleanup_function_exprs_in_expr(expr: &mut AstExpr) -> bool {
    match expr {
        AstExpr::FieldAccess(access) => cleanup_function_exprs_in_expr(&mut access.base),
        AstExpr::IndexAccess(access) => {
            cleanup_function_exprs_in_expr(&mut access.base)
                | cleanup_function_exprs_in_expr(&mut access.index)
        }
        AstExpr::Unary(unary) => cleanup_function_exprs_in_expr(&mut unary.expr),
        AstExpr::Binary(binary) => {
            cleanup_function_exprs_in_expr(&mut binary.lhs)
                | cleanup_function_exprs_in_expr(&mut binary.rhs)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            cleanup_function_exprs_in_expr(&mut logical.lhs)
                | cleanup_function_exprs_in_expr(&mut logical.rhs)
        }
        AstExpr::Call(call) => {
            let mut changed = cleanup_function_exprs_in_expr(&mut call.callee);
            for arg in &mut call.args {
                changed |= cleanup_function_exprs_in_expr(arg);
            }
            changed
        }
        AstExpr::MethodCall(call) => {
            let mut changed = cleanup_function_exprs_in_expr(&mut call.receiver);
            for arg in &mut call.args {
                changed |= cleanup_function_exprs_in_expr(arg);
            }
            changed
        }
        AstExpr::TableConstructor(table) => {
            let mut changed = false;
            for field in &mut table.fields {
                match field {
                    super::super::common::AstTableField::Array(value) => {
                        changed |= cleanup_function_exprs_in_expr(value);
                    }
                    super::super::common::AstTableField::Record(record) => {
                        if let super::super::common::AstTableKey::Expr(key) = &mut record.key {
                            changed |= cleanup_function_exprs_in_expr(key);
                        }
                        changed |= cleanup_function_exprs_in_expr(&mut record.value);
                    }
                }
            }
            changed
        }
        AstExpr::FunctionExpr(function) => cleanup_function_expr(function),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => false,
    }
}

fn collect_temp_uses_in_block(block: &AstBlock) -> BTreeMap<TempId, usize> {
    let mut uses = BTreeMap::new();
    for stmt in &block.stmts {
        collect_temp_uses_in_stmt(stmt, &mut uses);
    }
    uses
}

fn collect_temp_uses_in_stmt(stmt: &AstStmt, uses: &mut BTreeMap<TempId, usize>) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_temp_uses_in_expr(value, uses);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &global_decl.values {
                collect_temp_uses_in_expr(value, uses);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_temp_uses_in_lvalue(target, uses);
            }
            for value in &assign.values {
                collect_temp_uses_in_expr(value, uses);
            }
        }
        AstStmt::CallStmt(call_stmt) => collect_temp_uses_in_call(&call_stmt.call, uses),
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_temp_uses_in_expr(value, uses);
            }
        }
        AstStmt::If(if_stmt) => {
            collect_temp_uses_in_expr(&if_stmt.cond, uses);
            collect_temp_uses_in_block(&if_stmt.then_block)
                .into_iter()
                .for_each(|(temp, count)| *uses.entry(temp).or_insert(0) += count);
            if let Some(else_block) = &if_stmt.else_block {
                collect_temp_uses_in_block(else_block)
                    .into_iter()
                    .for_each(|(temp, count)| *uses.entry(temp).or_insert(0) += count);
            }
        }
        AstStmt::While(while_stmt) => {
            collect_temp_uses_in_expr(&while_stmt.cond, uses);
            collect_temp_uses_in_block(&while_stmt.body)
                .into_iter()
                .for_each(|(temp, count)| *uses.entry(temp).or_insert(0) += count);
        }
        AstStmt::Repeat(repeat_stmt) => {
            collect_temp_uses_in_block(&repeat_stmt.body)
                .into_iter()
                .for_each(|(temp, count)| *uses.entry(temp).or_insert(0) += count);
            collect_temp_uses_in_expr(&repeat_stmt.cond, uses);
        }
        AstStmt::NumericFor(numeric_for) => {
            collect_temp_uses_in_expr(&numeric_for.start, uses);
            collect_temp_uses_in_expr(&numeric_for.limit, uses);
            collect_temp_uses_in_expr(&numeric_for.step, uses);
            collect_temp_uses_in_block(&numeric_for.body)
                .into_iter()
                .for_each(|(temp, count)| *uses.entry(temp).or_insert(0) += count);
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &generic_for.iterator {
                collect_temp_uses_in_expr(expr, uses);
            }
            collect_temp_uses_in_block(&generic_for.body)
                .into_iter()
                .for_each(|(temp, count)| *uses.entry(temp).or_insert(0) += count);
        }
        AstStmt::DoBlock(block) => {
            collect_temp_uses_in_block(block)
                .into_iter()
                .for_each(|(temp, count)| *uses.entry(temp).or_insert(0) += count);
        }
        AstStmt::FunctionDecl(function_decl) => {
            collect_temp_uses_in_block(&function_decl.func.body)
                .into_iter()
                .for_each(|(temp, count)| *uses.entry(temp).or_insert(0) += count);
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            collect_temp_uses_in_block(&local_function_decl.func.body)
                .into_iter()
                .for_each(|(temp, count)| *uses.entry(temp).or_insert(0) += count);
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => {}
    }
}

fn collect_temp_uses_in_call(call: &AstCallKind, uses: &mut BTreeMap<TempId, usize>) {
    match call {
        AstCallKind::Call(call) => {
            collect_temp_uses_in_expr(&call.callee, uses);
            for arg in &call.args {
                collect_temp_uses_in_expr(arg, uses);
            }
        }
        AstCallKind::MethodCall(call) => {
            collect_temp_uses_in_expr(&call.receiver, uses);
            for arg in &call.args {
                collect_temp_uses_in_expr(arg, uses);
            }
        }
    }
}

fn collect_temp_uses_in_lvalue(target: &AstLValue, uses: &mut BTreeMap<TempId, usize>) {
    match target {
        AstLValue::Name(super::super::common::AstNameRef::Temp(temp)) => {
            *uses.entry(*temp).or_insert(0) += 1;
        }
        AstLValue::Name(_) => {}
        AstLValue::FieldAccess(access) => collect_temp_uses_in_expr(&access.base, uses),
        AstLValue::IndexAccess(access) => {
            collect_temp_uses_in_expr(&access.base, uses);
            collect_temp_uses_in_expr(&access.index, uses);
        }
    }
}

fn collect_temp_uses_in_expr(expr: &AstExpr, uses: &mut BTreeMap<TempId, usize>) {
    match expr {
        AstExpr::Var(super::super::common::AstNameRef::Temp(temp)) => {
            *uses.entry(*temp).or_insert(0) += 1;
        }
        AstExpr::FieldAccess(access) => collect_temp_uses_in_expr(&access.base, uses),
        AstExpr::IndexAccess(access) => {
            collect_temp_uses_in_expr(&access.base, uses);
            collect_temp_uses_in_expr(&access.index, uses);
        }
        AstExpr::Unary(unary) => collect_temp_uses_in_expr(&unary.expr, uses),
        AstExpr::Binary(binary) => {
            collect_temp_uses_in_expr(&binary.lhs, uses);
            collect_temp_uses_in_expr(&binary.rhs, uses);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            collect_temp_uses_in_expr(&logical.lhs, uses);
            collect_temp_uses_in_expr(&logical.rhs, uses);
        }
        AstExpr::Call(call) => collect_temp_uses_in_call(&AstCallKind::Call(call.clone()), uses),
        AstExpr::MethodCall(call) => {
            collect_temp_uses_in_call(&AstCallKind::MethodCall(call.clone()), uses)
        }
        AstExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    super::super::common::AstTableField::Array(value) => {
                        collect_temp_uses_in_expr(value, uses);
                    }
                    super::super::common::AstTableField::Record(record) => {
                        if let super::super::common::AstTableKey::Expr(key) = &record.key {
                            collect_temp_uses_in_expr(key, uses);
                        }
                        collect_temp_uses_in_expr(&record.value, uses);
                    }
                }
            }
        }
        AstExpr::FunctionExpr(function) => {
            collect_temp_uses_in_block(&function.body)
                .into_iter()
                .for_each(|(temp, count)| *uses.entry(temp).or_insert(0) += count);
        }
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => {}
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{
        AstBlock, AstExpr, AstFunctionExpr, AstIf, AstLocalFunctionDecl, AstModule, AstReturn,
        AstStmt, AstTargetDialect,
    };
    use crate::hir::{LocalId, ParamId};

    use super::{ReadabilityContext, apply};

    #[test]
    fn removes_trailing_empty_return_from_module_and_function_bodies() {
        let local = LocalId(0);
        let mut module = AstModule {
            entry_function: Default::default(),
            body: AstBlock {
                stmts: vec![
                    AstStmt::LocalFunctionDecl(Box::new(AstLocalFunctionDecl {
                        name: crate::ast::AstBindingRef::Local(local),
                        func: AstFunctionExpr {
                            function: Default::default(),
                            params: vec![ParamId(0)],
                            is_vararg: false,
                            body: AstBlock {
                                stmts: vec![AstStmt::Return(Box::new(AstReturn {
                                    values: vec![],
                                }))],
                            },
                        },
                    })),
                    AstStmt::Return(Box::new(AstReturn { values: vec![] })),
                ],
            },
        };

        assert!(apply(
            &mut module,
            ReadabilityContext {
                target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
                options: Default::default(),
            }
        ));

        let AstStmt::LocalFunctionDecl(local_fn) = &module.body.stmts[0] else {
            panic!("expected local function decl");
        };
        assert!(local_fn.func.body.stmts.is_empty(), "{module:#?}");
        assert_eq!(module.body.stmts.len(), 1, "{module:#?}");
    }

    #[test]
    fn keeps_empty_return_inside_nested_control_flow_blocks() {
        let mut module = AstModule {
            entry_function: Default::default(),
            body: AstBlock {
                stmts: vec![AstStmt::If(Box::new(AstIf {
                    cond: AstExpr::Boolean(true),
                    then_block: AstBlock {
                        stmts: vec![AstStmt::Return(Box::new(AstReturn { values: vec![] }))],
                    },
                    else_block: None,
                }))],
            },
        };

        assert!(!apply(
            &mut module,
            ReadabilityContext {
                target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
                options: Default::default(),
            }
        ));

        let AstStmt::If(ast_if) = &module.body.stmts[0] else {
            panic!("expected if statement");
        };
        assert!(matches!(
            ast_if.then_block.stmts.as_slice(),
            [AstStmt::Return(ret)] if ret.values.is_empty()
        ));
    }
}
