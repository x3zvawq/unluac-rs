//! 结构安全的 AST cleanup。

use std::collections::BTreeMap;

use super::super::common::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstModule, AstStmt,
};
use super::ReadabilityContext;
use super::binding_flow::count_binding_mentions_in_block;

pub(super) fn apply(module: &mut AstModule, _context: ReadabilityContext) -> bool {
    cleanup_block(&mut module.body, true)
}

fn cleanup_block(block: &mut AstBlock, allow_trailing_empty_return_elision: bool) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        changed |= cleanup_stmt(stmt);
    }

    let old_stmts = std::mem::take(&mut block.stmts);
    let mut flattened_stmts = Vec::with_capacity(old_stmts.len());
    for stmt in old_stmts {
        match stmt {
            AstStmt::DoBlock(nested)
                if nested.stmts.len() == 1 && can_elide_single_stmt_do_block(&nested.stmts[0]) =>
            {
                // 这里专门清理“只剩一条非局部作用域语句”的机械 do-end。
                // 它通常是前层为了暂存中间 local 范围而留下来的壳；一旦内部局部已经被
                // 其他 pass 收回，这层壳继续保留只会让源码多出无意义缩进。
                flattened_stmts.push(nested.stmts[0].clone());
                changed = true;
            }
            other => flattened_stmts.push(other),
        }
    }
    block.stmts = flattened_stmts;

    let mechanical_binding_uses = collect_mechanical_binding_uses(block);
    for stmt in &mut block.stmts {
        let AstStmt::LocalDecl(local_decl) = stmt else {
            continue;
        };
        if !local_decl.values.is_empty() {
            continue;
        }
        let original_len = local_decl.bindings.len();
        local_decl.bindings.retain(|binding| match binding.id {
            AstBindingRef::Temp(_) | AstBindingRef::SyntheticLocal(_) => {
                mechanical_binding_uses
                    .get(&binding.id)
                    .copied()
                    .unwrap_or_default()
                    > 0
            }
            AstBindingRef::Local(_) => true,
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

fn can_elide_single_stmt_do_block(stmt: &AstStmt) -> bool {
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
            | AstStmt::Break
            | AstStmt::Continue
            | AstStmt::Goto(_)
            | AstStmt::FunctionDecl(_)
    )
}

fn collect_mechanical_binding_uses(block: &AstBlock) -> BTreeMap<AstBindingRef, usize> {
    let mut uses = BTreeMap::new();
    for stmt in &block.stmts {
        let AstStmt::LocalDecl(local_decl) = stmt else {
            continue;
        };
        for binding in &local_decl.bindings {
            if matches!(
                binding.id,
                AstBindingRef::Temp(_) | AstBindingRef::SyntheticLocal(_)
            ) {
                uses.entry(binding.id)
                    .or_insert_with(|| count_binding_mentions_in_block(block, binding.id));
            }
        }
    }
    uses
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

#[cfg(test)]
mod tests;
