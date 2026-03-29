//! 这个文件负责清理已经没有源码意义的机械 AST 壳。
//!
//! 它依赖前面的结构恢复和 readability pass 已经把真正需要保留的局部作用域、
//! 控制流和显式 return 暴露出来；这里专门删除“只剩形式意义”的 do-end、空 local、
//! 以及 chunk/function 结尾的无值 return。它不会越权合并业务语句，也不会把仍有
//! 词法意义的块错误拍平。
//!
//! 例子：
//! - `do print(x) end` 会在内部没有局部作用域意义时折成 `print(x)`
//! - `local t0` 这种只剩机械 temp 壳、且没有值也没有使用的声明会被删除
//! - 函数尾部的 `return` 会在没有返回值时被去掉

use std::collections::BTreeMap;

use super::super::common::{AstBindingRef, AstBlock, AstModule, AstStmt};
use super::ReadabilityContext;
use super::binding_flow::{count_binding_mentions_in_block, count_binding_uses_in_stmts};
use super::expr_analysis::{is_context_safe_expr, is_copy_like_expr, is_lookup_inline_expr};
use super::walk::{self, AstRewritePass, BlockKind};

pub(super) fn apply(module: &mut AstModule, _context: ReadabilityContext) -> bool {
    walk::rewrite_module(module, &mut CleanupPass)
}

struct CleanupPass;

impl AstRewritePass for CleanupPass {
    fn rewrite_block(&mut self, block: &mut AstBlock, kind: BlockKind) -> bool {
        cleanup_block(
            block,
            matches!(kind, BlockKind::ModuleBody | BlockKind::FunctionBody),
        )
    }
}

fn cleanup_block(block: &mut AstBlock, allow_trailing_empty_return_elision: bool) -> bool {
    let mut changed = false;

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

    let discardable_unused_locals = collect_discardable_unused_locals(block);
    let original_len = block.stmts.len();
    block.stmts.retain(|stmt| {
        !matches!(
            stmt,
            AstStmt::LocalDecl(local_decl)
                if local_decl.bindings.len() == 1
                    && local_decl.values.len() == 1
                    && discardable_unused_locals.contains(&local_decl.bindings[0].id)
        )
    });
    changed |= block.stmts.len() != original_len;

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
                uses.entry(binding.id).or_insert_with(|| {
                    let mentions = count_binding_mentions_in_block(block, binding.id);
                    if block_captures_binding(block, binding.id) {
                        mentions.max(1)
                    } else {
                        mentions
                    }
                });
            }
        }
    }
    uses
}

fn collect_discardable_unused_locals(
    block: &AstBlock,
) -> std::collections::BTreeSet<AstBindingRef> {
    let mut bindings = std::collections::BTreeSet::new();
    for stmt in &block.stmts {
        let AstStmt::LocalDecl(local_decl) = stmt else {
            continue;
        };
        let [binding] = local_decl.bindings.as_slice() else {
            continue;
        };
        let [value] = local_decl.values.as_slice() else {
            continue;
        };
        if !matches!(binding.origin, crate::ast::AstLocalOrigin::Recovered) {
            continue;
        }
        if count_binding_uses_in_stmts(&block.stmts, binding.id) != 0
            || block_captures_binding(block, binding.id)
        {
            continue;
        }
        if is_discard_safe_local_value(value) {
            bindings.insert(binding.id);
        }
    }
    bindings
}

fn is_discard_safe_local_value(value: &crate::ast::AstExpr) -> bool {
    is_context_safe_expr(value) || is_copy_like_expr(value) || is_lookup_inline_expr(value)
}

fn block_captures_binding(block: &AstBlock, binding: AstBindingRef) -> bool {
    block
        .stmts
        .iter()
        .any(|stmt| stmt_captures_binding(stmt, binding))
}

fn stmt_captures_binding(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .any(|value| expr_captures_binding(value, binding)),
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .any(|value| expr_captures_binding(value, binding)),
        AstStmt::Assign(assign) => {
            assign
                .values
                .iter()
                .any(|value| expr_captures_binding(value, binding))
                || assign
                    .targets
                    .iter()
                    .any(|target| lvalue_captures_binding(target, binding))
        }
        AstStmt::CallStmt(call_stmt) => call_captures_binding(&call_stmt.call, binding),
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .any(|value| expr_captures_binding(value, binding)),
        AstStmt::If(if_stmt) => {
            expr_captures_binding(&if_stmt.cond, binding)
                || block_captures_binding(&if_stmt.then_block, binding)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|else_block| block_captures_binding(else_block, binding))
        }
        AstStmt::While(while_stmt) => {
            expr_captures_binding(&while_stmt.cond, binding)
                || block_captures_binding(&while_stmt.body, binding)
        }
        AstStmt::Repeat(repeat_stmt) => {
            block_captures_binding(&repeat_stmt.body, binding)
                || expr_captures_binding(&repeat_stmt.cond, binding)
        }
        AstStmt::NumericFor(numeric_for) => {
            expr_captures_binding(&numeric_for.start, binding)
                || expr_captures_binding(&numeric_for.limit, binding)
                || expr_captures_binding(&numeric_for.step, binding)
                || block_captures_binding(&numeric_for.body, binding)
        }
        AstStmt::GenericFor(generic_for) => {
            generic_for
                .iterator
                .iter()
                .any(|value| expr_captures_binding(value, binding))
                || block_captures_binding(&generic_for.body, binding)
        }
        AstStmt::DoBlock(block) => block_captures_binding(block, binding),
        AstStmt::FunctionDecl(function_decl) => {
            function_expr_captures_binding(&function_decl.func, binding)
        }
        AstStmt::LocalFunctionDecl(function_decl) => {
            function_expr_captures_binding(&function_decl.func, binding)
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => false,
    }
}

fn lvalue_captures_binding(lvalue: &crate::ast::AstLValue, binding: AstBindingRef) -> bool {
    match lvalue {
        crate::ast::AstLValue::Name(_) => false,
        crate::ast::AstLValue::FieldAccess(access) => expr_captures_binding(&access.base, binding),
        crate::ast::AstLValue::IndexAccess(access) => {
            expr_captures_binding(&access.base, binding)
                || expr_captures_binding(&access.index, binding)
        }
    }
}

fn call_captures_binding(call: &crate::ast::AstCallKind, binding: AstBindingRef) -> bool {
    match call {
        crate::ast::AstCallKind::Call(call) => {
            expr_captures_binding(&call.callee, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_captures_binding(arg, binding))
        }
        crate::ast::AstCallKind::MethodCall(call) => {
            expr_captures_binding(&call.receiver, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_captures_binding(arg, binding))
        }
    }
}

fn expr_captures_binding(expr: &crate::ast::AstExpr, binding: AstBindingRef) -> bool {
    match expr {
        crate::ast::AstExpr::Unary(unary) => expr_captures_binding(&unary.expr, binding),
        crate::ast::AstExpr::Binary(binary) => {
            expr_captures_binding(&binary.lhs, binding)
                || expr_captures_binding(&binary.rhs, binding)
        }
        crate::ast::AstExpr::LogicalAnd(logical) | crate::ast::AstExpr::LogicalOr(logical) => {
            expr_captures_binding(&logical.lhs, binding)
                || expr_captures_binding(&logical.rhs, binding)
        }
        crate::ast::AstExpr::FieldAccess(access) => expr_captures_binding(&access.base, binding),
        crate::ast::AstExpr::IndexAccess(access) => {
            expr_captures_binding(&access.base, binding)
                || expr_captures_binding(&access.index, binding)
        }
        crate::ast::AstExpr::Call(call) => {
            expr_captures_binding(&call.callee, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_captures_binding(arg, binding))
        }
        crate::ast::AstExpr::MethodCall(call) => {
            expr_captures_binding(&call.receiver, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_captures_binding(arg, binding))
        }
        crate::ast::AstExpr::SingleValue(expr) => expr_captures_binding(expr, binding),
        crate::ast::AstExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                crate::ast::AstTableField::Array(value) => expr_captures_binding(value, binding),
                crate::ast::AstTableField::Record(record) => {
                    (match &record.key {
                        crate::ast::AstTableKey::Name(_) => false,
                        crate::ast::AstTableKey::Expr(key) => expr_captures_binding(key, binding),
                    }) || expr_captures_binding(&record.value, binding)
                }
            })
        }
        crate::ast::AstExpr::FunctionExpr(function) => {
            function_expr_captures_binding(function, binding)
        }
        crate::ast::AstExpr::Nil
        | crate::ast::AstExpr::Boolean(_)
        | crate::ast::AstExpr::Integer(_)
        | crate::ast::AstExpr::Number(_)
        | crate::ast::AstExpr::String(_)
        | crate::ast::AstExpr::Int64(_)
        | crate::ast::AstExpr::UInt64(_)
        | crate::ast::AstExpr::Complex { .. }
        | crate::ast::AstExpr::Var(_)
        | crate::ast::AstExpr::VarArg => false,
    }
}

fn function_expr_captures_binding(
    function: &crate::ast::AstFunctionExpr,
    binding: AstBindingRef,
) -> bool {
    function.captured_bindings.contains(&binding) || block_captures_binding(&function.body, binding)
}

#[cfg(test)]
mod tests;
