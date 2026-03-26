//! 让结构等价的条件语句更接近源码。

use super::super::common::{
    AstBinaryExpr, AstBinaryOpKind, AstBlock, AstExpr, AstFunctionExpr, AstLValue, AstLogicalExpr,
    AstModule, AstStmt, AstUnaryExpr, AstUnaryOpKind,
};
use super::ReadabilityContext;

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let _ = context.target;
    rewrite_block(&mut module.body)
}

fn rewrite_block(block: &mut AstBlock) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    for mut stmt in old_stmts {
        changed |= rewrite_stmt(&mut stmt);
        match flatten_terminating_if(stmt) {
            Ok(flattened) => {
                new_stmts.extend(flattened);
                changed = true;
            }
            Err(stmt) => {
                new_stmts.push(stmt);
            }
        }
    }
    block.stmts = new_stmts;
    changed
}

fn rewrite_stmt(stmt: &mut AstStmt) -> bool {
    match stmt {
        AstStmt::If(if_stmt) => {
            let mut changed = rewrite_expr(&mut if_stmt.cond);
            changed |= rewrite_block(&mut if_stmt.then_block);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= rewrite_block(else_block);
            }
            if let AstExpr::Unary(unary) = &if_stmt.cond
                && unary.op == AstUnaryOpKind::Not
                && let Some(mut else_block) = if_stmt.else_block.take()
            {
                let inner = unary.expr.clone();
                std::mem::swap(&mut if_stmt.then_block, &mut else_block);
                if_stmt.else_block = Some(else_block);
                if_stmt.cond = inner;
                changed = true;
            }
            if collapse_nested_guard_if(if_stmt) {
                changed = true;
            }
            changed
        }
        AstStmt::While(while_stmt) => {
            rewrite_expr(&mut while_stmt.cond) | rewrite_block(&mut while_stmt.body)
        }
        AstStmt::Repeat(repeat_stmt) => {
            rewrite_block(&mut repeat_stmt.body) | rewrite_expr(&mut repeat_stmt.cond)
        }
        AstStmt::NumericFor(numeric_for) => {
            let mut changed = rewrite_expr(&mut numeric_for.start);
            changed |= rewrite_expr(&mut numeric_for.limit);
            changed |= rewrite_expr(&mut numeric_for.step);
            changed |= rewrite_block(&mut numeric_for.body);
            changed
        }
        AstStmt::GenericFor(generic_for) => {
            let mut changed = false;
            for expr in &mut generic_for.iterator {
                changed |= rewrite_expr(expr);
            }
            changed |= rewrite_block(&mut generic_for.body);
            changed
        }
        AstStmt::DoBlock(block) => rewrite_block(block),
        AstStmt::FunctionDecl(function_decl) => rewrite_function_expr(&mut function_decl.func),
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            rewrite_function_expr(&mut local_function_decl.func)
        }
        AstStmt::LocalDecl(local_decl) => {
            let mut changed = false;
            for value in &mut local_decl.values {
                changed |= rewrite_expr(value);
            }
            changed
        }
        AstStmt::GlobalDecl(global_decl) => {
            let mut changed = false;
            for value in &mut global_decl.values {
                changed |= rewrite_expr(value);
            }
            changed
        }
        AstStmt::Assign(assign) => {
            let mut changed = false;
            for target in &mut assign.targets {
                changed |= rewrite_lvalue(target);
            }
            for value in &mut assign.values {
                changed |= rewrite_expr(value);
            }
            changed
        }
        AstStmt::CallStmt(call_stmt) => rewrite_call(&mut call_stmt.call),
        AstStmt::Return(ret) => {
            let mut changed = false;
            for value in &mut ret.values {
                changed |= rewrite_expr(value);
            }
            changed
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => false,
    }
}

fn rewrite_function_expr(function: &mut AstFunctionExpr) -> bool {
    rewrite_block(&mut function.body)
}

fn rewrite_call(call: &mut super::super::common::AstCallKind) -> bool {
    match call {
        super::super::common::AstCallKind::Call(call) => {
            let mut changed = rewrite_expr(&mut call.callee);
            for arg in &mut call.args {
                changed |= rewrite_expr(arg);
            }
            changed
        }
        super::super::common::AstCallKind::MethodCall(call) => {
            let mut changed = rewrite_expr(&mut call.receiver);
            for arg in &mut call.args {
                changed |= rewrite_expr(arg);
            }
            changed
        }
    }
}

fn rewrite_lvalue(target: &mut AstLValue) -> bool {
    match target {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => rewrite_expr(&mut access.base),
        AstLValue::IndexAccess(access) => {
            rewrite_expr(&mut access.base) | rewrite_expr(&mut access.index)
        }
    }
}

fn rewrite_expr(expr: &mut AstExpr) -> bool {
    if let Some(pretty) = prettify_truthy_ternary(expr) {
        *expr = pretty;
        return true;
    }

    match expr {
        AstExpr::FieldAccess(access) => rewrite_expr(&mut access.base),
        AstExpr::IndexAccess(access) => {
            rewrite_expr(&mut access.base) | rewrite_expr(&mut access.index)
        }
        AstExpr::Unary(unary) => rewrite_expr(&mut unary.expr),
        AstExpr::Binary(binary) => rewrite_expr(&mut binary.lhs) | rewrite_expr(&mut binary.rhs),
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            rewrite_expr(&mut logical.lhs) | rewrite_expr(&mut logical.rhs)
        }
        AstExpr::Call(call) => {
            let mut changed = rewrite_expr(&mut call.callee);
            for arg in &mut call.args {
                changed |= rewrite_expr(arg);
            }
            changed
        }
        AstExpr::MethodCall(call) => {
            let mut changed = rewrite_expr(&mut call.receiver);
            for arg in &mut call.args {
                changed |= rewrite_expr(arg);
            }
            changed
        }
        AstExpr::TableConstructor(table) => {
            let mut changed = false;
            for field in &mut table.fields {
                match field {
                    super::super::common::AstTableField::Array(value) => {
                        changed |= rewrite_expr(value);
                    }
                    super::super::common::AstTableField::Record(record) => {
                        if let super::super::common::AstTableKey::Expr(key) = &mut record.key {
                            changed |= rewrite_expr(key);
                        }
                        changed |= rewrite_expr(&mut record.value);
                    }
                }
            }
            changed
        }
        AstExpr::FunctionExpr(function) => rewrite_function_expr(function),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => false,
    }
}

fn prettify_truthy_ternary(expr: &AstExpr) -> Option<AstExpr> {
    let AstExpr::LogicalOr(or_expr) = expr else {
        return None;
    };
    let AstExpr::LogicalAnd(and_expr) = &or_expr.lhs else {
        return None;
    };
    let AstExpr::Unary(unary) = &and_expr.lhs else {
        return None;
    };
    if unary.op != AstUnaryOpKind::Not {
        return None;
    }
    if !expr_is_always_truthy(&and_expr.rhs) || !expr_is_always_truthy(&or_expr.rhs) {
        return None;
    }

    Some(AstExpr::LogicalOr(Box::new(AstLogicalExpr {
        lhs: AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
            lhs: unary.expr.clone(),
            rhs: or_expr.rhs.clone(),
        })),
        rhs: and_expr.rhs.clone(),
    })))
}

fn collapse_nested_guard_if(if_stmt: &mut super::super::common::AstIf) -> bool {
    if if_stmt.else_block.is_some() {
        return false;
    }
    let [AstStmt::If(inner_if)] = if_stmt.then_block.stmts.as_slice() else {
        return false;
    };
    if inner_if.else_block.is_some() {
        return false;
    }

    if_stmt.cond = AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
        lhs: if_stmt.cond.clone(),
        rhs: inner_if.cond.clone(),
    }));
    if_stmt.then_block = inner_if.then_block.clone();
    true
}

fn flatten_terminating_if(stmt: AstStmt) -> Result<Vec<AstStmt>, AstStmt> {
    let AstStmt::If(mut if_stmt) = stmt else {
        return Err(stmt);
    };
    let Some(else_block) = if_stmt.else_block.take() else {
        return Err(AstStmt::If(if_stmt));
    };
    let then_terminates = block_always_terminates(&if_stmt.then_block);
    let else_terminates = block_always_terminates(&else_block);

    if then_terminates {
        let mut stmts = vec![AstStmt::If(if_stmt)];
        stmts.extend(lifted_tail_stmts(else_block));
        return Ok(stmts);
    }

    if else_terminates {
        if_stmt.cond = negate_guard_condition(if_stmt.cond);
        let then_block = std::mem::replace(&mut if_stmt.then_block, else_block);
        if_stmt.else_block = None;

        let mut stmts = vec![AstStmt::If(if_stmt)];
        stmts.extend(lifted_tail_stmts(then_block));
        return Ok(stmts);
    }

    if_stmt.else_block = Some(else_block);
    Err(AstStmt::If(if_stmt))
}

fn block_always_terminates(block: &AstBlock) -> bool {
    let Some(last_stmt) = block.stmts.last() else {
        return false;
    };
    stmt_always_terminates(last_stmt)
}

fn stmt_always_terminates(stmt: &AstStmt) -> bool {
    match stmt {
        AstStmt::Return(_) | AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) => true,
        AstStmt::If(if_stmt) => if_stmt.else_block.as_ref().is_some_and(|else_block| {
            block_always_terminates(&if_stmt.then_block) && block_always_terminates(else_block)
        }),
        AstStmt::DoBlock(block) => block_always_terminates(block),
        AstStmt::LocalDecl(_)
        | AstStmt::GlobalDecl(_)
        | AstStmt::Assign(_)
        | AstStmt::CallStmt(_)
        | AstStmt::While(_)
        | AstStmt::Repeat(_)
        | AstStmt::NumericFor(_)
        | AstStmt::GenericFor(_)
        | AstStmt::Label(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_) => false,
    }
}

fn lifted_tail_stmts(block: AstBlock) -> Vec<AstStmt> {
    if block_requires_scope_barrier(&block) {
        vec![AstStmt::DoBlock(Box::new(block))]
    } else {
        block.stmts
    }
}

fn block_requires_scope_barrier(block: &AstBlock) -> bool {
    block.stmts.iter().any(stmt_requires_scope_barrier)
}

fn stmt_requires_scope_barrier(stmt: &AstStmt) -> bool {
    matches!(
        stmt,
        AstStmt::LocalDecl(_)
            | AstStmt::LocalFunctionDecl(_)
            | AstStmt::Label(_)
            | AstStmt::Goto(_)
    )
}

fn negate_guard_condition(expr: AstExpr) -> AstExpr {
    match expr {
        AstExpr::Unary(unary) if unary.op == AstUnaryOpKind::Not => unary.expr,
        AstExpr::Binary(binary) => negate_relational_expr(*binary),
        other => AstExpr::Unary(Box::new(AstUnaryExpr {
            op: AstUnaryOpKind::Not,
            expr: other,
        })),
    }
}

fn negate_relational_expr(binary: AstBinaryExpr) -> AstExpr {
    match binary.op {
        // Lua AST 目前没有 `>` / `>=` / `~=` 节点，所以这里通过交换 operands
        // 只消掉那些可以无损改写成现有关系运算的情况；剩下的再回退成 `not (...)`。
        AstBinaryOpKind::Lt => AstExpr::Binary(Box::new(AstBinaryExpr {
            op: AstBinaryOpKind::Le,
            lhs: binary.rhs,
            rhs: binary.lhs,
        })),
        AstBinaryOpKind::Le => AstExpr::Binary(Box::new(AstBinaryExpr {
            op: AstBinaryOpKind::Lt,
            lhs: binary.rhs,
            rhs: binary.lhs,
        })),
        _ => AstExpr::Unary(Box::new(AstUnaryExpr {
            op: AstUnaryOpKind::Not,
            expr: AstExpr::Binary(Box::new(binary)),
        })),
    }
}

fn expr_is_always_truthy(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Boolean(true)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_) => true,
        AstExpr::Nil
        | AstExpr::Boolean(false)
        | AstExpr::Var(_)
        | AstExpr::FieldAccess(_)
        | AstExpr::IndexAccess(_)
        | AstExpr::Unary(_)
        | AstExpr::Binary(_)
        | AstExpr::LogicalAnd(_)
        | AstExpr::LogicalOr(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::VarArg => false,
    }
}

#[cfg(test)]
mod tests;
