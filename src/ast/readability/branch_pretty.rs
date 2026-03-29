//! 这个文件负责把“结构等价但不好看”的条件语句收回更像源码的形状。
//!
//! 它依赖 AST build / HIR 已经保证语义正确，只在 Readability 阶段做局部可读性整理，
//! 比如 guard flatten、`not` 交换 then/else、`not a and x or y` 还原成更自然的
//! 真值条件组合。它不会越权补语义，也不会替前层兜底修错误控制流。
//!
//! 例子：
//! - `if not cond then a() else b() end` 会整理成 `if cond then b() else a() end`
//! - `if a then if b then return end end` 会折成 `if a and b then return end`
//! - `if cond then return end else tail()` 会拉平成 `if cond then return end; tail()`

use super::super::common::{
    AstBinaryExpr, AstBinaryOpKind, AstBlock, AstExpr, AstIf, AstLogicalExpr, AstModule, AstStmt,
    AstUnaryExpr, AstUnaryOpKind,
};
use super::ReadabilityContext;
use super::walk::{self, AstRewritePass, BlockKind};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let _ = context.target;
    walk::rewrite_module(module, &mut BranchPrettyPass)
}

struct BranchPrettyPass;

impl AstRewritePass for BranchPrettyPass {
    fn rewrite_block(&mut self, block: &mut AstBlock, _kind: BlockKind) -> bool {
        let old_stmts = std::mem::take(&mut block.stmts);
        let mut new_stmts = Vec::with_capacity(old_stmts.len());
        let mut changed = false;
        for stmt in old_stmts {
            match flatten_terminating_if(stmt) {
                Ok(flattened) => {
                    new_stmts.extend(flattened);
                    changed = true;
                }
                Err(stmt) => new_stmts.push(stmt),
            }
        }
        block.stmts = new_stmts;
        changed
    }

    fn rewrite_stmt(&mut self, stmt: &mut AstStmt) -> bool {
        let AstStmt::If(if_stmt) = stmt else {
            return false;
        };

        let mut changed = false;
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
        changed || collapse_nested_guard_if(if_stmt)
    }

    fn rewrite_expr(&mut self, expr: &mut AstExpr) -> bool {
        let Some(pretty) = prettify_truthy_ternary(expr) else {
            return false;
        };
        *expr = pretty;
        true
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

fn collapse_nested_guard_if(if_stmt: &mut AstIf) -> bool {
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
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
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
        | AstExpr::SingleValue(_)
        | AstExpr::VarArg => false,
    }
}

#[cfg(test)]
mod tests;
