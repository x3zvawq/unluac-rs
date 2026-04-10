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
//! - `if exit then goto L1 end; body; ::L1:: tail` 会收成 `if not exit then body end; tail`
//! - `if cond then a(); goto L1 end; b(); ::L1::` 会收成 `if cond then a() else b() end`

use super::super::common::{
    AstBinaryExpr, AstBinaryOpKind, AstBlock, AstExpr, AstFunctionExpr, AstIf, AstLabelId,
    AstLogicalExpr, AstModule, AstReturn, AstStmt, AstUnaryExpr, AstUnaryOpKind,
};
use super::ReadabilityContext;
use super::expr_analysis::is_always_truthy_expr;
use super::visit::{self, AstVisitor};
use super::walk::{self, AstRewritePass, BlockKind};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let _ = context.target;
    walk::rewrite_module(module, &mut BranchPrettyPass)
}

struct BranchPrettyPass;

impl AstRewritePass for BranchPrettyPass {
    fn rewrite_block(&mut self, block: &mut AstBlock, kind: BlockKind) -> bool {
        let old_stmts = std::mem::take(&mut block.stmts);
        let mut flattened_stmts = Vec::with_capacity(old_stmts.len());
        let mut changed = false;
        for stmt in old_stmts {
            match flatten_terminating_if(stmt) {
                Ok(flattened) => {
                    flattened_stmts.extend(flattened);
                    changed = true;
                }
                Err(stmt) => flattened_stmts.push(stmt),
            }
        }
        block.stmts = flattened_stmts;
        let folded_else = fold_terminal_goto_else(block);
        let folded_guard = fold_guard_goto_labels(block);
        let folded_terminal_guard = fold_terminal_guard_return(block, kind);
        changed || folded_else || folded_guard || folded_terminal_guard
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
    if !is_always_truthy_expr(&and_expr.rhs) || !is_always_truthy_expr(&or_expr.rhs) {
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

fn fold_terminal_goto_else(block: &mut AstBlock) -> bool {
    let mut changed = false;

    while let Some(fold) = find_terminal_goto_else_fold(block) {
        let old_stmts = std::mem::take(&mut block.stmts);
        let mut rewritten =
            Vec::with_capacity(old_stmts.len() - (fold.label_index - fold.if_index));
        let mut rewritten_if = None;
        let mut else_body = Vec::new();

        for (index, stmt) in old_stmts.into_iter().enumerate() {
            if index < fold.if_index {
                rewritten.push(stmt);
                continue;
            }
            if index == fold.if_index {
                let AstStmt::If(mut if_stmt) = stmt else {
                    unreachable!("terminal-goto else fold should only target if statements");
                };
                let popped = if_stmt.then_block.stmts.pop();
                debug_assert!(matches!(popped, Some(AstStmt::Goto(_))));
                if_stmt.else_block = Some(AstBlock { stmts: Vec::new() });
                rewritten_if = Some(if_stmt);
                continue;
            }
            if index < fold.label_index {
                else_body.push(stmt);
                continue;
            }
            if index == fold.label_index {
                continue;
            }
            rewritten.push(stmt);
        }

        let mut rewritten_if =
            rewritten_if.expect("terminal-goto else fold should capture the rewritten if");
        rewritten_if.else_block = Some(AstBlock { stmts: else_body });
        rewritten.insert(fold.if_index, AstStmt::If(rewritten_if));
        block.stmts = rewritten;
        changed = true;
    }

    changed
}

fn fold_guard_goto_labels(block: &mut AstBlock) -> bool {
    let mut changed = false;

    while let Some(fold) = find_guard_goto_label_fold(block) {
        let old_stmts = std::mem::take(&mut block.stmts);
        let mut rewritten =
            Vec::with_capacity(old_stmts.len() - (fold.label_index - fold.if_index));
        let mut guarded_if = None;
        let mut guarded_body = Vec::new();

        for (index, stmt) in old_stmts.into_iter().enumerate() {
            if index < fold.if_index {
                rewritten.push(stmt);
                continue;
            }
            if index == fold.if_index {
                let AstStmt::If(mut if_stmt) = stmt else {
                    unreachable!("guard fold should only target if statements");
                };
                if_stmt.cond = negate_guard_condition(if_stmt.cond);
                if_stmt.then_block = AstBlock { stmts: Vec::new() };
                if_stmt.else_block = None;
                guarded_if = Some(if_stmt);
                continue;
            }
            if index < fold.label_index {
                guarded_body.push(stmt);
                continue;
            }
            if index == fold.label_index {
                continue;
            }
            rewritten.push(stmt);
        }

        let mut guarded_if = guarded_if.expect("guard fold should capture the rewritten if");
        guarded_if.then_block = AstBlock {
            stmts: guarded_body,
        };
        rewritten.insert(fold.if_index, AstStmt::If(guarded_if));
        block.stmts = rewritten;
        changed = true;
    }

    changed
}

fn fold_terminal_guard_return(block: &mut AstBlock, kind: BlockKind) -> bool {
    if !matches!(kind, BlockKind::ModuleBody | BlockKind::FunctionBody) {
        return false;
    }

    let Some((if_index, remove_terminal_empty_return)) = terminal_guard_return_candidate(block)
    else {
        return false;
    };
    let removed_if = block.stmts.remove(if_index);
    let AstStmt::If(mut if_stmt) = removed_if else {
        unreachable!("checked above, terminal guard candidate must remain an if");
    };
    if remove_terminal_empty_return {
        let popped = block.stmts.pop();
        debug_assert!(matches!(popped, Some(stmt) if is_empty_return_stmt(&stmt)));
    }

    let lifted_body = std::mem::replace(
        &mut if_stmt.then_block,
        AstBlock {
            stmts: vec![AstStmt::Return(Box::new(AstReturn { values: Vec::new() }))],
        },
    );
    if_stmt.cond = negate_guard_condition(if_stmt.cond);
    if_stmt.else_block = None;

    block.stmts.push(AstStmt::If(if_stmt));
    block.stmts.extend(lifted_body.stmts);
    true
}

fn terminal_guard_return_candidate(block: &AstBlock) -> Option<(usize, bool)> {
    let if_index = match block.stmts.as_slice() {
        [.., AstStmt::If(_)] => block.stmts.len() - 1,
        [.., AstStmt::If(_), tail] if is_empty_return_stmt(tail) => block.stmts.len() - 2,
        _ => return None,
    };
    let AstStmt::If(if_stmt) = block.stmts.get(if_index)? else {
        return None;
    };
    if if_stmt.else_block.is_some()
        || !block_always_terminates(&if_stmt.then_block)
        || !matches!(if_stmt.then_block.stmts.last(), Some(AstStmt::Return(_)))
        || block_contains_label_or_goto(&if_stmt.then_block)
    {
        return None;
    }

    Some((if_index, if_index + 1 < block.stmts.len()))
}

#[derive(Clone, Copy)]
struct GuardGotoFold {
    if_index: usize,
    label_index: usize,
}

fn find_terminal_goto_else_fold(block: &AstBlock) -> Option<GuardGotoFold> {
    for if_index in 0..block.stmts.len() {
        let Some(target) = terminal_goto_else_target(&block.stmts[if_index]) else {
            continue;
        };
        if count_goto_target_in_block(block, target) != 1 {
            continue;
        }
        let Some(label_index) = block.stmts[if_index + 1..]
            .iter()
            .position(|stmt| matches!(stmt, AstStmt::Label(label) if label.id == target))
            .map(|offset| if_index + 1 + offset)
        else {
            continue;
        };

        let else_body = &block.stmts[if_index + 1..label_index];
        // 这里会把线性尾部搬进 `else` block；如果尾部自己再声明 local/label，
        // 就会引入新的词法边界变化。Readability 只在这类结构风险不存在时才收回源码 sugar。
        if !else_body.is_empty() && can_fold_guard_goto_body(else_body) {
            return Some(GuardGotoFold {
                if_index,
                label_index,
            });
        }
    }

    None
}

fn find_guard_goto_label_fold(block: &AstBlock) -> Option<GuardGotoFold> {
    for if_index in 0..block.stmts.len() {
        let Some(target) = guard_goto_target(&block.stmts[if_index]) else {
            continue;
        };
        if count_goto_target_in_block(block, target) != 1 {
            continue;
        }
        let Some(label_index) = block.stmts[if_index + 1..]
            .iter()
            .position(|stmt| matches!(stmt, AstStmt::Label(label) if label.id == target))
            .map(|offset| if_index + 1 + offset)
        else {
            continue;
        };

        let guarded_body = &block.stmts[if_index + 1..label_index];
        if !guarded_body.is_empty() && can_fold_guard_goto_body(guarded_body) {
            return Some(GuardGotoFold {
                if_index,
                label_index,
            });
        }
    }

    None
}

fn terminal_goto_else_target(stmt: &AstStmt) -> Option<AstLabelId> {
    let AstStmt::If(if_stmt) = stmt else {
        return None;
    };
    if if_stmt.else_block.is_some() {
        return None;
    }
    if if_stmt.then_block.stmts.len() < 2 {
        return None;
    }
    let AstStmt::Goto(goto_stmt) = if_stmt.then_block.stmts.last()? else {
        return None;
    };
    Some(goto_stmt.target)
}

fn guard_goto_target(stmt: &AstStmt) -> Option<AstLabelId> {
    let AstStmt::If(if_stmt) = stmt else {
        return None;
    };
    if if_stmt.else_block.is_some() {
        return None;
    }
    let [AstStmt::Goto(goto_stmt)] = if_stmt.then_block.stmts.as_slice() else {
        return None;
    };
    Some(goto_stmt.target)
}

fn can_fold_guard_goto_body(stmts: &[AstStmt]) -> bool {
    stmts.iter().all(|stmt| {
        !matches!(
            stmt,
            AstStmt::Label(_) | AstStmt::LocalDecl(_) | AstStmt::LocalFunctionDecl(_)
        )
    })
}

fn count_goto_target_in_block(block: &AstBlock, target: AstLabelId) -> usize {
    let mut collector = GotoTargetCollector { target, count: 0 };
    visit::visit_block(block, &mut collector);
    collector.count
}

struct GotoTargetCollector {
    target: AstLabelId,
    count: usize,
}

impl AstVisitor for GotoTargetCollector {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        if let AstStmt::Goto(goto_stmt) = stmt
            && goto_stmt.target == self.target
        {
            self.count += 1;
        }
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        false
    }
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
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::Error(_) => false,
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

fn block_contains_label_or_goto(block: &AstBlock) -> bool {
    block.stmts.iter().any(stmt_contains_label_or_goto)
}

fn is_empty_return_stmt(stmt: &AstStmt) -> bool {
    matches!(stmt, AstStmt::Return(ret) if ret.values.is_empty())
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

fn stmt_contains_label_or_goto(stmt: &AstStmt) -> bool {
    match stmt {
        AstStmt::If(if_stmt) => {
            block_contains_label_or_goto(&if_stmt.then_block)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(block_contains_label_or_goto)
        }
        AstStmt::While(while_stmt) => block_contains_label_or_goto(&while_stmt.body),
        AstStmt::Repeat(repeat_stmt) => block_contains_label_or_goto(&repeat_stmt.body),
        AstStmt::NumericFor(numeric_for) => block_contains_label_or_goto(&numeric_for.body),
        AstStmt::GenericFor(generic_for) => block_contains_label_or_goto(&generic_for.body),
        AstStmt::DoBlock(block) => block_contains_label_or_goto(block),
        AstStmt::Label(_) | AstStmt::Goto(_) => true,
        AstStmt::LocalDecl(_)
        | AstStmt::GlobalDecl(_)
        | AstStmt::Assign(_)
        | AstStmt::CallStmt(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::Return(_)
        | AstStmt::Error(_) => false,
    }
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

#[cfg(test)]
mod tests;
