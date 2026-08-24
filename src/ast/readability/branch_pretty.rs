//! 这个文件负责把“结构等价但不好看”的条件语句收回更像源码的形状。
//!
//! 它依赖 AST build / HIR 已经保证语义正确，只在 Readability 阶段做局部可读性整理，
//! 比如 guard flatten、`not` 交换 then/else。它不会越权补语义，也不会替前层兜底
//! 修错误控制流。
//!
//! 例子：
//! - `if not cond then a() else b() end` 会整理成 `if cond then b() else a() end`
//! - `if cond then body else end` 会整理成 `if cond then body end`
//! - `if cond then return end else tail()` 会拉平成 `if cond then return end; tail()`
//! - `repeat if cond then break end; tail() until true` 会整理成 `if not cond then tail() end`

use super::super::common::{
    AstBlock, AstExpr, AstIf, AstModule, AstReturn, AstStmt, AstUnaryExpr, AstUnaryOpKind,
};
use super::ReadabilityContext;
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
        let folded_terminal_guard = fold_terminal_guard_return(block, kind);
        changed || folded_terminal_guard
    }

    fn rewrite_stmt(&mut self, stmt: &mut AstStmt) -> bool {
        match stmt {
            AstStmt::If(if_stmt) => {
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
                changed |= normalize_empty_if_arms(if_stmt);
                changed
            }
            AstStmt::Repeat(repeat_stmt)
                if matches!(repeat_stmt.cond, AstExpr::Boolean(true))
                    && !block_contains_single_pass_forbidden_nodes(&repeat_stmt.body)
                    && single_pass_block_flow(&repeat_stmt.body)
                        .is_some_and(|flow| flow.contains_break)
                    && single_pass_block_is_foldable(&repeat_stmt.body, false) =>
            {
                let body = fold_single_pass_block(std::mem::take(&mut repeat_stmt.body), None);
                *stmt = AstStmt::DoBlock(Box::new(body));
                true
            }
            _ => false,
        }
    }
}

#[derive(Clone, Copy)]
struct SinglePassFlow {
    falls_through: bool,
    contains_break: bool,
}

const FALLTHROUGH_FLOW: SinglePassFlow = SinglePassFlow {
    falls_through: true,
    contains_break: false,
};

fn single_pass_block_flow(block: &AstBlock) -> Option<SinglePassFlow> {
    let mut flow = FALLTHROUGH_FLOW;
    for stmt in &block.stmts {
        let stmt_flow = single_pass_stmt_flow(stmt)?;
        flow.contains_break |= stmt_flow.contains_break;
        flow.falls_through &= stmt_flow.falls_through;
    }
    Some(flow)
}

fn single_pass_stmt_flow(stmt: &AstStmt) -> Option<SinglePassFlow> {
    match stmt {
        AstStmt::Break => Some(SinglePassFlow {
            falls_through: false,
            contains_break: true,
        }),
        AstStmt::Return(_) => Some(SinglePassFlow {
            falls_through: false,
            contains_break: false,
        }),
        AstStmt::If(if_stmt) => {
            let then_flow = single_pass_block_flow(&if_stmt.then_block)?;
            let else_flow = match &if_stmt.else_block {
                Some(else_block) => single_pass_block_flow(else_block)?,
                None => FALLTHROUGH_FLOW,
            };
            Some(SinglePassFlow {
                falls_through: then_flow.falls_through || else_flow.falls_through,
                contains_break: then_flow.contains_break || else_flow.contains_break,
            })
        }
        AstStmt::DoBlock(block) => {
            let flow = single_pass_block_flow(block)?;
            (!flow.contains_break).then_some(flow)
        }
        AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) | AstStmt::Error(_) => None,
        AstStmt::LocalDecl(_)
        | AstStmt::GlobalDecl(_)
        | AstStmt::Assign(_)
        | AstStmt::CallStmt(_)
        | AstStmt::While(_)
        | AstStmt::Repeat(_)
        | AstStmt::NumericFor(_)
        | AstStmt::GenericFor(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_) => Some(FALLTHROUGH_FLOW),
    }
}

fn single_pass_block_is_foldable(block: &AstBlock, mut tail_is_nonempty: bool) -> bool {
    for stmt in block.stmts.iter().rev() {
        if matches!(stmt, AstStmt::Break) {
            tail_is_nonempty = false;
            continue;
        }

        let Some(stmt_flow) = single_pass_stmt_flow(stmt) else {
            return false;
        };
        if !stmt_flow.contains_break {
            tail_is_nonempty = true;
            continue;
        }

        let AstStmt::If(if_stmt) = stmt else {
            return false;
        };
        let Some(then_flow) = single_pass_block_flow(&if_stmt.then_block) else {
            return false;
        };
        let else_flow = match &if_stmt.else_block {
            Some(else_block) => {
                let Some(flow) = single_pass_block_flow(else_block) else {
                    return false;
                };
                flow
            }
            None => FALLTHROUGH_FLOW,
        };
        if then_flow.falls_through && else_flow.falls_through {
            return false;
        }

        if then_flow.falls_through {
            if tail_is_nonempty && block_requires_scope_barrier(&if_stmt.then_block) {
                return false;
            }
            if !single_pass_block_is_foldable(&if_stmt.then_block, tail_is_nonempty) {
                return false;
            }
        } else if !single_pass_block_is_foldable(&if_stmt.then_block, false) {
            return false;
        }

        if let Some(else_block) = &if_stmt.else_block {
            let else_tail_is_nonempty = else_flow.falls_through && tail_is_nonempty;
            if else_tail_is_nonempty && block_requires_scope_barrier(else_block) {
                return false;
            }
            if !single_pass_block_is_foldable(else_block, else_tail_is_nonempty) {
                return false;
            }
        }

        tail_is_nonempty = true;
    }
    true
}

fn fold_single_pass_block(block: AstBlock, tail: Option<AstBlock>) -> AstBlock {
    let mut reverse_tail: Vec<_> = tail
        .map(|tail| tail.stmts.into_iter().rev().collect())
        .unwrap_or_default();

    for stmt in block.stmts.into_iter().rev() {
        if matches!(stmt, AstStmt::Break) {
            reverse_tail.clear();
            continue;
        }

        let flow = single_pass_stmt_flow(&stmt)
            .expect("single-pass block is validated before it is rewritten");
        if !flow.contains_break {
            reverse_tail.push(stmt);
            continue;
        }

        let AstStmt::If(mut if_stmt) = stmt else {
            unreachable!("validated direct breaks can only remain under an if");
        };
        let then_flow = single_pass_block_flow(&if_stmt.then_block)
            .expect("validated then block must retain its flow");
        let else_flow = match &if_stmt.else_block {
            Some(else_block) => single_pass_block_flow(else_block)
                .expect("validated else block must retain its flow"),
            None => FALLTHROUGH_FLOW,
        };
        debug_assert!(!(then_flow.falls_through && else_flow.falls_through));

        let continuation = AstBlock {
            stmts: reverse_tail.into_iter().rev().collect(),
        };
        let (then_tail, else_tail) = if then_flow.falls_through {
            (Some(continuation), None)
        } else if else_flow.falls_through {
            (None, Some(continuation))
        } else {
            (None, None)
        };

        if_stmt.then_block = fold_single_pass_block(if_stmt.then_block, then_tail);
        if_stmt.else_block = match if_stmt.else_block.take() {
            Some(else_block) => Some(fold_single_pass_block(else_block, else_tail)),
            None => else_tail,
        };
        reverse_tail = vec![AstStmt::If(if_stmt)];
    }

    reverse_tail.reverse();
    AstBlock {
        stmts: reverse_tail,
    }
}

fn block_contains_single_pass_forbidden_nodes(block: &AstBlock) -> bool {
    block
        .stmts
        .iter()
        .any(stmt_contains_single_pass_forbidden_nodes)
}

fn stmt_contains_single_pass_forbidden_nodes(stmt: &AstStmt) -> bool {
    match stmt {
        AstStmt::If(if_stmt) => {
            block_contains_single_pass_forbidden_nodes(&if_stmt.then_block)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(block_contains_single_pass_forbidden_nodes)
        }
        AstStmt::While(while_stmt) => block_contains_single_pass_forbidden_nodes(&while_stmt.body),
        AstStmt::Repeat(repeat_stmt) => {
            block_contains_single_pass_forbidden_nodes(&repeat_stmt.body)
        }
        AstStmt::NumericFor(numeric_for) => {
            block_contains_single_pass_forbidden_nodes(&numeric_for.body)
        }
        AstStmt::GenericFor(generic_for) => {
            block_contains_single_pass_forbidden_nodes(&generic_for.body)
        }
        AstStmt::DoBlock(block) => block_contains_single_pass_forbidden_nodes(block),
        AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) | AstStmt::Error(_) => true,
        AstStmt::LocalDecl(_)
        | AstStmt::GlobalDecl(_)
        | AstStmt::Assign(_)
        | AstStmt::CallStmt(_)
        | AstStmt::Return(_)
        | AstStmt::Break
        | AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_) => false,
    }
}

fn normalize_empty_if_arms(if_stmt: &mut AstIf) -> bool {
    if if_stmt
        .else_block
        .as_ref()
        .is_some_and(|else_block| else_block.stmts.is_empty())
    {
        if_stmt.else_block = None;
        return true;
    }

    let Some(else_block) = if_stmt.else_block.take() else {
        return false;
    };
    if !if_stmt.then_block.stmts.is_empty() {
        if_stmt.else_block = Some(else_block);
        return false;
    }

    let old_cond = std::mem::replace(&mut if_stmt.cond, AstExpr::Boolean(false));
    if_stmt.cond = negate_guard_condition(old_cond);
    if_stmt.then_block = else_block;
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
        // 单独的空 return 没有可提升主体；取反只会与 cleanup 的尾 return 省略来回振荡。
        || matches!(if_stmt.then_block.stmts.as_slice(), [stmt] if is_empty_return_stmt(stmt))
        || block_contains_label_or_goto(&if_stmt.then_block)
    {
        return None;
    }

    Some((if_index, if_index + 1 < block.stmts.len()))
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
        // Lua 的 `<`/`<=` 可能走元方法，number 还可能遇到 NaN；`not (a < b)`
        // 不能安全改写成 `b <= a`，所以这里只消除显式双重否定。
        other => AstExpr::Unary(Box::new(AstUnaryExpr {
            op: AstUnaryOpKind::Not,
            expr: other,
        })),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::common::{
        AstBindingRef, AstCallExpr, AstCallKind, AstCallStmt, AstGlobalName, AstLocalAttr,
        AstLocalBinding, AstLocalDecl, AstLocalOrigin, AstRepeat, AstWhile,
    };
    use crate::hir::LocalId;

    fn global_expr(name: &str) -> AstExpr {
        AstExpr::Var(crate::ast::common::AstNameRef::Global(AstGlobalName {
            text: name.to_owned(),
        }))
    }

    fn call_stmt(name: &str) -> AstStmt {
        AstStmt::CallStmt(Box::new(AstCallStmt {
            call: AstCallKind::Call(Box::new(AstCallExpr {
                callee: global_expr(name),
                args: Vec::new(),
            })),
        }))
    }

    fn break_guard(name: &str) -> AstStmt {
        AstStmt::If(Box::new(AstIf {
            cond: global_expr(name),
            then_block: AstBlock {
                stmts: vec![AstStmt::Break],
            },
            else_block: None,
        }))
    }

    #[test]
    fn folds_single_pass_break_guard_without_duplicating_tail() {
        let mut stmt = AstStmt::Repeat(Box::new(AstRepeat {
            body: AstBlock {
                stmts: vec![break_guard("skip"), call_stmt("tail")],
            },
            cond: AstExpr::Boolean(true),
        }));

        assert!(BranchPrettyPass.rewrite_stmt(&mut stmt));

        let AstStmt::DoBlock(body) = stmt else {
            panic!("constant-true repeat should become a scoped block");
        };
        let [AstStmt::If(if_stmt)] = body.stmts.as_slice() else {
            panic!("break guard should own the linear tail");
        };
        assert!(if_stmt.then_block.stmts.is_empty());
        assert!(matches!(
            if_stmt
                .else_block
                .as_ref()
                .map(|block| block.stmts.as_slice()),
            Some([AstStmt::CallStmt(_)])
        ));
    }

    #[test]
    fn keeps_single_pass_fence_when_both_arms_can_fall_through() {
        let mut stmt = AstStmt::Repeat(Box::new(AstRepeat {
            body: AstBlock {
                stmts: vec![
                    AstStmt::If(Box::new(AstIf {
                        cond: global_expr("outer"),
                        then_block: AstBlock {
                            stmts: vec![break_guard("left")],
                        },
                        else_block: Some(AstBlock {
                            stmts: vec![break_guard("right")],
                        }),
                    })),
                    call_stmt("tail"),
                ],
            },
            cond: AstExpr::Boolean(true),
        }));

        assert!(!BranchPrettyPass.rewrite_stmt(&mut stmt));
        assert!(matches!(stmt, AstStmt::Repeat(_)));
    }

    #[test]
    fn keeps_single_pass_fence_when_tail_would_extend_local_scope() {
        let local_decl = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![AstLocalBinding {
                id: AstBindingRef::Local(LocalId(0)),
                attr: AstLocalAttr::None,
                origin: AstLocalOrigin::Recovered,
            }],
            values: vec![AstExpr::Integer(1)],
        }));
        let mut stmt = AstStmt::Repeat(Box::new(AstRepeat {
            body: AstBlock {
                stmts: vec![
                    AstStmt::If(Box::new(AstIf {
                        cond: global_expr("skip"),
                        then_block: AstBlock {
                            stmts: vec![AstStmt::Break],
                        },
                        else_block: Some(AstBlock {
                            stmts: vec![local_decl],
                        }),
                    })),
                    call_stmt("tail"),
                ],
            },
            cond: AstExpr::Boolean(true),
        }));

        assert!(!BranchPrettyPass.rewrite_stmt(&mut stmt));
        assert!(matches!(stmt, AstStmt::Repeat(_)));
    }

    #[test]
    fn nested_loop_break_does_not_identify_a_single_pass_fence() {
        let mut stmt = AstStmt::Repeat(Box::new(AstRepeat {
            body: AstBlock {
                stmts: vec![AstStmt::While(Box::new(AstWhile {
                    cond: AstExpr::Boolean(true),
                    body: AstBlock {
                        stmts: vec![AstStmt::Break],
                    },
                }))],
            },
            cond: AstExpr::Boolean(true),
        }));

        assert!(!BranchPrettyPass.rewrite_stmt(&mut stmt));
        assert!(matches!(stmt, AstStmt::Repeat(_)));
    }
}
