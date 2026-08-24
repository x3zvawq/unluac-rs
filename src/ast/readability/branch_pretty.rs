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
//! - `repeat ...; if G then continue; if B then break until C` 会整理成
//!   `repeat ... until not G and B or C`

use super::super::common::{
    AstBlock, AstExpr, AstFunctionExpr, AstIf, AstLocalAttr, AstLocalOrigin, AstLogicalExpr,
    AstModule, AstRepeat, AstReturn, AstStmt, AstUnaryExpr, AstUnaryOpKind,
};
use super::ReadabilityContext;
use super::control_flow::{block_contains_label_or_goto, block_contains_loop_control};
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
            // `fold_constant_if` deliberately refuses protected arms.  Do not pass such a
            // constant if to the older terminating-if rewrite, which could otherwise consume
            // the same shell through a different path before the next fixed-point round.
            if let AstStmt::If(if_stmt) = &stmt
                && matches!(if_stmt.cond, AstExpr::Boolean(_))
                && constant_if_has_protected_nodes(if_stmt)
            {
                flattened_stmts.push(stmt);
                continue;
            }
            match fold_constant_if(stmt).or_else(flatten_terminating_if) {
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
        if let AstStmt::Repeat(repeat_stmt) = stmt
            && fold_repeat_tail_continue_break(repeat_stmt)
        {
            return true;
        }
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
                changed |= merge_exact_nested_if(if_stmt);
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

fn fold_repeat_tail_continue_break(repeat_stmt: &mut AstRepeat) -> bool {
    let len = repeat_stmt.body.stmts.len();
    if len < 2
        || repeat_stmt.body.stmts[..len - 2]
            .iter()
            .any(stmt_contains_single_pass_forbidden_nodes)
    {
        return false;
    }
    let [AstStmt::If(continue_if), AstStmt::If(break_if)] = &repeat_stmt.body.stmts[len - 2..]
    else {
        return false;
    };
    if continue_if.else_block.is_some()
        || break_if.else_block.is_some()
        || !matches!(continue_if.then_block.stmts.as_slice(), [AstStmt::Continue])
        || !matches!(break_if.then_block.stmts.as_slice(), [AstStmt::Break])
    {
        return false;
    }

    let continued = negate_guard_condition(continue_if.cond.clone());
    if continued == repeat_stmt.cond {
        return false;
    }
    let broken = break_if.cond.clone();
    let latch = std::mem::replace(&mut repeat_stmt.cond, AstExpr::Boolean(false));
    repeat_stmt.body.stmts.truncate(len - 2);
    repeat_stmt.cond = AstExpr::LogicalOr(Box::new(AstLogicalExpr {
        lhs: AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
            lhs: continued,
            rhs: broken,
        })),
        rhs: latch,
    }));
    true
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

fn merge_exact_nested_if(if_stmt: &mut AstIf) -> bool {
    let [AstStmt::If(inner)] = if_stmt.then_block.stmts.as_slice() else {
        return false;
    };
    if if_stmt.else_block.is_some()
        || inner.else_block.is_some()
        || block_contains_label_or_goto(&inner.then_block)
    {
        return false;
    }

    let Some(AstStmt::If(mut inner)) = if_stmt.then_block.stmts.pop() else {
        unreachable!("validated nested if must remain the only then statement");
    };
    let lhs = std::mem::replace(&mut if_stmt.cond, AstExpr::Boolean(false));
    inner.cond = AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
        lhs,
        rhs: inner.cond,
    }));
    *if_stmt = *inner;
    true
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

/// 收回前层已经证明为常量的 `if`，但不越过诊断、跳转或词法作用域边界。
///
/// `literal-fold` 只会把无元方法的原始字面量条件变成 `Boolean`；因此选中的 arm
/// 不再有条件求值事件，未选中的 arm 也不会执行。不过，label/goto 可能从 arm 外部
/// 直接进入一个看似不可达的 arm，break/continue 也携带 loop owner，诊断节点不能被
/// 静默丢弃；`global` 是方言级的词法声明，搬出原 arm 会改变其可见范围；debug/物理根、
/// local-function 与 capture 则携带不可消除的 binding identity。任一边界存在时，外壳
/// 继续保留。含普通 recovered local 的选中 arm 用 `do ... end` 保持原 if block 的词法
/// 边界，包括 `<close>` 的退出点和 captured local 的 root lifetime。
fn fold_constant_if(stmt: AstStmt) -> Result<Vec<AstStmt>, AstStmt> {
    let AstStmt::If(mut if_stmt) = stmt else {
        return Err(stmt);
    };
    let selected_then = match &if_stmt.cond {
        AstExpr::Boolean(value) => *value,
        _ => return Err(AstStmt::If(if_stmt)),
    };

    if constant_if_has_protected_nodes(&if_stmt) {
        return Err(AstStmt::If(if_stmt));
    }

    let selected = if selected_then {
        if_stmt.then_block
    } else {
        if_stmt.else_block.take().unwrap_or_default()
    };
    if selected.stmts.is_empty() {
        Ok(Vec::new())
    } else {
        Ok(lifted_tail_stmts(selected))
    }
}

fn constant_if_has_protected_nodes(if_stmt: &AstIf) -> bool {
    let else_block = if_stmt.else_block.as_ref();
    block_contains_label_or_goto(&if_stmt.then_block)
        || else_block.is_some_and(block_contains_label_or_goto)
        || block_contains_loop_control(&if_stmt.then_block)
        || else_block.is_some_and(block_contains_loop_control)
        || block_contains_diagnostic(&if_stmt.then_block)
        || else_block.is_some_and(block_contains_diagnostic)
        || block_contains_global_decl(&if_stmt.then_block)
        || else_block.is_some_and(block_contains_global_decl)
        || block_contains_identity_boundary(&if_stmt.then_block)
        || else_block.is_some_and(block_contains_identity_boundary)
}

struct DiagnosticVisitor(bool);

impl AstVisitor for DiagnosticVisitor {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        self.0 |= matches!(stmt, AstStmt::Error(_));
    }

    fn visit_expr(&mut self, expr: &AstExpr) {
        self.0 |= matches!(expr, AstExpr::Error(_));
    }
}

fn block_contains_diagnostic(block: &AstBlock) -> bool {
    let mut visitor = DiagnosticVisitor(false);
    visit::visit_block(block, &mut visitor);
    visitor.0
}

struct GlobalDeclVisitor(bool);

impl AstVisitor for GlobalDeclVisitor {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        self.0 |= matches!(stmt, AstStmt::GlobalDecl(_));
    }
}

fn block_contains_global_decl(block: &AstBlock) -> bool {
    let mut visitor = GlobalDeclVisitor(false);
    visit::visit_block(block, &mut visitor);
    visitor.0
}

struct IdentityBoundaryVisitor(bool);

impl AstVisitor for IdentityBoundaryVisitor {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        match stmt {
            AstStmt::LocalDecl(local_decl) => {
                self.0 |= local_decl.bindings.iter().any(|binding| {
                    binding.origin != AstLocalOrigin::Recovered
                        || !matches!(binding.attr, AstLocalAttr::None)
                });
            }
            // A local-function declaration carries a binding identity even when its body has no
            // explicit capture; dropping it from an unselected arm would erase that evidence.
            AstStmt::LocalFunctionDecl(_) => self.0 = true,
            _ => {}
        }
    }

    fn visit_function_expr(&mut self, function: &AstFunctionExpr) -> bool {
        self.0 |= !function.captured_bindings.is_empty() || !function.captured_params.is_empty();
        true
    }
}

fn block_contains_identity_boundary(block: &AstBlock) -> bool {
    let mut visitor = IdentityBoundaryVisitor(false);
    visit::visit_block(block, &mut visitor);
    visitor.0
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
    block.stmts.extend(lifted_tail_stmts(lifted_body));
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
        // The ordinary statement loop fences protected constant-if nodes.  Keep the same
        // boundary here because terminal-guard folding runs after that loop and would
        // otherwise consume the shell through a second path.
        || (matches!(if_stmt.cond, AstExpr::Boolean(_))
            && constant_if_has_protected_nodes(if_stmt))
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

fn is_empty_return_stmt(stmt: &AstStmt) -> bool {
    matches!(stmt, AstStmt::Return(ret) if ret.values.is_empty())
}

fn stmt_requires_scope_barrier(stmt: &AstStmt) -> bool {
    matches!(
        stmt,
        AstStmt::LocalDecl(_)
            | AstStmt::LocalFunctionDecl(_)
            | AstStmt::GlobalDecl(_)
            | AstStmt::Label(_)
            | AstStmt::Goto(_)
    )
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
        AstBindingRef, AstCallExpr, AstCallKind, AstCallStmt, AstGlobalAttr, AstGlobalBinding,
        AstGlobalBindingTarget, AstGlobalDecl, AstGlobalName, AstLocalAttr, AstLocalBinding,
        AstLocalDecl, AstLocalOrigin, AstRepeat, AstWhile,
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

    fn recovered_local(id: usize) -> AstStmt {
        AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![AstLocalBinding {
                id: AstBindingRef::Local(LocalId(id)),
                attr: AstLocalAttr::None,
                origin: AstLocalOrigin::Recovered,
            }],
            values: vec![AstExpr::Integer(1)],
        }))
    }

    fn global_decl_stmt(name: &str) -> AstStmt {
        AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
            bindings: vec![AstGlobalBinding {
                target: AstGlobalBindingTarget::Name(AstGlobalName {
                    text: name.to_owned(),
                }),
                attr: AstGlobalAttr::None,
            }],
            values: Vec::new(),
        }))
    }

    #[test]
    fn folds_constant_if_to_the_selected_arm() {
        let stmt = AstStmt::If(Box::new(AstIf {
            cond: AstExpr::Boolean(true),
            then_block: AstBlock {
                stmts: vec![call_stmt("selected")],
            },
            else_block: Some(AstBlock {
                stmts: vec![call_stmt("unreachable")],
            }),
        }));

        assert_eq!(fold_constant_if(stmt), Ok(vec![call_stmt("selected")]));
    }

    #[test]
    fn constant_if_keeps_selected_local_scope() {
        let stmt = AstStmt::If(Box::new(AstIf {
            cond: AstExpr::Boolean(false),
            then_block: AstBlock {
                stmts: vec![call_stmt("unreachable")],
            },
            else_block: Some(AstBlock {
                stmts: vec![recovered_local(0), call_stmt("selected")],
            }),
        }));

        let Ok(selected_stmts) = fold_constant_if(stmt) else {
            panic!("selected local block must retain a lexical scope barrier");
        };
        let [AstStmt::DoBlock(selected)] = selected_stmts.as_slice() else {
            panic!("selected local block must retain a lexical scope barrier");
        };
        assert_eq!(
            selected.stmts,
            vec![recovered_local(0), call_stmt("selected")]
        );
    }

    #[test]
    fn constant_if_does_not_drop_unreachable_diagnostic() {
        let stmt = AstStmt::If(Box::new(AstIf {
            cond: AstExpr::Boolean(true),
            then_block: AstBlock {
                stmts: vec![call_stmt("selected")],
            },
            else_block: Some(AstBlock {
                stmts: vec![AstStmt::Error("unresolved".to_owned())],
            }),
        }));

        assert!(fold_constant_if(stmt).is_err());
    }

    #[test]
    fn constant_if_keeps_global_declaration_scope() {
        let stmt = AstStmt::If(Box::new(AstIf {
            cond: AstExpr::Boolean(true),
            then_block: AstBlock {
                stmts: vec![global_decl_stmt("selected")],
            },
            else_block: None,
        }));

        assert!(fold_constant_if(stmt).is_err());
    }

    #[test]
    fn constant_if_keeps_unselected_debug_identity() {
        let mut debug_local = recovered_local(0);
        let AstStmt::LocalDecl(local_decl) = &mut debug_local else {
            unreachable!("recovered_local must produce a local declaration");
        };
        local_decl.bindings[0].origin = AstLocalOrigin::DebugHinted;
        let stmt = AstStmt::If(Box::new(AstIf {
            cond: AstExpr::Boolean(true),
            then_block: AstBlock {
                stmts: vec![call_stmt("selected")],
            },
            else_block: Some(AstBlock {
                stmts: vec![debug_local],
            }),
        }));

        assert!(fold_constant_if(stmt).is_err());
    }

    #[test]
    fn constant_if_keeps_loop_control_owner() {
        let stmt = AstStmt::If(Box::new(AstIf {
            cond: AstExpr::Boolean(false),
            then_block: AstBlock {
                stmts: vec![AstStmt::Break],
            },
            else_block: Some(AstBlock {
                stmts: vec![call_stmt("selected")],
            }),
        }));

        assert!(fold_constant_if(stmt).is_err());
    }

    #[test]
    fn protected_constant_if_does_not_reenter_terminating_flatten() {
        let mut block = AstBlock {
            stmts: vec![AstStmt::If(Box::new(AstIf {
                cond: AstExpr::Boolean(true),
                then_block: AstBlock {
                    stmts: vec![AstStmt::Break],
                },
                else_block: Some(AstBlock {
                    stmts: vec![AstStmt::Return(Box::new(AstReturn { values: vec![] }))],
                }),
            }))],
        };

        assert!(!BranchPrettyPass.rewrite_block(&mut block, BlockKind::Regular));
        assert!(matches!(block.stmts.as_slice(), [AstStmt::If(_)]));
    }

    #[test]
    fn terminal_guard_keeps_lifted_local_scope() {
        let mut block = AstBlock {
            stmts: vec![AstStmt::If(Box::new(AstIf {
                cond: global_expr("guard"),
                then_block: AstBlock {
                    stmts: vec![
                        recovered_local(0),
                        AstStmt::Return(Box::new(AstReturn { values: vec![] })),
                    ],
                },
                else_block: None,
            }))],
        };

        assert!(BranchPrettyPass.rewrite_block(&mut block, BlockKind::FunctionBody));
        let [AstStmt::If(_), AstStmt::DoBlock(body)] = block.stmts.as_slice() else {
            panic!("terminal guard must retain the lifted local scope");
        };
        assert!(matches!(
            body.stmts.as_slice(),
            [AstStmt::LocalDecl(_), AstStmt::Return(_)]
        ));
    }

    #[test]
    fn terminal_guard_does_not_reenter_protected_constant_if() {
        let mut debug_local = recovered_local(0);
        let AstStmt::LocalDecl(local_decl) = &mut debug_local else {
            unreachable!("recovered_local must produce a local declaration");
        };
        local_decl.bindings[0].origin = AstLocalOrigin::DebugHinted;
        let mut block = AstBlock {
            stmts: vec![AstStmt::If(Box::new(AstIf {
                cond: AstExpr::Boolean(true),
                then_block: AstBlock {
                    stmts: vec![
                        debug_local,
                        AstStmt::Return(Box::new(AstReturn { values: vec![] })),
                    ],
                },
                else_block: None,
            }))],
        };

        assert!(!BranchPrettyPass.rewrite_block(&mut block, BlockKind::FunctionBody));
        assert!(matches!(block.stmts.as_slice(), [AstStmt::If(_)]));
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
        let local_decl = recovered_local(0);
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
