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
//! - 嵌套循环自己的 `continue` 保留原 owner，不会阻止外层 `repeat` 的尾部整理

use super::super::common::{
    AstBlock, AstExpr, AstFunctionExpr, AstIf, AstLocalAttr, AstLocalOrigin, AstLogicalExpr,
    AstModule, AstRepeat, AstReturn, AstStmt, AstUnaryExpr, AstUnaryOpKind,
};
use super::ReadabilityContext;
use super::control_flow::block_contains_label_or_goto;
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
            // 候选拒绝[ConvergenceGuard/LayerBoundary]：`fold_constant_if` deliberately refuses
            // protected arms；不要把该 constant-if 交给旧 terminating-if rewrite，否则同一
            // shell 可能沿另一条 owner 路径被消费，直到下一轮 fixed-point 才暴露归属漂移。
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
    if len < 2 {
        return false;
    }
    if repeat_stmt.body.stmts[..len - 2]
        .iter()
        .any(|stmt| stmt_contains_single_pass_forbidden_nodes(stmt, 0))
    {
        // 候选拒绝[SemanticBarrier:ControlFlow]：prefix 中较早的 `continue` 原本直接进入旧 latch；折叠后会额外求值尾部 G/B（regress_294）。
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
        // 候选拒绝[PolicyBoundary]：折叠会生成与原 latch 重复的条件，只增加源码复杂度而无可读性收益。
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
        AstStmt::DoBlock(block) => single_pass_block_flow(block),
        // 候选拒绝[SemanticBarrier:ControlFlow]：continue/goto/label 有独立 owner/入口，
        // 不能按当前 repeat 的单次 break fence 重写。
        AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => None,
        // 候选拒绝[LayerBoundary]：Error 是必须保留的前层诊断。
        AstStmt::Error(_) => None,
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
            // 候选拒绝[SemanticBarrier:ControlFlow]：当前子树含 goto/continue/label 时不能用线性后缀传播模型重写；候选拒绝[LayerBoundary]：前层诊断必须原位保留。
            return false;
        };
        if !stmt_flow.contains_break {
            tail_is_nonempty = true;
            continue;
        }

        if let AstStmt::DoBlock(do_block) = stmt {
            let do_tail_is_nonempty = stmt_flow.falls_through && tail_is_nonempty;
            if do_tail_is_nonempty && block_requires_scope_barrier(do_block) {
                // 候选拒绝[SemanticBarrier:Scope/Lifetime]：把后缀移入可继续执行的
                // do 会推迟 local、`<close>` 或 closure root 离开该显式作用域。
                return false;
            }
            if !single_pass_block_is_foldable(do_block, do_tail_is_nonempty) {
                return false;
            }
            tail_is_nonempty = true;
            continue;
        }

        let AstStmt::If(if_stmt) = stmt else {
            // 候选拒绝[ProofIncomplete]：当前证明只会把 break 所在的 if 分配给唯一后缀；缺少其它复合语句的精确路径 owner 分析。
            return false;
        };
        let Some(then_flow) = single_pass_block_flow(&if_stmt.then_block) else {
            // 候选拒绝[SemanticBarrier:ControlFlow]：then 内含未归属到本 repeat 的
            // continue/goto/label；候选拒绝[LayerBoundary]：Error 诊断不得被重建吞掉。
            return false;
        };
        let else_flow = match &if_stmt.else_block {
            Some(else_block) => {
                let Some(flow) = single_pass_block_flow(else_block) else {
                    // 候选拒绝[SemanticBarrier:ControlFlow]：else 内未归属的非局部控制不能
                    // 进入线性 fence；候选拒绝[LayerBoundary]：Error 必须原位保留。
                    return false;
                };
                flow
            }
            None => FALLTHROUGH_FLOW,
        };
        if then_flow.falls_through && else_flow.falls_through && tail_is_nonempty {
            // 候选拒绝[ProofIncomplete]：两臂互斥但共享 continuation 非空；当前 AST 没有共享表示，复制 tail 还缺少作用域与代码膨胀成本模型（regress_242）。
            return false;
        }

        if then_flow.falls_through {
            if tail_is_nonempty && block_requires_scope_barrier(&if_stmt.then_block) {
                // 候选拒绝[SemanticBarrier:Scope/Lifetime]：把后缀塞进含 local/global 的 arm 会延长声明、`<close>` 或 closure root 生命周期。
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
                // 候选拒绝[SemanticBarrier:Scope/Lifetime]：把后缀塞进 else 的 local/global 作用域会扩大声明可见性并推迟资源退出。
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

        if let AstStmt::DoBlock(do_block) = stmt {
            let continuation = AstBlock {
                stmts: reverse_tail.into_iter().rev().collect(),
            };
            let do_tail = flow.falls_through.then_some(continuation);
            let do_block = fold_single_pass_block(*do_block, do_tail);
            reverse_tail = vec![AstStmt::DoBlock(Box::new(do_block))];
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
        debug_assert!(
            !(then_flow.falls_through && else_flow.falls_through) || reverse_tail.is_empty(),
            "both fallthrough arms require an empty continuation"
        );

        let continuation = AstBlock {
            stmts: reverse_tail.into_iter().rev().collect(),
        };
        let (then_tail, else_tail) = if then_flow.falls_through && else_flow.falls_through {
            (None, None)
        } else if then_flow.falls_through {
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
    block_contains_single_pass_forbidden_nodes_at_loop_depth(block, 0)
}

fn block_contains_single_pass_forbidden_nodes_at_loop_depth(
    block: &AstBlock,
    loop_depth: usize,
) -> bool {
    block
        .stmts
        .iter()
        .any(|stmt| stmt_contains_single_pass_forbidden_nodes(stmt, loop_depth))
}

fn stmt_contains_single_pass_forbidden_nodes(stmt: &AstStmt, loop_depth: usize) -> bool {
    match stmt {
        AstStmt::If(if_stmt) => {
            block_contains_single_pass_forbidden_nodes_at_loop_depth(
                &if_stmt.then_block,
                loop_depth,
            ) || if_stmt.else_block.as_ref().is_some_and(|else_block| {
                block_contains_single_pass_forbidden_nodes_at_loop_depth(else_block, loop_depth)
            })
        }
        AstStmt::While(while_stmt) => block_contains_single_pass_forbidden_nodes_at_loop_depth(
            &while_stmt.body,
            loop_depth + 1,
        ),
        AstStmt::Repeat(repeat_stmt) => block_contains_single_pass_forbidden_nodes_at_loop_depth(
            &repeat_stmt.body,
            loop_depth + 1,
        ),
        AstStmt::NumericFor(numeric_for) => {
            block_contains_single_pass_forbidden_nodes_at_loop_depth(
                &numeric_for.body,
                loop_depth + 1,
            )
        }
        AstStmt::GenericFor(generic_for) => {
            block_contains_single_pass_forbidden_nodes_at_loop_depth(
                &generic_for.body,
                loop_depth + 1,
            )
        }
        AstStmt::DoBlock(block) => {
            block_contains_single_pass_forbidden_nodes_at_loop_depth(block, loop_depth)
        }
        // 候选拒绝[SemanticBarrier:ControlFlow]：当前 loop owner 的 continue 会绕过外层 latch/fence 尾部求值（regress_294）；嵌套 owner 则原位保留。
        AstStmt::Continue => loop_depth == 0,
        // 候选拒绝[ProofIncomplete]：goto/label 仍缺少相对当前 repeat 的精确入口与目标 owner，不能重建 single-pass fence。
        AstStmt::Goto(_) | AstStmt::Label(_) => true,
        // 候选拒绝[LayerBoundary]：Error 是前层诊断，不参与展示层控制重建。
        AstStmt::Error(_) => true,
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
        // 候选拒绝[SemanticBarrier:ControlFlow]：存在 else 时 `A and B` 不能表达两层独立分支；label/goto 还可从外部进入被删除的内层 block。
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
/// 直接进入一个看似不可达的 arm，诊断节点也不能被静默丢弃；`global` 是方言级
/// 的词法声明，搬出原 arm 会改变其可见范围；debug/物理根、
/// local-function 与 capture 则携带不可消除的 binding identity。任一边界存在时，外壳
/// 继续保留。含普通 recovered local 的选中 arm 用 `do ... end` 保持原 if block 的词法
/// 边界，包括 `<close>` 的退出点和 captured local 的 root lifetime。`break`/`continue`
/// 只跨过非循环的 `if` 外壳，最近 loop owner 不变。
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
    // 候选拒绝[SemanticBarrier:ControlFlow]：label/goto 可从条件壳外进入 arm，删除 Boolean if 会删除合法入口或改变目标。
    block_contains_label_or_goto(&if_stmt.then_block)
        || else_block.is_some_and(block_contains_label_or_goto)
        // 候选拒绝[LayerBoundary]：Error 节点是前层失败诊断，readability 不删除其承载外壳。
        || block_contains_diagnostic(&if_stmt.then_block)
        || else_block.is_some_and(block_contains_diagnostic)
        // 候选拒绝[PolicyBoundary]：方言 global 声明作为源码级编译期证据保留；选中 arm
        // 可用 do 保持范围、未选 arm 也可删除，因此这不是运行语义不等价证明。
        || block_contains_global_decl(&if_stmt.then_block)
        || else_block.is_some_and(block_contains_global_decl)
        // 候选拒绝[PolicyBoundary]：debug/physical/local-function/capture 身份即使位于未选 arm 也按项目的源码证据保留策略记账。
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
    let Some((if_index, remove_terminal_empty_return)) = terminal_guard_return_candidate(block)
    else {
        return false;
    };
    if matches!(kind, BlockKind::Regular) && !remove_terminal_empty_return {
        // 候选拒绝[SemanticBarrier:ControlFlow]：nested block 没有显式 fallback return 时，
        // condition=false 原本会继续父级后缀；插入 guard return 会提前结束函数。
        return false;
    }
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
    // 候选拒绝[LayerBoundary]：带 else 的终止分支由同 pass 的 flatten_terminating_if owner
    // 消费，terminal-guard 只处理单臂函数尾。
    if if_stmt.else_block.is_some() {
        return None;
    }
    if !block_always_terminates(&if_stmt.then_block)
        || !matches!(if_stmt.then_block.stmts.last(), Some(AstStmt::Return(_)))
    {
        return None;
    }
    // 候选拒绝[ConvergenceGuard]：单独空 return 没有可提升主体，取反后会与 cleanup 的
    // 尾 return 省略来回振荡。
    if matches!(if_stmt.then_block.stmts.as_slice(), [stmt] if is_empty_return_stmt(stmt)) {
        return None;
    }
    // 候选拒绝[SemanticBarrier:ControlFlow]：label/goto 可从外部进入将被提升的 arm，
    // 删除 if block 会改变入口与目标词法范围。
    if block_contains_label_or_goto(&if_stmt.then_block) {
        return None;
    }
    // The ordinary statement loop fences protected constant-if nodes. Keep the same boundary
    // here because terminal-guard folding runs after that loop and could consume a second path.
    if matches!(if_stmt.cond, AstExpr::Boolean(_)) && constant_if_has_protected_nodes(if_stmt) {
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
                method_name: None,
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
    fn constant_if_preserves_selected_loop_control_owner() {
        let stmt = AstStmt::If(Box::new(AstIf {
            cond: AstExpr::Boolean(true),
            then_block: AstBlock {
                stmts: vec![AstStmt::Break],
            },
            else_block: Some(AstBlock {
                stmts: vec![call_stmt("selected")],
            }),
        }));

        assert_eq!(fold_constant_if(stmt), Ok(vec![AstStmt::Break]));
    }

    #[test]
    fn protected_constant_if_does_not_reenter_terminating_flatten() {
        let mut block = AstBlock {
            stmts: vec![AstStmt::If(Box::new(AstIf {
                cond: AstExpr::Boolean(true),
                then_block: AstBlock {
                    stmts: vec![AstStmt::Error("protected".to_owned())],
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
    fn terminal_guard_uses_explicit_nested_fallback_return() {
        let mut block = AstBlock {
            stmts: vec![
                AstStmt::If(Box::new(AstIf {
                    cond: global_expr("guard"),
                    then_block: AstBlock {
                        stmts: vec![
                            call_stmt("selected"),
                            AstStmt::Return(Box::new(AstReturn {
                                values: vec![AstExpr::Integer(7)],
                            })),
                        ],
                    },
                    else_block: None,
                })),
                AstStmt::Return(Box::new(AstReturn { values: vec![] })),
            ],
        };

        assert!(BranchPrettyPass.rewrite_block(&mut block, BlockKind::Regular));
        let [AstStmt::If(guard), selected, AstStmt::Return(ret)] = block.stmts.as_slice() else {
            panic!("nested terminal guard must lift the selected body");
        };
        assert!(matches!(guard.cond, AstExpr::Unary(_)));
        assert!(matches!(selected, AstStmt::CallStmt(_)));
        assert_eq!(ret.values, vec![AstExpr::Integer(7)]);
    }

    #[test]
    fn terminal_guard_keeps_nested_parent_fallthrough() {
        let mut block = AstBlock {
            stmts: vec![
                call_stmt("prepare"),
                AstStmt::If(Box::new(AstIf {
                    cond: global_expr("guard"),
                    then_block: AstBlock {
                        stmts: vec![
                            call_stmt("selected"),
                            AstStmt::Return(Box::new(AstReturn {
                                values: vec![AstExpr::Integer(7)],
                            })),
                        ],
                    },
                    else_block: None,
                })),
            ],
        };
        let original = block.clone();

        assert!(!BranchPrettyPass.rewrite_block(&mut block, BlockKind::Regular));
        assert_eq!(block, original);
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
    fn folds_nonfallthrough_do_break_without_extending_local_scope() {
        let mut stmt = AstStmt::Repeat(Box::new(AstRepeat {
            body: AstBlock {
                stmts: vec![
                    AstStmt::If(Box::new(AstIf {
                        cond: global_expr("gate"),
                        then_block: AstBlock {
                            stmts: vec![AstStmt::DoBlock(Box::new(AstBlock {
                                stmts: vec![recovered_local(0), AstStmt::Break],
                            }))],
                        },
                        else_block: None,
                    })),
                    call_stmt("tail"),
                ],
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
        let [AstStmt::DoBlock(do_block)] = if_stmt.then_block.stmts.as_slice() else {
            panic!("the explicit do scope must remain around its local");
        };
        assert!(matches!(do_block.stmts.as_slice(), [AstStmt::LocalDecl(_)]));
        assert!(matches!(
            if_stmt
                .else_block
                .as_ref()
                .map(|block| block.stmts.as_slice()),
            Some([AstStmt::CallStmt(_)])
        ));
    }

    #[test]
    fn folds_fallthrough_do_break_when_tail_stays_scope_neutral() {
        let mut stmt = AstStmt::Repeat(Box::new(AstRepeat {
            body: AstBlock {
                stmts: vec![
                    AstStmt::DoBlock(Box::new(AstBlock {
                        stmts: vec![break_guard("skip")],
                    })),
                    call_stmt("tail"),
                ],
            },
            cond: AstExpr::Boolean(true),
        }));

        assert!(BranchPrettyPass.rewrite_stmt(&mut stmt));

        let AstStmt::DoBlock(body) = stmt else {
            panic!("constant-true repeat should become a scoped block");
        };
        let [AstStmt::DoBlock(do_block)] = body.stmts.as_slice() else {
            panic!("the original do wrapper must remain");
        };
        let [AstStmt::If(if_stmt)] = do_block.stmts.as_slice() else {
            panic!("the inner break guard should own the tail");
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
    fn keeps_fallthrough_do_break_when_tail_would_extend_local_scope() {
        let mut stmt = AstStmt::Repeat(Box::new(AstRepeat {
            body: AstBlock {
                stmts: vec![
                    AstStmt::DoBlock(Box::new(AstBlock {
                        stmts: vec![recovered_local(0), break_guard("skip")],
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
