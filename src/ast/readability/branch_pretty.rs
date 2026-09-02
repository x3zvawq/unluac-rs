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
//!
//! capture 边界只消费直接 closure 已保存的 metadata，不进入子函数的独立 LocalId 空间。

use super::super::common::{
    AstBindingRef, AstBlock, AstExpr, AstFunctionExpr, AstIf, AstLocalAttr, AstLogicalExpr,
    AstModule, AstRepeat, AstReturn, AstStmt, AstUnaryExpr, AstUnaryOpKind,
};
use super::ReadabilityContext;
use super::binding_flow::binding_is_directly_written_in_suffix;
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
            let is_constant_if = matches!(
                &stmt,
                AstStmt::If(if_stmt) if matches!(if_stmt.cond, AstExpr::Boolean(_))
            );
            let folded = if is_constant_if {
                fold_constant_if(stmt)
            } else {
                flatten_terminating_if(stmt)
            };
            match folded {
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
    if repeat_stmt.body.stmts[..len - 2]
        .iter()
        .any(|stmt| stmt_contains_current_loop_continue(stmt, 0))
    {
        // 候选拒绝[SemanticBarrier:ControlFlow]：prefix 中较早的 `continue` 原本直接进入旧 latch；折叠后会额外求值尾部 G/B（regress_294）。
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

fn stmt_contains_current_loop_continue(stmt: &AstStmt, loop_depth: usize) -> bool {
    match stmt {
        AstStmt::If(if_stmt) => {
            if_stmt
                .then_block
                .stmts
                .iter()
                .any(|stmt| stmt_contains_current_loop_continue(stmt, loop_depth))
                || if_stmt.else_block.as_ref().is_some_and(|else_block| {
                    else_block
                        .stmts
                        .iter()
                        .any(|stmt| stmt_contains_current_loop_continue(stmt, loop_depth))
                })
        }
        AstStmt::DoBlock(block) => block
            .stmts
            .iter()
            .any(|stmt| stmt_contains_current_loop_continue(stmt, loop_depth)),
        AstStmt::While(while_stmt) => while_stmt
            .body
            .stmts
            .iter()
            .any(|stmt| stmt_contains_current_loop_continue(stmt, loop_depth + 1)),
        AstStmt::Repeat(repeat_stmt) => repeat_stmt
            .body
            .stmts
            .iter()
            .any(|stmt| stmt_contains_current_loop_continue(stmt, loop_depth + 1)),
        AstStmt::NumericFor(numeric_for) => numeric_for
            .body
            .stmts
            .iter()
            .any(|stmt| stmt_contains_current_loop_continue(stmt, loop_depth + 1)),
        AstStmt::GenericFor(generic_for) => generic_for
            .body
            .stmts
            .iter()
            .any(|stmt| stmt_contains_current_loop_continue(stmt, loop_depth + 1)),
        AstStmt::Continue => loop_depth == 0,
        AstStmt::LocalDecl(_)
        | AstStmt::GlobalDecl(_)
        | AstStmt::Assign(_)
        | AstStmt::CallStmt(_)
        | AstStmt::Return(_)
        | AstStmt::Break
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::Error(_) => false,
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
        AstStmt::DoBlock(block) => single_pass_block_flow(block),
        AstStmt::Continue => {
            // 候选拒绝[SemanticBarrier:ControlFlow]：当前 repeat owner 的 continue 会跳过
            // 被下沉的共享后缀并直接进入 latch（regress_294）。
            None
        }
        // goto/label 已由 single-pass 候选入口的 forbidden-node 预检拒绝；这里保留
        // None 只是让 flow helper 对全部 AST 节点保持封闭。
        AstStmt::Goto(_) | AstStmt::Label(_) => None,
        // 候选拒绝[PolicyBoundary]：项目保留 Error 作为 best-effort 反编译诊断，不把它
        // 当成可执行语句参与 single-pass 控制流美化。
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
            return false;
        };
        if !stmt_flow.contains_break {
            tail_is_nonempty = true;
            continue;
        }

        if let AstStmt::DoBlock(do_block) = stmt {
            let do_tail_is_nonempty = stmt_flow.falls_through && tail_is_nonempty;
            if do_tail_is_nonempty && block_prevents_tail_extension(do_block) {
                return false;
            }
            if !single_pass_block_is_foldable(do_block, do_tail_is_nonempty) {
                return false;
            }
            tail_is_nonempty = true;
            continue;
        }

        let AstStmt::If(if_stmt) = stmt else {
            unreachable!("validated direct breaks can only remain under an if");
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
        if then_flow.falls_through && else_flow.falls_through && tail_is_nonempty {
            // 候选拒绝[PolicyBoundary]：两臂都可能 fallthrough 时只能把非空 continuation
            // 复制进两个互斥 arm；项目不为消除 single-pass fence 复制整段源码或重复声明
            // binding identity（regress_242）。
            return false;
        }

        if then_flow.falls_through {
            if tail_is_nonempty && block_prevents_tail_extension(&if_stmt.then_block) {
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
            if else_tail_is_nonempty && block_prevents_tail_extension(else_block) {
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
        assert!(
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
        // 候选拒绝[SemanticBarrier:ControlFlow]：显式 goto 可从待搬动区间外进入
        // label，也可回跳到区间头；把线性尾部收入单次 break arm 会删除
        // 外部入口或后续迭代（regress_368）。
        AstStmt::Goto(_) | AstStmt::Label(_) => true,
        // 候选拒绝[PolicyBoundary]：项目要求 Error 诊断原位保留，不参与展示层控制重建。
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
    if if_stmt.else_block.is_some() || inner.else_block.is_some() {
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
/// 不再有条件求值事件，未选中的 arm 也不会执行。不过，未选 arm 的 permissive
/// label/goto 与 Error 都是项目要求保留的诊断证据；DebugHinted local 与显式 local
/// attr 则携带项目要求保留的源码 identity。纯 PhysicalRoot、recovered local-function、
/// capture 与 `global` 声明在未选 arm 都不会产生运行期事件；`global` 的词法效力也不会
/// 越过该 arm，因此它们不构成删除边界。
/// 这些证据只在未选 arm 会被删除时阻止改写；位于选中 arm 时节点本身继续保留，
/// 需要词法范围的语句用 `do ... end` 保持原 if block 的边界，包括 `<close>` 的退出点和
/// captured local 的 root lifetime。`break`/`continue` 只跨过非循环的 `if` 外壳，最近
/// loop owner 不变。
fn fold_constant_if(stmt: AstStmt) -> Result<Vec<AstStmt>, AstStmt> {
    let AstStmt::If(mut if_stmt) = stmt else {
        return Err(stmt);
    };
    let selected_then = match &if_stmt.cond {
        AstExpr::Boolean(value) => *value,
        _ => return Err(AstStmt::If(if_stmt)),
    };

    if constant_if_unselected_arm_is_protected(&if_stmt, selected_then) {
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

fn constant_if_unselected_arm_is_protected(if_stmt: &AstIf, selected_then: bool) -> bool {
    let unselected = if selected_then {
        if_stmt.else_block.as_ref()
    } else {
        Some(&if_stmt.then_block)
    };
    let Some(unselected) = unselected else {
        return false;
    };

    // 候选拒绝[PolicyBoundary]：未选 arm 的 label/goto 是 permissive 控制诊断证据；
    // 即使常量条件令它不可执行，项目也不在展示层静默删除。
    block_contains_label_or_goto(unselected)
        // 候选拒绝[PolicyBoundary]：删除常量 arm 外壳会连同 best-effort Error 诊断一起
        // 消失；项目选择保留失败证据，即使该 arm 按运行语义不可达。
        || block_contains_diagnostic(unselected)
        // 候选拒绝[PolicyBoundary]：DebugHinted（含同时为 PhysicalRoot）的源码身份与
        // 显式 local attr 即使位于未选 arm 也按项目的源码证据保留策略记账；纯
        // PhysicalRoot、recovered local-function 与 capture 在恒不可达 arm 没有运行期。
        || block_contains_identity_boundary(unselected)
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

struct IdentityBoundaryVisitor(bool);

impl AstVisitor for IdentityBoundaryVisitor {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        match stmt {
            AstStmt::LocalDecl(local_decl) => {
                self.0 |= local_decl.bindings.iter().any(|binding| {
                    binding.origin.is_debug_hinted()
                        || !matches!(binding.attr, AstLocalAttr::None)
                        || binding.rewrite_authority.must_preserve()
                });
            }
            AstStmt::LocalFunctionDecl(local_function) => {
                self.0 |= local_function.origin.is_debug_hinted()
                    || local_function.rewrite_authority.must_preserve();
            }
            _ => {}
        }
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
        // condition=false 原本会继续父级后缀；插入 guard return 会提前结束函数
        // （regress_382）。
        return false;
    }
    let removed_if = block.stmts.remove(if_index);
    let AstStmt::If(mut if_stmt) = removed_if else {
        unreachable!("checked above, terminal guard candidate must remain an if");
    };
    if remove_terminal_empty_return {
        let popped = block
            .stmts
            .pop()
            .expect("validated terminal guard must retain its fallback return");
        assert!(
            is_empty_return_stmt(&popped),
            "validated terminal guard fallback must remain an empty return"
        );
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
    // terminal-guard 的候选本就是单臂函数尾；带 else 的 if 不属于该形状。
    if if_stmt.else_block.is_some() {
        return None;
    }
    if !block_always_terminates(&if_stmt.then_block)
        || !matches!(if_stmt.then_block.stmts.last(), Some(AstStmt::Return(_)))
    {
        return None;
    }
    // 单独空 return 没有可提升主体，不形成 terminal-guard 候选。
    if matches!(if_stmt.then_block.stmts.as_slice(), [stmt] if is_empty_return_stmt(stmt)) {
        return None;
    }
    if matches!(if_stmt.cond, AstExpr::Boolean(_)) {
        assert!(
            constant_if_unselected_arm_is_protected(
                if_stmt,
                matches!(if_stmt.cond, AstExpr::Boolean(true)),
            ),
            "unprotected Boolean if must be consumed by the constant-if owner"
        );
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

fn block_prevents_tail_extension(block: &AstBlock) -> bool {
    if block_captures_direct_local(block) {
        // 候选拒绝[SemanticBarrier:Capture]：continuation 原本在 captured local 的词法块
        // 之外；下沉会延长该 cell 的开放期及 closure root，regress_378 的弱表/GC
        // 观察可以区分两个释放点。
        return true;
    }

    block
        .stmts
        .iter()
        .enumerate()
        .any(|(stmt_index, stmt)| match stmt {
            AstStmt::LocalDecl(local_decl) => {
                local_decl
                    .bindings
                    .iter()
                    .enumerate()
                    .any(|(binding_index, binding)| {
                        if binding.attr == AstLocalAttr::Close {
                            // 候选拒绝[SemanticBarrier:Lifetime]：把 continuation 收进该 arm 会把
                            // `<close>` 的关闭点从原 arm 末尾推迟到 continuation 之后（regress_378）。
                            true
                        } else if binding.origin.is_physical_root() {
                            // 候选拒绝[SemanticBarrier:Lifetime]：把 continuation 收进该 arm 会延长
                            // PhysicalRoot 的强引用期，弱表或 `__gc` 可以观察到差异（regress_378）。
                            true
                        } else if binding.origin.is_debug_hinted() {
                            // 候选拒绝[SemanticBarrier:DebugScope]：continuation 原本位于 debug local
                            // 的词法范围外；下沉后 debug API 会在 continuation 中观察到该 binding
                            // （regress_351）。
                            true
                        } else if !binding.rewrite_authority.may_shorten_lifetime() {
                            // 候选拒绝[LayerBoundary]：HIR 已冻结该 binding 的结束边界；把
                            // continuation 收进 arm 会延长它，AST 不再重建底层生命周期证明。
                            true
                        } else if local_decl.initializer_root_profile.as_ref().is_none_or(
                            |profile| profile.may_affect_collectable_lifetime(binding_index),
                        ) {
                            // 候选拒绝[SemanticBarrier:Lifetime]：initializer 的原始 VM 结果类别
                            // 只消费 HIR 发布的逐槽证明；缺失或越界事实必须 fail closed，AST
                            // 不从最终表达式形状重建 value-pack 或 stack-root 语义。
                            true
                        } else {
                            // 候选拒绝[ProofIncomplete]：HIR profile 只证明 declaration
                            // initializer。若 binding 到原 block fallthrough 之间又被写入，scope-end
                            // 值已不是该 initializer；AST 只证明候选区间没有写入，不分析 RHS
                            // 类型。更精确的接受需要未来的 HIR endpoint certificate。
                            binding_is_directly_written_in_suffix(
                                &block.stmts,
                                stmt_index + 1,
                                binding.id,
                            )
                        }
                    })
            }
            AstStmt::LocalFunctionDecl(local_function) => {
                if local_function.origin.is_physical_root() {
                    // 候选拒绝[SemanticBarrier:Lifetime]：local function 的 PhysicalRoot 原本在
                    // arm 末尾释放，下沉 continuation 会延长闭包强引用期。
                    true
                } else if local_function.origin.is_debug_hinted() {
                    // 候选拒绝[SemanticBarrier:DebugScope]：下沉 continuation 会扩大 debug
                    // local-function binding 的可观察词法范围。
                    true
                } else {
                    // 候选拒绝[SemanticBarrier:Lifetime]：local-function binding 本身持有闭包；
                    // 把 continuation 收进 arm 会延长闭包及其 capture 的强引用期
                    // （regress_378 用 `collectgarbage` 观察 captured object 的释放点）。
                    true
                }
            }
            AstStmt::GlobalDecl(_) => {
                // 候选拒绝[SemanticBarrier:Scope]：Lua 5.5 中 `global x` 的词法效力原本
                // 在 arm 末尾结束；把后缀 `x = value` 收进 arm 会把未声明访问变成已声明访问
                // （cleanup::keeps_repeat_tail_global_declaration_scope 使用同一边界）。
                true
            }
            _ => false,
        })
}

fn block_captures_direct_local(block: &AstBlock) -> bool {
    let direct_bindings = block
        .stmts
        .iter()
        .flat_map(|stmt| match stmt {
            AstStmt::LocalDecl(local_decl) => local_decl
                .bindings
                .iter()
                .map(|binding| binding.id)
                .collect::<Vec<_>>(),
            AstStmt::LocalFunctionDecl(local_function) => vec![local_function.name],
            _ => Vec::new(),
        })
        .collect::<Vec<_>>();
    if direct_bindings.is_empty() {
        return false;
    }

    struct DirectCaptureVisitor<'a> {
        direct_bindings: &'a [AstBindingRef],
        found: bool,
    }

    impl AstVisitor for DirectCaptureVisitor<'_> {
        fn visit_function_expr(&mut self, function: &AstFunctionExpr) -> bool {
            self.found |= self
                .direct_bindings
                .iter()
                .any(|binding| function.captured_bindings.contains(binding));
            // `captured_bindings` 已完整描述这个直接 closure 对当前 owner 的 capture；
            // 不能再进入 child body 比较裸 LocalId，因为 child 使用独立的 local
            // 命名空间，相同数字不表示同一 binding。
            false
        }
    }

    let mut visitor = DirectCaptureVisitor {
        direct_bindings: &direct_bindings,
        found: false,
    };
    visit::visit_block(block, &mut visitor);
    visitor.found
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
    use std::collections::BTreeSet;

    use super::*;
    use crate::ast::common::{
        AstAssign, AstBindingRef, AstCallExpr, AstCallKind, AstCallStmt, AstGlobalAttr,
        AstGlobalBinding, AstGlobalBindingTarget, AstGlobalDecl, AstGlobalName, AstGoto, AstLValue,
        AstLabel, AstLabelId, AstLocalAttr, AstLocalBinding, AstLocalDecl, AstLocalOrigin,
        AstRepeat, AstWhile,
    };
    use crate::decompile::DecompileDialect;
    use crate::hir::{HirExpr, HirProtoRef, HirValuePack, LocalId, initializer_root_profile};

    fn global_expr(name: &str) -> AstExpr {
        AstExpr::Var(crate::ast::common::AstNameRef::Global(AstGlobalName {
            text: name.to_owned(),
        }))
    }

    fn call_expr(name: &str) -> AstExpr {
        AstExpr::Call(Box::new(AstCallExpr {
            callee: global_expr(name),
            args: Vec::new(),
            method_key: None,
            callee_root_handoff: None,
            method_rewrite_transaction: None,
        }))
    }

    fn call_stmt(name: &str) -> AstStmt {
        let AstExpr::Call(call) = call_expr(name) else {
            unreachable!("call_expr must produce a call");
        };
        AstStmt::CallStmt(Box::new(AstCallStmt {
            call: AstCallKind::Call(call),
        }))
    }

    fn capturing_call_stmt(name: &str, binding: AstBindingRef) -> AstStmt {
        AstStmt::CallStmt(Box::new(AstCallStmt {
            call: AstCallKind::Call(Box::new(AstCallExpr {
                callee: global_expr(name),
                args: vec![AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
                    function: HirProtoRef(1),
                    params: Vec::new(),
                    is_vararg: false,
                    named_vararg: None,
                    body: AstBlock::default(),
                    captured_bindings: BTreeSet::from([binding]),
                    captured_params: BTreeSet::new(),
                    capture_names_by_upvalue: std::collections::BTreeMap::new(),
                    capture_write_names: BTreeSet::new(),
                }))],
                method_key: None,
                callee_root_handoff: None,
                method_rewrite_transaction: None,
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

    fn single_pass_fallthrough_arm(arm_stmts: Vec<AstStmt>) -> AstStmt {
        AstStmt::Repeat(Box::new(AstRepeat {
            body: AstBlock {
                stmts: vec![
                    AstStmt::If(Box::new(AstIf {
                        cond: global_expr("skip"),
                        then_block: AstBlock {
                            stmts: vec![AstStmt::Break],
                        },
                        else_block: Some(AstBlock { stmts: arm_stmts }),
                    })),
                    call_stmt("tail"),
                ],
            },
            cond: AstExpr::Boolean(true),
            lifetime: Default::default(),
        }))
    }

    fn recovered_local(id: usize) -> AstStmt {
        AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![AstLocalBinding {
                id: AstBindingRef::Local(LocalId(id)),
                attr: AstLocalAttr::None,
                origin: AstLocalOrigin::Recovered,
                rewrite_authority: crate::ast::common::AstRewriteAuthority::AstOwned,
            }],
            values: vec![AstExpr::Integer(1)],
            initializer_merge_transaction: None,
            initializer_root_profile: Some(initializer_root_profile(
                DecompileDialect::Lua54,
                &HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                1,
            )),
        }))
    }

    fn physical_local(id: usize) -> AstStmt {
        let mut stmt = recovered_local(id);
        let AstStmt::LocalDecl(local_decl) = &mut stmt else {
            unreachable!("recovered_local must produce a local declaration");
        };
        local_decl.bindings[0].origin = AstLocalOrigin::PhysicalRoot;
        stmt
    }

    fn close_local(id: usize) -> AstStmt {
        let mut stmt = recovered_local(id);
        let AstStmt::LocalDecl(local_decl) = &mut stmt else {
            unreachable!("recovered_local must produce a local declaration");
        };
        local_decl.bindings[0].attr = AstLocalAttr::Close;
        local_decl.values[0] = AstExpr::Nil;
        stmt
    }

    fn recovered_call_local(id: usize) -> AstStmt {
        let mut stmt = recovered_local(id);
        let AstStmt::LocalDecl(local_decl) = &mut stmt else {
            unreachable!("recovered_local must produce a local declaration");
        };
        local_decl.values[0] = call_expr("make_value");
        local_decl.initializer_root_profile = Some(initializer_root_profile(
            DecompileDialect::Lua54,
            &HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(id + 1))]),
            1,
        ));
        stmt
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
    fn constant_if_folds_selected_global_declaration_with_scope() {
        let stmt = AstStmt::If(Box::new(AstIf {
            cond: AstExpr::Boolean(true),
            then_block: AstBlock {
                stmts: vec![global_decl_stmt("selected")],
            },
            else_block: None,
        }));

        let Ok(selected_stmts) = fold_constant_if(stmt) else {
            panic!("selected global declaration must not protect an absent arm");
        };
        let [AstStmt::DoBlock(selected)] = selected_stmts.as_slice() else {
            panic!("selected global declaration must retain its lexical scope");
        };
        assert_eq!(selected.stmts, vec![global_decl_stmt("selected")]);
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
    fn nested_if_merge_keeps_internal_goto_scope() {
        let label = AstLabelId(0);
        let mut if_stmt = AstIf {
            cond: global_expr("outer"),
            then_block: AstBlock {
                stmts: vec![AstStmt::If(Box::new(AstIf {
                    cond: global_expr("inner"),
                    then_block: AstBlock {
                        stmts: vec![
                            AstStmt::Label(Box::new(AstLabel { id: label })),
                            AstStmt::Goto(Box::new(AstGoto { target: label })),
                        ],
                    },
                    else_block: None,
                }))],
            },
            else_block: None,
        };

        assert!(merge_exact_nested_if(&mut if_stmt));
        assert!(matches!(if_stmt.cond, AstExpr::LogicalAnd(_)));
        assert!(matches!(
            if_stmt.then_block.stmts.as_slice(),
            [AstStmt::Label(_), AstStmt::Goto(_)]
        ));
    }

    #[test]
    fn selected_diagnostic_survives_constant_if_folding() {
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

        assert!(BranchPrettyPass.rewrite_block(&mut block, BlockKind::Regular));
        assert!(matches!(block.stmts.as_slice(), [AstStmt::Error(_)]));
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
    fn terminal_guard_keeps_internal_goto_scope() {
        let label = AstLabelId(0);
        let mut block = AstBlock {
            stmts: vec![AstStmt::If(Box::new(AstIf {
                cond: global_expr("guard"),
                then_block: AstBlock {
                    stmts: vec![
                        AstStmt::Label(Box::new(AstLabel { id: label })),
                        AstStmt::Goto(Box::new(AstGoto { target: label })),
                        AstStmt::Return(Box::new(AstReturn { values: vec![] })),
                    ],
                },
                else_block: None,
            }))],
        };

        assert!(BranchPrettyPass.rewrite_block(&mut block, BlockKind::FunctionBody));
        let [AstStmt::If(_), AstStmt::DoBlock(selected)] = block.stmts.as_slice() else {
            panic!("lifted control must retain the original arm scope");
        };
        assert!(matches!(
            selected.stmts.as_slice(),
            [AstStmt::Label(_), AstStmt::Goto(_), AstStmt::Return(_)]
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
    fn selected_debug_identity_survives_constant_if_folding() {
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

        assert!(BranchPrettyPass.rewrite_block(&mut block, BlockKind::FunctionBody));
        let [AstStmt::DoBlock(selected)] = block.stmts.as_slice() else {
            panic!("selected debug identity must retain its lexical scope");
        };
        assert!(matches!(
            selected.stmts.as_slice(),
            [AstStmt::LocalDecl(_), AstStmt::Return(_)]
        ));
    }

    #[test]
    fn repeat_tail_fold_keeps_prefix_diagnostic() {
        let mut repeat_stmt = AstRepeat {
            body: AstBlock {
                stmts: vec![
                    AstStmt::Error("diagnostic".to_owned()),
                    AstStmt::If(Box::new(AstIf {
                        cond: global_expr("skip"),
                        then_block: AstBlock {
                            stmts: vec![AstStmt::Continue],
                        },
                        else_block: None,
                    })),
                    break_guard("stop"),
                ],
            },
            cond: global_expr("latch"),
            lifetime: Default::default(),
        };

        assert!(fold_repeat_tail_continue_break(&mut repeat_stmt));
        assert!(matches!(
            repeat_stmt.body.stmts.as_slice(),
            [AstStmt::Error(_)]
        ));
        assert!(matches!(repeat_stmt.cond, AstExpr::LogicalOr(_)));
    }

    #[test]
    fn folds_single_pass_break_guard_without_duplicating_tail() {
        let mut stmt = AstStmt::Repeat(Box::new(AstRepeat {
            body: AstBlock {
                stmts: vec![break_guard("skip"), call_stmt("tail")],
            },
            cond: AstExpr::Boolean(true),
            lifetime: Default::default(),
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
            lifetime: Default::default(),
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
            lifetime: Default::default(),
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
    fn folds_fallthrough_do_break_across_inert_local_scope() {
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
            lifetime: Default::default(),
        }));

        assert!(BranchPrettyPass.rewrite_stmt(&mut stmt));
        assert!(matches!(stmt, AstStmt::DoBlock(_)));
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
            lifetime: Default::default(),
        }));

        assert!(!BranchPrettyPass.rewrite_stmt(&mut stmt));
        assert!(matches!(stmt, AstStmt::Repeat(_)));
    }

    #[test]
    fn folds_single_pass_fence_across_inert_local_scope() {
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
            lifetime: Default::default(),
        }));

        assert!(BranchPrettyPass.rewrite_stmt(&mut stmt));
        assert!(matches!(stmt, AstStmt::DoBlock(_)));
    }

    #[test]
    fn keeps_single_pass_fence_when_inert_local_is_captured() {
        let binding = AstBindingRef::Local(LocalId(0));
        let mut stmt = single_pass_fallthrough_arm(vec![
            recovered_local(0),
            capturing_call_stmt("sink", binding),
        ]);

        assert!(!BranchPrettyPass.rewrite_stmt(&mut stmt));
        assert!(matches!(stmt, AstStmt::Repeat(_)));
    }

    #[test]
    fn keeps_single_pass_fence_when_tail_would_extend_physical_root() {
        let mut stmt = single_pass_fallthrough_arm(vec![physical_local(0)]);

        assert!(!BranchPrettyPass.rewrite_stmt(&mut stmt));
        assert!(matches!(stmt, AstStmt::Repeat(_)));
    }

    #[test]
    fn keeps_single_pass_fence_when_tail_would_extend_recovered_or_reassigned_root() {
        let mut stmt = single_pass_fallthrough_arm(vec![recovered_call_local(0)]);

        assert!(!BranchPrettyPass.rewrite_stmt(&mut stmt));
        assert!(matches!(stmt, AstStmt::Repeat(_)));

        let binding = AstBindingRef::Local(LocalId(0));
        let write = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![AstLValue::Name(binding.to_name_ref())],
            values: vec![call_expr("make_value")],
            initializer_merge_transaction: None,
            method_rewrite_transaction: None,
        }));
        let mut reassigned = single_pass_fallthrough_arm(vec![recovered_local(0), write]);

        assert!(!BranchPrettyPass.rewrite_stmt(&mut reassigned));
        assert!(matches!(reassigned, AstStmt::Repeat(_)));
    }

    #[test]
    fn keeps_single_pass_fence_when_tail_would_delay_close() {
        let mut stmt = single_pass_fallthrough_arm(vec![close_local(0)]);

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
            lifetime: Default::default(),
        }));

        assert!(!BranchPrettyPass.rewrite_stmt(&mut stmt));
        assert!(matches!(stmt, AstStmt::Repeat(_)));
    }
}
