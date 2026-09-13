//! 这个文件负责把“结构等价但不好看”的条件语句收回更像源码的形状。
//!
//! 它依赖 AST build / HIR 已经保证语义正确，只在 Readability 阶段做局部可读性整理，
//! 比如 guard flatten、`not` 交换 then/else。它不会越权补语义，也不会替前层兜底
//! 修错误控制流。
//!
//! 例子：
//! - `if not cond then a() else b() end` 会整理成 `if cond then b() else a() end`
//! - 只有受保护匿名 nil 声明的一臂保持完整并置于 else；普通 not 交换服从该方向，避免反复翻转
//! - `if cond then body else end` 会整理成 `if cond then body end`
//! - `if cond then return end else tail()` 会拉平成 `if cond then return end; tail()`
//! - `repeat if cond then break end; tail() until true` 会整理成 `if not cond then tail() end`
//! - `repeat ...; if G then continue; if B then break until C` 会整理成
//!   `repeat ... until not G and B or C`
//! - 嵌套循环自己的 `continue` 保留原 owner，不会阻止外层 `repeat` 的尾部整理
//!
//! capture 边界只消费直接 closure 已保存的 metadata，不进入子函数的独立 LocalId 空间。

use super::super::common::{
    AstBlock, AstExpr, AstIf, AstLocalAttr, AstLogicalExpr, AstModule, AstRepeat, AstReturn,
    AstStmt, AstUnaryExpr, AstUnaryOpKind,
};
use super::ReadabilityContext;
use super::binding_flow::{BindingWriteIndex, block_captures_direct_local};
use super::control_flow::block_contains_label_or_goto;
use super::walk::{self, AstRewritePass};
use crate::ast::traverse::BlockKind;
use crate::ast::visit::{self, AstVisitor};

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
                    && !(if_stmt
                        .else_block
                        .as_ref()
                        .is_some_and(only_preserved_nil_declarations)
                        && !only_preserved_nil_declarations(&if_stmt.then_block))
                    && let Some(mut else_block) = if_stmt.else_block.take()
                {
                    let inner = unary.expr.clone();
                    std::mem::swap(&mut if_stmt.then_block, &mut else_block);
                    if_stmt.else_block = Some(else_block);
                    if_stmt.cond = inner;
                    changed = true;
                }
                if only_preserved_nil_declarations(&if_stmt.then_block)
                    && if_stmt.else_block.as_ref().is_some_and(|block| {
                        !block.stmts.is_empty() && !only_preserved_nil_declarations(block)
                    })
                {
                    let else_block = if_stmt.else_block.take().unwrap();
                    let old_then = std::mem::replace(&mut if_stmt.then_block, else_block);
                    if_stmt.else_block = Some(old_then);
                    if_stmt.cond = negate_guard_condition(std::mem::replace(
                        &mut if_stmt.cond,
                        AstExpr::Boolean(false),
                    ));
                    changed = true;
                }
                changed |= normalize_empty_if_arms(if_stmt);
                changed |= merge_exact_nested_if(if_stmt);
                changed
            }
            AstStmt::Repeat(repeat_stmt)
                if matches!(repeat_stmt.cond, AstExpr::Boolean(true))
                    && !block_contains_single_pass_forbidden_nodes(&repeat_stmt.body)
                    && let Some(plan) = SinglePassBlockPlan::analyze(&repeat_stmt.body)
                    && plan.flow.contains_break
                    && single_pass_block_is_foldable(&repeat_stmt.body, &plan, false) =>
            {
                let body =
                    fold_single_pass_block(std::mem::take(&mut repeat_stmt.body), plan, None);
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

// 计划只属于本次不可变候选，与直属语句顺序及 If/Do 子块一一对应；许可完成后随原树
// 一起移动，不按 AST 地址查找，也不为下沉的 continuation 重建事实。嵌套 loop 保持 opaque，
// 其 goto/label/Error 仍由独立 forbidden 预检检查。例如连续嵌套的 break arm 只后序分析一次。
struct SinglePassBlockPlan {
    flow: SinglePassFlow,
    stmts: Vec<SinglePassStmtPlan>,
}

enum SinglePassStmtPlan {
    Leaf(SinglePassFlow),
    If(SinglePassBlockPlan, Option<SinglePassBlockPlan>),
    Do(SinglePassBlockPlan),
}

impl SinglePassBlockPlan {
    fn analyze(block: &AstBlock) -> Option<Self> {
        let mut flow = FALLTHROUGH_FLOW;
        let mut stmts = Vec::with_capacity(block.stmts.len());
        for stmt in &block.stmts {
            let plan = SinglePassStmtPlan::analyze(stmt)?;
            let stmt_flow = plan.flow();
            flow.contains_break |= stmt_flow.contains_break;
            flow.falls_through &= stmt_flow.falls_through;
            stmts.push(plan);
        }
        Some(Self { flow, stmts })
    }
}

impl SinglePassStmtPlan {
    fn analyze(stmt: &AstStmt) -> Option<Self> {
        Some(match stmt {
            AstStmt::Break => Self::Leaf(SinglePassFlow {
                falls_through: false,
                contains_break: true,
            }),
            AstStmt::Return(_) => Self::Leaf(SinglePassFlow {
                falls_through: false,
                contains_break: false,
            }),
            AstStmt::If(if_stmt) => Self::If(
                SinglePassBlockPlan::analyze(&if_stmt.then_block)?,
                match &if_stmt.else_block {
                    Some(block) => Some(SinglePassBlockPlan::analyze(block)?),
                    None => None,
                },
            ),
            AstStmt::DoBlock(block) => Self::Do(SinglePassBlockPlan::analyze(block)?),
            // 候选拒绝[SemanticBarrier:ControlFlow]：当前 repeat 的 continue 会跳过下沉
            // 的后缀（regress_294）；goto/label 及不可执行 Error 由 forbidden 预检拒绝。
            AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) | AstStmt::Error(_) => {
                return None;
            }
            AstStmt::LocalDecl(_)
            | AstStmt::GlobalDecl(_)
            | AstStmt::Assign(_)
            | AstStmt::CallStmt(_)
            | AstStmt::While(_)
            | AstStmt::Repeat(_)
            | AstStmt::NumericFor(_)
            | AstStmt::GenericFor(_)
            | AstStmt::FunctionDecl(_)
            | AstStmt::LocalFunctionDecl(_) => Self::Leaf(FALLTHROUGH_FLOW),
        })
    }

    fn flow(&self) -> SinglePassFlow {
        match self {
            Self::Leaf(flow) => *flow,
            Self::Do(block) => block.flow,
            Self::If(then_plan, else_plan) => {
                let else_flow = else_plan
                    .as_ref()
                    .map_or(FALLTHROUGH_FLOW, |plan| plan.flow);
                SinglePassFlow {
                    falls_through: then_plan.flow.falls_through || else_flow.falls_through,
                    contains_break: then_plan.flow.contains_break || else_flow.contains_break,
                }
            }
        }
    }
}

fn single_pass_block_is_foldable(
    block: &AstBlock,
    plan: &SinglePassBlockPlan,
    mut tail_is_nonempty: bool,
) -> bool {
    for (stmt, stmt_plan) in block.stmts.iter().zip(&plan.stmts).rev() {
        if matches!(stmt, AstStmt::Break) {
            tail_is_nonempty = false;
            continue;
        }

        let stmt_flow = stmt_plan.flow();
        if !stmt_flow.contains_break {
            tail_is_nonempty = true;
            continue;
        }

        if let (AstStmt::DoBlock(do_block), SinglePassStmtPlan::Do(do_plan)) = (stmt, stmt_plan) {
            let do_tail_is_nonempty = stmt_flow.falls_through && tail_is_nonempty;
            if do_tail_is_nonempty && block_prevents_tail_extension(do_block) {
                return false;
            }
            if !single_pass_block_is_foldable(do_block, do_plan, do_tail_is_nonempty) {
                return false;
            }
            tail_is_nonempty = true;
            continue;
        }

        let (AstStmt::If(if_stmt), SinglePassStmtPlan::If(then_plan, else_plan)) =
            (stmt, stmt_plan)
        else {
            unreachable!("validated direct breaks can only remain under an if");
        };
        let then_flow = then_plan.flow;
        let else_flow = else_plan
            .as_ref()
            .map_or(FALLTHROUGH_FLOW, |plan| plan.flow);
        if then_flow.falls_through && else_flow.falls_through && tail_is_nonempty {
            // 候选拒绝[PolicyBoundary]：两臂都可能 fallthrough 时只能把非空 continuation
            // 复制进两个互斥 arm；项目不为消除 single-pass fence 复制整段源码或重复声明
            // binding identity（regress_242）。
            return false;
        }

        for (arm, arm_plan) in std::iter::once((&if_stmt.then_block, then_plan))
            .chain(if_stmt.else_block.iter().zip(else_plan))
        {
            let arm_tail_is_nonempty = arm_plan.flow.falls_through && tail_is_nonempty;
            if arm_tail_is_nonempty && block_prevents_tail_extension(arm) {
                return false;
            }
            if !single_pass_block_is_foldable(arm, arm_plan, arm_tail_is_nonempty) {
                return false;
            }
        }

        tail_is_nonempty = true;
    }
    true
}

fn fold_single_pass_block(
    block: AstBlock,
    plan: SinglePassBlockPlan,
    tail: Option<AstBlock>,
) -> AstBlock {
    let mut reverse_tail: Vec<_> = tail
        .map(|tail| tail.stmts.into_iter().rev().collect())
        .unwrap_or_default();

    for (stmt, stmt_plan) in block.stmts.into_iter().zip(plan.stmts).rev() {
        if matches!(stmt, AstStmt::Break) {
            reverse_tail.clear();
            continue;
        }

        let flow = stmt_plan.flow();
        if !flow.contains_break {
            reverse_tail.push(stmt);
            continue;
        }

        if let SinglePassStmtPlan::Do(do_plan) = stmt_plan {
            let AstStmt::DoBlock(do_block) = stmt else {
                unreachable!("single-pass plan must retain its do block");
            };
            let continuation = AstBlock {
                stmts: reverse_tail.into_iter().rev().collect(),
            };
            let do_tail = flow.falls_through.then_some(continuation);
            let do_block = fold_single_pass_block(*do_block, do_plan, do_tail);
            reverse_tail = vec![AstStmt::DoBlock(Box::new(do_block))];
            continue;
        }

        let (AstStmt::If(mut if_stmt), SinglePassStmtPlan::If(then_plan, else_plan)) =
            (stmt, stmt_plan)
        else {
            unreachable!("validated direct breaks can only remain under an if");
        };
        let then_flow = then_plan.flow;
        let else_flow = else_plan
            .as_ref()
            .map_or(FALLTHROUGH_FLOW, |plan| plan.flow);
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

        if_stmt.then_block = fold_single_pass_block(if_stmt.then_block, then_plan, then_tail);
        if_stmt.else_block = match (if_stmt.else_block.take(), else_plan) {
            (Some(else_block), Some(else_plan)) => {
                Some(fold_single_pass_block(else_block, else_plan, else_tail))
            }
            (None, None) => else_tail,
            _ => unreachable!("single-pass plan must retain its else block"),
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

/// 保留原清槽臂，只把有实际主体的一臂放在前面。否定规范化必须服从同一方向，
/// 否则下一轮又会翻回去；这不删除 nil、缩短其块或改变条件的求值次数。
fn only_preserved_nil_declarations(block: &AstBlock) -> bool {
    !block.stmts.is_empty()
        && block.stmts.iter().all(|stmt| {
            let AstStmt::LocalDecl(decl) = stmt else {
                return false;
            };
            !decl.bindings.is_empty()
                && decl.values.len() == decl.bindings.len()
                && decl
                    .values
                    .iter()
                    .all(|value| matches!(value, AstExpr::Nil))
                && decl.bindings.iter().all(|binding| {
                    binding.attr == AstLocalAttr::None
                        && !binding.origin.is_debug_hinted()
                        && binding.rewrite_authority.must_preserve()
                })
        })
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
        self.0 |= stmt.local_bindings().any(|binding| {
            binding.origin.is_debug_hinted()
                || !matches!(binding.attr, AstLocalAttr::None)
                || binding.rewrite_authority.must_preserve()
        });
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

    let writes = std::cell::OnceCell::new();
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
                            writes
                                .get_or_init(|| BindingWriteIndex::for_stmts(&block.stmts))
                                .has_rebinding_after(stmt_index, binding.id)
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
