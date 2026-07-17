//! 这个 pass 负责把“紧邻 loop header 的机械 local alias run”收回控制头。
//!
//! 常见形状是：
//! `local start = 1; local limit = 10; local step = 1; for i = start, limit, step do`
//! 这些 local 往往只是前层为了保持单值边界而提前物化的中间 binding。
//! 普通 loop 只移动稳定字面量：当 alias run 中有未被删除的语句时，把元方法运算、
//! lookup 或 binding 读取折进 header 会跨过这些语句，改变求值顺序或读到的值。

use crate::ast::ReadabilityOptions;

use super::super::common::{AstBlock, AstExpr, AstLocalAttr, AstLocalOrigin, AstModule, AstStmt};
use super::ReadabilityContext;
use super::binding_flow::{BindingUseIndex, count_binding_uses_in_stmt};
use super::binding_ref::{binding_from_name_ref, name_matches_binding};
use super::binding_tree::{
    count_name_expr_uses, replace_binding_use_in_expr, stmt_mentions_binding_target,
};
use super::expr_analysis::expr_complexity;
use super::stmt_plan::{PlannedStmt, materialize_stmt_plan};
use super::walk::{self, AstRewritePass, BlockKind};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    walk::rewrite_module(
        module,
        &mut LoopHeaderMergePass {
            options: context.options,
        },
    )
}

struct LoopHeaderMergePass {
    options: ReadabilityOptions,
}

impl AstRewritePass for LoopHeaderMergePass {
    fn rewrite_block(&mut self, block: &mut AstBlock, _kind: BlockKind) -> bool {
        let mut changed = false;
        let mut old_stmts = std::mem::take(&mut block.stmts);
        let mut use_index = BindingUseIndex::for_stmts(&old_stmts);
        let mut repeat_changed = false;

        for (index, stmt) in old_stmts.iter_mut().enumerate() {
            let AstStmt::Repeat(repeat_stmt) = stmt else {
                continue;
            };
            let collapsed =
                collapse_repeat_tail_binding(repeat_stmt, &use_index, index + 1, self.options);
            repeat_changed |= collapsed;
            changed |= collapsed;
        }
        if repeat_changed {
            use_index = BindingUseIndex::for_stmts(&old_stmts);
        }

        let mut stmt_plan = Vec::with_capacity(old_stmts.len());
        let mut index = 0;
        while index < old_stmts.len() {
            let mut run_end = index;
            while run_end < old_stmts.len() && loop_header_candidate(&old_stmts[run_end]).is_some()
            {
                run_end += 1;
            }

            if run_end == index || run_end >= old_stmts.len() {
                stmt_plan.push(PlannedStmt::Original(index));
                index += 1;
                continue;
            }

            let mut rewritten_loop = None;
            let mut removed = vec![false; run_end - index];
            let mut collapsed_count = 0usize;

            for candidate_index in (index..run_end).rev() {
                let Some((binding, value)) = loop_header_candidate(&old_stmts[candidate_index])
                else {
                    continue;
                };
                if !is_loop_header_reorder_safe_expr(value) {
                    continue;
                }
                if use_index.count_uses_in_range(candidate_index + 1, run_end + 1, binding.id) != 1
                {
                    continue;
                }
                if use_index.count_uses_in_suffix(run_end + 1, binding.id) != 0 {
                    continue;
                }
                if use_index.count_uses_in_range(candidate_index + 1, run_end, binding.id) != 0 {
                    continue;
                }
                let current_loop = rewritten_loop.as_ref().unwrap_or(&old_stmts[run_end]);
                if !header_uses_binding_exactly_once(current_loop, binding.id) {
                    continue;
                }

                let mut trial_loop = current_loop.clone();
                if rewrite_loop_header_binding(&mut trial_loop, binding.id, value) {
                    rewritten_loop = Some(trial_loop);
                    removed[candidate_index - index] = true;
                    collapsed_count += 1;
                }
            }

            if collapsed_count >= 2 {
                changed = true;
                for (offset, removed) in removed.iter().enumerate() {
                    if !removed {
                        stmt_plan.push(PlannedStmt::Original(index + offset));
                    }
                }
                stmt_plan.push(PlannedStmt::Rewritten(
                    rewritten_loop.expect("collapsed loop header must rewrite the loop"),
                ));
                index = run_end + 1;
                continue;
            }

            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
        }

        block.stmts = materialize_stmt_plan(old_stmts, stmt_plan);
        changed
    }
}

fn loop_header_candidate(
    stmt: &AstStmt,
) -> Option<(&super::super::common::AstLocalBinding, &AstExpr)> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [value] = local_decl.values.as_slice() else {
        return None;
    };
    if binding.attr != AstLocalAttr::None || binding.origin != AstLocalOrigin::Recovered {
        return None;
    }
    Some((binding, value))
}

fn collapse_repeat_tail_binding(
    repeat_stmt: &mut super::super::common::AstRepeat,
    suffix_use_index: &BindingUseIndex,
    suffix_start: usize,
    options: ReadabilityOptions,
) -> bool {
    let Some((binding, replacement)) = repeat_tail_candidate(repeat_stmt, options) else {
        return false;
    };
    if suffix_use_index.count_uses_in_suffix(suffix_start, binding) != 0 {
        return false;
    }
    if !replace_binding_use_in_expr(&mut repeat_stmt.cond, binding, &replacement) {
        return false;
    }
    repeat_stmt.body.stmts.pop();
    true
}

fn repeat_tail_candidate(
    repeat_stmt: &super::super::common::AstRepeat,
    options: ReadabilityOptions,
) -> Option<(super::super::common::AstBindingRef, AstExpr)> {
    let tail_index = repeat_stmt.body.stmts.len().checked_sub(1)?;
    let tail_stmt = repeat_stmt.body.stmts.get(tail_index)?;
    let (binding, value) = repeat_tail_assignment(tail_stmt)?;
    if !matches!(
        binding,
        super::super::common::AstBindingRef::Temp(_)
            | super::super::common::AstBindingRef::SyntheticLocal(_)
    ) {
        return None;
    }
    if !is_loop_header_inline_expr(value, options) {
        return None;
    }
    let body_use_index = BindingUseIndex::for_stmts(&repeat_stmt.body.stmts);
    if body_use_index.count_uses_in_range(0, tail_index, binding) != 0 {
        return None;
    }
    if repeat_stmt.body.stmts[..tail_index]
        .iter()
        .any(|stmt| stmt_mentions_binding_target(stmt, binding))
    {
        return None;
    }
    if count_name_expr_uses(&repeat_stmt.cond, binding) != 1 {
        return None;
    }
    if !cond_evaluates_binding_first(&repeat_stmt.cond, binding) {
        return None;
    }
    Some((binding, value.clone()))
}

fn repeat_tail_assignment(
    stmt: &AstStmt,
) -> Option<(super::super::common::AstBindingRef, &AstExpr)> {
    let AstStmt::Assign(assign) = stmt else {
        return None;
    };
    let [super::super::common::AstLValue::Name(name)] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.as_slice() else {
        return None;
    };
    let binding = binding_from_name_ref(name)?;
    Some((binding, value))
}

fn is_loop_header_inline_expr(expr: &AstExpr, options: ReadabilityOptions) -> bool {
    expr_complexity(expr) <= options.return_inline_max_complexity
        && !matches!(
            expr,
            AstExpr::VarArg | AstExpr::TableConstructor(_) | AstExpr::FunctionExpr(_)
        )
}

fn is_loop_header_reorder_safe_expr(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. } => true,
        AstExpr::SingleValue(expr) => is_loop_header_reorder_safe_expr(expr),
        _ => false,
    }
}

fn cond_evaluates_binding_first(
    expr: &AstExpr,
    binding: super::super::common::AstBindingRef,
) -> bool {
    match expr {
        AstExpr::Var(name) => name_matches_binding(name, binding),
        AstExpr::SingleValue(expr) => cond_evaluates_binding_first(expr, binding),
        AstExpr::Unary(unary) => cond_evaluates_binding_first(&unary.expr, binding),
        AstExpr::Binary(binary) => cond_evaluates_binding_first(&binary.lhs, binding),
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            cond_evaluates_binding_first(&logical.lhs, binding)
        }
        AstExpr::FieldAccess(access) => cond_evaluates_binding_first(&access.base, binding),
        AstExpr::IndexAccess(access) => cond_evaluates_binding_first(&access.base, binding),
        AstExpr::Call(call) => cond_evaluates_binding_first(&call.callee, binding),
        AstExpr::MethodCall(call) => cond_evaluates_binding_first(&call.receiver, binding),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_)
        | AstExpr::Error(_) => false,
    }
}

fn header_uses_binding_exactly_once(
    stmt: &AstStmt,
    binding: super::super::common::AstBindingRef,
) -> bool {
    count_binding_uses_in_loop_header(stmt, binding) == 1
        && count_binding_uses_in_stmt(stmt, binding) == 1
}

fn rewrite_loop_header_binding(
    stmt: &mut AstStmt,
    binding: super::super::common::AstBindingRef,
    replacement: &AstExpr,
) -> bool {
    match stmt {
        AstStmt::NumericFor(numeric_for) => {
            let mut changed = replace_exact_name_expr(&mut numeric_for.start, binding, replacement);
            changed |= replace_exact_name_expr(&mut numeric_for.limit, binding, replacement);
            changed |= replace_exact_name_expr(&mut numeric_for.step, binding, replacement);
            changed
        }
        AstStmt::GenericFor(generic_for) => {
            let mut changed = false;
            for expr in &mut generic_for.iterator {
                changed |= replace_exact_name_expr(expr, binding, replacement);
            }
            changed
        }
        _ => false,
    }
}

fn count_binding_uses_in_loop_header(
    stmt: &AstStmt,
    binding: super::super::common::AstBindingRef,
) -> usize {
    match stmt {
        AstStmt::NumericFor(numeric_for) => {
            count_name_expr_uses(&numeric_for.start, binding)
                + count_name_expr_uses(&numeric_for.limit, binding)
                + count_name_expr_uses(&numeric_for.step, binding)
        }
        AstStmt::GenericFor(generic_for) => generic_for
            .iterator
            .iter()
            .map(|expr| count_name_expr_uses(expr, binding))
            .sum(),
        _ => 0,
    }
}

fn replace_exact_name_expr(
    expr: &mut AstExpr,
    binding: super::super::common::AstBindingRef,
    replacement: &AstExpr,
) -> bool {
    if matches!(expr, AstExpr::Var(name) if name_matches_binding(name, binding)) {
        *expr = replacement.clone();
        true
    } else {
        false
    }
}
