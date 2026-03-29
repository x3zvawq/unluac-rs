//! 这个 pass 负责把“紧邻 loop header 的机械 local alias run”收回控制头。
//!
//! 常见形状是：
//! `local start = 1; local limit = #list; local step = 1; for i = start, limit, step do`
//! 这些 local 往往只是前层为了保持单值边界而提前物化的中间 binding。
//! 当它们只在 loop header 被读取时，把它们重新折回控制头会更接近源码。

use crate::readability::ReadabilityOptions;

use super::super::common::{AstBlock, AstExpr, AstLocalAttr, AstLocalOrigin, AstModule, AstStmt};
use super::ReadabilityContext;
use super::binding_flow::{
    count_binding_uses_in_stmt, count_binding_uses_in_stmts, name_matches_binding,
};
use super::binding_tree::{
    binding_from_name_ref, count_name_expr_uses, replace_binding_use_in_expr,
    stmt_mentions_binding_target,
};
use super::expr_analysis::expr_complexity;
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

        for index in 0..block.stmts.len() {
            let (head, tail) = block.stmts.split_at_mut(index + 1);
            let Some(AstStmt::Repeat(repeat_stmt)) = head.last_mut() else {
                continue;
            };
            changed |= collapse_repeat_tail_binding(repeat_stmt, tail, self.options);
        }

        let old_stmts = std::mem::take(&mut block.stmts);
        let mut new_stmts = Vec::with_capacity(old_stmts.len());
        let mut index = 0;
        while index < old_stmts.len() {
            let mut run_end = index;
            while run_end < old_stmts.len() && loop_header_candidate(&old_stmts[run_end]).is_some()
            {
                run_end += 1;
            }

            if run_end == index || run_end >= old_stmts.len() {
                new_stmts.push(old_stmts[index].clone());
                index += 1;
                continue;
            }

            let mut rewritten_loop = old_stmts[run_end].clone();
            let mut removed = vec![false; run_end - index];
            let mut collapsed_count = 0usize;

            for candidate_index in (index..run_end).rev() {
                let Some((binding, value)) = loop_header_candidate(&old_stmts[candidate_index])
                else {
                    continue;
                };
                if !is_loop_header_inline_expr(value, self.options) {
                    continue;
                }
                if count_binding_uses_in_stmts(
                    &old_stmts[(candidate_index + 1)..(run_end + 1)],
                    binding.id,
                ) != 1
                {
                    continue;
                }
                if count_binding_uses_in_stmts(&old_stmts[(run_end + 1)..], binding.id) != 0 {
                    continue;
                }
                if count_binding_uses_in_stmts(
                    &old_stmts[(candidate_index + 1)..run_end],
                    binding.id,
                ) != 0
                {
                    continue;
                }
                if !header_uses_binding_exactly_once(&rewritten_loop, binding.id) {
                    continue;
                }

                let mut trial_loop = rewritten_loop.clone();
                if rewrite_loop_header_binding(&mut trial_loop, binding.id, value) {
                    rewritten_loop = trial_loop;
                    removed[candidate_index - index] = true;
                    collapsed_count += 1;
                }
            }

            if collapsed_count >= 2 {
                changed = true;
                for (offset, stmt) in old_stmts[index..run_end].iter().enumerate() {
                    if !removed[offset] {
                        new_stmts.push(stmt.clone());
                    }
                }
                new_stmts.push(rewritten_loop);
                index = run_end + 1;
                continue;
            }

            new_stmts.push(old_stmts[index].clone());
            index += 1;
        }

        block.stmts = new_stmts;
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
    tail_stmts: &[AstStmt],
    options: ReadabilityOptions,
) -> bool {
    let Some((binding, replacement)) = repeat_tail_candidate(repeat_stmt, options) else {
        return false;
    };
    if count_binding_uses_in_stmts(tail_stmts, binding) != 0 {
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
    if count_binding_uses_in_stmts(&repeat_stmt.body.stmts[..tail_index], binding) != 0 {
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
        AstStmt::GenericFor(generic_for) => generic_for
            .iterator
            .iter_mut()
            .fold(false, |changed, expr| {
                replace_exact_name_expr(expr, binding, replacement) || changed
            }),
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

#[cfg(test)]
mod tests;
