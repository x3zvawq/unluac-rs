//! 受阈值约束的保守表达式内联。
//!
//! 这里只处理非常窄的一类模式：
//! - 单值 temp / local 别名
//! - 后续只使用一次
//! - 使用点出现在 return / 调用参数 / 索引位 / 调用目标
//! - 被内联表达式必须是我们能证明“纯且无元方法副作用”的安全子集
//! - 相邻 recovered local run 里，只有末尾 local 仍会跨语句存活的机械链

mod candidate;
mod use_sites;

use crate::readability::ReadabilityOptions;

use self::candidate::{
    InlinePolicy, inline_candidate, stmt_is_adjacent_call_result_sink,
    stmt_is_alias_initializer_sink, stmt_is_direct_return_value_sink,
};
use self::use_sites::rewrite_stmt_use_sites_with_policy;
use super::super::common::{AstBindingRef, AstBlock, AstModule, AstStmt};
use super::ReadabilityContext;
use super::binding_flow::{count_binding_uses_in_stmt, count_binding_uses_in_stmts};
use super::binding_tree::{
    expr_references_binding, stmt_has_access_base_binding_use,
    stmt_has_direct_call_arg_binding_use, stmt_has_index_binding_use, stmt_has_nested_binding_use,
};
use super::walk::{self, AstRewritePass, BlockKind};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let _ = context.target;
    walk::rewrite_module(
        module,
        &mut InlineExprsPass {
            options: context.options,
        },
    )
}

struct InlineExprsPass {
    options: ReadabilityOptions,
}

impl AstRewritePass for InlineExprsPass {
    fn rewrite_block(&mut self, block: &mut AstBlock, _kind: BlockKind) -> bool {
        rewrite_current_block(block, self.options)
    }
}

fn rewrite_current_block(block: &mut AstBlock, options: ReadabilityOptions) -> bool {
    let mut changed = false;

    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut index = 0;
    while index < old_stmts.len() {
        let Some(next_stmt) = old_stmts.get(index + 1) else {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        };

        let Some((candidate, value)) = inline_candidate(&old_stmts[index]) else {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        };
        let policy = if matches!(candidate, candidate::InlineCandidate::LocalAlias { .. })
            && stmt_is_alias_initializer_sink(next_stmt)
        {
            InlinePolicy::AliasInitializerChain
        } else if matches!(candidate, candidate::InlineCandidate::LocalAlias { .. })
            && stmt_is_adjacent_call_result_sink(next_stmt)
        {
            InlinePolicy::AdjacentCallResultCallee
        } else if matches!(candidate, candidate::InlineCandidate::LocalAlias { .. })
            && stmt_is_direct_return_value_sink(next_stmt)
        {
            InlinePolicy::DirectReturnConstructor
        } else {
            InlinePolicy::Conservative
        };
        if matches!(policy, InlinePolicy::AliasInitializerChain)
            && candidate::is_lookup_inline_expr(value)
            && stmt_starts_lookup_mechanical_run(&old_stmts, index, candidate.binding())
        {
            // 这里故意不提前把 lookup 链压成“下一条 local 的初始化式”：
            // `local item = items[i]; local weight = item.weight; sum = sum + weight`
            // 如果太早收成 `local weight = items[i].weight`，后面的机械 run 就只剩一层，
            // 无法再判断“整条链都只是脚手架”。让它留到 run-collapse 一次性处理，
            // 才能既收回 for-loop 里的机械局部，又保住 return 场景下的阶段 local。
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        }
        let allows_special_lookup_access_base = matches!(
            candidate,
            candidate::InlineCandidate::LocalAlias {
                origin: super::super::common::AstLocalOrigin::Recovered,
                ..
            }
        ) && matches!(policy, InlinePolicy::Conservative)
            && matches!(next_stmt, AstStmt::Assign(_))
            && candidate::is_lookup_inline_expr(value)
            && stmt_has_access_base_binding_use(next_stmt, candidate.binding());
        let allows_special_index_sink = matches!(
            candidate,
            candidate::InlineCandidate::LocalAlias {
                origin: super::super::common::AstLocalOrigin::Recovered,
                ..
            }
        ) && matches!(policy, InlinePolicy::Conservative)
            && matches!(next_stmt, AstStmt::Assign(_))
            && super::expr_analysis::is_mechanical_run_inline_expr(value)
            && stmt_has_index_binding_use(next_stmt, candidate.binding());
        let effective_policy = if allows_special_index_sink {
            InlinePolicy::MechanicalRun
        } else {
            policy
        };
        if !candidate.allows_expr_with_policy(value, effective_policy)
            && !allows_special_lookup_access_base
        {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        }
        if count_binding_uses_in_stmts(&old_stmts[(index + 1)..], candidate.binding()) != 1 {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        }

        let mut rewritten_next = next_stmt.clone();
        let mut rewrite_policy = effective_policy;
        if !rewrite_stmt_use_sites_with_policy(
            &mut rewritten_next,
            candidate,
            value,
            options,
            rewrite_policy,
        ) {
            if matches!(policy, InlinePolicy::AliasInitializerChain)
                && candidate::is_recallable_inline_expr(value)
                && stmt_has_direct_call_arg_binding_use(next_stmt, candidate.binding())
            {
                rewritten_next = next_stmt.clone();
                rewrite_policy = InlinePolicy::ExtendedCallChain;
                if !rewrite_stmt_use_sites_with_policy(
                    &mut rewritten_next,
                    candidate,
                    value,
                    options,
                    rewrite_policy,
                ) {
                    new_stmts.push(old_stmts[index].clone());
                    index += 1;
                    continue;
                }
            } else {
                new_stmts.push(old_stmts[index].clone());
                index += 1;
                continue;
            }
        }

        new_stmts.push(rewritten_next);
        changed = true;
        index += 2;
    }

    block.stmts = new_stmts;
    changed |= collapse_adjacent_call_alias_runs(block, options);
    changed |= collapse_terminal_local_mechanical_runs(block, options);
    changed |= collapse_adjacent_mechanical_alias_runs(block, options);
    changed
}

fn collapse_adjacent_call_alias_runs(block: &mut AstBlock, options: ReadabilityOptions) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while index < old_stmts.len() {
        let mut run_end = index;
        while run_end < old_stmts.len() && inline_candidate(&old_stmts[run_end]).is_some() {
            run_end += 1;
        }

        if run_end == index
            || run_end >= old_stmts.len()
            || !matches!(old_stmts[run_end], AstStmt::CallStmt(_))
        {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        }

        let mut rewritten_sink = old_stmts[run_end].clone();
        let mut removed = vec![false; run_end - index];
        let mut collapsed_count = 0usize;

        for candidate_index in (index..run_end).rev() {
            let Some((candidate, value)) = inline_candidate(&old_stmts[candidate_index]) else {
                continue;
            };
            if !matches!(candidate, candidate::InlineCandidate::LocalAlias { .. }) {
                continue;
            }
            if count_binding_uses_in_stmts(
                &old_stmts[(candidate_index + 1)..(run_end + 1)],
                candidate.binding(),
            ) != 1
            {
                continue;
            }
            let intermediate_uses = if candidate::is_lookup_inline_expr(value) {
                count_binding_uses_in_remaining_run(
                    &old_stmts[(candidate_index + 1)..run_end],
                    &removed[(candidate_index + 1 - index)..],
                    candidate.binding(),
                )
            } else {
                count_binding_uses_in_stmts(
                    &old_stmts[(candidate_index + 1)..run_end],
                    candidate.binding(),
                )
            };
            if intermediate_uses != 0 {
                continue;
            }

            let mut trial_sink = rewritten_sink.clone();
            if rewrite_stmt_use_sites_with_policy(
                &mut trial_sink,
                candidate,
                value,
                options,
                InlinePolicy::ExtendedCallChain,
            ) {
                rewritten_sink = trial_sink;
                removed[candidate_index - index] = true;
                collapsed_count += 1;
            }
        }

        // 这里只折叠真正的“局部别名包”：
        // 至少一次收回两层相邻别名，才能证明我们是在还原机械展开的调用准备序列，
        // 而不是把源码里本来就有阶段语义的 local（例如 stage1 / stage2）继续吞掉。
        if collapsed_count >= 2 {
            changed = true;
            for (offset, stmt) in old_stmts[index..run_end].iter().enumerate() {
                if !removed[offset] {
                    new_stmts.push(stmt.clone());
                }
            }
            new_stmts.push(rewritten_sink);
            index = run_end + 1;
            continue;
        }

        new_stmts.push(old_stmts[index].clone());
        index += 1;
    }

    block.stmts = new_stmts;
    changed
}

fn collapse_adjacent_mechanical_alias_runs(
    block: &mut AstBlock,
    options: ReadabilityOptions,
) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while index < old_stmts.len() {
        let mut run_end = index;
        while run_end < old_stmts.len() && inline_candidate(&old_stmts[run_end]).is_some() {
            run_end += 1;
        }

        if run_end == index
            || run_end >= old_stmts.len()
            || !stmt_can_absorb_mechanical_run(&old_stmts[run_end])
        {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        }

        let mut rewritten_sink = old_stmts[run_end].clone();
        let mut removed = vec![false; run_end - index];
        let mut collapsed_count = 0usize;
        let mut has_non_lookup_piece = false;
        let mut has_dependent_lookup_piece = false;

        for candidate_index in (index..run_end).rev() {
            let Some((candidate, value)) = inline_candidate(&old_stmts[candidate_index]) else {
                continue;
            };
            if !candidate.allows_expr_with_policy(value, InlinePolicy::MechanicalRun) {
                continue;
            }
            if count_binding_uses_in_stmts(
                &old_stmts[(candidate_index + 1)..(run_end + 1)],
                candidate.binding(),
            ) != 1
            {
                continue;
            }
            if count_binding_uses_in_stmts(&old_stmts[(run_end + 1)..], candidate.binding()) != 0 {
                continue;
            }
            if count_binding_uses_in_remaining_run(
                &old_stmts[(candidate_index + 1)..run_end],
                &removed[(candidate_index + 1 - index)..],
                candidate.binding(),
            ) != 0
            {
                continue;
            }
            if !stmt_has_nested_binding_use(&rewritten_sink, candidate.binding()) {
                continue;
            }

            let mut trial_sink = rewritten_sink.clone();
            if rewrite_stmt_use_sites_with_policy(
                &mut trial_sink,
                candidate,
                value,
                options,
                InlinePolicy::MechanicalRun,
            ) {
                rewritten_sink = trial_sink;
                removed[candidate_index - index] = true;
                collapsed_count += 1;
                has_non_lookup_piece |= !candidate::is_lookup_inline_expr(value);
                has_dependent_lookup_piece |= candidate::is_lookup_inline_expr(value)
                    && expr_references_any_run_binding(
                        value,
                        &old_stmts[index..run_end],
                        candidate.binding(),
                    );
            }
        }

        if collapsed_count >= 2
            && (has_non_lookup_piece
                || stmt_prefers_pure_lookup_run_collapse(&rewritten_sink)
                || (has_dependent_lookup_piece
                    && stmt_prefers_dependent_lookup_run_collapse(&rewritten_sink)))
        {
            changed = true;
            for (offset, stmt) in old_stmts[index..run_end].iter().enumerate() {
                if !removed[offset] {
                    new_stmts.push(stmt.clone());
                }
            }
            new_stmts.push(rewritten_sink);
            index = run_end + 1;
            continue;
        }

        new_stmts.push(old_stmts[index].clone());
        index += 1;
    }

    block.stmts = new_stmts;
    changed
}

fn collapse_terminal_local_mechanical_runs(
    block: &mut AstBlock,
    options: ReadabilityOptions,
) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while index < old_stmts.len() {
        let mut run_end = index;
        while run_end < old_stmts.len() && inline_candidate(&old_stmts[run_end]).is_some() {
            run_end += 1;
        }

        if run_end <= index + 1 || run_end >= old_stmts.len() {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        }

        let Some((sink_candidate, _)) = inline_candidate(&old_stmts[run_end - 1]) else {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        };
        // 这里只处理“run 末尾这个 local 自己还会跨语句活下去”的情况：
        // 前面的 recovered local 只是为了把最终表达式拆成多个机械阶段，
        // 但末尾这个 binding 仍然是后续语句要继续引用的源码锚点。
        if !matches!(
            sink_candidate,
            candidate::InlineCandidate::LocalAlias { .. }
        ) || count_binding_uses_in_stmts(&old_stmts[run_end..], sink_candidate.binding()) == 0
        {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        }

        let mut rewritten_sink = old_stmts[run_end - 1].clone();
        let mut removed = vec![false; run_end - index - 1];
        let mut collapsed_count = 0usize;

        for candidate_index in (index..(run_end - 1)).rev() {
            let Some((candidate, value)) = inline_candidate(&old_stmts[candidate_index]) else {
                continue;
            };
            if !candidate.allows_expr_with_policy(value, InlinePolicy::MechanicalRun) {
                continue;
            }
            if count_binding_uses_in_stmts(&old_stmts[(candidate_index + 1)..], candidate.binding())
                != 1
            {
                continue;
            }
            if count_binding_uses_in_stmts(&old_stmts[run_end..], candidate.binding()) != 0 {
                continue;
            }
            if count_binding_uses_in_remaining_run(
                &old_stmts[(candidate_index + 1)..(run_end - 1)],
                &removed[(candidate_index + 1 - index)..],
                candidate.binding(),
            ) != 0
            {
                continue;
            }
            if !stmt_has_nested_binding_use(&rewritten_sink, candidate.binding()) {
                continue;
            }

            let mut trial_sink = rewritten_sink.clone();
            if rewrite_stmt_use_sites_with_policy(
                &mut trial_sink,
                candidate,
                value,
                options,
                InlinePolicy::MechanicalRun,
            ) {
                rewritten_sink = trial_sink;
                removed[candidate_index - index] = true;
                collapsed_count += 1;
            }
        }

        if collapsed_count >= 2 {
            changed = true;
            for (offset, stmt) in old_stmts[index..(run_end - 1)].iter().enumerate() {
                if !removed[offset] {
                    new_stmts.push(stmt.clone());
                }
            }
            new_stmts.push(rewritten_sink);
            index = run_end;
            continue;
        }

        new_stmts.push(old_stmts[index].clone());
        index += 1;
    }

    block.stmts = new_stmts;
    changed
}

fn stmt_can_absorb_mechanical_run(stmt: &AstStmt) -> bool {
    matches!(
        stmt,
        AstStmt::Assign(_)
            | AstStmt::CallStmt(_)
            | AstStmt::Return(_)
            | AstStmt::If(_)
            | AstStmt::While(_)
            | AstStmt::Repeat(_)
            | AstStmt::NumericFor(_)
            | AstStmt::GenericFor(_)
    )
}

fn stmt_prefers_pure_lookup_run_collapse(stmt: &AstStmt) -> bool {
    matches!(
        stmt,
        // 纯 lookup bag 如果只是为了拼一个复合左值（例如 `tbl[tbl.n] = ...`），
        // 保留中间 local 只会把“地址计算”拆成多行机械脚手架；这里允许把它们收回赋值本身。
        AstStmt::Assign(assign)
            if assign
                .targets
                .iter()
                .any(|target| !matches!(target, super::super::common::AstLValue::Name(_)))
    )
}

fn stmt_prefers_dependent_lookup_run_collapse(stmt: &AstStmt) -> bool {
    matches!(stmt, AstStmt::Assign(_))
}

fn stmt_starts_lookup_mechanical_run(
    stmts: &[AstStmt],
    index: usize,
    binding: AstBindingRef,
) -> bool {
    let mut run_end = index;
    while run_end < stmts.len() && inline_candidate(&stmts[run_end]).is_some() {
        run_end += 1;
    }

    run_end > index + 1
        && run_end < stmts.len()
        && stmt_can_absorb_mechanical_run(&stmts[run_end])
        && stmts
            .get(index + 1)
            .and_then(inline_candidate)
            .is_some_and(|(_, next_value)| {
                candidate::is_lookup_inline_expr(next_value)
                    && expr_references_binding(next_value, binding)
            })
}

fn expr_references_any_run_binding(
    expr: &super::super::common::AstExpr,
    run: &[AstStmt],
    except: AstBindingRef,
) -> bool {
    run.iter().any(|stmt| {
        inline_candidate(stmt).is_some_and(|(candidate, _)| {
            let binding = candidate.binding();
            binding != except && expr_references_binding(expr, binding)
        })
    })
}

fn count_binding_uses_in_remaining_run(
    stmts: &[AstStmt],
    removed: &[bool],
    binding: AstBindingRef,
) -> usize {
    stmts
        .iter()
        .zip(removed.iter())
        .filter(|(_, removed)| !**removed)
        .map(|(stmt, _)| count_binding_uses_in_stmt(stmt, binding))
        .sum()
}

#[cfg(test)]
mod tests;
