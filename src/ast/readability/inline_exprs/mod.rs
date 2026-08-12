//! 受阈值约束的保守表达式内联。
//!
//! 这里只处理非常窄的一类模式：
//! - 单值 local 别名；原生 temp 的语义内联归 HIR
//! - 后续只使用一次
//! - 使用点出现在 return / 调用参数 / 索引位 / 调用目标
//! - 被内联表达式必须是我们能证明“纯且无元方法副作用”的安全子集
//! - 相邻调用准备 run 中的简单表构造参数，可以随同 receiver/callee 一起收回调用位
//! - 相邻 recovered local run 里，只有末尾 local 仍会跨语句存活的机械链
//! - generic-for 的 method receiver 允许收回一个紧邻的 recovered binding 别名

mod candidate;
mod eval_order;
mod use_sites;

use std::collections::BTreeMap;

use crate::ast::ReadabilityOptions;

use self::candidate::{
    InlineCandidate, InlinePolicy, inline_candidate, stmt_is_adjacent_call_result_sink,
    stmt_is_alias_initializer_sink, stmt_is_direct_return_value_sink,
};
use self::use_sites::rewrite_stmt_use_sites_with_policy;
use super::super::common::{
    AstBindingRef, AstBlock, AstExpr, AstFunctionExpr, AstFunctionName, AstLValue, AstModule,
    AstNameRef, AstStmt,
};
use super::ReadabilityContext;
use super::binding_flow::{
    BindingUseIndex, MutableSnapshotNames, binding_mentions_in_expr,
    mutable_snapshot_names_in_block,
};
use super::binding_ref::binding_from_name_ref;
use super::binding_tree::{
    expr_references_binding, stmt_has_access_base_binding_use, stmt_has_call_callee_binding_use,
    stmt_has_direct_call_arg_binding_use, stmt_has_index_binding_use, stmt_has_nested_binding_use,
    stmt_has_nested_binding_value_use,
};
use super::stmt_plan::{PlannedStmt, materialize_stmt_plan};
use super::visit::AstVisitor;
use super::walk::{self, AstRewritePass, BlockKind};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let _ = context.target;
    let root_mutable_snapshots = mutable_snapshot_names_in_block(&module.body);
    walk::rewrite_module(
        module,
        &mut InlineExprsPass {
            options: context.options,
            mutable_snapshot_stack: vec![root_mutable_snapshots],
        },
    )
}

struct InlineExprsPass {
    options: ReadabilityOptions,
    mutable_snapshot_stack: Vec<MutableSnapshotNames>,
}

#[derive(Default)]
struct BindingWriteIndex {
    last_write_by_binding: BTreeMap<AstBindingRef, usize>,
}

impl BindingWriteIndex {
    fn for_stmts(stmts: &[AstStmt]) -> Self {
        let mut index = Self::default();
        for (stmt_index, stmt) in stmts.iter().enumerate() {
            let mut collector = BindingWriteCollector {
                stmt_index,
                index: &mut index,
            };
            super::visit::visit_stmt(stmt, &mut collector);
        }
        index
    }

    fn record(&mut self, stmt_index: usize, binding: AstBindingRef) {
        self.last_write_by_binding.insert(binding, stmt_index);
    }

    fn has_write_after(&self, stmt_index: usize, binding: AstBindingRef) -> bool {
        self.last_write_by_binding
            .get(&binding)
            .is_some_and(|last_write| *last_write > stmt_index)
    }
}

fn removable_inline_candidate<'a>(
    stmts: &'a [AstStmt],
    stmt_index: usize,
    write_index: &BindingWriteIndex,
) -> Option<(InlineCandidate, &'a AstExpr)> {
    let (candidate, value) = inline_candidate(stmts.get(stmt_index)?)?;
    (!write_index.has_write_after(stmt_index, candidate.binding())).then_some((candidate, value))
}

struct BindingWriteCollector<'a> {
    stmt_index: usize,
    index: &'a mut BindingWriteIndex,
}

impl AstVisitor for BindingWriteCollector<'_> {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        let AstStmt::FunctionDecl(function) = stmt else {
            return;
        };
        let AstFunctionName::Plain(path) = &function.target else {
            return;
        };
        if path.fields.is_empty()
            && let Some(binding) = binding_from_name_ref(&path.root)
        {
            self.index.record(self.stmt_index, binding);
        }
    }

    fn visit_lvalue(&mut self, lvalue: &AstLValue) {
        let AstLValue::Name(name) = lvalue else {
            return;
        };
        if let Some(binding) = binding_from_name_ref(name) {
            self.index.record(self.stmt_index, binding);
        }
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        false
    }
}

impl AstRewritePass for InlineExprsPass {
    fn enter_function(&mut self, function: &AstFunctionExpr) {
        self.mutable_snapshot_stack
            .push(mutable_snapshot_names_in_block(&function.body));
    }

    fn leave_function(&mut self, _function: &AstFunctionExpr) {
        self.mutable_snapshot_stack.pop();
    }

    fn rewrite_block(&mut self, block: &mut AstBlock, _kind: BlockKind) -> bool {
        rewrite_current_block(
            block,
            self.options,
            self.mutable_snapshot_stack
                .last()
                .expect("module scope must remain active"),
        )
    }
}

fn rewrite_current_block(
    block: &mut AstBlock,
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
) -> bool {
    let mut changed = false;

    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts(&old_stmts);
    let write_index = BindingWriteIndex::for_stmts(&old_stmts);
    let mut stmt_plan = Vec::with_capacity(old_stmts.len());
    let mut index = 0;
    while index < old_stmts.len() {
        let Some(next_stmt) = old_stmts.get(index + 1) else {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        };

        let Some((candidate, value)) = removable_inline_candidate(&old_stmts, index, &write_index)
        else {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        };
        let policy = if stmt_is_alias_initializer_sink(next_stmt) {
            InlinePolicy::AliasInitializerChain
        } else if stmt_is_adjacent_call_result_sink(next_stmt) {
            InlinePolicy::AdjacentCallResultCallee
        } else if stmt_is_direct_return_value_sink(next_stmt) {
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
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        let is_recovered = candidate.origin() == super::super::common::AstLocalOrigin::Recovered;
        let allows_special_lookup_access_base = is_recovered
            && matches!(policy, InlinePolicy::Conservative)
            && matches!(next_stmt, AstStmt::Assign(_))
            && candidate::is_lookup_inline_expr(value)
            && stmt_has_access_base_binding_use(next_stmt, candidate.binding());
        let allows_special_index_sink = is_recovered
            && matches!(policy, InlinePolicy::Conservative)
            && matches!(next_stmt, AstStmt::Assign(_))
            && super::expr_analysis::is_mechanical_run_inline_expr(value)
            && stmt_has_index_binding_use(next_stmt, candidate.binding());
        let allows_special_adjacent_value_sink = is_recovered
            && matches!(
                policy,
                InlinePolicy::Conservative | InlinePolicy::AliasInitializerChain
            )
            && matches!(next_stmt, AstStmt::Assign(_) | AstStmt::LocalDecl(_))
            && stmt_sink_binding_allows_adjacent_value_inline(&old_stmts, index + 1)
            && ((candidate::is_raw_global_alias_expr(value)
                && stmt_has_direct_call_arg_binding_use(next_stmt, candidate.binding()))
                || (stmt_has_nested_binding_value_use(next_stmt, candidate.binding())
                    && (candidate::is_recallable_inline_expr(value)
                        || (candidate::is_lookup_inline_expr(value)
                            && assign_targets_same_lookup_expr(next_stmt, value)))));
        let effective_policy = if allows_special_index_sink {
            InlinePolicy::MechanicalRun
        } else if allows_special_adjacent_value_sink {
            InlinePolicy::AdjacentValueSink
        } else {
            policy
        };
        if !candidate.allows_expr_with_policy(value, effective_policy)
            && !allows_special_lookup_access_base
        {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        if use_index.count_uses_in_suffix(index + 1, candidate.binding()) != 1 {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        if inline_crosses_evaluation_boundary(
            value,
            next_stmt,
            candidate.binding(),
            mutable_snapshots,
        ) {
            stmt_plan.push(PlannedStmt::Original(index));
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
                    stmt_plan.push(PlannedStmt::Original(index));
                    index += 1;
                    continue;
                }
            } else {
                stmt_plan.push(PlannedStmt::Original(index));
                index += 1;
                continue;
            }
        }

        stmt_plan.push(PlannedStmt::Rewritten(rewritten_next));
        changed = true;
        index += 2;
    }

    block.stmts = materialize_stmt_plan(old_stmts, stmt_plan);
    changed |= collapse_adjacent_call_alias_runs(block, options, mutable_snapshots);
    changed |= collapse_terminal_call_result_alias_runs(block, options, mutable_snapshots);
    changed |= collapse_terminal_local_mechanical_runs(block, options, mutable_snapshots);
    changed |= collapse_adjacent_mechanical_alias_runs(block, options, mutable_snapshots);
    changed
}

fn inline_crosses_evaluation_boundary(
    value: &AstExpr,
    next_stmt: &AstStmt,
    binding: AstBindingRef,
    mutable_snapshots: &MutableSnapshotNames,
) -> bool {
    (matches!(next_stmt, AstStmt::While(_) | AstStmt::Repeat(_))
        && !super::expr_analysis::is_stable_inline_value(value))
        || (super::expr_analysis::expr_requires_ordered_snapshot(value, mutable_snapshots)
            && !eval_order::preserves_adjacent_eval_order(
                next_stmt,
                binding,
                value,
                mutable_snapshots,
            ))
}

fn collapse_adjacent_call_alias_runs(
    block: &mut AstBlock,
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts(&old_stmts);
    let write_index = BindingWriteIndex::for_stmts(&old_stmts);
    let mut stmt_plan = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while index < old_stmts.len() {
        let mut run_end = index;
        while run_end < old_stmts.len() && inline_candidate(&old_stmts[run_end]).is_some() {
            run_end += 1;
        }

        if run_end == index
            || run_end >= old_stmts.len()
            || !stmt_is_terminal_call_alias_sink(&old_stmts[run_end])
        {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        };
        if super::function_sugar::run_belongs_to_method_alias_owner(
            &old_stmts,
            index,
            run_end,
            &use_index,
            mutable_snapshots,
        ) {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }

        let mut rewritten_sink = None;
        let rewrite_policy = if stmt_is_generic_for_call_alias_sink(&old_stmts[run_end]) {
            InlinePolicy::LoopHeaderCall
        } else {
            InlinePolicy::ExtendedCallChain
        };
        let mut removed = vec![false; run_end - index];
        let mut collapsed_count = 0usize;
        let mut remaining_run_uses = BTreeMap::new();

        for candidate_index in (index..run_end).rev() {
            add_next_kept_stmt_uses(
                &use_index,
                candidate_index,
                run_end,
                index,
                &removed,
                &mut remaining_run_uses,
            );
            let Some((candidate, value)) =
                removable_inline_candidate(&old_stmts, candidate_index, &write_index)
            else {
                continue;
            };
            if use_index.count_uses_in_suffix(candidate_index + 1, candidate.binding()) != 1 {
                continue;
            }
            let intermediate_uses = if candidate::is_lookup_inline_expr(value) {
                remaining_run_uses
                    .get(&candidate.binding())
                    .copied()
                    .unwrap_or(0)
            } else {
                use_index.count_uses_in_range(candidate_index + 1, run_end, candidate.binding())
            };
            if intermediate_uses != 0 {
                continue;
            }

            let mut trial_sink = rewritten_sink
                .as_ref()
                .unwrap_or(&old_stmts[run_end])
                .clone();
            if rewrite_stmt_use_sites_with_policy(
                &mut trial_sink,
                candidate,
                value,
                options,
                rewrite_policy,
            ) {
                rewritten_sink = Some(trial_sink);
                removed[candidate_index - index] = true;
                collapsed_count += 1;
            }
        }

        // 常规路径只折叠真正的“局部别名包”，避免吞掉有阶段语义的源码 local。
        // 单项只接受 method fact 已经冻结后的直接 receiver binding；若迭代器仍引用
        // 待物化 temp，则留到下一轮与整个调用准备包一起收回。
        let allows_single_receiver_alias = collapsed_count == 1
            && single_generic_for_method_receiver_alias(&old_stmts, index, run_end);
        if (collapsed_count >= 2 || allows_single_receiver_alias)
            && eval_order::run_preserves_eval_order(
                &old_stmts,
                index,
                run_end,
                &removed,
                mutable_snapshots,
            )
        {
            changed = true;
            plan_collapsed_run(
                &mut stmt_plan,
                index,
                &removed,
                rewritten_sink.expect("collapsed alias run must rewrite its sink"),
            );
            index = run_end + 1;
            continue;
        }

        stmt_plan.push(PlannedStmt::Original(index));
        index += 1;
    }

    block.stmts = materialize_stmt_plan(old_stmts, stmt_plan);
    changed
}

fn stmt_is_generic_for_call_alias_sink(stmt: &AstStmt) -> bool {
    matches!(
        stmt,
        AstStmt::GenericFor(generic_for)
            if matches!(
                generic_for.iterator.as_slice(),
                [AstExpr::Call(_) | AstExpr::MethodCall(_)]
            )
    )
}

fn single_generic_for_method_receiver_alias(
    stmts: &[AstStmt],
    run_start: usize,
    sink_index: usize,
) -> bool {
    let Some((candidate, AstExpr::Var(source))) = (sink_index == run_start + 1)
        .then(|| inline_candidate(&stmts[run_start]))
        .flatten()
    else {
        return false;
    };
    let AstStmt::GenericFor(generic_for) = &stmts[sink_index] else {
        return false;
    };
    let [AstExpr::MethodCall(call)] = generic_for.iterator.as_slice() else {
        return false;
    };
    let AstExpr::Var(receiver) = &call.receiver else {
        return false;
    };
    candidate.origin() == super::super::common::AstLocalOrigin::Recovered
        && !matches!(source, AstNameRef::Global(_) | AstNameRef::Temp(_))
        && candidate.binding().matches_name_ref(receiver)
        && !binding_mentions_in_expr(&generic_for.iterator[0])
            .iter()
            .any(|binding| matches!(binding, AstBindingRef::Temp(_)))
}

fn stmt_is_terminal_call_alias_sink(stmt: &AstStmt) -> bool {
    match stmt {
        AstStmt::CallStmt(_) => true,
        // generic-for 的 iterator 表达式也是调用准备 run 的自然终点：
        // `local iter = ipairs; local items = {...}; for k, v in iter(items) do`
        // 应恢复成 `for k, v in ipairs({...}) do`。这里只接受单个 iterator call，
        // 避免把多表达式 iterator list 里的阶段 local 误吞掉。
        AstStmt::GenericFor(_) => stmt_is_generic_for_call_alias_sink(stmt),
        // `return f(...)` 在字节码里也常由同一段调用准备 run 供给 callee/args。
        // 这里只接单个返回值，避免把别名内联进 `return a(), f(x)` 这类多返回式时
        // 改变 alias 求值相对前置返回值的顺序。
        AstStmt::Return(ret) => matches!(
            ret.values.as_slice(),
            [super::super::common::AstExpr::Call(_)]
        ),
        _ => false,
    }
}

fn collapse_terminal_call_result_alias_runs(
    block: &mut AstBlock,
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts(&old_stmts);
    let write_index = BindingWriteIndex::for_stmts(&old_stmts);
    let mut stmt_plan = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while index < old_stmts.len() {
        let Some(sink_index) = find_terminal_call_result_sink(&old_stmts, index) else {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        };
        if super::function_sugar::run_belongs_to_method_alias_owner(
            &old_stmts,
            index,
            sink_index,
            &use_index,
            mutable_snapshots,
        ) {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }

        let mut rewritten_sink = None;
        let mut removed = vec![false; sink_index - index];
        let mut collapsed_count = 0usize;
        let mut remaining_run_uses = BTreeMap::new();

        for candidate_index in (index..sink_index).rev() {
            add_next_kept_stmt_uses(
                &use_index,
                candidate_index,
                sink_index,
                index,
                &removed,
                &mut remaining_run_uses,
            );
            let Some((candidate, value)) =
                removable_inline_candidate(&old_stmts, candidate_index, &write_index)
            else {
                continue;
            };
            if use_index.count_uses_in_suffix(candidate_index + 1, candidate.binding()) != 1 {
                continue;
            }
            let intermediate_uses = if candidate::is_lookup_inline_expr(value) {
                remaining_run_uses
                    .get(&candidate.binding())
                    .copied()
                    .unwrap_or(0)
            } else {
                use_index.count_uses_in_range(candidate_index + 1, sink_index, candidate.binding())
            };
            let current_sink = rewritten_sink.as_ref().unwrap_or(&old_stmts[sink_index]);
            if intermediate_uses != 0
                || !stmt_has_nested_binding_use(current_sink, candidate.binding())
            {
                continue;
            }

            let mut trial_sink = current_sink.clone();
            if rewrite_stmt_use_sites_with_policy(
                &mut trial_sink,
                candidate,
                value,
                options,
                InlinePolicy::ExtendedCallChain,
            ) {
                rewritten_sink = Some(trial_sink);
                removed[candidate_index - index] = true;
                collapsed_count += 1;
            }
        }

        // 这里专门处理“调用准备 run 的终点自己还是一个 local/assign”：
        // `local f = obj.m; local x = f(arg)`、`local a = t[i]; local v = call(a, ...)`
        // 这类形状和最终 `call_stmt(...)` 属于同一 owner，只是 sink 还保留在结果声明里。
        if collapsed_count >= 2
            && eval_order::run_preserves_eval_order(
                &old_stmts,
                index,
                sink_index,
                &removed,
                mutable_snapshots,
            )
        {
            changed = true;
            plan_collapsed_run(
                &mut stmt_plan,
                index,
                &removed,
                rewritten_sink.expect("collapsed call-result run must rewrite its sink"),
            );
            index = sink_index + 1;
            continue;
        }

        stmt_plan.push(PlannedStmt::Original(index));
        index += 1;
    }

    block.stmts = materialize_stmt_plan(old_stmts, stmt_plan);
    changed
}

fn find_terminal_call_result_sink(stmts: &[AstStmt], index: usize) -> Option<usize> {
    inline_candidate(stmts.get(index)?)?;

    let mut sink_index = index + 1;
    while sink_index < stmts.len() && inline_candidate(&stmts[sink_index]).is_some() {
        if stmt_is_adjacent_call_result_sink(&stmts[sink_index]) {
            return Some(sink_index);
        }
        sink_index += 1;
    }

    None
}

fn stmt_sink_binding_allows_adjacent_value_inline(stmts: &[AstStmt], sink_index: usize) -> bool {
    let Some(stmt) = stmts.get(sink_index) else {
        return false;
    };
    if matches!(stmt, AstStmt::Assign(_)) {
        return true;
    }
    let Some((sink_candidate, _)) = inline_candidate(stmt) else {
        return false;
    };
    !stmts[(sink_index + 1)..]
        .iter()
        .any(|stmt| stmt_has_call_callee_binding_use(stmt, sink_candidate.binding()))
}

fn collapse_adjacent_mechanical_alias_runs(
    block: &mut AstBlock,
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts(&old_stmts);
    let write_index = BindingWriteIndex::for_stmts(&old_stmts);
    let mut stmt_plan = Vec::with_capacity(old_stmts.len());
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
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }

        let mut rewritten_sink = None;
        let mut removed = vec![false; run_end - index];
        let mut collapsed_count = 0usize;
        let mut has_non_lookup_piece = false;
        let mut has_dependent_lookup_piece = false;
        let mut remaining_run_uses = BTreeMap::new();

        for candidate_index in (index..run_end).rev() {
            add_next_kept_stmt_uses(
                &use_index,
                candidate_index,
                run_end,
                index,
                &removed,
                &mut remaining_run_uses,
            );
            let Some((candidate, value)) =
                removable_inline_candidate(&old_stmts, candidate_index, &write_index)
            else {
                continue;
            };
            if !candidate.allows_expr_with_policy(value, InlinePolicy::MechanicalRun) {
                continue;
            }
            if use_index.count_uses_in_range(candidate_index + 1, run_end + 1, candidate.binding())
                != 1
            {
                continue;
            }
            if use_index.count_uses_in_suffix(run_end + 1, candidate.binding()) != 0 {
                continue;
            }
            if remaining_run_uses
                .get(&candidate.binding())
                .is_some_and(|count| *count != 0)
            {
                continue;
            }
            let current_sink = rewritten_sink.as_ref().unwrap_or(&old_stmts[run_end]);
            if !stmt_has_mechanical_run_sink_binding_use(current_sink, candidate.binding()) {
                continue;
            }

            let mut trial_sink = current_sink.clone();
            if rewrite_stmt_use_sites_with_policy(
                &mut trial_sink,
                candidate,
                value,
                options,
                InlinePolicy::MechanicalRun,
            ) {
                rewritten_sink = Some(trial_sink);
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

        if rewritten_sink.as_ref().is_some_and(|rewritten_sink| {
            collapsed_count >= 2
                && (has_non_lookup_piece
                    || stmt_prefers_pure_lookup_run_collapse(rewritten_sink)
                    || (has_dependent_lookup_piece
                        && stmt_prefers_dependent_lookup_run_collapse(rewritten_sink)))
                && eval_order::run_preserves_eval_order(
                    &old_stmts,
                    index,
                    run_end,
                    &removed,
                    mutable_snapshots,
                )
        }) {
            changed = true;
            plan_collapsed_run(
                &mut stmt_plan,
                index,
                &removed,
                rewritten_sink.expect("collapsed mechanical run must rewrite its sink"),
            );
            index = run_end + 1;
            continue;
        }

        stmt_plan.push(PlannedStmt::Original(index));
        index += 1;
    }

    block.stmts = materialize_stmt_plan(old_stmts, stmt_plan);
    changed
}

fn collapse_terminal_local_mechanical_runs(
    block: &mut AstBlock,
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts(&old_stmts);
    let write_index = BindingWriteIndex::for_stmts(&old_stmts);
    let mut stmt_plan = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while index < old_stmts.len() {
        let mut run_end = index;
        while run_end < old_stmts.len() && inline_candidate(&old_stmts[run_end]).is_some() {
            run_end += 1;
        }

        if run_end <= index + 1 || run_end >= old_stmts.len() {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }

        let Some((sink_candidate, _)) = inline_candidate(&old_stmts[run_end - 1]) else {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        };
        // 这里只处理“run 末尾这个 local 自己还会跨语句活下去”的情况：
        // 前面的 recovered local 只是为了把最终表达式拆成多个机械阶段，
        // 但末尾这个 binding 仍然是后续语句要继续引用的源码锚点。
        if use_index.count_uses_in_suffix(run_end, sink_candidate.binding()) == 0 {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }

        let mut rewritten_sink = None;
        let mut removed = vec![false; run_end - index - 1];
        let mut collapsed_count = 0usize;
        let mut remaining_run_uses = BTreeMap::new();

        for candidate_index in (index..(run_end - 1)).rev() {
            add_next_kept_stmt_uses(
                &use_index,
                candidate_index,
                run_end - 1,
                index,
                &removed,
                &mut remaining_run_uses,
            );
            let Some((candidate, value)) =
                removable_inline_candidate(&old_stmts, candidate_index, &write_index)
            else {
                continue;
            };
            if !candidate.allows_expr_with_policy(value, InlinePolicy::MechanicalRun) {
                continue;
            }
            if use_index.count_uses_in_suffix(candidate_index + 1, candidate.binding()) != 1 {
                continue;
            }
            if use_index.count_uses_in_suffix(run_end, candidate.binding()) != 0 {
                continue;
            }
            if remaining_run_uses
                .get(&candidate.binding())
                .is_some_and(|count| *count != 0)
            {
                continue;
            }
            let current_sink = rewritten_sink.as_ref().unwrap_or(&old_stmts[run_end - 1]);
            if !stmt_has_nested_binding_use(current_sink, candidate.binding()) {
                continue;
            }

            let mut trial_sink = current_sink.clone();
            if rewrite_stmt_use_sites_with_policy(
                &mut trial_sink,
                candidate,
                value,
                options,
                InlinePolicy::MechanicalRun,
            ) {
                rewritten_sink = Some(trial_sink);
                removed[candidate_index - index] = true;
                collapsed_count += 1;
            }
        }

        if collapsed_count >= 2
            && eval_order::run_preserves_eval_order(
                &old_stmts,
                index,
                run_end - 1,
                &removed,
                mutable_snapshots,
            )
        {
            changed = true;
            plan_collapsed_run(
                &mut stmt_plan,
                index,
                &removed,
                rewritten_sink.expect("collapsed terminal-local run must rewrite its sink"),
            );
            index = run_end;
            continue;
        }

        stmt_plan.push(PlannedStmt::Original(index));
        index += 1;
    }

    block.stmts = materialize_stmt_plan(old_stmts, stmt_plan);
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

fn plan_collapsed_run(
    stmt_plan: &mut Vec<PlannedStmt>,
    run_start: usize,
    removed: &[bool],
    rewritten_sink: AstStmt,
) {
    for (offset, removed) in removed.iter().enumerate() {
        if !removed {
            stmt_plan.push(PlannedStmt::Original(run_start + offset));
        }
    }
    stmt_plan.push(PlannedStmt::Rewritten(rewritten_sink));
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
    ) || matches!(
        stmt,
        // generic-for 的迭代器位天然就是机械准备 run 的消费点：
        // `local f = _G.ipairs; local t = obj.items; for k, v in f(t) do`
        // 保留这些 lookup local 只会把迭代器表达式拆散。
        AstStmt::GenericFor(_)
    )
}

fn stmt_has_mechanical_run_sink_binding_use(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    stmt_has_nested_binding_use(stmt, binding)
        || stmt_has_access_base_binding_use(stmt, binding)
        || stmt_has_call_callee_binding_use(stmt, binding)
        || stmt_has_direct_call_arg_binding_use(stmt, binding)
        || stmt_has_index_binding_use(stmt, binding)
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

fn assign_targets_same_lookup_expr(stmt: &AstStmt, expr: &super::super::common::AstExpr) -> bool {
    let AstStmt::Assign(assign) = stmt else {
        return false;
    };
    assign
        .targets
        .iter()
        .any(|target| lvalue_matches_lookup_expr(target, expr))
}

fn lvalue_matches_lookup_expr(
    target: &super::super::common::AstLValue,
    expr: &super::super::common::AstExpr,
) -> bool {
    match (target, expr) {
        (
            super::super::common::AstLValue::FieldAccess(lhs),
            super::super::common::AstExpr::FieldAccess(rhs),
        ) => lhs.field == rhs.field && lhs.base == rhs.base,
        (
            super::super::common::AstLValue::IndexAccess(lhs),
            super::super::common::AstExpr::IndexAccess(rhs),
        ) => lhs.base == rhs.base && lhs.index == rhs.index,
        _ => false,
    }
}

fn add_next_kept_stmt_uses(
    use_index: &BindingUseIndex,
    candidate_index: usize,
    run_end: usize,
    run_start: usize,
    removed: &[bool],
    remaining_uses: &mut BTreeMap<AstBindingRef, usize>,
) {
    let next_index = candidate_index + 1;
    if next_index >= run_end || removed[next_index - run_start] {
        return;
    }
    for (binding, count) in use_index.uses_in_stmt_index(next_index) {
        *remaining_uses.entry(binding).or_default() += count;
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::common::{
        AstAssign, AstCallExpr, AstCallKind, AstCallStmt, AstGlobalName, AstLocalAttr,
        AstLocalBinding, AstLocalDecl, AstLocalOrigin, AstNameRef,
    };
    use crate::hir::LocalId;

    use super::*;

    #[test]
    fn keeps_local_declaration_before_later_direct_write() {
        let binding = AstBindingRef::Local(LocalId(0));
        let global = |text: &str| {
            AstExpr::Var(AstNameRef::Global(AstGlobalName {
                text: text.to_owned(),
            }))
        };
        let mut block = AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: binding,
                        attr: AstLocalAttr::None,
                        origin: AstLocalOrigin::Recovered,
                    }],
                    values: vec![global("factory")],
                })),
                AstStmt::CallStmt(Box::new(AstCallStmt {
                    call: AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(binding.to_name_ref()),
                        args: Vec::new(),
                    })),
                })),
                AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::Name(binding.to_name_ref())],
                    values: vec![global("replacement")],
                })),
            ],
        };
        let expected = block.clone();

        assert!(!rewrite_current_block(
            &mut block,
            ReadabilityOptions::default(),
            &MutableSnapshotNames::new(),
        ));
        assert_eq!(block, expected);
    }
}
