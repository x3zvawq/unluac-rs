//! 折叠相邻调用、lookup 与机械 local run；依赖父模块的 candidate/use/eval-order 合同，不负责单次 alias inline；例如把 recovered callee/receiver 链收回调用或赋值 sink。

use super::*;

/// 把非 debug call-result local 的紧邻自调用更新收回初始化式。
///
/// `local x = first(); x = x:next()` 的两次 call 原本就在同一条无条件求值链上；
/// 第二句只读一次 `x` 时，第一段结果在原程序中由 local、在折叠后由 receiver/callee
/// 求值槽持有，求值顺序、单值宽度与 GC root 都不变。binding 本身仍由 local 声明，
/// 因而这里只消除机械更新，不做 binding 身份收敛。
pub(super) fn collapse_adjacent_self_call_updates(
    block: &mut AstBlock,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&old_stmts, trailing_condition);
    let mut stmt_plan = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while index < old_stmts.len() {
        let AstStmt::LocalDecl(local_decl) = &old_stmts[index] else {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        };
        let ([binding], [initial]) = (local_decl.bindings.as_slice(), local_decl.values.as_slice())
        else {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        };
        if binding.attr == AstLocalAttr::Close {
            // 候选拒绝[SemanticBarrier:Lifetime]：吞掉 `<close>` binding 会删除退出作用域时的关闭动作。
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        if binding.attr == AstLocalAttr::Const || binding.origin == AstLocalOrigin::DebugHinted {
            // 候选拒绝[PolicyBoundary]：`<const>` 与 DebugHinted 的源码声明身份按保真策略保留。
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        if use_index.count_uses_in_range(index, index + 1, binding.id) != 0 {
            // 候选拒绝[SemanticBarrier:Scope]：initializer 自引用时 `local x = x()` 的 `x` 解析到外层；折叠后续更新会改变该绑定。
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        if !matches!(initial, AstExpr::Call(_) | AstExpr::MethodCall(_)) {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }

        let mut value = initial.clone();
        let mut run_end = index + 1;
        while use_index.count_uses_in_range(run_end, run_end + 1, binding.id) == 1
            && let Some(next) = old_stmts.get(run_end)
            && let Some(rewritten) = self_call_update_value(next, binding.id, &value)
        {
            value = rewritten;
            run_end += 1;
        }
        if run_end == index + 1 {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }

        let mut rewritten = (**local_decl).clone();
        rewritten.values[0] = value;
        stmt_plan.push(PlannedStmt::Rewritten(AstStmt::LocalDecl(Box::new(
            rewritten,
        ))));
        changed = true;
        index = run_end;
    }

    block.stmts = materialize_stmt_plan(old_stmts, stmt_plan);
    changed
}

fn self_call_update_value(
    stmt: &AstStmt,
    binding: AstBindingRef,
    receiver: &AstExpr,
) -> Option<AstExpr> {
    let AstStmt::Assign(assign) = stmt else {
        return None;
    };
    let ([AstLValue::Name(target)], [value]) =
        (assign.targets.as_slice(), assign.values.as_slice())
    else {
        return None;
    };
    if !binding.matches_name_ref(target) {
        return None;
    }

    match value {
        AstExpr::Call(call) if matches!(&call.callee, AstExpr::Var(name) if binding.matches_name_ref(name)) =>
        {
            let mut call = (**call).clone();
            call.callee = receiver.clone();
            Some(AstExpr::Call(Box::new(call)))
        }
        AstExpr::MethodCall(call) if matches!(&call.receiver, AstExpr::Var(name) if binding.matches_name_ref(name)) =>
        {
            let mut call = (**call).clone();
            call.receiver = receiver.clone();
            Some(AstExpr::MethodCall(Box::new(call)))
        }
        _ => None,
    }
}

pub(super) fn collapse_adjacent_call_alias_runs(
    block: &mut AstBlock,
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&old_stmts, trailing_condition);
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
        if super::super::function_sugar::run_belongs_to_method_alias_owner(
            &old_stmts,
            index,
            run_end,
            &use_index,
            mutable_snapshots,
        ) {
            // 候选拒绝[LayerBoundary]：完整 method receiver/field/call run 由 function-sugar 原子消费，不能先删除其中 alias。
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
            let suffix_uses =
                use_index.count_uses_in_suffix(candidate_index + 1, candidate.binding());
            if suffix_uses == 0 {
                // 候选拒绝[LayerBoundary]：零 use 的声明归 cleanup/dead-local，不属于 run inline。
                continue;
            }
            if suffix_uses > 1 {
                // 候选拒绝[SemanticBarrier:EvalCount]：alias 多次使用会复制 lookup/call producer。
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
                // 候选拒绝[SemanticBarrier:EvalOrder/Lifetime]：候选在抵达 sink 前已有读取，删除声明会改变快照时点或重复 producer。
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

        // 候选拒绝[PolicyBoundary]：普通 run 至少收回两项（仅 generic-for method receiver 例外）；候选拒绝[SemanticBarrier:EvalOrder]：移动事件必须仍是 sink 的同序前缀。

        stmt_plan.push(PlannedStmt::Original(index));
        index += 1;
    }

    block.stmts = materialize_stmt_plan(old_stmts, stmt_plan);
    changed
}

pub(super) fn stmt_is_generic_for_call_alias_sink(stmt: &AstStmt) -> bool {
    matches!(
        stmt,
        AstStmt::GenericFor(generic_for)
            if matches!(
                generic_for.iterator.as_slice(),
                [AstExpr::Call(_) | AstExpr::MethodCall(_)]
            )
    )
}

pub(super) fn single_generic_for_method_receiver_alias(
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
    // 候选拒绝[LayerBoundary]：Temp 归 HIR；候选拒绝[SemanticBarrier:EvalOrder]：global/source 或非直接 receiver 缺少稳定快照证明，不能走单项例外。
    candidate.origin() == super::super::super::common::AstLocalOrigin::Recovered
        && !matches!(source, AstNameRef::Global(_) | AstNameRef::Temp(_))
        && candidate.binding().matches_name_ref(receiver)
        && !binding_mentions_in_expr(&generic_for.iterator[0])
            .iter()
            .any(|binding| matches!(binding, AstBindingRef::Temp(_)))
}

pub(super) fn stmt_is_terminal_call_alias_sink(stmt: &AstStmt) -> bool {
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
        // 候选拒绝[SemanticBarrier:EvalOrder/ValueArity]：多值 return 的前置值与尾 call 有固定次序/展开协议，当前 run 只证明单个 call 返回位。
        AstStmt::Return(ret) => matches!(
            ret.values.as_slice(),
            [super::super::super::common::AstExpr::Call(_)]
        ),
        _ => false,
    }
}

pub(super) fn collapse_terminal_call_result_alias_runs(
    block: &mut AstBlock,
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&old_stmts, trailing_condition);
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
        if super::super::function_sugar::run_belongs_to_method_alias_owner(
            &old_stmts,
            index,
            sink_index,
            &use_index,
            mutable_snapshots,
        ) {
            // 候选拒绝[LayerBoundary]：method alias transaction 归 function-sugar，不能由 call-result run 局部消费。
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
            let suffix_uses =
                use_index.count_uses_in_suffix(candidate_index + 1, candidate.binding());
            if suffix_uses == 0 {
                // 候选拒绝[LayerBoundary]：零 use 的声明归 cleanup/dead-local。
                continue;
            }
            if suffix_uses > 1 {
                // 候选拒绝[SemanticBarrier:EvalCount]：多次 use 会复制 call-result producer。
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
                // 候选拒绝[SemanticBarrier:EvalOrder]：中间读取会改变快照/次数；候选拒绝[ProofIncomplete]：非 nested sink 位置缺少该 run 的位置级证明。
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

        // 候选拒绝[PolicyBoundary]：call-result 只收回至少两个机械阶段；候选拒绝[SemanticBarrier:EvalOrder]：完整事件前缀必须同序。

        stmt_plan.push(PlannedStmt::Original(index));
        index += 1;
    }

    block.stmts = materialize_stmt_plan(old_stmts, stmt_plan);
    changed
}

pub(super) fn find_terminal_call_result_sink(stmts: &[AstStmt], index: usize) -> Option<usize> {
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

pub(super) fn stmt_sink_binding_allows_adjacent_value_inline(
    stmts: &[AstStmt],
    sink_index: usize,
) -> bool {
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
        // 候选拒绝[ProofIncomplete]：sink local 后续还作为 callee 时，当前相邻值规则未证明删掉前置 alias 后的调用身份链。
        .any(|stmt| stmt_has_call_callee_binding_use(stmt, sink_candidate.binding()))
}

pub(super) fn collapse_adjacent_mechanical_alias_runs(
    block: &mut AstBlock,
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&old_stmts, trailing_condition);
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
                // 候选拒绝[ProofIncomplete]：该 RHS 不在 mechanical-run 已证明的 copy/lookup/call 子集，缺少值宽度与事件事实。
                continue;
            }
            let run_uses = use_index.count_uses_in_range(
                candidate_index + 1,
                run_end + 1,
                candidate.binding(),
            );
            if run_uses == 0 {
                // 候选拒绝[LayerBoundary]：未被当前 run/sink 消费的声明不属于本规则。
                continue;
            }
            if run_uses > 1 {
                // 候选拒绝[SemanticBarrier:EvalCount]：候选在 run+sink 中多次读取时，替换会复制 RHS。
                continue;
            }
            if use_index.count_uses_in_suffix(run_end + 1, candidate.binding()) != 0 {
                // 候选拒绝[SemanticBarrier:Scope]：binding 在 sink 后仍活跃，删除声明会使后缀读取失去 local 身份。
                continue;
            }
            if remaining_run_uses
                .get(&candidate.binding())
                .is_some_and(|count| *count != 0)
            {
                // 候选拒绝[SemanticBarrier:EvalOrder]：保留的中间语句仍读取候选快照，不能只在最终 sink 替换。
                continue;
            }
            let current_sink = rewritten_sink.as_ref().unwrap_or(&old_stmts[run_end]);
            if !stmt_has_mechanical_run_sink_binding_use(current_sink, candidate.binding()) {
                // 候选拒绝[ProofIncomplete]：候选 use 不在 mechanical-run 拥有的位置集合，需扩展 use-site 证明后再消费。
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

        // 候选拒绝[PolicyBoundary]：至少两项且形状值得收回；候选拒绝[SemanticBarrier:EvalOrder]：全部 producer 必须仍构成 sink 的同序可观察前缀。

        stmt_plan.push(PlannedStmt::Original(index));
        index += 1;
    }

    block.stmts = materialize_stmt_plan(old_stmts, stmt_plan);
    changed
}

pub(super) fn collapse_terminal_local_mechanical_runs(
    block: &mut AstBlock,
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&old_stmts, trailing_condition);
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
            // 候选拒绝[LayerBoundary]：末项不跨语句存活时不属于 terminal-local 规则，交由其它 run/single-item owner。
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
                // 候选拒绝[ProofIncomplete]：RHS 超出 terminal mechanical-run 已证明的表达式集合。
                continue;
            }
            let suffix_uses =
                use_index.count_uses_in_suffix(candidate_index + 1, candidate.binding());
            if suffix_uses == 0 {
                // 候选拒绝[LayerBoundary]：零 use 的声明归 cleanup/dead-local。
                continue;
            }
            if suffix_uses > 1 {
                // 候选拒绝[SemanticBarrier:EvalCount]：多次 use 会复制 producer。
                continue;
            }
            if use_index.count_uses_in_suffix(run_end, candidate.binding()) != 0 {
                // 候选拒绝[SemanticBarrier:Scope]：前置 binding 在 terminal local 之后仍活跃，不能随准备阶段一起删除。
                continue;
            }
            if remaining_run_uses
                .get(&candidate.binding())
                .is_some_and(|count| *count != 0)
            {
                // 候选拒绝[SemanticBarrier:EvalOrder]：保留的 run 片段仍读取候选，不能只重写 terminal local。
                continue;
            }
            let current_sink = rewritten_sink.as_ref().unwrap_or(&old_stmts[run_end - 1]);
            if !stmt_has_nested_binding_use(current_sink, candidate.binding()) {
                // 候选拒绝[ProofIncomplete]：候选 use 不在 terminal-local 当前拥有的 nested value 位置。
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

        // 候选拒绝[PolicyBoundary]：少于两个机械阶段不做展示折叠；候选拒绝[SemanticBarrier:EvalOrder]：事件前缀不一致会改变调用/lookup/快照次序。

        stmt_plan.push(PlannedStmt::Original(index));
        index += 1;
    }

    block.stmts = materialize_stmt_plan(old_stmts, stmt_plan);
    changed
}

pub(super) fn stmt_can_absorb_mechanical_run(stmt: &AstStmt) -> bool {
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

pub(super) fn plan_collapsed_run(
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

pub(super) fn stmt_prefers_pure_lookup_run_collapse(stmt: &AstStmt) -> bool {
    matches!(
        stmt,
        // 纯 lookup bag 如果只是为了拼一个复合左值（例如 `tbl[tbl.n] = ...`），
        // 保留中间 local 只会把“地址计算”拆成多行机械脚手架；这里允许把它们收回赋值本身。
        AstStmt::Assign(assign)
            if assign
                .targets
                .iter()
                .any(|target| !matches!(target, super::super::super::common::AstLValue::Name(_)))
    ) || matches!(
        stmt,
        // generic-for 的迭代器位天然就是机械准备 run 的消费点：
        // `local f = _G.ipairs; local t = obj.items; for k, v in f(t) do`
        // 保留这些 lookup local 只会把迭代器表达式拆散。
        AstStmt::GenericFor(_)
    )
}

pub(super) fn stmt_has_mechanical_run_sink_binding_use(
    stmt: &AstStmt,
    binding: AstBindingRef,
) -> bool {
    stmt_has_nested_binding_use(stmt, binding)
        || stmt_has_access_base_binding_use(stmt, binding)
        || stmt_has_call_callee_binding_use(stmt, binding)
        || stmt_has_direct_call_arg_binding_use(stmt, binding)
        || stmt_has_index_binding_use(stmt, binding)
}

pub(super) fn stmt_prefers_dependent_lookup_run_collapse(stmt: &AstStmt) -> bool {
    matches!(stmt, AstStmt::Assign(_))
}

pub(super) fn stmt_starts_lookup_mechanical_run(
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

pub(super) fn expr_references_any_run_binding(
    expr: &super::super::super::common::AstExpr,
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

pub(super) fn assign_targets_same_lookup_expr(
    stmt: &AstStmt,
    expr: &super::super::super::common::AstExpr,
) -> bool {
    let AstStmt::Assign(assign) = stmt else {
        return false;
    };
    assign
        .targets
        .iter()
        .any(|target| lvalue_matches_lookup_expr(target, expr))
}

pub(super) fn lvalue_matches_lookup_expr(
    target: &super::super::super::common::AstLValue,
    expr: &super::super::super::common::AstExpr,
) -> bool {
    match (target, expr) {
        (
            super::super::super::common::AstLValue::FieldAccess(lhs),
            super::super::super::common::AstExpr::FieldAccess(rhs),
        ) => lhs.field == rhs.field && lhs.base == rhs.base,
        (
            super::super::super::common::AstLValue::IndexAccess(lhs),
            super::super::super::common::AstExpr::IndexAccess(rhs),
        ) => lhs.base == rhs.base && lhs.index == rhs.index,
        _ => false,
    }
}

pub(super) fn add_next_kept_stmt_uses(
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
