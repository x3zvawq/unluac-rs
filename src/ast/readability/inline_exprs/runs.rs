//! 折叠相邻调用、lookup 与机械 local run；依赖父模块的 candidate/use/eval-order 合同，不负责单次 alias inline；例如把 recovered callee/receiver 链收回调用或赋值 sink。

use std::collections::BTreeMap;

use super::*;

fn extended_run_allows_recovered_expr(
    candidate: InlineCandidate,
    value: &AstExpr,
    policy: InlinePolicy,
) -> bool {
    if candidate.origin() != super::super::super::common::AstLocalOrigin::Recovered {
        return false;
    }
    match policy {
        InlinePolicy::ExtendedCallChain => {
            super::super::expr_analysis::is_context_safe_expr(value)
                || candidate::is_lookup_inline_expr(value)
                || super::super::expr_analysis::is_call_arg_constructor_inline_expr(value)
                || matches!(value, AstExpr::VarArg)
        }
        _ => false,
    }
}

fn rewrite_direct_call_arg_as_single_value(stmt: &mut AstStmt, binding: AstBindingRef) -> bool {
    fn rewrite_expr(expr: &mut AstExpr, binding: AstBindingRef) -> bool {
        let args = match expr {
            AstExpr::Call(call) => &mut call.args,
            AstExpr::MethodCall(call) => &mut call.args,
            AstExpr::SingleValue(inner) => return rewrite_expr(inner, binding),
            _ => return false,
        };
        let Some(arg) = args
            .iter_mut()
            .find(|arg| matches!(arg, AstExpr::Var(name) if binding.matches_name_ref(name)))
        else {
            return false;
        };
        *arg = AstExpr::SingleValue(Box::new(AstExpr::VarArg));
        true
    }

    match stmt {
        AstStmt::LocalDecl(decl) => decl
            .values
            .iter_mut()
            .any(|value| rewrite_expr(value, binding)),
        AstStmt::Assign(assign) => assign
            .values
            .iter_mut()
            .any(|value| rewrite_expr(value, binding)),
        AstStmt::Return(ret) => ret
            .values
            .iter_mut()
            .any(|value| rewrite_expr(value, binding)),
        AstStmt::CallStmt(call) => match &mut call.call {
            AstCallKind::Call(call) => call.args.iter_mut().any(|arg| {
                if matches!(arg, AstExpr::Var(name) if binding.matches_name_ref(name)) {
                    *arg = AstExpr::SingleValue(Box::new(AstExpr::VarArg));
                    true
                } else {
                    false
                }
            }),
            AstCallKind::MethodCall(call) => call.args.iter_mut().any(|arg| {
                if matches!(arg, AstExpr::Var(name) if binding.matches_name_ref(name)) {
                    *arg = AstExpr::SingleValue(Box::new(AstExpr::VarArg));
                    true
                } else {
                    false
                }
            }),
        },
        _ => false,
    }
}

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
        if binding.attr == AstLocalAttr::Const {
            // 候选拒绝[PolicyBoundary]：`<const>` 的源码声明身份按展示策略保留。
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        if binding.origin.is_debug_hinted() {
            // 候选拒绝[SemanticBarrier:DebugScope]：DebugHinted 是 IR 已保留的源码 binding；吞掉更新壳会改写其显式值 epoch。
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        if !binding.rewrite_authority.may_remove_binding() {
            // 候选拒绝[LayerBoundary]：self-call update run 会折叠 binding 的中间 value
            // epoch；HIR 已保留的 binding 不由 AST 重审。
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
    target: AstTargetDialect,
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&old_stmts, trailing_condition);
    let write_index = BindingWriteIndex::for_stmts(&old_stmts);
    let run_facts = CandidateRunFacts::new(&old_stmts);
    let mut stmt_plan = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while index < old_stmts.len() {
        let run_end = run_facts.end(index);

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
            &write_index,
            mutable_snapshots,
        ) {
            // 候选拒绝[LayerBoundary]：Deferred function-sugar 的 method_alias owner 会把
            // receiver/field/call 整段原子消费；scheduler 随后重跑 Normal phase，不能先删除 alias。
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
            if !candidate.allows_expr_with_policy(value, rewrite_policy)
                && !extended_run_allows_recovered_expr(candidate, value, rewrite_policy)
            {
                // 候选拒绝[SemanticBarrier:DebugScope]：DebugHinted local 可被调用中的 debug.getlocal 观察（regress_351）。
                // 候选拒绝[SemanticBarrier:Lifetime]：当前 run policy 不接管 PhysicalRoot 的原词法根。
                // call 已由当前 policy 接受；loop-header 的 lookup/构造器也已进入逐 site 审查。
                // 候选拒绝[SemanticBarrier:ValueArity]：Extended run 的裸 vararg 仅在直接 call 参数位由下方单值特例接管；loop-header/其它开放尾位继续保留。
                // 候选拒绝[SemanticBarrier:Capture]：closure 搬到 sink 会改变分配/capture 时点；安全的直接 return 由相邻 DirectReturnValue owner 消费。
                // 候选拒绝[PolicyBoundary]：Error residual 是 best-effort 输出保留的失败证据，
                // call-alias run 不把它埋入普通调用表达式。
                continue;
            }
            let suffix_uses =
                use_index.count_uses_in_suffix(candidate_index + 1, candidate.binding());
            if suffix_uses == 0 {
                // 候选拒绝[SemanticBarrier:EvalCount]：cleanup 已在本轮先行；可丢弃值和
                // 可降为 CallStmt 的 producer 不会抵达这里。残留零-use lookup/dynamic
                // initializer 没有合法 expression-statement 载体，删除会少一次求值。
                // 候选拒绝[SemanticBarrier:Metamethod]：例如 `local dead = proxy.key` 的
                // `__index` 必须继续执行，当前 sink 又没有该 binding 的替换位置。
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
                // 候选拒绝[SemanticBarrier:EvalOrder]：候选在抵达 sink 前已有读取，删除声明会改变快照时点；
                // 候选拒绝[SemanticBarrier:EvalCount]：有事件 producer 会被中间读取与 sink 重复消费。
                continue;
            }

            let current_sink = rewritten_sink.as_ref().unwrap_or(&old_stmts[run_end]);
            if candidate.initializer_may_affect_collectable_lifetime()
                && !call_alias_sink_preserves_root_lifetime(current_sink, candidate.binding())
            {
                // 候选拒绝[SemanticBarrier:Lifetime]：callee/receiver/argument 的源码位置
                // 不能证明 producer local 在普通调用或 generic-for body 期间仍是强根。
                // 只有单值 tail return、顶层 return value 或同一 call occurrence 的 HIR
                // method-callee handoff 可以接管这一边界。
                continue;
            }

            let mut trial_sink = current_sink.clone();
            if rewrite_stmt_use_sites_with_policy(
                &mut trial_sink,
                candidate,
                value,
                options,
                rewrite_policy,
            ) || (matches!(value, AstExpr::VarArg)
                && rewrite_direct_call_arg_as_single_value(&mut trial_sink, candidate.binding()))
            {
                rewritten_sink = Some(trial_sink);
                removed[candidate_index - index] = true;
                collapsed_count += 1;
            }
        }

        // 常规路径只折叠真正的“局部别名包”，避免吞掉有阶段语义的源码 local。
        // 单项只接受 method fact 已经冻结后的直接 receiver binding；若迭代器仍引用
        // 待物化 temp，则留到下一轮与整个调用准备包一起收回。
        let allows_single_receiver_alias = collapsed_count == 1
            && (single_generic_for_method_receiver_alias(&old_stmts, index, run_end)
                || single_call_callee_alias(&old_stmts, index, run_end));
        if collapsed_count >= 2 || allows_single_receiver_alias {
            if eval_order::run_preserves_eval_order(
                &old_stmts,
                index,
                run_end,
                &removed,
                target,
                mutable_snapshots,
                &write_index,
            ) {
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
            // 候选拒绝[SemanticBarrier:EvalOrder]：已形成足量 rewrite 的移动事件必须仍是
            // sink 的同序前缀；多值 return 的前置快照/事件会改变可观察顺序
            // （regress_352、regress_353）。
        } else if collapsed_count != 0 {
            // 候选拒绝[PolicyBoundary]：普通 run 至少收回两项；单项仅为 generic-for
            // method receiver 或 terminal call-callee 时才值得消除独立声明。
        }

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
    // 候选拒绝[LayerBoundary]：Temp 由 Deferred materialize_temps 转成 synthetic local，
    // scheduler 随后重跑 inline_exprs。
    // 候选拒绝[SemanticBarrier:Lifetime]：global receiver 的 alias 原本在整个 generic-for
    // 词法域保持强 root；`iter()` 可清空该 global 且不让 iterator 捕获 receiver，内联会让
    // receiver 在 loop body 的 collectgarbage 前失活，使弱表或 `__gc` 可观察。
    candidate.origin() == super::super::super::common::AstLocalOrigin::Recovered
        && !matches!(source, AstNameRef::Global(_) | AstNameRef::Temp(_))
        && candidate.binding().matches_name_ref(receiver)
        && !binding_mentions_in_expr(&generic_for.iterator[0])
            .iter()
            .any(|binding| matches!(binding, AstBindingRef::Temp(_)))
}

pub(super) fn single_call_callee_alias(
    stmts: &[AstStmt],
    run_start: usize,
    sink_index: usize,
) -> bool {
    let Some((candidate, value)) = (sink_index == run_start + 1)
        .then(|| inline_candidate(&stmts[run_start]))
        .flatten()
    else {
        // 这不是紧邻 local + terminal call 的单项 run。
        return false;
    };
    if candidate.origin() != super::super::super::common::AstLocalOrigin::Recovered
        || !matches!(value, AstExpr::Call(_) | AstExpr::MethodCall(_))
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：仅 recovered call producer 有 callee 栈槽接管
        // 证明；其它 origin 或非 call RHS 仍需普通多项 run 证明。
        return false;
    }
    let callee_matches = match &stmts[sink_index] {
        AstStmt::CallStmt(call_stmt) => {
            let AstCallKind::Call(call) = &call_stmt.call else {
                // 候选拒绝[SemanticBarrier:EvalOrder]：method call 的隐式 self/lookup 顺序不属于
                // 该直接 callee 证明。
                return false;
            };
            let AstExpr::Var(callee) = &call.callee else {
                // 候选拒绝[PolicyBoundary]：caller 已证明唯一 use 并完成 trial rewrite；单项展示例外只收回直接 callee，非直接 callee 仍需普通多项 run。
                return false;
            };
            candidate.binding().matches_name_ref(callee)
        }
        AstStmt::GenericFor(_) => {
            // 候选拒绝[SemanticBarrier:Lifetime]：iterator call 不保证保存 callable producer；
            // 原 local 还会跨 iterator setup 与 loop body 持根。缺少 HIR producer/sink
            // 双端事务时，generic-for 不接受 call-result callee 单项折叠。
            return false;
        }
        AstStmt::Return(ret) => {
            let [AstExpr::Call(call)] = ret.values.as_slice() else {
                // 候选拒绝[SemanticBarrier:Lifetime]：只有唯一 return call 会终结 caller
                // frame；一旦有前置返回值，该 call 不再是 tail call，原 producer local
                // 会在调用期间继续持根。
                return false;
            };
            let AstExpr::Var(callee) = &call.callee else {
                // 候选拒绝[PolicyBoundary]：单项展示例外只收回直接 callee；嵌套 callee
                // 需要普通多项 run 证明其结构值得折叠。
                return false;
            };
            candidate.binding().matches_name_ref(callee)
        }
        _ => {
            // dispatcher 只把 call statement、generic-for 与
            // terminal return call 交给该单项证明。
            return false;
        }
    };
    if !callee_matches {
        // 候选拒绝[SemanticBarrier:Scope]：callee 必须正是该 local binding，避免误吞其它变量。
        return false;
    }
    if matches!(&stmts[sink_index], AstStmt::CallStmt(_))
        && !proven_method_call_consumes_callee(&stmts[sink_index], candidate.binding())
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：普通 call callee 槽不证明 producer local
        // 跨调用持根；只有同一 occurrence 的 HIR method-callee handoff 可以放行。
        return false;
    }
    // 单值 return call 会在进入 callee 前终结 caller frame；普通 CallStmt 则只接受 HIR
    // 已对同一 occurrence 签发的 method-callee root handoff。结合外层唯一 use/write 与
    // eval-order 证明，移除 local 不复制 producer 或缩短已证明的 root 生命周期。
    true
}

pub(super) fn stmt_is_terminal_call_alias_sink(stmt: &AstStmt) -> bool {
    match stmt {
        AstStmt::CallStmt(_) => true,
        // generic-for 的 iterator 表达式也是调用准备 run 的自然终点：
        // `local iter = ipairs; local items = {...}; for k, v in iter(items) do`
        // 应恢复成 `for k, v in ipairs({...}) do`。这里只接受单个 iterator call，
        // 避免把多表达式 iterator list 里的阶段 local 误吞掉。
        AstStmt::GenericFor(_) => stmt_is_generic_for_call_alias_sink(stmt),
        // Lua 只展开 return 列表的最后一项；保持尾项为 call 即保持值宽度。前置返回值
        // 与搬入 producer 的相对顺序由 run_preserves_eval_order 逐项证明，不能在这里整类拒绝。
        AstStmt::Return(ret) => matches!(
            ret.values.last(),
            Some(
                super::super::super::common::AstExpr::Call(_)
                    | super::super::super::common::AstExpr::MethodCall(_)
            )
        ),
        _ => false,
    }
}

pub(super) fn collapse_terminal_call_result_alias_runs(
    block: &mut AstBlock,
    target: AstTargetDialect,
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&old_stmts, trailing_condition);
    let write_index = BindingWriteIndex::for_stmts(&old_stmts);
    let run_facts = CandidateRunFacts::new(&old_stmts);
    let mut stmt_plan = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while index < old_stmts.len() {
        let Some(sink_index) = run_facts.call_result_after(index) else {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        };
        if super::super::function_sugar::run_belongs_to_method_alias_owner(
            &old_stmts,
            index,
            sink_index,
            &use_index,
            &write_index,
            mutable_snapshots,
        ) {
            // 候选拒绝[LayerBoundary]：Deferred function-sugar 的 method_alias owner 会原子
            // 消费该 transaction；scheduler 随后重跑 Normal phase，call-result run 不能先拆段。
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
            if !candidate.allows_expr_with_policy(value, InlinePolicy::ExtendedCallChain)
                && !extended_run_allows_recovered_expr(
                    candidate,
                    value,
                    InlinePolicy::ExtendedCallChain,
                )
            {
                // 候选拒绝[SemanticBarrier:DebugScope]：DebugHinted local 可被调用中的 debug.getlocal 观察（regress_351）。
                // 候选拒绝[SemanticBarrier:Lifetime]：call-result run 不接管 PhysicalRoot 的原词法根。
                // call 已由 ExtendedCallChain 接受；lookup、context-safe 运算与受限构造器由逐 site 合同审查。
                // 候选拒绝[SemanticBarrier:ValueArity]：裸 vararg 仅在直接 call 参数位由下方单值特例接管。
                // 候选拒绝[SemanticBarrier:Capture]：closure 的分配/capture 时点不能由 call-result run 搬移；直接 return 归相邻 owner。
                // 候选拒绝[PolicyBoundary]：Error residual 是 best-effort 输出保留的失败证据，
                // call-result run 不把它埋入普通调用表达式。
                continue;
            }
            let suffix_uses =
                use_index.count_uses_in_suffix(candidate_index + 1, candidate.binding());
            if suffix_uses == 0 {
                // 候选拒绝[SemanticBarrier:EvalCount]：cleanup 已先删除无事件值并把裸 call
                // 降为 CallStmt；残留零-use lookup/dynamic initializer 没有 sink use-site，
                // 删除会少一次求值。
                // 候选拒绝[SemanticBarrier:Metamethod]：proxy[key] 等残留读取可能调用协议。
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
            if intermediate_uses != 0 {
                // 候选拒绝[SemanticBarrier:EvalOrder]：仍保留的中间读取会把声明点快照与 sink 求值交错。
                continue;
            }
            if !stmt_has_nested_binding_use(current_sink, candidate.binding()) {
                // 当前 call-result sink 不读取该 binding；scanner
                // 只是越过了一个与 sink 无关、在更后面才使用的声明，本 run 没有替换位置。
                continue;
            }

            let mut trial_sink = current_sink.clone();
            if rewrite_stmt_use_sites_with_policy(
                &mut trial_sink,
                candidate,
                value,
                options,
                InlinePolicy::ExtendedCallChain,
            ) || (matches!(value, AstExpr::VarArg)
                && rewrite_direct_call_arg_as_single_value(&mut trial_sink, candidate.binding()))
            {
                rewritten_sink = Some(trial_sink);
                removed[candidate_index - index] = true;
                collapsed_count += 1;
            }
        }

        // 这里专门处理“调用准备 run 的终点自己还是一个 local/assign”：
        // `local f = obj.m; local x = f(arg)`、`local a = t[i]; local v = call(a, ...)`
        // 这类形状和最终 `call_stmt(...)` 属于同一 owner，只是 sink 还保留在结果声明里。
        if collapsed_count >= 2 {
            if eval_order::run_preserves_eval_order(
                &old_stmts,
                index,
                sink_index,
                &removed,
                target,
                mutable_snapshots,
                &write_index,
            ) {
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
            // 候选拒绝[SemanticBarrier:EvalOrder]：已形成足量 call-result rewrite 时，
            // 完整事件前缀仍必须保持同序。
        } else if collapsed_count != 0 {
            // 候选拒绝[PolicyBoundary]：call-result 只收回至少两个机械准备阶段。
        }

        stmt_plan.push(PlannedStmt::Original(index));
        index += 1;
    }

    block.stmts = materialize_stmt_plan(old_stmts, stmt_plan);
    changed
}

pub(super) fn collapse_adjacent_mechanical_alias_runs(
    block: &mut AstBlock,
    target: AstTargetDialect,
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&old_stmts, trailing_condition);
    let write_index = BindingWriteIndex::for_stmts(&old_stmts);
    let run_facts = CandidateRunFacts::new(&old_stmts);
    let mut stmt_plan = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while index < old_stmts.len() {
        let run_end = run_facts.end(index);

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
                // 候选拒绝[SemanticBarrier:DebugScope]：DebugHinted 不能删除（regress_351）；
                // 候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot 不能脱离原 root（regress_353）；
                // call/受限 table/标量 vararg 的调用消费点由前置 call-run owner 处理；直接 return 的 table/closure 由相邻 owner 处理。
                // 候选拒绝[SemanticBarrier:ValueArity]：其它 call/vararg 尾位可能重新打开多值。
                // 候选拒绝[SemanticBarrier:Capture]：nested closure 会改变分配/capture 时点。
                // 候选拒绝[PolicyBoundary]：Error residual 是项目保留的 best-effort 失败证据。
                continue;
            }
            let run_uses = use_index.count_uses_in_range(
                candidate_index + 1,
                run_end + 1,
                candidate.binding(),
            );
            if run_uses == 0 {
                // 声明未被当前 run 或 sink 读取，不是该 transaction 的成员。
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
            if !matches!(current_sink, AstStmt::While(_) | AstStmt::Repeat(_))
                && candidate.initializer_may_affect_collectable_lifetime()
                && !mechanical_sink_preserves_root_lifetime(current_sink, candidate.binding())
            {
                // 候选拒绝[SemanticBarrier:Lifetime]：把 recovered lookup/object/动态运算结果搬入非终态 sink 会在 sink 后提前释放唯一强 root（regress_355）。
                // 候选拒绝[TargetConstraint]：只有目标已定义的 literal 运算可证明结果为标量；动态 operand 仍可能经元方法返回 collectable。
                // 候选拒绝[SemanticBarrier:EvalOrder]：fresh table/container 在字段前先分配，不能充当 producer 的透明 handoff；否则会交换 allocation/GC 事件。
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
                has_dependent_lookup_piece = has_dependent_lookup_piece
                    || (candidate::is_lookup_inline_expr(value)
                        && run_facts.reads_other_candidate(value, index, candidate.binding()));
            }
        }

        if let Some(rewritten_sink_ref) = rewritten_sink.as_ref() {
            let display_worthy = has_non_lookup_piece
                || stmt_prefers_pure_lookup_run_collapse(rewritten_sink_ref)
                || (has_dependent_lookup_piece
                    && stmt_prefers_dependent_lookup_run_collapse(rewritten_sink_ref));
            if collapsed_count >= 2 && display_worthy {
                if eval_order::run_preserves_eval_order(
                    &old_stmts,
                    index,
                    run_end,
                    &removed,
                    target,
                    mutable_snapshots,
                    &write_index,
                ) {
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
                // 候选拒绝[SemanticBarrier:EvalOrder]：已形成足量且值得展示的 mechanical
                // rewrite 时，全部 producer 必须仍构成 sink 的同序可观察前缀。
            } else if collapsed_count != 0 {
                // 候选拒绝[PolicyBoundary]：mechanical run 至少收回两项，且 lookup 组合
                // 必须达到项目选择的展示收益。
            }
        }

        stmt_plan.push(PlannedStmt::Original(index));
        index += 1;
    }

    block.stmts = materialize_stmt_plan(old_stmts, stmt_plan);
    changed
}

pub(super) fn collapse_terminal_local_mechanical_runs(
    block: &mut AstBlock,
    target: AstTargetDialect,
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&old_stmts, trailing_condition);
    let write_index = BindingWriteIndex::for_stmts(&old_stmts);
    let run_facts = CandidateRunFacts::new(&old_stmts);
    let mut stmt_plan = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while index < old_stmts.len() {
        let run_end = run_facts.end(index);

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
            // 末项没有后续读取，不是 terminal-local 源码锚点。
            // cleanup 已先删除无事件值或把裸 call 降为 CallStmt；若声明仍存在，其 lookup/
            // dynamic initializer 必须保留求值，不能假借 terminal-local run 删除。
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
                // 候选拒绝[SemanticBarrier:DebugScope]：DebugHinted 不能删除（regress_351）；
                // 候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot 不能脱离原 root（regress_353）；
                // call/受限 table/标量 vararg 的调用消费点由 call-run owner 处理；直接 return 的 table/closure 由相邻 owner 处理。
                // 候选拒绝[SemanticBarrier:ValueArity]：其它 call/vararg 尾位可能重新打开多值。
                // 候选拒绝[SemanticBarrier:Capture]：nested closure 会改变分配/capture 时点。
                // 候选拒绝[PolicyBoundary]：Error residual 是项目保留的 best-effort 失败证据。
                continue;
            }
            let suffix_uses =
                use_index.count_uses_in_suffix(candidate_index + 1, candidate.binding());
            if suffix_uses == 0 {
                // 候选拒绝[SemanticBarrier:EvalCount]：cleanup 已先处理可丢弃值与裸 call；
                // 残留零-use lookup/dynamic initializer 没有 rewrite site，删除会少一次求值。
                // 候选拒绝[SemanticBarrier:Metamethod]：动态读取/运算可能触发协议。
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
            if candidate.initializer_may_affect_collectable_lifetime()
                && (!terminal_local_hands_off_root(current_sink, candidate.binding())
                    || write_index.has_write_after(run_end - 1, sink_candidate.binding()))
            {
                // 候选拒绝[SemanticBarrier:Lifetime]：nested terminal initializer 可能在后续语句前释放 recovered lookup/object root（regress_355）；只有无后续写入的顶层 copy 仍直接持有同一对象。
                // 候选拒绝[SemanticBarrier:Lifetime]：table/container 后续可被设为 weak 或经 alias 清空，不能等同于 local 的持续强 root。
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

        if collapsed_count >= 2 {
            if eval_order::run_preserves_eval_order(
                &old_stmts,
                index,
                run_end - 1,
                &removed,
                target,
                mutable_snapshots,
                &write_index,
            ) {
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
            // 候选拒绝[SemanticBarrier:EvalOrder]：足量 terminal-local rewrite 的事件前缀
            // 不一致时，会改变调用、lookup 或可变快照的次序。
        } else if collapsed_count != 0 {
            // 候选拒绝[PolicyBoundary]：少于两个机械阶段不做 terminal-local 展示折叠。
        }

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

fn mechanical_sink_preserves_root_lifetime(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    candidate::stmt_has_top_level_return_binding_use(stmt, binding)
        || proven_method_call_consumes_callee(stmt, binding)
}

fn call_alias_sink_preserves_root_lifetime(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    candidate::stmt_has_top_level_return_binding_use(stmt, binding)
        || matches!(stmt, AstStmt::Return(ret) if matches!(ret.values.as_slice(), [AstExpr::Call(_) | AstExpr::MethodCall(_)]))
        || proven_method_call_consumes_callee(stmt, binding)
}

fn proven_method_call_consumes_callee(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    matches!(
        stmt,
        AstStmt::CallStmt(call_stmt)
            if matches!(
                &call_stmt.call,
                AstCallKind::Call(call)
                    if matches!(
                        call.callee_root_handoff,
                        Some(crate::hir::HirCallRootHandoff::MethodCallee(_))
                    )
                        && matches!(&call.callee, AstExpr::Var(name) if binding.matches_name_ref(name))
            )
    )
}

fn terminal_local_hands_off_root(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    matches!(
        stmt,
        AstStmt::LocalDecl(local)
            if matches!(local.values.as_slice(), [AstExpr::Var(name)] if binding.matches_name_ref(name))
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

pub(super) fn stmt_prefers_dependent_lookup_run_collapse(stmt: &AstStmt) -> bool {
    matches!(stmt, AstStmt::Assign(_))
}

pub(super) fn stmt_starts_lookup_mechanical_run(
    stmts: &[AstStmt],
    index: usize,
    binding: AstBindingRef,
    run_end: usize,
) -> bool {
    run_end > index + 1
        && run_end < stmts.len()
        && stmt_can_absorb_mechanical_run(&stmts[run_end])
        && stmts
            .get(index + 1)
            .and_then(inline_candidate)
            .is_some_and(|(_, next_value)| {
                candidate::is_lookup_inline_expr(next_value)
                    && expr_reads_binding(next_value, binding)
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

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::LuaString;
    use crate::ast::common::{
        AstCallExpr, AstCallStmt, AstFunctionExpr, AstGenericFor, AstLocalBinding, AstLocalDecl,
        AstLocalOrigin, AstReturn, AstTableConstructor, AstTableField,
    };
    use crate::decompile::DecompileDialect;
    use crate::hir::{
        HirBinaryExpr, HirBinaryOpKind, HirCallRootHandoff, HirExpr, HirProtoRef, HirUnaryExpr,
        HirUnaryOpKind, HirValuePack, LocalId, ParamId, initializer_root_profile,
    };

    use super::*;

    fn recovered_local(binding: AstBindingRef, value: AstExpr) -> AstStmt {
        AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![AstLocalBinding {
                id: binding,
                attr: AstLocalAttr::None,
                origin: AstLocalOrigin::Recovered,
                rewrite_authority: crate::ast::common::AstRewriteAuthority::AstOwned,
            }],
            values: vec![value],
            initializer_merge_transaction: None,
            initializer_root_profile: None,
        }))
    }

    fn direct_call(callee: AstExpr, arg: AstExpr) -> AstStmt {
        AstStmt::CallStmt(Box::new(AstCallStmt {
            call: AstCallKind::Call(Box::new(AstCallExpr {
                callee,
                args: vec![arg],
                method_key: None,
                callee_root_handoff: None,
                method_rewrite_transaction: None,
            })),
        }))
    }

    fn call_expr(callee: AstExpr) -> AstExpr {
        AstExpr::Call(Box::new(AstCallExpr {
            callee,
            args: Vec::new(),
            method_key: None,
            callee_root_handoff: None,
            method_rewrite_transaction: None,
        }))
    }

    fn collapse_call_run(block: &mut AstBlock) -> bool {
        collapse_adjacent_call_alias_runs(
            block,
            AstTargetDialect::new(DecompileDialect::Lua54),
            ReadabilityOptions::default(),
            &MutableSnapshotNames::new(),
            None,
        )
    }

    #[test]
    fn extended_call_run_keeps_unproven_table_and_vararg_roots() {
        let first = AstBindingRef::Local(LocalId(0));
        let second = AstBindingRef::Local(LocalId(1));
        let table = AstExpr::TableConstructor(Box::new(AstTableConstructor {
            allocation: Default::default(),
            fields: vec![AstTableField::Array(AstExpr::Integer(1))],
        }));
        let mut table_block = AstBlock {
            stmts: vec![
                recovered_local(first, table),
                recovered_local(second, AstExpr::Var(AstNameRef::Param(ParamId(1)))),
                direct_call(
                    AstExpr::Var(second.to_name_ref()),
                    AstExpr::Var(first.to_name_ref()),
                ),
            ],
        };
        let (table_candidate, table_value) = inline_candidate(&table_block.stmts[0]).unwrap();
        assert!(extended_run_allows_recovered_expr(
            table_candidate,
            table_value,
            InlinePolicy::ExtendedCallChain
        ));
        let original = table_block.clone();
        assert!(!collapse_call_run(&mut table_block));
        assert_eq!(table_block, original);

        let mut vararg_block = AstBlock {
            stmts: vec![
                recovered_local(first, AstExpr::VarArg),
                recovered_local(second, AstExpr::Var(AstNameRef::Param(ParamId(1)))),
                direct_call(
                    AstExpr::Var(second.to_name_ref()),
                    AstExpr::Var(first.to_name_ref()),
                ),
            ],
        };
        let original = vararg_block.clone();
        assert!(!collapse_call_run(&mut vararg_block));
        assert_eq!(vararg_block, original);
    }

    #[test]
    fn extended_call_run_accepts_hir_proven_scalar_arguments() {
        let first = AstBindingRef::Local(LocalId(0));
        let second = AstBindingRef::Local(LocalId(1));
        let mut first_decl = recovered_local(first, AstExpr::Integer(1));
        let mut second_decl = recovered_local(second, AstExpr::Integer(2));
        for (decl, value) in [(&mut first_decl, 1), (&mut second_decl, 2)] {
            let AstStmt::LocalDecl(local_decl) = decl else {
                unreachable!("recovered_local must produce a local declaration");
            };
            local_decl.initializer_root_profile = Some(initializer_root_profile(
                DecompileDialect::Lua54,
                &HirValuePack::fixed(vec![HirExpr::Integer(value)]),
                1,
            ));
        }
        let mut block = AstBlock {
            stmts: vec![
                first_decl,
                second_decl,
                AstStmt::CallStmt(Box::new(AstCallStmt {
                    call: AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Param(ParamId(0))),
                        args: vec![
                            AstExpr::Var(first.to_name_ref()),
                            AstExpr::Var(second.to_name_ref()),
                        ],
                        method_key: None,
                        callee_root_handoff: None,
                        method_rewrite_transaction: None,
                    })),
                })),
            ],
        };

        assert!(collapse_call_run(&mut block));
        assert!(matches!(
            block.stmts.as_slice(),
            [AstStmt::CallStmt(call)]
                if matches!(&call.call, AstCallKind::Call(call)
                    if call.args == vec![AstExpr::Integer(1), AstExpr::Integer(2)])
        ));
    }

    #[test]
    fn single_call_result_can_become_a_terminal_return_callee() {
        let callee = AstBindingRef::Local(LocalId(0));
        let producer = call_expr(AstExpr::Var(AstNameRef::Param(ParamId(0))));
        let mut block = AstBlock {
            stmts: vec![
                recovered_local(callee, producer.clone()),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![call_expr(AstExpr::Var(callee.to_name_ref()))],
                })),
            ],
        };

        assert!(collapse_call_run(&mut block));
        assert!(matches!(
            block.stmts.as_slice(),
            [AstStmt::Return(ret)]
                if matches!(ret.values.as_slice(), [AstExpr::Call(call)]
                    if call.callee == producer)
        ));
    }

    #[test]
    fn single_return_callee_keeps_producer_before_an_effectful_prefix() {
        let callee = AstBindingRef::Local(LocalId(0));
        let mut block = AstBlock {
            stmts: vec![
                recovered_local(
                    callee,
                    call_expr(AstExpr::Var(AstNameRef::Param(ParamId(0)))),
                ),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![
                        call_expr(AstExpr::Var(AstNameRef::Param(ParamId(1)))),
                        call_expr(AstExpr::Var(callee.to_name_ref())),
                    ],
                })),
            ],
        };
        let original = block.clone();

        assert!(!collapse_call_run(&mut block));
        assert_eq!(block, original);
    }

    #[test]
    fn call_result_callee_requires_tail_return_or_hir_handoff() {
        let callee = AstBindingRef::Local(LocalId(0));
        let producer = call_expr(AstExpr::Var(AstNameRef::Param(ParamId(0))));

        let mut call_stmt = AstBlock {
            stmts: vec![
                recovered_local(callee, producer.clone()),
                direct_call(AstExpr::Var(callee.to_name_ref()), AstExpr::Nil),
            ],
        };
        let original = call_stmt.clone();
        assert!(!collapse_call_run(&mut call_stmt));
        assert_eq!(call_stmt, original);

        let mut prefixed_return = AstBlock {
            stmts: vec![
                recovered_local(callee, producer.clone()),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![
                        AstExpr::Integer(42),
                        call_expr(AstExpr::Var(callee.to_name_ref())),
                    ],
                })),
            ],
        };
        let original = prefixed_return.clone();
        assert!(!collapse_call_run(&mut prefixed_return));
        assert_eq!(prefixed_return, original);

        let mut generic_for = AstBlock {
            stmts: vec![
                recovered_local(callee, producer),
                AstStmt::GenericFor(Box::new(AstGenericFor {
                    bindings: vec![AstBindingRef::Local(LocalId(1))],
                    iterator: vec![call_expr(AstExpr::Var(callee.to_name_ref()))],
                    body: AstBlock::default(),
                })),
            ],
        };
        let original = generic_for.clone();
        assert!(!collapse_call_run(&mut generic_for));
        assert_eq!(generic_for, original);
    }

    #[test]
    fn call_run_keeps_closure_allocation_and_terminal_container_is_not_a_root_handoff() {
        let first = AstBindingRef::Local(LocalId(0));
        let second = AstBindingRef::Local(LocalId(1));
        let closure = AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
            function: HirProtoRef(1),
            params: Vec::new(),
            is_vararg: false,
            named_vararg: None,
            body: AstBlock::default(),
            captured_bindings: BTreeSet::new(),
            captured_params: BTreeSet::new(),
            capture_names_by_upvalue: std::collections::BTreeMap::new(),
            capture_write_names: BTreeSet::new(),
        }));
        let mut block = AstBlock {
            stmts: vec![
                recovered_local(first, closure),
                recovered_local(second, AstExpr::Var(AstNameRef::Param(ParamId(1)))),
                direct_call(
                    AstExpr::Var(second.to_name_ref()),
                    AstExpr::Var(first.to_name_ref()),
                ),
            ],
        };
        let original = block.clone();
        assert!(!collapse_call_run(&mut block));
        assert_eq!(block, original);

        let direct_copy = recovered_local(second, AstExpr::Var(first.to_name_ref()));
        assert!(terminal_local_hands_off_root(&direct_copy, first));
        let container = recovered_local(
            second,
            AstExpr::TableConstructor(Box::new(AstTableConstructor {
                allocation: Default::default(),
                fields: vec![AstTableField::Array(AstExpr::Var(first.to_name_ref()))],
            })),
        );
        assert!(!terminal_local_hands_off_root(&container, first));
    }

    #[test]
    fn mechanical_root_gate_uses_the_hir_initializer_profile() {
        let binding = AstBindingRef::Local(LocalId(0));
        let mut proven = recovered_local(binding, AstExpr::Integer(3));
        let AstStmt::LocalDecl(local_decl) = &mut proven else {
            unreachable!("recovered_local must produce a local declaration");
        };
        local_decl.initializer_root_profile = Some(initializer_root_profile(
            DecompileDialect::Lua54,
            &HirValuePack::fixed(vec![HirExpr::Integer(3)]),
            1,
        ));
        let (candidate, _) =
            inline_candidate(&proven).expect("single local is an inline candidate");
        assert!(!candidate.initializer_may_affect_collectable_lifetime());

        let unknown = recovered_local(binding, AstExpr::Integer(3));
        let (candidate, _) =
            inline_candidate(&unknown).expect("single local is an inline candidate");
        assert!(candidate.initializer_may_affect_collectable_lifetime());

        for value in [
            HirExpr::Binary(Box::new(HirBinaryExpr {
                op: HirBinaryOpKind::Concat,
                lhs: HirExpr::String(LuaString::from("left")),
                rhs: HirExpr::String(LuaString::from("right")),
            })),
            HirExpr::Unary(Box::new(HirUnaryExpr {
                op: HirUnaryOpKind::BitNot,
                expr: HirExpr::Number(1.5),
            })),
        ] {
            let mut guarded = recovered_local(binding, AstExpr::Integer(3));
            let AstStmt::LocalDecl(local_decl) = &mut guarded else {
                unreachable!("recovered_local must produce a local declaration");
            };
            local_decl.initializer_root_profile = Some(initializer_root_profile(
                DecompileDialect::Lua54,
                &HirValuePack::fixed(vec![value]),
                1,
            ));
            let (candidate, _) =
                inline_candidate(&guarded).expect("single local is an inline candidate");
            assert!(candidate.initializer_may_affect_collectable_lifetime());
        }
    }

    #[test]
    fn method_callee_root_gate_requires_hir_occurrence_proof() {
        let binding = AstBindingRef::Local(LocalId(0));
        let mut stmt = direct_call(
            AstExpr::Var(binding.to_name_ref()),
            AstExpr::Var(AstNameRef::Param(ParamId(0))),
        );
        if let AstStmt::CallStmt(call_stmt) = &mut stmt
            && let AstCallKind::Call(call) = &mut call_stmt.call
        {
            call.method_key = Some(LuaString::from("run"));
        } else {
            unreachable!("direct_call must produce an ordinary call statement");
        }
        assert!(!proven_method_call_consumes_callee(&stmt, binding));

        if let AstStmt::CallStmt(call_stmt) = &mut stmt
            && let AstCallKind::Call(call) = &mut call_stmt.call
        {
            call.callee_root_handoff = Some(HirCallRootHandoff::MethodCallee(
                crate::hir::HirMethodSetupProtocolId::new(0),
            ));
        }
        assert!(proven_method_call_consumes_callee(&stmt, binding));
    }
}
