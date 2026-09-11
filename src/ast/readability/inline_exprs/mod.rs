//! 受阈值约束的保守表达式内联。
//!
//! 这里只处理非常窄的一类模式：
//! - 单值 local 别名；原生 temp 的语义内联归 HIR
//! - 通用候选只使用一次；稳定 local copy 可原子替换多个顶层语句内的全部后续读取
//! - 使用点出现在 return / 调用参数 / 索引位 / 调用目标
//! - 被内联表达式必须是我们能证明“纯且无元方法副作用”的安全子集
//! - 相邻调用准备 run 中的简单表构造参数，可以随同 receiver/callee 一起收回调用位
//! - 相邻 recovered local run 里，只有末尾 local 仍会跨语句存活的机械链
//! - while/repeat 条件只接收无事件且循环不变的机械 RHS；依赖候选会递归展开，
//!   外部 local/param 则必须未捕获且循环体没有直接写入
//! - generic-for 的 method receiver 允许收回一个紧邻的 recovered binding 别名
//! - repeat body 的 stable-copy 事务把 until 条件计作可改写的尾随 owner，正文、条件与
//!   declaration removal 必须一起提交
//! - 多值 return 顶层只收回 context-safe 或已证明为单值布尔比较的唯一 alias；可变快照仍通过求值前缀证明
//! - 单值 return 短路树只收回最左、必达位置的布尔比较 alias；右臂仍保留原 binding
//! - 稳定 local copy 与无事件 truthiness 快照可跨越无关语句收回；复合/primitive 多 use
//!   仍只在同一 owner 内替换，避免跨业务语句复制概念值
//! - 完整 call-alias run 先于单项相邻内联取得所有权；run 拒绝后，单项规则仍可消费局部安全形状

mod candidate;
mod eval_order;
mod run_facts;
mod use_sites;
use run_facts::CandidateRunFacts;

use std::collections::BTreeSet;

use crate::decompile::ReadabilityOptions;

pub(super) use self::candidate::local_attr_belongs_to_inline_pipeline;
use self::candidate::{
    InlineCandidate, InlineExprRejection, InlinePolicy, inline_candidate, is_lookup_inline_expr,
    stmt_is_alias_initializer_sink, stmt_is_boolean_return_value_sink,
    stmt_is_direct_return_value_sink, stmt_is_multi_return_value_sink,
    stmt_is_terminal_lookup_return_sink, stmt_uses_binding_as_direct_call_callee,
};
use self::use_sites::{
    rewrite_condition_use_sites_with_policy, rewrite_stmt_use_sites_with_policy,
};
use super::super::common::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstLocalAttr,
    AstModule, AstNameRef, AstStmt, AstTargetDialect,
};
use super::ReadabilityContext;
use super::binding_flow::{
    BindingUseIndex, BindingWriteIndex, MutableSnapshotNames, binding_mentions_in_expr,
    expr_reads_binding, expr_reads_name, expr_uses_binding, mutable_snapshot_names_in_block,
    stmt_uses_binding, stmt_writes_name,
};
use super::binding_tree::{
    stmt_has_access_base_binding_use, stmt_has_direct_call_arg_binding_use,
    stmt_has_index_binding_use, stmt_has_nested_binding_use, stmt_has_nested_binding_value_use,
    stmt_stores_binding_in_table,
};
use super::expr_analysis::{collect_stable_copy_snapshot_names, result_cannot_root_collectable};
use super::stmt_plan::{PlannedStmt, materialize_stmt_plan};
use super::walk::{self, AstRewritePass};
use crate::ast::traverse::BlockKind;

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let root_mutable_snapshots = mutable_snapshot_names_in_block(&module.body);
    walk::rewrite_module(
        module,
        &mut InlineExprsPass {
            target: context.target,
            options: context.options,
            mutable_snapshot_stack: vec![root_mutable_snapshots],
        },
    )
}

struct InlineExprsPass {
    target: AstTargetDialect,
    options: ReadabilityOptions,
    mutable_snapshot_stack: Vec<MutableSnapshotNames>,
}

#[derive(Clone, Copy)]
enum AdjacentInlineRejection {
    DebugScope,
    Lifetime,
    ValueArity,
    PolicyBoundary,
}

fn adjacent_inline_rejection(
    candidate: InlineCandidate,
    value: &AstExpr,
    policy: InlinePolicy,
) -> Option<AdjacentInlineRejection> {
    match candidate.expr_rejection_with_policy(value, policy)? {
        InlineExprRejection::DebugScope => Some(AdjacentInlineRejection::DebugScope),
        InlineExprRejection::Lifetime => Some(AdjacentInlineRejection::Lifetime),
        InlineExprRejection::PolicyMismatch
            if matches!(
                policy,
                InlinePolicy::DirectReturnValue | InlinePolicy::MultiReturnValue
            ) && matches!(
                value,
                AstExpr::Call(_) | AstExpr::MethodCall(_) | AstExpr::VarArg
            ) =>
        {
            Some(AdjacentInlineRejection::ValueArity)
        }
        InlineExprRejection::PolicyMismatch
            if matches!(
                policy,
                InlinePolicy::Conservative | InlinePolicy::AliasInitializerChain
            ) && matches!(
                value,
                AstExpr::TableConstructor(_) | AstExpr::FunctionExpr(_)
            ) =>
        {
            Some(AdjacentInlineRejection::Lifetime)
        }
        InlineExprRejection::PolicyMismatch => Some(AdjacentInlineRejection::PolicyBoundary),
    }
}

fn removable_inline_candidate<'a>(
    identified: Option<(InlineCandidate, &'a AstExpr)>,
    stmt_index: usize,
    write_index: &BindingWriteIndex,
) -> Option<(InlineCandidate, &'a AstExpr)> {
    let (candidate, value) = identified?;
    if write_index.has_write_after(stmt_index, candidate.binding()) {
        // 候选拒绝[SemanticBarrier:Scope]：删除仍有后续 direct write 的 local 声明，会把保留赋值渲染成外层/global 写入。
        return None;
    }
    Some((candidate, value))
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
            self.target,
            self.options,
            self.mutable_snapshot_stack
                .last()
                .expect("module scope must remain active"),
            None,
        )
    }

    fn rewrite_repeat_body_and_condition(
        &mut self,
        block: &mut AstBlock,
        condition: &mut AstExpr,
    ) -> bool {
        rewrite_current_block(
            block,
            self.target,
            self.options,
            self.mutable_snapshot_stack
                .last()
                .expect("module scope must remain active"),
            Some(condition),
        )
    }
}

fn rewrite_current_block(
    block: &mut AstBlock,
    target: AstTargetDialect,
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
    mut trailing_condition: Option<&mut AstExpr>,
) -> bool {
    let mut changed = collapse_adjacent_self_call_updates(block, trailing_condition.as_deref());
    changed |= collapse_adjacent_call_alias_runs(
        block,
        target,
        options,
        mutable_snapshots,
        trailing_condition.as_deref(),
    );

    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index =
        BindingUseIndex::for_stmts_with_trailing_expr(&old_stmts, trailing_condition.as_deref());
    let write_index = BindingWriteIndex::for_stmts(&old_stmts);
    let run_facts = CandidateRunFacts::new(&old_stmts);
    let mut stmt_plan = Vec::with_capacity(old_stmts.len());
    let mut index = 0;
    while index < old_stmts.len() {
        let Some(next_stmt) = old_stmts.get(index + 1) else {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        };

        let Some((candidate, value)) =
            removable_inline_candidate(run_facts.candidate_at(index), index, &write_index)
        else {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        };
        if index.checked_sub(1).is_some_and(|run_start| {
            super::function_sugar::run_belongs_to_method_alias_owner(
                &old_stmts,
                run_start,
                index + 1,
                &use_index,
                &write_index,
                mutable_snapshots,
            )
        }) {
            // Preserve the field alias until function-sugar can consume the receiver snapshot,
            // lookup, and call atomically. Inlining only the lookup loses the method proof.
            // 候选拒绝[LayerBoundary]：Deferred function-sugar 的 method-alias owner 必须
            // 原子消费 receiver + field alias + call；它在 Normal inline-exprs 收敛后运行，
            // 成功时发出 StatementAdjacency/ExprShape，使调度器返回 Normal cleanup/inline。
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        if matches!(value, AstExpr::Call(_) | AstExpr::MethodCall(_))
            && stmt_stores_binding_in_table(next_stmt, candidate.binding())
        {
            // Keep a call result local while it is the table's only strong root.  A later
            // rawset/clear may otherwise make the generated expression collectable earlier.
            // 候选拒绝[SemanticBarrier:Lifetime]：`local x=f(); t[k]=x` 中 local 可能是弱表外唯一强 root，内联会让 `x` 在 rawset/clear 前提前可回收。
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        let policy = if stmt_uses_binding_as_direct_call_callee(next_stmt, candidate.binding()) {
            InlinePolicy::AdjacentCallResultCallee
        } else if stmt_is_alias_initializer_sink(next_stmt) {
            InlinePolicy::AliasInitializerChain
        } else if stmt_is_direct_return_value_sink(next_stmt) {
            InlinePolicy::DirectReturnValue
        } else if stmt_is_multi_return_value_sink(next_stmt, candidate.binding()) {
            InlinePolicy::MultiReturnValue
        } else if stmt_is_boolean_return_value_sink(next_stmt, candidate.binding()) {
            InlinePolicy::BooleanReturnValue
        } else {
            InlinePolicy::Conservative
        };
        if matches!(policy, InlinePolicy::AliasInitializerChain)
            && alias_initializer_shortens_root(&old_stmts, index + 1, candidate, &write_index)
        {
            // 候选拒绝[SemanticBarrier:Lifetime]：删除 source declaration 后，sink 的后续
            // 覆盖会提前释放原 source root。只有 `if sink == nil then sink = ... end`
            // 能证明发生覆盖的路径旧值必为 nil；regress_36 是该安全反例。
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        if matches!(policy, InlinePolicy::AliasInitializerChain)
            && candidate::is_lookup_inline_expr(value)
            && stmt_starts_lookup_mechanical_run(
                &old_stmts,
                index,
                candidate.binding(),
                run_facts.end(index),
            )
        {
            // 这里故意不提前把 lookup 链压成“下一条 local 的初始化式”：
            // `local item = items[i]; local weight = item.weight; sum = sum + weight`
            // 如果太早收成 `local weight = items[i].weight`，后面的机械 run 就只剩一层，
            // 无法再判断“整条链都只是脚手架”。让它留到 run-collapse 一次性处理，
            // 才能既收回 for-loop 里的机械局部，又保住 return 场景下的阶段 local。
            // 这只是同一个 inline-exprs transaction 内的 helper 交接：相邻单项 scanner
            // 不拆开完整 run，最后的机械 run 规划会在本次调用中
            // 重新判断整段是否值得且能够原子收回；它不是跨 layer 的候选拒绝。
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
        if matches!(
            effective_policy,
            InlinePolicy::DirectReturnValue
                | InlinePolicy::MultiReturnValue
                | InlinePolicy::BooleanReturnValue
        ) && binding_mentions_in_expr(value).contains(&candidate.binding())
        {
            // A closure capture or self-reference would still depend on the local's lexical
            // identity after the declaration is removed.  The ordinary use index starts after
            // this declaration, so reject that case explicitly before the unique-use check.
            // 候选拒绝[SemanticBarrier:Scope]：`local x=function() return x end; return x` 删除声明会改变 closure 捕获的词法身份。
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        if let Some(rejection) = (!allows_special_lookup_access_base)
            .then(|| adjacent_inline_rejection(candidate, value, effective_policy))
            .flatten()
        {
            match rejection {
                AdjacentInlineRejection::DebugScope => {
                    // 候选拒绝[SemanticBarrier:DebugScope]：删除 DebugHinted local 会改变
                    // 调用中 debug.getlocal 可观察的名字与作用域（regress_351）。
                }
                AdjacentInlineRejection::Lifetime => {
                    // 候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot 必须保留原强根区间；
                    // 普通 recovered allocation 移入非终态 sink 也会缩短原 local root。
                }
                AdjacentInlineRejection::ValueArity => {
                    // 候选拒绝[SemanticBarrier:ValueArity]：裸 call/method/vararg 从单值
                    // initializer 移到 return 开放尾位可能重新展开。
                }
                AdjacentInlineRejection::PolicyBoundary => {
                    // 候选拒绝[PolicyBoundary]：Error、非本 policy 所有的表达式形状与超过
                    // 当前展示集合的候选留给 stable-copy、mechanical-run 或 terminal owner。
                }
            }
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        let suffix_uses = use_index.count_uses_in_suffix(index + 1, candidate.binding());
        if suffix_uses == 0 {
            // 没有 use site 就不是表达式内联事务；本轮之前的
            // cleanup 已消费可安全丢弃的 initializer/裸 call，仍保留者具有 lookup、
            // metamethod、allocation 或失败证据等可观察求值，不能在这里删除。
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        if suffix_uses > 1 {
            // 候选拒绝[SemanticBarrier:EvalCount]：多次使用会复制 RHS，如 `local x=f(); g(x,x)` 会把 `f()` 从一次变两次。
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        if inline_crosses_evaluation_boundary(
            value,
            next_stmt,
            candidate.binding(),
            mutable_snapshots,
            effective_policy,
        ) {
            // 候选拒绝[SemanticBarrier:EvalOrder]：producer 不能跨过 sink 的调用、lookup
            // 或 mutable snapshot；如 `v=side(); guard()==v` 不等价于 `guard()==side()`。
            // 候选拒绝[SemanticBarrier:EvalTime]：while/repeat condition 会逐轮重求值非稳定 RHS。
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
                    // 候选拒绝[PolicyBoundary]：已证明的 call-arg/callee 位置仍可能超过展示复杂度预算；
                    stmt_plan.push(PlannedStmt::Original(index));
                    index += 1;
                    continue;
                }
            } else {
                // 候选拒绝[PolicyBoundary]：精确 use-site 仍可能超过对应展示复杂度预算；
                // bare stable copy 及其直接 nested-block use 由
                // 本函数稍后的 copy-inline 原子消费；其它 policy 不拥有该位置。
                // 候选拒绝[SemanticBarrier:Capture]：FunctionExpr capture 需要 alias 的
                // 独立 cell identity，不能把捕获元数据改写成 source binding。
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
    changed |= collapse_stable_copy_aliases(
        block,
        target,
        options,
        mutable_snapshots,
        trailing_condition.as_deref_mut(),
    );
    changed |= collapse_terminal_call_result_alias_runs(
        block,
        target,
        options,
        mutable_snapshots,
        trailing_condition.as_deref(),
    );
    for kind in [
        MechanicalRunKind::TerminalLocal,
        MechanicalRunKind::FollowingStmt,
    ] {
        changed |= collapse_mechanical_runs(
            block,
            kind,
            target,
            options,
            mutable_snapshots,
            trailing_condition.as_deref(),
        );
    }
    changed
}

fn alias_initializer_shortens_root(
    stmts: &[AstStmt],
    sink_index: usize,
    source: InlineCandidate,
    write_index: &BindingWriteIndex,
) -> bool {
    if !source.initializer_may_affect_collectable_lifetime() {
        return false;
    }
    let Some((sink, _)) = stmts.get(sink_index).and_then(inline_candidate) else {
        return false;
    };
    write_index.has_write_after(sink_index, sink.binding())
        && !alias_sink_has_nil_only_overwrite(stmts, sink_index, sink.binding(), write_index)
}

fn alias_sink_has_nil_only_overwrite(
    stmts: &[AstStmt],
    sink_index: usize,
    sink: AstBindingRef,
    write_index: &BindingWriteIndex,
) -> bool {
    let Some(fallback_index) = sink_index.checked_add(1) else {
        return false;
    };
    if !write_index.writes_only_at(fallback_index, sink) {
        return false;
    }
    let Some(AstStmt::If(if_stmt)) = stmts.get(fallback_index) else {
        return false;
    };
    if if_stmt.else_block.is_some() || !condition_is_binding_nil(&if_stmt.cond, sink) {
        return false;
    }
    let [AstStmt::Assign(assign)] = if_stmt.then_block.stmts.as_slice() else {
        return false;
    };
    matches!(assign.targets.as_slice(), [AstLValue::Name(name)] if sink.matches_name_ref(name))
        && assign.values.len() == 1
}

fn condition_is_binding_nil(condition: &AstExpr, binding: AstBindingRef) -> bool {
    let AstExpr::Binary(binary) = condition else {
        return false;
    };
    if binary.op != crate::ast::common::AstBinaryOpKind::Eq {
        return false;
    }
    (matches!(&binary.lhs, AstExpr::Var(name) if binding.matches_name_ref(name))
        && matches!(&binary.rhs, AstExpr::Nil))
        || (matches!(&binary.rhs, AstExpr::Var(name) if binding.matches_name_ref(name))
            && matches!(&binary.lhs, AstExpr::Nil))
}

/// 收回跨越无关语句的稳定 local copy 与无事件 truthiness 快照。
///
/// 这条规则与相邻表达式内联故意分开：相邻规则可以凭 sink 形状证明调用/lookup 的
/// 求值前缀，而这里只接受 local/param、primitive 以及由它们组成的 `not` / `and` / `or`。
/// 复合快照的所有依赖在候选之后没有 direct write 或 closure capture，因此 use 点重复读取
/// 不改变值；若逻辑结果是 collectable，未改写的 source binding 也会继续持有同一 root。
/// 直接 local copy 另有精确 repeat trailing handoff：source 在 use 后写入时由 target 接管
/// root 直到 `until` 条件。两条路径都不改变调用顺序或对象存活期。
fn collapse_stable_copy_aliases(
    block: &mut AstBlock,
    target: AstTargetDialect,
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
    mut trailing_condition: Option<&mut AstExpr>,
) -> bool {
    let mut stmts = std::mem::take(&mut block.stmts);
    let use_index =
        BindingUseIndex::for_stmts_with_trailing_expr(&stmts, trailing_condition.as_deref());
    let write_index = BindingWriteIndex::for_stmts(&stmts);
    // 本批只替换表达式，声明删除延迟到批末；label、终结语句和顶层下标均保持不变。
    // 因此所有 handoff 候选可按需共用当前快照的支配事实。
    let control_flow = std::cell::OnceCell::new();
    let mut removed = vec![false; stmts.len()];

    for (candidate_index, is_removed) in removed.iter_mut().enumerate() {
        let Some((candidate, value)) = removable_inline_candidate(
            inline_candidate(&stmts[candidate_index]),
            candidate_index,
            &write_index,
        ) else {
            continue;
        };
        if [candidate_index + 1, candidate_index + 2]
            .into_iter()
            .any(|sink_index| {
                super::function_sugar::run_belongs_to_method_alias_owner(
                    &stmts,
                    candidate_index,
                    sink_index,
                    &use_index,
                    &write_index,
                    mutable_snapshots,
                )
            })
        {
            // 候选拒绝[LayerBoundary]：Deferred function-sugar 的 method-alias owner 原子
            // 消费 receiver snapshot 与 direct/field method sink；它在 Normal 收敛后运行，
            // 并以 StatementAdjacency/ExprShape invalidation 触发后续 Normal cleanup/inline。
            continue;
        }
        if candidate.origin() != super::super::common::AstLocalOrigin::Recovered {
            // 候选拒绝[SemanticBarrier:DebugScope]：删除 DebugHinted 会改变 debug.getlocal 可观察的作用域（regress_351）；候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot 若在 use 后仍处于原词法作用域，会延后弱表消失或 `__gc`。
            continue;
        }
        let mut snapshot_names = BTreeSet::new();
        if !collect_stable_copy_snapshot_names(value, &mut snapshot_names, target) {
            // 候选拒绝[SemanticBarrier:EvalTime]：调用/lookup 从声明点搬到 use 会改变可观察时点；
            // 候选拒绝[SemanticBarrier:EvalCount]：多 use 会复制调用/lookup；
            // 候选拒绝[SemanticBarrier:ValueArity]：vararg 搬入新位置可能重新打开值宽；
            // 候选拒绝[SemanticBarrier:Metamethod]：算术、比较和 lookup 可能触发协议；
            // 候选拒绝[SemanticBarrier:Lifetime]：分配值或 logical operand 可能改变对象 identity/root 生命周期（regress_387）；
            // 候选拒绝[SemanticBarrier:EvalTime]：global/upvalue 可能由当前函数外部改写，
            // 重读不等价于声明点快照；带名字的算术/比较也缺少稳定 operand 类型。
            // 候选拒绝[TargetConstraint]：非有限 number 与 Int64/UInt64/Vector/Complex 的
            // 源码物化可能增加运算或对象 identity；目标已定义的 literal-only 运算已放行。
            // Temp/Error 分别归 HIR/materialize 与错误输出 owner；
            // call/lookup/table/closure 不是 stable-copy。
            continue;
        }
        if mutable_snapshots.contains(&candidate.binding().to_name_ref()) {
            // 候选拒绝[SemanticBarrier:EvalOrder]：captured/mutable snapshot 的值可能被中间调用改写，直接替换会读取新值。
            continue;
        }
        if snapshot_names
            .iter()
            .any(|name| mutable_snapshots.contains(name))
        {
            // 候选拒绝[SemanticBarrier:EvalOrder]：sink 前的未知 closure 调用可能经可写
            // capture 改写声明点快照。
            continue;
        }
        let use_stmt_indices =
            use_index.use_stmt_indices_in_suffix(candidate_index + 1, candidate.binding());
        if use_stmt_indices.is_empty() {
            // 没有读取就不存在 copy-inline site；cleanup 在
            // inline-exprs 之前及其 invalidation 后重跑，负责删除无 use 的安全 initializer。
            continue;
        }
        if !matches!(value, AstExpr::Var(_)) {
            let last_use = use_stmt_indices
                .last()
                .copied()
                .expect("uses are non-empty");
            if snapshot_names.iter().any(|name| {
                write_index.name_has_write_in_range(candidate_index + 1, last_use, name)
            }) {
                // 候选拒绝[SemanticBarrier:EvalOrder]：声明后、最后 use 前的 direct write 会让内联表达式读取新值，regress_387 的 written dependency 可观察差异。
                continue;
            }
            if matches!(stmts[last_use], AstStmt::While(_) | AstStmt::Repeat(_))
                && snapshot_names
                    .iter()
                    .any(|name| write_index.stmt_directly_writes_name(last_use, name))
            {
                // 候选拒绝[SemanticBarrier:EvalTime]：while/repeat condition 会在 body write
                // 后逐轮重读 source；声明点 snapshot 不能改成循环时读取（regress_387）。
                continue;
            }
            if !result_cannot_root_collectable(value)
                && snapshot_names
                    .iter()
                    .any(|name| write_index.name_has_write_after(candidate_index, name))
            {
                // 候选拒绝[SemanticBarrier:Lifetime]：可能返回 operand 对象的 logical 快照必须在 source 覆盖后继续保留旧 root；删除 alias 会提前释放它。
                continue;
            }
        }
        if use_stmt_indices.len() > 1 && !matches!(value, AstExpr::Var(_)) {
            // 候选拒绝[PolicyBoundary]：把 primitive 复制进多个业务语句会抹掉复用概念并
            // 增加重复；同一 owner 仍可内联，多 owner 只删除纯名字 alias（regress_80/316）。
            continue;
        }

        let mut trailing_root_handoff = None;
        if let AstExpr::Var(source_name) = value {
            match source_name {
                AstNameRef::Param(_) => {
                    if write_index.name_has_write_after(candidate_index, source_name) {
                        // 候选拒绝[SemanticBarrier:EvalOrder]：参数后续写入会让 alias 保存旧值；
                        // 候选拒绝[SemanticBarrier:Lifetime]：旧值若是对象，alias 还保存旧 root。
                        // 参数没有 AstBindingRef，当前不走 repeat handoff。
                        continue;
                    }
                }
                AstNameRef::Local(_) | AstNameRef::SyntheticLocal(_) => {
                    let source_binding = AstBindingRef::from_name_ref(source_name)
                        .expect("local-like name must have an AST binding identity");
                    // A bound local/synthetic name can only appear while its lexical declaration
                    // is active, so the AST binding identity itself supplies the dominance proof.
                    if write_index.has_write_after(candidate_index, source_binding) {
                        trailing_root_handoff = (use_stmt_indices.len() == 1
                            && use_stmt_indices[0] < stmts.len())
                        .then(|| {
                            stable_copy_trailing_root_handoff(
                                &stmts,
                                trailing_condition.as_deref(),
                                &write_index,
                                mutable_snapshots,
                                candidate_index..=use_stmt_indices[0],
                                source_binding,
                                &control_flow,
                            )
                        })
                        .flatten();
                    }
                    if write_index.has_write_after(candidate_index, source_binding)
                        && trailing_root_handoff.is_none()
                    {
                        // 候选拒绝[SemanticBarrier:EvalOrder]：source 写入会让 alias 保存旧快照；
                        // 候选拒绝[SemanticBarrier:Lifetime]：旧值若是对象，alias 还保存旧 root。
                        // 只有单 owner 的精确 repeat handoff 已证明安全。
                        continue;
                    }
                }
                AstNameRef::Environment
                | AstNameRef::Global(_)
                | AstNameRef::Upvalue(_)
                | AstNameRef::Temp(_) => {
                    unreachable!("stable-copy expression filter only admits lexical names")
                }
            }
        }

        let replacement = value.clone();
        let mut rewritten_stmts = Vec::with_capacity(use_stmt_indices.len());
        let mut rewritten_condition = None;
        let all_rewritten = use_stmt_indices.iter().all(|use_stmt_index| {
            if *use_stmt_index == stmts.len() {
                let Some(condition) = trailing_condition.as_deref() else {
                    return false;
                };
                let mut rewritten = condition.clone();
                if !rewrite_condition_use_sites_with_policy(
                    &mut rewritten,
                    candidate,
                    &replacement,
                    options,
                    InlinePolicy::StableCopy,
                ) || expr_uses_binding(&rewritten, candidate.binding())
                {
                    return false;
                }
                rewritten_condition = Some(rewritten);
                return true;
            }
            if *use_stmt_index > stmts.len() {
                return false;
            }
            let mut rewritten_stmt = stmts[*use_stmt_index].clone();
            let rewritten = trailing_root_handoff.as_ref().is_some_and(|handoff| {
                handoff.structured
                    && handoff.use_stmt_index == *use_stmt_index
                    && rewrite_structured_handoff_stmt(
                        &mut rewritten_stmt,
                        candidate.binding(),
                        &replacement,
                        &handoff.target,
                    )
            }) || rewrite_stmt_use_sites_with_policy(
                &mut rewritten_stmt,
                candidate,
                &replacement,
                options,
                InlinePolicy::StableCopy,
            );
            if !rewritten || stmt_uses_binding(&rewritten_stmt, candidate.binding()) {
                return false;
            }
            rewritten_stmts.push((*use_stmt_index, rewritten_stmt));
            true
        });
        if all_rewritten {
            // 候选接受：所有顶层 owner 都已在副本中完整替换且没有 residual use；统一写回
            // 后再删除 recovered 声明；primitive/local 与稳定 truthiness 快照的值和 root
            // 均由未改写依赖保持，且没有求值事件被移动。
            for (use_stmt_index, rewritten_stmt) in rewritten_stmts {
                stmts[use_stmt_index] = rewritten_stmt;
            }
            if let Some(rewritten_condition) = rewritten_condition {
                *trailing_condition
                    .as_deref_mut()
                    .expect("planned trailing rewrite must retain its condition") =
                    rewritten_condition;
            }
            *is_removed = true;
        }
    }

    let changed = removed.contains(&true);
    block.stmts = stmts
        .into_iter()
        .enumerate()
        .filter_map(|(index, stmt)| (!removed[index]).then_some(stmt))
        .collect();
    changed
}

struct StableCopyRootHandoff {
    use_stmt_index: usize,
    target: AstNameRef,
    structured: bool,
}

fn stable_copy_trailing_root_handoff(
    stmts: &[AstStmt],
    trailing_condition: Option<&AstExpr>,
    write_index: &BindingWriteIndex,
    mutable_snapshots: &MutableSnapshotNames,
    interval: std::ops::RangeInclusive<usize>,
    source: AstBindingRef,
    control_flow: &std::cell::OnceCell<Option<super::control_flow::RepeatBodyControlFlow>>,
) -> Option<StableCopyRootHandoff> {
    let (candidate_index, use_stmt_index) = (*interval.start(), *interval.end());
    let candidate = inline_candidate(&stmts[candidate_index])
        .expect("planned stable-copy handoff must retain its candidate declaration")
        .0
        .binding();
    if !write_index.writes_start_after(use_stmt_index, source) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：source 若非只在 handoff 后写入，alias 与 source 在 use 点不保证同值。
        return None;
    }
    let (target, structured) = match &stmts[use_stmt_index] {
        AstStmt::Assign(assign) => {
            let Some(target) = direct_assign_handoff_target(assign, candidate) else {
                // 候选拒绝[SemanticBarrier:Lifetime]：candidate 只作为 nested value 使用时，
                // call/constructor/table store 不保证在 source 覆盖后继续持有同一强 root。
                return None;
            };
            (target, false)
        }
        AstStmt::LocalDecl(local_decl) => {
            let Some(target) = direct_local_handoff_target(local_decl, candidate) else {
                // 候选拒绝[SemanticBarrier:Lifetime]：nested initializer 不等同于把旧值
                // 直接交给一个可追踪至 latch 的 local binding。
                return None;
            };
            (target, false)
        }
        AstStmt::If(if_stmt) => (structured_if_handoff_target(if_stmt, candidate)?, true),
        AstStmt::DoBlock(block) => (structured_do_handoff_target(block, candidate)?, true),
        AstStmt::GlobalDecl(_) => {
            // 候选拒绝[SemanticBarrier:Metamethod]：global declaration/store 可经 _ENV
            // __newindex 截获而不保存值，不能充当强 root handoff。
            return None;
        }
        AstStmt::Return(_) => {
            // 合法 AST block 的 return 是终结语句，不会同时
            // 满足“同一 block 内 source 在其后写入”的 handoff 入口条件。
            return None;
        }
        AstStmt::While(_)
        | AstStmt::Repeat(_)
        | AstStmt::NumericFor(_)
        | AstStmt::GenericFor(_) => {
            // 候选拒绝[SemanticBarrier:ControlFlow]：while/for 可以零次执行，repeat 首轮
            // continue 也可绕过内部 handoff 后直接求值 inner latch；删除 alias 会让这些
            // 路径在 source 覆盖前没有旧值 carrier。迭代 owner 不能按单次 statement 支配处理。
            // 候选拒绝[SemanticBarrier:Lifetime]：上述绕过路径会让旧对象 root 在外层 latch
            // 前提前消失，弱表或 `__gc` 可观察。
            return None;
        }
        AstStmt::CallStmt(_) => {
            // 候选拒绝[SemanticBarrier:Lifetime]：callee 不保证保存参数强 root；调用返回后
            // 覆盖 source 时，原 alias 仍存活而实参可能已经失活。
            return None;
        }
        AstStmt::FunctionDecl(_) | AstStmt::LocalFunctionDecl(_) => {
            // 候选拒绝[SemanticBarrier:Capture]：把 closure capture 从 snapshot binding 改为
            // source binding 后，后续 source write 会改变 closure 观察值。
            return None;
        }
        AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => {
            unreachable!("a non-expression statement cannot own the candidate's unique use")
        }
    };
    match &target {
        AstNameRef::Global(_) => {
            // 候选拒绝[SemanticBarrier:Metamethod]：global store 可经 _ENV.__newindex
            // 截获而不保存值，不能充当强 root handoff。
            return None;
        }
        AstNameRef::Upvalue(_) | AstNameRef::Environment => {
            // 候选拒绝[SemanticBarrier:Capture]：sibling closure 可在 handoff 后、latch 前
            // 覆盖同一 upvalue；当前函数内的 write index 无法把该外部写排除，target 因而
            // 不保证继续承载旧快照/root。
            return None;
        }
        AstNameRef::Param(_)
        | AstNameRef::Local(_)
        | AstNameRef::Temp(_)
        | AstNameRef::SyntheticLocal(_) => {}
    }
    if mutable_snapshots.contains(&target) {
        // 候选拒绝[SemanticBarrier:Capture]：target 被 closure 捕获时，接管前后的 binding 写入可被观察。
        return None;
    }
    let local_like_target = AstBindingRef::from_name_ref(&target).is_some();
    if structured && !local_like_target {
        return None;
    }
    if local_like_target {
        let cfg = control_flow
            .get_or_init(|| super::control_flow::RepeatBodyControlFlow::new(stmts))
            .as_ref()?;
        if !cfg.dominates(candidate_index, use_stmt_index)
            || !cfg.dominates(use_stmt_index, cfg.exit())
            || write_index
                .name_write_indices_after(use_stmt_index, &source.to_name_ref())
                .iter()
                .any(|&write_stmt_index| !cfg.dominates(use_stmt_index, write_stmt_index))
        {
            // 候选拒绝[SemanticBarrier:ControlFlow]：goto 可绕过 alias 初始化或 handoff，
            // 使 source 覆盖/latch 路径重读新值或失去旧 root；block CFG 必须证明双重支配。
            return None;
        }
    } else {
        let goto_index = super::control_flow::BlockGotoIndex::new(stmts);
        if goto_index.has_external_entry(candidate_index, use_stmt_index + 1)
            || stmts[candidate_index..=use_stmt_index]
                .iter()
                .any(super::control_flow::stmt_contains_label_or_goto)
        {
            // Param carriers retain the pre-existing lexical interval proof: without a
            // binding identity, neither an internal edge nor an external entry may bypass
            // snapshot initialization or the handoff.
            return None;
        }
    }
    if write_index.name_has_write_after(use_stmt_index, &target) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：target 在 latch 前再次写入时不能继续承载同一快照/root。
        return None;
    }
    let Some(condition) = trailing_condition else {
        // 候选拒绝[SemanticBarrier:Lifetime]：没有 repeat latch 的保留读取时，后续 cleanup
        // 可删除 dead carrier assignment；原 alias 本会让旧对象活到词法 block 末尾。
        return None;
    };
    if !expr_reads_name(condition, &target) {
        // 候选拒绝[SemanticBarrier:Lifetime]：cleanup 会继续删除 dead target；只有 latch
        // 的保留读取能在当前 pass 组合中保证 carrier 持有旧 root 到 repeat 尾端。
        return None;
    }
    Some(StableCopyRootHandoff {
        use_stmt_index,
        target,
        structured,
    })
}

#[derive(Clone, Eq, PartialEq)]
enum StructuredHandoffState {
    Pending,
    HandedOff(AstNameRef),
    Terminated,
}

fn structured_if_handoff_target(
    if_stmt: &super::super::common::AstIf,
    candidate: AstBindingRef,
) -> Option<AstNameRef> {
    if super::control_flow::block_contains_label_or_goto(&if_stmt.then_block)
        || if_stmt
            .else_block
            .as_ref()
            .is_some_and(super::control_flow::block_contains_label_or_goto)
    {
        // 候选拒绝[SemanticBarrier:ControlFlow]：top-level CFG 只能证明 structured owner
        // 整体支配；外部 goto 可进入内部 label 并绕过 owner 内的 handoff。
        return None;
    }
    let then_state = structured_handoff_block_outcome(&if_stmt.then_block, candidate)?;
    let else_state = if let Some(else_block) = &if_stmt.else_block {
        structured_handoff_block_outcome(else_block, candidate)?
    } else {
        StructuredHandoffState::Pending
    };
    common_structured_handoff_target([then_state, else_state])
}

fn structured_do_handoff_target(block: &AstBlock, candidate: AstBindingRef) -> Option<AstNameRef> {
    if super::control_flow::block_contains_label_or_goto(block) {
        // 候选拒绝[SemanticBarrier:ControlFlow]：外部 goto 可直接进入 do 内部 label，
        // 顶层 owner 的支配关系不能证明 owner 内的 handoff 已执行。
        return None;
    }
    common_structured_handoff_target([structured_handoff_block_outcome(block, candidate)?])
}

fn common_structured_handoff_target(
    outcomes: impl IntoIterator<Item = StructuredHandoffState>,
) -> Option<AstNameRef> {
    let mut targets = outcomes.into_iter().filter_map(|state| match state {
        StructuredHandoffState::Terminated => None,
        StructuredHandoffState::Pending => Some(None),
        StructuredHandoffState::HandedOff(target) => Some(Some(target)),
    });
    let target = targets.next().flatten()?;
    targets
        .all(|other| other.as_ref() == Some(&target))
        .then_some(target)
}

fn structured_handoff_block_outcome(
    block: &AstBlock,
    candidate: AstBindingRef,
) -> Option<StructuredHandoffState> {
    let mut state = StructuredHandoffState::Pending;
    for stmt in &block.stmts {
        if let Some(target) = direct_handoff_target(stmt, candidate) {
            if state != StructuredHandoffState::Pending {
                return None;
            }
            state = StructuredHandoffState::HandedOff(target);
            continue;
        }
        if stmt_uses_binding(stmt, candidate) {
            return None;
        }
        if let StructuredHandoffState::HandedOff(target) = &state
            && stmt_writes_name(stmt, target)
        {
            return None;
        }
        // 整棵语句已排除 candidate 读取和 target 写入，嵌套路径不能产生不同的交接
        // 状态，只能保留或终止当前状态；控制归约无需为每个子块重建读写索引。
        if !handoff_stmt_may_continue(stmt, state != StructuredHandoffState::Pending)? {
            return Some(StructuredHandoffState::Terminated);
        }
    }
    Some(state)
}

fn handoff_block_may_continue(block: &AstBlock, handed_off: bool) -> Option<bool> {
    for stmt in &block.stmts {
        if !handoff_stmt_may_continue(stmt, handed_off)? {
            return Some(false);
        }
    }
    Some(true)
}

fn handoff_stmt_may_continue(stmt: &AstStmt, handed_off: bool) -> Option<bool> {
    match stmt {
        AstStmt::If(if_stmt) => {
            let then_continues = handoff_block_may_continue(&if_stmt.then_block, handed_off)?;
            let else_continues = match &if_stmt.else_block {
                Some(block) => handoff_block_may_continue(block, handed_off)?,
                None => true,
            };
            Some(then_continues || else_continues)
        }
        AstStmt::DoBlock(block) => handoff_block_may_continue(block, handed_off),
        AstStmt::Return(_) | AstStmt::Break => Some(false),
        AstStmt::Continue if handed_off => Some(false),
        AstStmt::Continue | AstStmt::Goto(_) => None,
        _ => Some(true),
    }
}

fn direct_handoff_target(stmt: &AstStmt, candidate: AstBindingRef) -> Option<AstNameRef> {
    match stmt {
        AstStmt::Assign(assign) => direct_assign_handoff_target(assign, candidate),
        AstStmt::LocalDecl(local_decl) => direct_local_handoff_target(local_decl, candidate),
        _ => None,
    }
}

fn direct_assign_handoff_target(
    assign: &super::super::common::AstAssign,
    candidate: AstBindingRef,
) -> Option<AstNameRef> {
    let value_index = unique_direct_candidate_value_index(&assign.values, candidate)?;
    let AstLValue::Name(target) = assign.targets.get(value_index)? else {
        return None;
    };
    (assign
        .targets
        .iter()
        .filter(|other| matches!(other, AstLValue::Name(name) if name == target))
        .count()
        == 1)
        .then(|| target.clone())
}

fn direct_local_handoff_target(
    local_decl: &super::super::common::AstLocalDecl,
    candidate: AstBindingRef,
) -> Option<AstNameRef> {
    let value_index = unique_direct_candidate_value_index(&local_decl.values, candidate)?;
    Some(local_decl.bindings.get(value_index)?.id.to_name_ref())
}

fn unique_direct_candidate_value_index(
    values: &[AstExpr],
    candidate: AstBindingRef,
) -> Option<usize> {
    let mut indices = values.iter().enumerate().filter_map(|(index, value)| {
        matches!(value, AstExpr::Var(name) if candidate.matches_name_ref(name)).then_some(index)
    });
    let index = indices.next()?;
    indices.next().is_none().then_some(index)
}

fn rewrite_structured_handoff_stmt(
    stmt: &mut AstStmt,
    candidate: AstBindingRef,
    replacement: &AstExpr,
    target: &AstNameRef,
) -> bool {
    if direct_handoff_target(stmt, candidate).as_ref() == Some(target) {
        let values = match stmt {
            AstStmt::Assign(assign) => &mut assign.values,
            AstStmt::LocalDecl(local_decl) => &mut local_decl.values,
            _ => unreachable!("direct handoff target requires assignment-like statement"),
        };
        let index = unique_direct_candidate_value_index(values, candidate)
            .expect("validated handoff must retain its unique candidate value");
        values[index] = replacement.clone();
        return true;
    }
    match stmt {
        AstStmt::If(if_stmt) => {
            let mut changed = rewrite_structured_handoff_block(
                &mut if_stmt.then_block,
                candidate,
                replacement,
                target,
            );
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |=
                    rewrite_structured_handoff_block(else_block, candidate, replacement, target);
            }
            changed
        }
        AstStmt::DoBlock(block) => {
            rewrite_structured_handoff_block(block, candidate, replacement, target)
        }
        _ => false,
    }
}

fn rewrite_structured_handoff_block(
    block: &mut AstBlock,
    candidate: AstBindingRef,
    replacement: &AstExpr,
    target: &AstNameRef,
) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        changed |= rewrite_structured_handoff_stmt(stmt, candidate, replacement, target);
    }
    changed
}

fn inline_crosses_evaluation_boundary(
    value: &AstExpr,
    next_stmt: &AstStmt,
    binding: AstBindingRef,
    mutable_snapshots: &MutableSnapshotNames,
    policy: InlinePolicy,
) -> bool {
    if matches!(policy, InlinePolicy::BooleanReturnValue) && is_lookup_inline_expr(value) {
        if stmt_is_terminal_lookup_return_sink(next_stmt, binding) {
            // The lookup is the first and only observable producer in the return expression.  The
            // remaining short-circuit suffix is context-safe, so the expression temporary itself
            // carries the value through the same truthiness/return operation as the old local root.
            return false;
        }
        // 候选拒绝[SemanticBarrier:Lifetime]：非终态短路尾部可调用或分配；删除 lookup
        // alias 后，左值临时槽不保证把旧对象 root 保留到右臂完成，弱表或 `__gc` 可观察。
        return true;
    }
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

mod runs;
use runs::*;
