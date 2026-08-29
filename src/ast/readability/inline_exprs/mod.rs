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
//! - repeat body 的 use index 把 until 条件计作尾随表达式，不删除仍对条件可见的 local
//! - 多值 return 顶层只收回 context-safe 或已证明为单值布尔比较的唯一 alias；可变快照仍通过求值前缀证明
//! - 单值 return 短路树只收回最左、必达位置的布尔比较 alias；右臂仍保留原 binding
//! - 稳定 local copy 与无事件 truthiness 快照可跨越无关语句收回；复合/primitive 多 use
//!   仍只在同一 owner 内替换，避免跨业务语句复制概念值
//! - 完整 call-alias run 先于单项相邻内联取得所有权；run 拒绝后，单项规则仍可消费局部安全形状

mod candidate;
mod eval_order;
mod use_sites;

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::ReadabilityOptions;

use self::candidate::{
    InlineCandidate, InlinePolicy, inline_candidate, is_lookup_inline_expr,
    stmt_is_adjacent_call_result_sink, stmt_is_alias_initializer_sink,
    stmt_is_boolean_return_value_sink, stmt_is_direct_return_value_sink,
    stmt_is_multi_return_value_sink, stmt_is_terminal_lookup_return_sink,
};
use self::use_sites::rewrite_stmt_use_sites_with_policy;
use super::super::common::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstFunctionName, AstLValue,
    AstLocalAttr, AstLocalOrigin, AstModule, AstNameRef, AstStmt,
};
use super::ReadabilityContext;
use super::binding_flow::{
    BindingUseIndex, MutableSnapshotNames, binding_mentions_in_expr,
    mutable_snapshot_names_in_block,
};
use super::binding_ref::binding_from_name_ref;
use super::binding_tree::{
    expr_references_binding, stmt_has_access_base_binding_use,
    stmt_has_direct_call_arg_binding_use, stmt_has_index_binding_use, stmt_has_nested_binding_use,
    stmt_has_nested_binding_value_use, stmt_stores_binding_in_table,
};
use super::expr_analysis::collect_stable_copy_snapshot_names;
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
    write_bounds_by_binding: BTreeMap<AstBindingRef, (usize, usize)>,
    write_bounds_by_name: BTreeMap<AstNameRef, (usize, usize)>,
    direct_write_names_by_stmt: Vec<BTreeSet<AstNameRef>>,
}

impl BindingWriteIndex {
    fn for_stmts(stmts: &[AstStmt]) -> Self {
        let mut index = Self {
            write_bounds_by_binding: BTreeMap::new(),
            write_bounds_by_name: BTreeMap::new(),
            direct_write_names_by_stmt: vec![BTreeSet::new(); stmts.len()],
        };
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
        self.write_bounds_by_binding
            .entry(binding)
            .and_modify(|bounds| bounds.1 = stmt_index)
            .or_insert((stmt_index, stmt_index));
    }

    fn record_name(&mut self, stmt_index: usize, name: &AstNameRef) {
        self.direct_write_names_by_stmt[stmt_index].insert(name.clone());
        self.write_bounds_by_name
            .entry(name.clone())
            .and_modify(|bounds| bounds.1 = stmt_index)
            .or_insert((stmt_index, stmt_index));
        if let Some(binding) = binding_from_name_ref(name) {
            self.record(stmt_index, binding);
        }
    }

    fn stmt_directly_writes_name(&self, stmt_index: usize, name: &AstNameRef) -> bool {
        self.direct_write_names_by_stmt
            .get(stmt_index)
            .is_some_and(|names| names.contains(name))
    }

    fn has_write_after(&self, stmt_index: usize, binding: AstBindingRef) -> bool {
        self.write_bounds_by_binding
            .get(&binding)
            .is_some_and(|(_, last_write)| *last_write > stmt_index)
    }

    fn name_has_write_after(&self, stmt_index: usize, name: &AstNameRef) -> bool {
        self.write_bounds_by_name
            .get(name)
            .is_some_and(|(_, last_write)| *last_write > stmt_index)
    }

    fn writes_start_after(&self, stmt_index: usize, binding: AstBindingRef) -> bool {
        self.write_bounds_by_binding
            .get(&binding)
            .is_some_and(|(first_write, _)| *first_write > stmt_index)
    }
}

fn removable_inline_candidate<'a>(
    stmts: &'a [AstStmt],
    stmt_index: usize,
    write_index: &BindingWriteIndex,
) -> Option<(InlineCandidate, &'a AstExpr)> {
    let (candidate, value) = inline_candidate(stmts.get(stmt_index)?)?;
    if write_index.has_write_after(stmt_index, candidate.binding()) {
        // 候选拒绝[SemanticBarrier:Scope]：删除仍有后续 direct write 的 local 声明，会把保留赋值渲染成外层/global 写入。
        return None;
    }
    Some((candidate, value))
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
        if path.fields.is_empty() {
            self.index.record_name(self.stmt_index, &path.root);
        }
    }

    fn visit_lvalue(&mut self, lvalue: &AstLValue) {
        let AstLValue::Name(name) = lvalue else {
            return;
        };
        self.index.record_name(self.stmt_index, name);
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
            None,
        )
    }

    fn rewrite_repeat_body(&mut self, block: &mut AstBlock, condition: &AstExpr) -> bool {
        rewrite_current_block(
            block,
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
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let mut changed = collapse_adjacent_self_call_updates(block, trailing_condition);
    changed |=
        collapse_adjacent_call_alias_runs(block, options, mutable_snapshots, trailing_condition);

    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&old_stmts, trailing_condition);
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
        if index.checked_sub(1).is_some_and(|run_start| {
            super::function_sugar::run_belongs_to_method_alias_owner(
                &old_stmts,
                run_start,
                index + 1,
                &use_index,
                mutable_snapshots,
            )
        }) {
            // Preserve the field alias until function-sugar can consume the receiver snapshot,
            // lookup, and call atomically. Inlining only the lookup loses the method proof.
            // 候选拒绝[LayerBoundary]：receiver + field alias + call 必须由 function-sugar 原子消费，单独内联 lookup 会销毁 method 证明。
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
        let policy = if stmt_is_alias_initializer_sink(next_stmt) {
            InlinePolicy::AliasInitializerChain
        } else if stmt_is_adjacent_call_result_sink(next_stmt) {
            InlinePolicy::AdjacentCallResultCallee
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
            && candidate::is_lookup_inline_expr(value)
            && stmt_starts_lookup_mechanical_run(&old_stmts, index, candidate.binding())
        {
            // 这里故意不提前把 lookup 链压成“下一条 local 的初始化式”：
            // `local item = items[i]; local weight = item.weight; sum = sum + weight`
            // 如果太早收成 `local weight = items[i].weight`，后面的机械 run 就只剩一层，
            // 无法再判断“整条链都只是脚手架”。让它留到 run-collapse 一次性处理，
            // 才能既收回 for-loop 里的机械局部，又保住 return 场景下的阶段 local。
            // 候选拒绝[LayerBoundary]：连续 lookup 由本 pass 的 mechanical-run 事务统一证明，单项先吞会丢掉整段候选边界。
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
        if !candidate.allows_expr_with_policy(value, effective_policy)
            && !allows_special_lookup_access_base
        {
            // 候选拒绝[ProofIncomplete]：当前策略缺少把此 RHS 放入该 sink 后的值宽度、求值时点或 root 生命周期证明；需扩展对应 expr/site 事实而非猜测。
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        let suffix_uses = use_index.count_uses_in_suffix(index + 1, candidate.binding());
        if suffix_uses == 0 {
            // 候选拒绝[LayerBoundary]：未使用声明的删除归 cleanup/dead-local，不属于表达式内联。
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
            // 候选拒绝[SemanticBarrier:EvalOrder/Lifetime]：producer 不能跨过 sink 的调用、lookup、循环重求值或 mutable snapshot；如 `v=side(); guard()==v` 不等价于 `guard()==side()`。
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
                    // 候选拒绝[ProofIncomplete]：扩展调用链仍找不到已证明安全的唯一 use-site；需要更精确的位置/值宽度事实。
                    stmt_plan.push(PlannedStmt::Original(index));
                    index += 1;
                    continue;
                }
            } else {
                // 候选拒绝[ProofIncomplete]：候选通过表达式级检查但当前 sink 没有可证明安全的替换位置，需补 use-site 分类。
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
    changed |= collapse_stable_copy_aliases(block, options, mutable_snapshots, trailing_condition);
    changed |= collapse_terminal_call_result_alias_runs(
        block,
        options,
        mutable_snapshots,
        trailing_condition,
    );
    changed |= collapse_terminal_local_mechanical_runs(
        block,
        options,
        mutable_snapshots,
        trailing_condition,
    );
    changed |= collapse_adjacent_mechanical_alias_runs(
        block,
        options,
        mutable_snapshots,
        trailing_condition,
    );
    changed
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
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let mut stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&stmts, trailing_condition);
    let write_index = BindingWriteIndex::for_stmts(&stmts);
    let mut removed = vec![false; stmts.len()];

    for (candidate_index, is_removed) in removed.iter_mut().enumerate() {
        let Some((candidate, value)) =
            removable_inline_candidate(&stmts, candidate_index, &write_index)
        else {
            continue;
        };
        if candidate.origin() != super::super::common::AstLocalOrigin::Recovered {
            // 候选拒绝[SemanticBarrier:DebugScope]：删除 DebugHinted 会改变 debug.getlocal 可观察的作用域（regress_351）；候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot 若在 use 后仍处于原词法作用域，会延后弱表消失或 `__gc`。
            continue;
        }
        let mut snapshot_names = BTreeSet::new();
        if !candidate.allows_expr_with_policy(value, InlinePolicy::StableCopy)
            || !collect_stable_copy_snapshot_names(value, &mut snapshot_names)
        {
            // 候选拒绝[SemanticBarrier:EvalTime/EvalCount/ValueArity/Metamethod/Lifetime]：带可观察调用、lookup、元方法、vararg 或分配的输入搬到 use 会改变次数、快照、值宽度、对象身份或 root 生命周期（regress_387）；候选拒绝[ProofIncomplete]：该形状 guard 仍 blanket 覆盖稳定 global/upvalue、已知 primitive 运算、非有限 number 与 Int64/UInt64/Vector/Complex，当前缺外部写入、操作数类型及目标方言物化事实；候选拒绝[LayerBoundary]：残留 Temp/Error 分别归 HIR/materialize 与错误输出 owner。
            continue;
        }
        if mutable_snapshots.contains(&candidate.binding().to_name_ref()) {
            // 候选拒绝[SemanticBarrier:EvalOrder]：captured/mutable snapshot 的值可能被中间调用改写，直接替换会读取新值。
            continue;
        }
        if !matches!(value, AstExpr::Var(_))
            && snapshot_names.iter().any(|name| {
                mutable_snapshots.contains(name)
                    || write_index.name_has_write_after(candidate_index, name)
            })
        {
            // 候选拒绝[ProofIncomplete]：当前用 suffix-wide write/capture 保证复合快照稳定，尚不能区分最后 use 后的无关写或不会改写的 closure；声明到 use 之间的改写会从 use 点读到新值（regress_387）。
            continue;
        }

        let use_stmt_indices =
            use_index.use_stmt_indices_in_suffix(candidate_index + 1, candidate.binding());
        if use_stmt_indices.is_empty() {
            // 候选拒绝[LayerBoundary]：未使用声明的删除归 cleanup/dead-local，不属于 copy-inline。
            continue;
        }
        if use_stmt_indices
            .iter()
            .any(|use_stmt_index| *use_stmt_index >= stmts.len())
        {
            // 候选拒绝[LayerBoundary]：repeat trailing condition 位于当前 block 的 statement
            // rewrite 边界之外；不能只提交正文 use 而留下条件中的悬空 binding。
            continue;
        }
        if use_stmt_indices.len() > 1 && !matches!(value, AstExpr::Var(_)) {
            // 候选拒绝[PolicyBoundary]：把 primitive 复制进多个业务语句会抹掉复用概念并
            // 增加重复；同一 owner 仍可内联，多 owner 只删除纯名字 alias（regress_80/316）。
            continue;
        }

        if let AstExpr::Var(source_name) = value {
            let Some(source_binding) = binding_from_name_ref(source_name) else {
                // Parameters are intentionally owned by HIR local convergence; globals,
                // upvalues and temps have no stable copy proof at this AST stage.
                // 候选拒绝[LayerBoundary]：参数 alias 归 HIR locals；候选拒绝[ProofIncomplete]：global/upvalue 缺少声明点快照与写入事实，AST 不能跨语句猜测。
                continue;
            };
            // A bound local/synthetic name can only appear while its lexical declaration is
            // active, so the AST binding identity itself supplies the dominance proof.
            if !matches!(
                source_binding,
                AstBindingRef::Local(_) | AstBindingRef::SyntheticLocal(_)
            ) || mutable_snapshots.contains(source_name)
            {
                // 候选拒绝[SemanticBarrier:EvalOrder]：captured/upvalue/global/temp source 可在中间调用中改变；只允许当前词法域内未捕获 local/synthetic 快照。
                continue;
            }
            if write_index.has_write_after(candidate_index, source_binding)
                && (use_stmt_indices.len() != 1
                    || !stable_copy_has_trailing_root_handoff(
                        &stmts,
                        trailing_condition,
                        &write_index,
                        mutable_snapshots,
                        use_stmt_indices[0],
                        candidate.binding(),
                        source_binding,
                    ))
            {
                // 候选拒绝[SemanticBarrier:EvalOrder/Lifetime]：source 在 use 前后写入时 alias
                // 保存的是旧快照/root；只有单 owner 的精确 repeat handoff 已证明安全。
                continue;
            }
        }

        let replacement = value.clone();
        let mut rewritten_stmts = Vec::with_capacity(use_stmt_indices.len());
        let all_rewritten = use_stmt_indices.iter().all(|use_stmt_index| {
            let mut rewritten_stmt = stmts[*use_stmt_index].clone();
            if !rewrite_stmt_use_sites_with_policy(
                &mut rewritten_stmt,
                candidate,
                &replacement,
                options,
                InlinePolicy::StableCopy,
            ) || BindingUseIndex::for_stmts(std::slice::from_ref(&rewritten_stmt))
                .count_uses_in_suffix(0, candidate.binding())
                != 0
            {
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

fn stable_copy_has_trailing_root_handoff(
    stmts: &[AstStmt],
    trailing_condition: Option<&AstExpr>,
    write_index: &BindingWriteIndex,
    mutable_snapshots: &MutableSnapshotNames,
    use_stmt_index: usize,
    candidate: AstBindingRef,
    source: AstBindingRef,
) -> bool {
    if stmts
        .iter()
        .any(super::control_flow::stmt_contains_label_or_goto)
    {
        // 候选拒绝[ProofIncomplete]：当前 AST write index 没有 CFG 可达性，不能区分无关 goto 与可绕过或重入 handoff 的路径。
        return false;
    }
    if !write_index.writes_start_after(use_stmt_index, source) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：source 若非只在 handoff 后写入，alias 与 source 在 use 点不保证同值。
        return false;
    }
    let AstStmt::Assign(assign) = &stmts[use_stmt_index] else {
        // 候选拒绝[ProofIncomplete]：trailing root handoff 目前只证明单目标赋值形状。
        return false;
    };
    let ([AstLValue::Name(target)], [AstExpr::Var(value)]) =
        (assign.targets.as_slice(), assign.values.as_slice())
    else {
        // 候选拒绝[ProofIncomplete]：多目标/非变量 handoff 尚无精确的 root 接管证明。
        return false;
    };
    let Some(target) = binding_from_name_ref(target).filter(|_| candidate.matches_name_ref(value))
    else {
        // 候选拒绝[ProofIncomplete]：只有 `target = candidate` 的直接接管形状纳入当前证明。
        return false;
    };
    if mutable_snapshots.contains(&target.to_name_ref()) {
        // 候选拒绝[SemanticBarrier:Capture]：target 被 closure 捕获时，接管前后的 binding 写入可被观察。
        return false;
    }
    if write_index.has_write_after(use_stmt_index, target) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：target 在 latch 前再次写入时不能继续承载同一快照/root。
        return false;
    }
    let Some(condition) = trailing_condition else {
        // 候选拒绝[LayerBoundary]：没有 repeat trailing condition 时不属于此 handoff 规则。
        return false;
    };
    if !expr_references_binding(condition, target) {
        // 候选拒绝[ProofIncomplete]：当前证明要求 latch 条件消费 target，以确认 root 接管覆盖到循环尾。
        return false;
    }
    true
}

fn inline_crosses_evaluation_boundary(
    value: &AstExpr,
    next_stmt: &AstStmt,
    binding: AstBindingRef,
    mutable_snapshots: &MutableSnapshotNames,
    policy: InlinePolicy,
) -> bool {
    if matches!(policy, InlinePolicy::BooleanReturnValue)
        && is_lookup_inline_expr(value)
        && stmt_is_terminal_lookup_return_sink(next_stmt, binding)
    {
        // The lookup is the first and only observable producer in the return expression.  The
        // remaining short-circuit suffix is context-safe, so the expression temporary itself
        // carries the value through the same truthiness/return operation as the old local root.
        return false;
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

#[cfg(test)]
mod tests {
    use crate::ast::common::{
        AstAssign, AstBinaryExpr, AstBinaryOpKind, AstCallExpr, AstCallKind, AstCallStmt,
        AstFieldAccess, AstGlobalName, AstIndexAccess, AstLocalAttr, AstLocalBinding, AstLocalDecl,
        AstLocalOrigin, AstLogicalExpr, AstNameRef, AstReturn,
    };
    use crate::hir::{LocalId, ParamId};

    use super::*;

    fn recovered_local(binding: AstBindingRef, value: AstExpr) -> AstStmt {
        AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![AstLocalBinding {
                id: binding,
                attr: AstLocalAttr::None,
                origin: AstLocalOrigin::Recovered,
            }],
            values: vec![value],
        }))
    }

    fn debug_local(binding: AstBindingRef, value: AstExpr) -> AstStmt {
        AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![AstLocalBinding {
                id: binding,
                attr: AstLocalAttr::None,
                origin: AstLocalOrigin::DebugHinted,
            }],
            values: vec![value],
        }))
    }

    fn equals(lhs: AstExpr, rhs: AstExpr) -> AstExpr {
        AstExpr::Binary(Box::new(AstBinaryExpr {
            op: AstBinaryOpKind::Eq,
            lhs,
            rhs,
        }))
    }

    fn return_values(values: Vec<AstExpr>) -> AstStmt {
        AstStmt::Return(Box::new(AstReturn { values }))
    }

    fn indexed(base: AstExpr, index: AstExpr) -> AstExpr {
        AstExpr::IndexAccess(Box::new(AstIndexAccess { base, index }))
    }

    fn call_with_arg(name: &str, arg: AstExpr) -> AstStmt {
        AstStmt::CallStmt(Box::new(AstCallStmt {
            call: AstCallKind::Call(Box::new(AstCallExpr {
                callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                    text: name.to_owned(),
                })),
                args: vec![arg],
                method_name: None,
            })),
        }))
    }

    #[test]
    fn stable_copy_rewrites_all_top_level_use_owners_atomically() {
        let source = AstBindingRef::Local(LocalId(0));
        let binding = AstBindingRef::Local(LocalId(1));
        let mut block = AstBlock {
            stmts: vec![
                debug_local(source, AstExpr::Integer(7)),
                recovered_local(binding, AstExpr::Var(source.to_name_ref())),
                call_with_arg("sink", AstExpr::Var(binding.to_name_ref())),
                return_values(vec![AstExpr::Var(binding.to_name_ref())]),
            ],
        };

        assert!(collapse_stable_copy_aliases(
            &mut block,
            ReadabilityOptions::default(),
            &MutableSnapshotNames::new(),
            None,
        ));
        assert!(matches!(
            block.stmts.as_slice(),
            [AstStmt::LocalDecl(_), AstStmt::CallStmt(call), AstStmt::Return(ret)]
                if matches!(&call.call, AstCallKind::Call(call)
                    if call.args == vec![AstExpr::Var(source.to_name_ref())])
                    && ret.values == vec![AstExpr::Var(source.to_name_ref())]
        ));
    }

    #[test]
    fn stable_copy_keeps_all_owners_when_a_nested_use_cannot_rewrite() {
        let source = AstBindingRef::Local(LocalId(0));
        let binding = AstBindingRef::Local(LocalId(1));
        let mut block = AstBlock {
            stmts: vec![
                debug_local(source, AstExpr::Integer(7)),
                recovered_local(binding, AstExpr::Var(source.to_name_ref())),
                call_with_arg("sink", AstExpr::Var(binding.to_name_ref())),
                AstStmt::DoBlock(Box::new(AstBlock {
                    stmts: vec![call_with_arg("nested", AstExpr::Var(binding.to_name_ref()))],
                })),
            ],
        };
        let original = block.clone();

        assert!(!collapse_stable_copy_aliases(
            &mut block,
            ReadabilityOptions::default(),
            &MutableSnapshotNames::new(),
            None,
        ));
        assert_eq!(block, original);
    }

    #[test]
    fn stable_copy_keeps_body_uses_when_until_is_outside_rewrite_boundary() {
        let source = AstBindingRef::Local(LocalId(0));
        let binding = AstBindingRef::Local(LocalId(1));
        let mut block = AstBlock {
            stmts: vec![
                debug_local(source, AstExpr::Integer(7)),
                recovered_local(binding, AstExpr::Var(source.to_name_ref())),
                call_with_arg("sink", AstExpr::Var(binding.to_name_ref())),
            ],
        };
        let original = block.clone();
        let condition = equals(AstExpr::Var(binding.to_name_ref()), AstExpr::Integer(7));

        assert!(!collapse_stable_copy_aliases(
            &mut block,
            ReadabilityOptions::default(),
            &MutableSnapshotNames::new(),
            Some(&condition),
        ));
        assert_eq!(block, original);
    }

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
                        method_name: None,
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
            None,
        ));
        assert_eq!(block, expected);
    }

    #[test]
    fn inlines_global_callee_when_the_call_is_adjacent() {
        for origin in [AstLocalOrigin::Recovered, AstLocalOrigin::PhysicalRoot] {
            let binding = AstBindingRef::Local(LocalId(0));
            let global = AstExpr::Var(AstNameRef::Global(AstGlobalName {
                text: "assert".to_owned(),
            }));
            let mut block = AstBlock {
                stmts: vec![
                    AstStmt::LocalDecl(Box::new(AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: binding,
                            attr: AstLocalAttr::None,
                            origin,
                        }],
                        values: vec![global],
                    })),
                    AstStmt::CallStmt(Box::new(AstCallStmt {
                        call: AstCallKind::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Var(binding.to_name_ref()),
                            args: vec![AstExpr::Boolean(true)],
                            method_name: None,
                        })),
                    })),
                ],
            };

            assert!(rewrite_current_block(
                &mut block,
                ReadabilityOptions::default(),
                &MutableSnapshotNames::new(),
                None,
            ));
            assert!(matches!(
                block.stmts.as_slice(),
                [AstStmt::CallStmt(call)]
                    if matches!(
                        &call.call,
                        AstCallKind::Call(call)
                            if matches!(call.callee, AstExpr::Var(AstNameRef::Global(_)))
                    )
            ));
        }
    }

    #[test]
    fn inlines_proven_boolean_alias_in_multi_return() {
        let binding = AstBindingRef::Local(LocalId(0));
        let parameter = AstExpr::Var(AstNameRef::Param(ParamId(0)));
        let mut block = AstBlock {
            stmts: vec![
                recovered_local(
                    binding,
                    equals(parameter, AstExpr::String("target".to_owned().into())),
                ),
                return_values(vec![
                    AstExpr::Var(binding.to_name_ref()),
                    AstExpr::Integer(1),
                ]),
            ],
        };

        assert!(rewrite_current_block(
            &mut block,
            ReadabilityOptions::default(),
            &MutableSnapshotNames::new(),
            None,
        ));
        assert!(matches!(
            block.stmts.as_slice(),
            [AstStmt::Return(ret)]
                if matches!(
                    ret.values.as_slice(),
                    [AstExpr::Binary(binary), AstExpr::Integer(1)]
                        if binary.op == AstBinaryOpKind::Eq
                )
        ));
    }

    #[test]
    fn inlines_proven_boolean_alias_in_return_short_circuit_prefix() {
        let binding = AstBindingRef::Local(LocalId(0));
        let logical = AstExpr::LogicalOr(Box::new(AstLogicalExpr {
            lhs: AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                lhs: AstExpr::Var(binding.to_name_ref()),
                rhs: AstExpr::Boolean(true),
            })),
            rhs: AstExpr::Boolean(false),
        }));
        let mut block = AstBlock {
            stmts: vec![
                recovered_local(
                    binding,
                    equals(
                        AstExpr::Var(AstNameRef::Param(ParamId(0))),
                        AstExpr::String("target".to_owned().into()),
                    ),
                ),
                return_values(vec![logical]),
            ],
        };

        assert!(rewrite_current_block(
            &mut block,
            ReadabilityOptions::default(),
            &MutableSnapshotNames::new(),
            None,
        ));
        assert!(matches!(
            block.stmts.as_slice(),
            [AstStmt::Return(ret)]
                if matches!(
                    &ret.values[0],
                    AstExpr::LogicalOr(logical)
                        if matches!(&logical.lhs, AstExpr::LogicalAnd(and)
                            if matches!(&and.lhs, AstExpr::Binary(binary)
                                if binary.op == AstBinaryOpKind::Eq))
                )
        ));
    }

    #[test]
    fn inlines_lookup_alias_in_terminal_short_circuit_return() {
        let binding = AstBindingRef::Local(LocalId(0));
        let lookup = indexed(
            AstExpr::Var(AstNameRef::Local(LocalId(1))),
            AstExpr::Var(AstNameRef::Param(ParamId(0))),
        );
        let logical = AstExpr::LogicalOr(Box::new(AstLogicalExpr {
            lhs: AstExpr::Var(binding.to_name_ref()),
            rhs: AstExpr::Integer(0),
        }));
        let mut block = AstBlock {
            stmts: vec![
                recovered_local(binding, lookup),
                return_values(vec![logical]),
            ],
        };

        assert!(rewrite_current_block(
            &mut block,
            ReadabilityOptions::default(),
            &MutableSnapshotNames::new(),
            None,
        ));
        assert!(matches!(
            block.stmts.as_slice(),
            [AstStmt::Return(ret)]
                if matches!(&ret.values[0], AstExpr::LogicalOr(logical)
                    if matches!(&logical.lhs, AstExpr::IndexAccess(_)))
        ));
    }

    #[test]
    fn keeps_lookup_alias_when_terminal_short_circuit_tail_calls() {
        let binding = AstBindingRef::Local(LocalId(0));
        let lookup = indexed(
            AstExpr::Var(AstNameRef::Local(LocalId(1))),
            AstExpr::Var(AstNameRef::Param(ParamId(0))),
        );
        let fallback = AstExpr::Call(Box::new(AstCallExpr {
            callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                text: "fallback".to_owned(),
            })),
            args: Vec::new(),
            method_name: None,
        }));
        let logical = AstExpr::LogicalOr(Box::new(AstLogicalExpr {
            lhs: AstExpr::Var(binding.to_name_ref()),
            rhs: fallback,
        }));
        let mut block = AstBlock {
            stmts: vec![
                recovered_local(binding, lookup),
                return_values(vec![logical]),
            ],
        };
        let expected = block.clone();

        assert!(!rewrite_current_block(
            &mut block,
            ReadabilityOptions::default(),
            &MutableSnapshotNames::new(),
            None,
        ));
        assert_eq!(block, expected);
    }

    #[test]
    fn keeps_lookup_alias_for_protected_origins() {
        for origin in [AstLocalOrigin::DebugHinted, AstLocalOrigin::PhysicalRoot] {
            let binding = AstBindingRef::Local(LocalId(0));
            let lookup = indexed(
                AstExpr::Var(AstNameRef::Local(LocalId(1))),
                AstExpr::Var(AstNameRef::Param(ParamId(0))),
            );
            let logical = AstExpr::LogicalOr(Box::new(AstLogicalExpr {
                lhs: AstExpr::Var(binding.to_name_ref()),
                rhs: AstExpr::Integer(0),
            }));
            let mut block = AstBlock {
                stmts: vec![
                    AstStmt::LocalDecl(Box::new(AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: binding,
                            attr: AstLocalAttr::None,
                            origin,
                        }],
                        values: vec![lookup],
                    })),
                    return_values(vec![logical]),
                ],
            };
            let expected = block.clone();

            assert!(!rewrite_current_block(
                &mut block,
                ReadabilityOptions::default(),
                &MutableSnapshotNames::new(),
                None,
            ));
            assert_eq!(block, expected);
        }
    }

    #[test]
    fn keeps_boolean_alias_in_return_short_circuit_rhs() {
        let binding = AstBindingRef::Local(LocalId(0));
        let logical = AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
            lhs: AstExpr::Var(AstNameRef::Param(ParamId(1))),
            rhs: AstExpr::Var(binding.to_name_ref()),
        }));
        let mut block = AstBlock {
            stmts: vec![
                recovered_local(
                    binding,
                    equals(
                        AstExpr::Var(AstNameRef::Param(ParamId(0))),
                        AstExpr::String("target".to_owned().into()),
                    ),
                ),
                return_values(vec![logical]),
            ],
        };
        let expected = block.clone();

        assert!(!rewrite_current_block(
            &mut block,
            ReadabilityOptions::default(),
            &MutableSnapshotNames::new(),
            None,
        ));
        assert_eq!(block, expected);
    }

    #[test]
    fn keeps_boolean_alias_when_an_earlier_return_value_observes_order() {
        let binding = AstBindingRef::Local(LocalId(0));
        let mut block = AstBlock {
            stmts: vec![
                recovered_local(
                    binding,
                    equals(
                        AstExpr::Var(AstNameRef::Local(LocalId(1))),
                        AstExpr::Integer(1),
                    ),
                ),
                return_values(vec![
                    AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "observe".to_owned(),
                        })),
                        field: "value".to_owned(),
                    })),
                    AstExpr::Var(binding.to_name_ref()),
                ]),
            ],
        };
        let expected = block.clone();

        assert!(!rewrite_current_block(
            &mut block,
            ReadabilityOptions::default(),
            &MutableSnapshotNames::new(),
            None,
        ));
        assert_eq!(block, expected);
    }
}
