//! 合并机械拆开的声明与初始化，并将 hoisted local 下沉到实际使用的作用域。
//!
//! 消费 AST binding/use 和词法控制流事实，保持声明对读写的支配及原求值顺序。
//! 例如 local a; a=f() 可合成 local a=f()；仍在分支外被读取或写入的声明不能
//! 只沉入某个分支。单次别名内联属于 inline-exprs，不在这里提前固化成多目标声明。

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::super::common::{
    AstBindingRef, AstBlock, AstExpr, AstLValue, AstLabelId, AstLocalAttr, AstLocalBinding,
    AstLocalDecl, AstModule, AstStmt,
};
use super::ReadabilityContext;
use super::binding_flow::{
    BindingRefSet, BindingUseIndex, BindingWriteIndex, binding_mentions_in_block,
    binding_mentions_in_expr, binding_mentions_in_stmt, block_references_binding_set,
    expr_references_any_binding, expr_references_binding_set, stmt_references_binding_set,
};
use super::expr_analysis::{expr_complexity, is_copy_like_expr, is_discard_safe_expr};
use super::walk::{self, AstRewritePass};
use crate::ast::traverse::BlockKind;
use crate::ast::visit::any_stmt_structure;

const ADJACENT_LOCAL_VALUE_COMPLEXITY_LIMIT: usize = 4;

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let _ = context.target;
    walk::rewrite_module(module, &mut StatementMergePass)
}

struct StatementMergePass;

impl AstRewritePass for StatementMergePass {
    fn rewrite_block(&mut self, block: &mut AstBlock, _kind: BlockKind) -> bool {
        rewrite_current_block(block, None)
    }

    fn rewrite_repeat_body(&mut self, block: &mut AstBlock, condition: &AstExpr) -> bool {
        rewrite_current_block(block, Some(condition))
    }
}

fn rewrite_current_block(block: &mut AstBlock, trailing_condition: Option<&AstExpr>) -> bool {
    let mut changed = sink_hoisted_temp_decls(block, trailing_condition);

    let mut old_stmts = VecDeque::from(std::mem::take(&mut block.stmts));
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    while let Some(mut stmt) = old_stmts.pop_front() {
        let Some(next_stmt) = old_stmts.front_mut() else {
            new_stmts.push(stmt);
            continue;
        };

        if try_merge_local_decl_with_assign(&mut stmt, next_stmt) {
            new_stmts.push(stmt);
            old_stmts.pop_front();
            changed = true;
            continue;
        }

        new_stmts.push(stmt);
    }

    block.stmts = new_stmts;
    changed |= merge_adjacent_empty_local_decls(block);
    changed |= merge_adjacent_single_value_local_decls(block, trailing_condition);
    changed
}

fn merge_adjacent_empty_local_decls(block: &mut AstBlock) -> bool {
    let mut old_stmts = VecDeque::from(std::mem::take(&mut block.stmts));
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut changed = false;

    while let Some(stmt) = old_stmts.pop_front() {
        let Some(bindings) = empty_local_decl_bindings(&stmt) else {
            new_stmts.push(stmt);
            continue;
        };
        if bindings.iter().any(|binding| {
            binding.origin.is_debug_hinted()
                || !binding
                    .rewrite_authority
                    .may_merge_adjacent_inert_declarations()
        }) {
            // 候选拒绝[SemanticBarrier:DebugScope]：`local debug_name; local t` 合并后，
            // 首个 binding 要到第二条声明之后才进入作用域；原第二行的 line hook 本可
            // 通过 debug.getlocal 观察它，合并会丢失这段已保留的源码可见期。
            new_stmts.push(stmt);
            continue;
        }

        let mut merged_bindings = bindings.to_vec();
        let mut consumed = 0;
        for next_bindings in old_stmts.iter().map_while(empty_local_decl_bindings) {
            if next_bindings.iter().any(|binding| {
                binding.origin.is_debug_hinted()
                    || !binding
                        .rewrite_authority
                        .may_merge_adjacent_inert_declarations()
            }) {
                // 候选拒绝[SemanticBarrier:DebugScope]：line hook 能在相邻声明间观察
                // DebugHinted local 的边界，不能把后续声明提前到同一 local list。
                break;
            }
            match local_attr_merge_barrier(&merged_bindings, next_bindings) {
                Some(LocalAttrMergeBarrier::MultipleClose) => {
                    // 候选拒绝[TargetConstraint]：Lua 5.4/5.5 的同一 local list 最多只能声明一个 `<close>` binding。
                    break;
                }
                Some(LocalAttrMergeBarrier::NonTrailingClose) => {
                    // 候选拒绝[TargetConstraint]：Lua 5.4/5.5 要求 `<close>` binding 位于 local list 末位；继续合并会生成目标语法不允许的非末位 `<close>`（regress_379）。
                    break;
                }
                None => {}
            }
            merged_bindings.extend_from_slice(next_bindings);
            consumed += 1;
        }

        if merged_bindings.len() > bindings.len() {
            new_stmts.push(AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings: merged_bindings,
                values: Vec::new(),
                initializer_merge_transaction: None,
                initializer_root_profile: None,
            })));
            old_stmts.drain(..consumed);
            changed = true;
        } else {
            new_stmts.push(stmt);
        }
    }

    block.stmts = new_stmts;
    changed
}

fn empty_local_decl_bindings(stmt: &AstStmt) -> Option<&[AstLocalBinding]> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    if !local_decl.values.is_empty() {
        return None;
    }
    Some(&local_decl.bindings)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LocalAttrMergeBarrier {
    MultipleClose,
    NonTrailingClose,
}

fn local_attr_merge_barrier(
    current: &[AstLocalBinding],
    next: &[AstLocalBinding],
) -> Option<LocalAttrMergeBarrier> {
    let close_count = current
        .iter()
        .chain(next)
        .filter(|binding| binding.attr == AstLocalAttr::Close)
        .count();
    if close_count > 1 {
        return Some(LocalAttrMergeBarrier::MultipleClose);
    }
    if close_count == 1
        && current
            .iter()
            .chain(next)
            .next_back()
            .is_none_or(|binding| binding.attr != AstLocalAttr::Close)
    {
        return Some(LocalAttrMergeBarrier::NonTrailingClose);
    }
    None
}

fn may_merge_single_value_declaration(binding: &AstLocalBinding, value: &AstExpr) -> bool {
    binding.rewrite_authority.may_move_scope_start()
        || matches!(
            value,
            AstExpr::Nil
                | AstExpr::Boolean(_)
                | AstExpr::Integer(_)
                | AstExpr::Number(_)
                | AstExpr::String(_)
        ) && binding
            .rewrite_authority
            .may_merge_adjacent_inert_declarations()
}

fn merge_adjacent_single_value_local_decls(
    block: &mut AstBlock,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&old_stmts, trailing_condition);
    let write_index = BindingWriteIndex::for_stmts(&old_stmts);
    let mut old_stmts = VecDeque::from(old_stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while let Some(stmt) = old_stmts.pop_front() {
        let Some((binding, value)) = single_value_local_decl(&stmt) else {
            new_stmts.push(stmt);
            index += 1;
            continue;
        };
        if binding.origin.is_debug_hinted() || !may_merge_single_value_declaration(binding, value) {
            // 候选拒绝[SemanticBarrier:DebugScope]：后续 RHS 求值期间 line hook/元方法可观察
            // 当前 DebugHinted local；并行声明会把它的作用域起点推迟到整组 RHS 之后。
            new_stmts.push(stmt);
            index += 1;
            continue;
        }
        if !is_mergeable_adjacent_local_value(value) {
            // 候选拒绝[PolicyBoundary]：相邻声明合并只接受复杂度不超过 4 的 copy-like RHS，避免把阶段性复杂声明压成难读的并行列表。
            new_stmts.push(stmt);
            index += 1;
            continue;
        }
        if binding_needs_independent_declaration(&use_index, &write_index, index + 1, binding) {
            // 候选拒绝[LayerBoundary]：待清理或内联的独立 local 不能先固化为 multi-local；
            // cleanup 无法删除其中的非尾槽，残留的无用别名还可能延长对象生命周期。
            new_stmts.push(stmt);
            index += 1;
            continue;
        }

        let mut bindings = vec![binding.clone()];
        let mut values = vec![value.clone()];
        let mut lookahead = index + 1;
        while let Some((next_binding, next_value)) = old_stmts
            .get(lookahead - index - 1)
            .and_then(single_value_local_decl)
        {
            if next_binding.origin.is_debug_hinted()
                || !may_merge_single_value_declaration(next_binding, next_value)
            {
                // 候选拒绝[SemanticBarrier:DebugScope]：line hook 可在相邻声明间观察
                // DebugHinted local；并行声明会让该名字提前可见。
                break;
            }
            // 这里故意只收“连续复制/lookup”式的 local：
            // 目标是把 `local a = x; local b = y; local c = t[k]` 这类明显属于同一段
            // 源码声明的机械拆分重新压回去，而不是把有阶段语义的复杂 local 都并成一行。
            if !is_mergeable_adjacent_local_value(next_value) {
                // 候选拒绝[PolicyBoundary]：复杂 RHS 受展示预算限制。
                break;
            }
            if binding_needs_independent_declaration(
                &use_index,
                &write_index,
                lookahead + 1,
                next_binding,
            ) {
                // 候选拒绝[LayerBoundary]：cleanup/inline-exprs 的独立候选是合并分段点。
                break;
            }
            if bindings
                .iter()
                .any(|binding| binding.attr == AstLocalAttr::Const)
            {
                // 候选拒绝[SemanticBarrier:DebugScope]：PUC 只把 local list 末项的 const literal 提升为无栈槽常量；继续追加会让原 `<const>` 变成 debug 可见的真实 local。
                break;
            }
            match local_attr_merge_barrier(&bindings, std::slice::from_ref(next_binding)) {
                Some(LocalAttrMergeBarrier::MultipleClose) => {
                    // 候选拒绝[TargetConstraint]：Lua 5.4/5.5 的同一 local list 最多只能声明一个 `<close>` binding。
                    break;
                }
                Some(LocalAttrMergeBarrier::NonTrailingClose) => {
                    // 候选拒绝[TargetConstraint]：Lua 5.4/5.5 要求 `<close>` binding 位于 local list 末位；继续合并会生成目标语法不允许的非末位 `<close>`（regress_379）。
                    break;
                }
                None => {}
            }
            if expr_references_any_binding(next_value, &bindings) {
                // 候选拒绝[SemanticBarrier:Scope]：`local a=x; local b=a` 合成并行声明后 RHS 的 `a` 会解析到外层。
                break;
            }
            if !is_discard_safe_expr(next_value) {
                // 候选拒绝[SemanticBarrier:DebugScope]：regress_341 的 `probe.value` 可在
                // `__index` 中用 debug.getlocal 观察前一个顺序 local；并行声明会把它推迟到 RHS 全部求值之后。
                break;
            }
            bindings.push(next_binding.clone());
            values.push(next_value.clone());
            lookahead += 1;
        }

        if bindings.len() >= 2
            && bindings.iter().any(|b| {
                use_index.count_uses_in_suffix(lookahead, b.id) > 1
                    || write_index.has_write_after(index, b.id)
            })
        {
            new_stmts.push(AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings,
                values,
                initializer_merge_transaction: None,
                initializer_root_profile: None,
            })));
            changed = true;
            old_stmts.drain(..(lookahead - index - 1));
            index = lookahead;
            continue;
        }

        // 剥离交给 inline-exprs 的尾 binding 后只剩一个声明时，已经不存在并行声明候选。
        new_stmts.push(stmt);
        index += 1;
    }

    block.stmts = new_stmts;
    changed
}

fn binding_needs_independent_declaration(
    use_index: &BindingUseIndex,
    write_index: &BindingWriteIndex,
    suffix_start: usize,
    binding: &AstLocalBinding,
) -> bool {
    let uses = use_index.count_uses_in_suffix(suffix_start, binding.id);
    if uses == 0 {
        // 下沉可能刚产生尚未被 cleanup 消费的 dead copy；不能让它因并入另一个
        // 有用声明而继续持有对象。仍有生命周期职责的 binding 也保持原独立边界。
        return true;
    }
    super::inline_exprs::local_attr_belongs_to_inline_pipeline(binding.attr)
        && uses == 1
        // 分支更新后的唯一读取不是初始化值的单次使用，不能把这种状态绑定留给内联。
        && !write_index.has_write_after(suffix_start - 1, binding.id)
}

fn sink_hoisted_temp_decls(block: &mut AstBlock, trailing_condition: Option<&AstExpr>) -> bool {
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&block.stmts, trailing_condition);
    let write_index = BindingWriteIndex::for_stmts(&block.stmts);
    let forward_gotos = ForwardGotoIndex::new(&block.stmts);
    let mut index = 0;
    while index < block.stmts.len() {
        let Some(pending_bindings) = hoisted_temp_bindings(&block.stmts[index]) else {
            index += 1;
            continue;
        };

        let mut remaining = pending_bindings;
        let mut pinned: Vec<super::super::common::AstLocalBinding> = Vec::new();
        let mut sink_changed = false;
        let mut lookahead = index + 1;
        while lookahead < block.stmts.len() && !remaining.is_empty() {
            let crosses_forward_goto = forward_gotos.has_forward_goto_past_index(lookahead);
            let enters_backward_cycle = forward_gotos.move_enters_backward_cycle(index, lookahead);
            if crosses_forward_goto || enters_backward_cycle {
                if enters_backward_cycle {
                    // 候选拒绝[SemanticBarrier:ControlFlow]：`local t; ::L::; t = v; ...; goto L`
                    // 中原声明只建立一次 cell；把它沉到 L 与回跳之间会改成每轮新建 cell，
                    // 逃逸 closure 可观察到不同 identity。只拒绝声明点在 label 前、sink
                    // 位于该回边区间内的候选；不相交回边不影响本次移动。
                } else {
                    // 候选拒绝[SemanticBarrier:Scope]：`goto L; local t; ...; ::L:: use(t)` 若把声明沉到 label 前后，会让跳转进入 local 作用域或改变读取绑定。
                }

                // 不能越过已经读取 binding 的控制边界后再尝试 nested sink；否则后续
                // 子块候选只看自己的 owner/suffix，会遗漏这次较早读取。
                let mentions = binding_mentions_in_stmt(&block.stmts[lookahead]);
                pinned.extend(remaining.extract_if(.., |binding| mentions.contains(&binding.id)));
                lookahead += 1;
                continue;
            }
            if let Some(attempt) = try_sink_hoisted_decl_into_stmt(
                &remaining,
                &remaining,
                &mut block.stmts[lookahead],
                &use_index,
                index + 1,
                lookahead,
            ) {
                let consumed = attempt.consumed;
                remaining.drain(..consumed);
                pin_sink_dependencies(&mut remaining, &mut pinned, &attempt.dependencies);
                sink_changed = true;
                lookahead += 1;
                continue;
            }
            let nested_owners = NestedSinkOwners::new(&block.stmts[lookahead]);
            if let Some(attempt) = nested_owners.as_ref().and_then(|owners| {
                try_sink_hoisted_decl_into_nested_stmt_anywhere(
                    &remaining,
                    &mut block.stmts[lookahead],
                    &use_index,
                    &write_index,
                    lookahead,
                    owners,
                )
            }) {
                remaining.drain(attempt.start..(attempt.start + attempt.consumed));
                pin_sink_dependencies(&mut remaining, &mut pinned, &attempt.dependencies);
                sink_changed = true;
                // 不要前进 lookahead：同一条 if / loop 语句可能还有其它分支可以
                // 接收剩余 binding。例如 `local t12, t7; if ... then t12 = A else
                // t7 = B end` —— 第一轮把 t12 沉进 then，第二轮把 t7 沉进 else。
                continue;
            }
            if let Some(attempt) = try_sink_hoisted_decl_into_stmt_anywhere(
                &remaining,
                &remaining,
                &mut block.stmts[lookahead],
                &use_index,
                index + 1,
                lookahead,
                lookahead + 1,
            ) {
                let consumed = attempt.consumed;
                remaining.drain(attempt.start..attempt.start + consumed);
                pin_sink_dependencies(&mut remaining, &mut pinned, &attempt.dependencies);
                sink_changed = true;
                lookahead += 1;
                continue;
            }
            // 候选拒绝[SemanticBarrier:Scope]：被引用但无法下沉的 binding 必须留在
            // hoist 点。失败不改树，故嵌套 owner 的键仍是当前语句的完整 mention 集合。
            if let Some(owners) = &nested_owners {
                pinned
                    .extend(remaining.extract_if(.., |binding| owners.0.contains_key(&binding.id)));
            } else {
                let mentions = binding_mentions_in_stmt(&block.stmts[lookahead]);
                pinned.extend(remaining.extract_if(.., |binding| mentions.contains(&binding.id)));
            }
            lookahead += 1;
        }

        if !sink_changed {
            index += 1;
            continue;
        }

        // 将钉住的（不可下沉的）binding 合并回 remaining，按原始声明顺序
        // 排序，以保证输出的 `local` 列表确定且可读。
        remaining.extend(pinned);
        remaining.sort_by_key(|b| b.id);

        // use/forward-goto 索引只对本轮 block 快照有效；改写后交给下一轮重建。
        if remaining.is_empty() {
            block.stmts.remove(index);
            return true;
        }

        let AstStmt::LocalDecl(local_decl) = &mut block.stmts[index] else {
            unreachable!("hoisted temp decl scan must point at local decl");
        };
        local_decl.bindings = remaining;
        local_decl.initializer_root_profile = None;
        return true;
    }
    false
}

struct SinkAttempt {
    start: usize,
    consumed: usize,
    dependencies: Vec<AstBindingRef>,
}

struct BlockSinkAttempt {
    consumed: usize,
    dependencies: Vec<AstBindingRef>,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum NestedSinkOwner {
    Blocked,
    Then,
    Else,
    Body,
}

struct NestedSinkOwners(BTreeMap<AstBindingRef, NestedSinkOwner>);

impl NestedSinkOwners {
    fn new(stmt: &AstStmt) -> Option<Self> {
        let mut owners = Self(BTreeMap::new());
        let body = match stmt {
            AstStmt::If(if_stmt) => {
                owners.add(
                    binding_mentions_in_expr(&if_stmt.cond),
                    NestedSinkOwner::Blocked,
                );
                owners.add(
                    binding_mentions_in_block(&if_stmt.then_block),
                    NestedSinkOwner::Then,
                );
                if let Some(else_block) = &if_stmt.else_block {
                    owners.add(binding_mentions_in_block(else_block), NestedSinkOwner::Else);
                }
                return Some(owners);
            }
            AstStmt::While(while_stmt) => {
                owners.add(
                    binding_mentions_in_expr(&while_stmt.cond),
                    NestedSinkOwner::Blocked,
                );
                &while_stmt.body
            }
            AstStmt::Repeat(repeat_stmt) => {
                owners.add(
                    binding_mentions_in_expr(&repeat_stmt.cond),
                    NestedSinkOwner::Blocked,
                );
                &repeat_stmt.body
            }
            AstStmt::NumericFor(numeric_for) => {
                owners.add(
                    binding_mentions_in_expr(&numeric_for.start)
                        .into_iter()
                        .chain(binding_mentions_in_expr(&numeric_for.limit))
                        .chain(binding_mentions_in_expr(&numeric_for.step))
                        .chain(std::iter::once(numeric_for.binding)),
                    NestedSinkOwner::Blocked,
                );
                &numeric_for.body
            }
            AstStmt::GenericFor(generic_for) => {
                owners.add(
                    generic_for.bindings.iter().copied().chain(
                        generic_for
                            .iterator
                            .iter()
                            .flat_map(binding_mentions_in_expr),
                    ),
                    NestedSinkOwner::Blocked,
                );
                &generic_for.body
            }
            AstStmt::DoBlock(block) => block,
            AstStmt::FunctionDecl(_)
            | AstStmt::LocalFunctionDecl(_)
            | AstStmt::LocalDecl(_)
            | AstStmt::GlobalDecl(_)
            | AstStmt::Assign(_)
            | AstStmt::CallStmt(_)
            | AstStmt::Return(_)
            | AstStmt::Break
            | AstStmt::Continue
            | AstStmt::Goto(_)
            | AstStmt::Label(_)
            | AstStmt::Error(_) => return None,
        };
        owners.add(binding_mentions_in_block(body), NestedSinkOwner::Body);
        Some(owners)
    }

    fn add(&mut self, bindings: impl IntoIterator<Item = AstBindingRef>, owner: NestedSinkOwner) {
        for binding in bindings {
            self.0
                .entry(binding)
                .and_modify(|current| {
                    if *current != owner {
                        *current = NestedSinkOwner::Blocked;
                    }
                })
                .or_insert(owner);
        }
    }

    fn owner(&self, binding: AstBindingRef) -> Option<NestedSinkOwner> {
        self.0.get(&binding).copied()
    }
}

fn binding_has_access_after(
    use_index: &BindingUseIndex,
    write_index: &BindingWriteIndex,
    stmt_index: usize,
    binding: AstBindingRef,
) -> bool {
    // 候选拒绝[SemanticBarrier:Scope]：后缀读写都必须由声明支配，不能只证明值不再被读。
    use_index.count_uses_in_suffix(stmt_index + 1, binding) != 0
        || write_index.has_write_after(stmt_index, binding)
}

fn try_sink_hoisted_decl_into_nested_stmt_anywhere(
    pending: &[super::super::common::AstLocalBinding],
    stmt: &mut AstStmt,
    use_index: &BindingUseIndex,
    write_index: &BindingWriteIndex,
    stmt_index: usize,
    owners: &NestedSinkOwners,
) -> Option<SinkAttempt> {
    let mut start = 0usize;
    while start < pending.len() {
        if binding_has_access_after(use_index, write_index, stmt_index, pending[start].id) {
            start += 1;
            continue;
        }

        let run_start = start;
        let mut run_end = start;
        let mut mentioned_owners = Vec::new();
        while run_end < pending.len()
            && !binding_has_access_after(use_index, write_index, stmt_index, pending[run_end].id)
        {
            if let Some(owner) = owners.owner(pending[run_end].id) {
                mentioned_owners.push((run_end, owner));
            }
            run_end += 1;
        }

        let Some(&(_, first_owner)) = mentioned_owners.first() else {
            start = run_end;
            continue;
        };

        let mut owner_ends = vec![run_end; mentioned_owners.len()];
        for index in (0..mentioned_owners.len().saturating_sub(1)).rev() {
            owner_ends[index] = if mentioned_owners[index].1 == mentioned_owners[index + 1].1 {
                owner_ends[index + 1]
            } else {
                mentioned_owners[index + 1].0
            };
        }

        let candidates = std::iter::once((run_start, first_owner, owner_ends[0]))
            .chain(
                mentioned_owners
                    .iter()
                    .copied()
                    .zip(owner_ends)
                    .filter(|((index, _), _)| *index != run_start)
                    .map(|((index, owner), end)| (index, owner, end)),
            )
            // 候选拒绝[SemanticBarrier:Scope]：header 或多个 arm 同时 mention 的 binding
            // 没有唯一 nested owner，声明必须留在共同支配点。
            .filter(|(_, owner, _)| *owner != NestedSinkOwner::Blocked)
            .map(|(index, _, end)| (index, end));

        // 对每个真实 mention 起点只尝试 owner 改变前的最大切片。未提及 binding
        // 继续随同该组下沉，以保留并行赋值的声明/RHS 词法边界。
        for (slice_start, slice_end) in candidates {
            // owner 分组只能缩窄 candidate 的落点，不能缩窄 initializer 的依赖全集：
            // `if cond then a=b else use(b)` 会让 a 属于 Then、b 属于 Blocked，传入的
            // candidate slice 只有 a，但 b 仍必须固定在原 hoist 点。
            if let Some(attempt) = try_sink_hoisted_decl_into_nested_stmt(
                &pending[slice_start..slice_end],
                pending,
                stmt,
                use_index,
                write_index,
                stmt_index,
            ) {
                return Some(SinkAttempt {
                    start: slice_start,
                    consumed: attempt.consumed,
                    dependencies: attempt.dependencies,
                });
            }
        }

        start = run_end;
    }

    None
}

fn try_sink_hoisted_decl_into_nested_stmt(
    pending: &[super::super::common::AstLocalBinding],
    dependency_universe: &[super::super::common::AstLocalBinding],
    stmt: &mut AstStmt,
    use_index: &BindingUseIndex,
    write_index: &BindingWriteIndex,
    stmt_index: usize,
) -> Option<BlockSinkAttempt> {
    if !stmt_can_accept_nested_hoisted_sink(stmt) {
        return None;
    }

    let sinkable_len = pending
        .iter()
        .take_while(|binding| {
            !binding_has_access_after(use_index, write_index, stmt_index, binding.id)
        })
        .count();
    if sinkable_len == 0 {
        // 候选拒绝[SemanticBarrier:Scope]：后缀仍有读写，声明沉入子 block 会缩短所需作用域。
        return None;
    }
    let sinkable = &pending[..sinkable_len];
    let sinkable_refs = BindingRefSet::from_bindings(sinkable);

    let target_block = match stmt {
        AstStmt::If(if_stmt) => {
            if expr_references_binding_set(&if_stmt.cond, &sinkable_refs) {
                // 候选拒绝[SemanticBarrier:Scope]：条件先于 arm 执行；把条件读取的 binding 声明沉进 arm 会令该读取失去原绑定。
                return None;
            }
            let then_refs = block_references_binding_set(&if_stmt.then_block, &sinkable_refs);
            let else_refs = if_stmt
                .else_block
                .as_ref()
                .is_some_and(|block| block_references_binding_set(block, &sinkable_refs));
            if !then_refs && !else_refs {
                return None;
            }
            if then_refs && else_refs {
                // 候选拒绝[SemanticBarrier:ControlFlow]：两臂都读取 binding 时声明必须支配整个 if；沉入任一臂都会破坏另一条路径。
                return None;
            }

            if then_refs {
                &mut if_stmt.then_block
            } else {
                if_stmt
                    .else_block
                    .as_mut()
                    .expect("else refs imply else block")
            }
        }
        AstStmt::While(while_stmt) => {
            if expr_references_binding_set(&while_stmt.cond, &sinkable_refs) {
                // 候选拒绝[SemanticBarrier:Scope]：`while t do ... end` 的条件在 body 外且逐轮先求值，声明不能沉入 body。
                return None;
            }
            &mut while_stmt.body
        }
        AstStmt::Repeat(repeat_stmt) => {
            if expr_references_binding_set(&repeat_stmt.cond, &sinkable_refs) {
                // 候选拒绝[SemanticBarrier:Scope]：`until t` 与 body 共享外层词法域；把 `t` 声明沉入更窄子块会让条件不可见。
                return None;
            }
            &mut repeat_stmt.body
        }
        AstStmt::NumericFor(numeric_for) => {
            if expr_references_binding_set(&numeric_for.start, &sinkable_refs)
                || expr_references_binding_set(&numeric_for.limit, &sinkable_refs)
                || expr_references_binding_set(&numeric_for.step, &sinkable_refs)
            {
                // 候选拒绝[SemanticBarrier:Scope]：numeric-for header 在循环 binding/body 作用域建立前求值，声明不能沉入 body。
                return None;
            }
            &mut numeric_for.body
        }
        AstStmt::GenericFor(generic_for) => {
            if generic_for
                .iterator
                .iter()
                .any(|expr| expr_references_binding_set(expr, &sinkable_refs))
            {
                // 候选拒绝[SemanticBarrier:Scope]：generic-for iterator 在 body 外求值，沉入 body 会改变 header 的绑定解析。
                return None;
            }
            &mut generic_for.body
        }
        AstStmt::DoBlock(inner) => inner,
        AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::LocalDecl(_)
        | AstStmt::GlobalDecl(_)
        | AstStmt::Assign(_)
        | AstStmt::CallStmt(_)
        | AstStmt::Return(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => return None,
    };
    let attempt = sink_pending_bindings_into_block(target_block, sinkable, dependency_universe);
    (attempt.consumed > 0).then_some(attempt)
}

fn stmt_can_accept_nested_hoisted_sink(stmt: &AstStmt) -> bool {
    // 嵌套下沉只可能改写带子 block 的语句。对普通赋值/调用/return 先做
    // pending 全量搜索没有语义收益，在大函数的块首 hoisted local 上会放大成性能黑洞。
    matches!(
        stmt,
        AstStmt::If(_)
            | AstStmt::While(_)
            | AstStmt::Repeat(_)
            | AstStmt::NumericFor(_)
            | AstStmt::GenericFor(_)
            | AstStmt::DoBlock(_)
    )
}

/// 每个写入分支都消费非空 binding；零消费意味着原块未变，调用方可继续尝试其它候选。
fn sink_pending_bindings_into_block(
    block: &mut AstBlock,
    pending: &[super::super::common::AstLocalBinding],
    dependency_universe: &[super::super::common::AstLocalBinding],
) -> BlockSinkAttempt {
    let use_index = BindingUseIndex::for_stmts(&block.stmts);
    let write_index = BindingWriteIndex::for_stmts(&block.stmts);
    let forward_gotos = ForwardGotoIndex::new(&block.stmts);
    let mut consumed = 0usize;
    let mut index = 0usize;
    while index < block.stmts.len() && consumed < pending.len() {
        let remaining = &pending[consumed..];
        let crosses_forward_goto = forward_gotos.has_forward_goto_past_index(index);
        let enters_backward_cycle = forward_gotos.insertion_enters_backward_cycle(index);
        if crosses_forward_goto || enters_backward_cycle {
            if enters_backward_cycle {
                // 候选拒绝[SemanticBarrier:ControlFlow]：pending 声明位于子 block 外；若在
                // `::L:: ... goto L` 区间内新建 local，会把同一外层 cell 改成逐轮 cell。
            } else {
                // 候选拒绝[SemanticBarrier:Scope]：已有 forward goto 跨过此点时新增 local 会制造非法的“跳入 local 作用域”。
            }
            if stmt_references_binding_set(
                &block.stmts[index],
                &BindingRefSet::from_bindings(remaining),
            ) {
                // 当前首次读取点本身不能接收声明；继续扫描后再插入会让这次读取落到
                // 声明之前，因此本层没有合法 sink。
                return BlockSinkAttempt {
                    consumed,
                    dependencies: Vec::new(),
                };
            }
            index += 1;
            continue;
        }
        if let Some(attempt) = try_sink_hoisted_decl_into_stmt(
            remaining,
            dependency_universe,
            &mut block.stmts[index],
            &use_index,
            0,
            index,
        ) {
            consumed += attempt.consumed;
            if !attempt.dependencies.is_empty() {
                // 依赖仍须由最外层 hoisted 声明支配 RHS；立即上送，避免本次子块扫描
                // 把它继续沉到 initializer 之后。
                return BlockSinkAttempt {
                    consumed,
                    dependencies: attempt.dependencies,
                };
            }
            index += 1;
            continue;
        }
        if let Some(nested_attempt) = try_sink_hoisted_decl_into_nested_stmt(
            remaining,
            dependency_universe,
            &mut block.stmts[index],
            &use_index,
            &write_index,
            index,
        ) {
            consumed += nested_attempt.consumed;
            if !nested_attempt.dependencies.is_empty() {
                return BlockSinkAttempt {
                    consumed,
                    dependencies: nested_attempt.dependencies,
                };
            }
            continue;
        }
        let remaining_refs = BindingRefSet::from_bindings(remaining);
        if stmt_references_binding_set(&block.stmts[index], &remaining_refs) {
            // 该 binding 在此语句中被使用，但无法直接合并或下沉到嵌套块里
            // （例如在某个嵌套 `if` 内赋值但在后续兄弟节点中读取）。
            // 在此语句前插入裸 `local` 声明，使声明处于最窄的包围作用域。
            let decl = AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings: remaining.to_vec(),
                values: vec![],
                initializer_merge_transaction: None,
                initializer_root_profile: None,
            }));
            block.stmts.insert(index, decl);
            consumed += remaining.len();
            break;
        }
        index += 1;
    }
    BlockSinkAttempt {
        consumed,
        dependencies: Vec::new(),
    }
}

fn single_value_local_decl(
    stmt: &AstStmt,
) -> Option<(
    &super::super::common::AstLocalBinding,
    &super::super::common::AstExpr,
)> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [value] = local_decl.values.as_slice() else {
        return None;
    };
    Some((binding, value))
}

// 完整证明后才移动原 RHS，并清除已消费的 transaction/profile；
// 失败须保持 declaration 和 assignment 原样，不能提交半次初始化合并。
fn try_merge_local_decl_with_assign(current: &mut AstStmt, next: &mut AstStmt) -> bool {
    let AstStmt::LocalDecl(local_decl) = current else {
        return false;
    };
    let AstStmt::Assign(assign) = next else {
        return false;
    };
    if !local_decl.values.is_empty() || local_decl.bindings.is_empty() {
        return false;
    }
    if local_decl
        .bindings
        .iter()
        .any(|binding| binding.attr != AstLocalAttr::None)
    {
        // `<const>`/`<close>` local 在目标 Lua 中不可在声明后
        // 普通赋值；该异常 AST pair 不属于 initializer merge 候选。
        return false;
    }
    if local_decl
        .bindings
        .iter()
        .any(|binding| binding.origin.is_debug_hinted())
    {
        // 候选拒绝[SemanticBarrier:DebugScope]：regress_342 中条件调用通过 `debug.getlocal`
        // 观察空声明；合并到 initializer 会把 debug local 的作用域起点后移到调用之后。
        return false;
    }
    if local_decl
        .bindings
        .iter()
        .any(|binding| !binding.rewrite_authority.may_move_scope_start())
    {
        // 候选拒绝[LayerBoundary]：initializer merge 会把空声明起点移动到赋值处；
        // HIR 已保留的 binding 不能由 AST 重新缩短。
        return false;
    }
    if local_decl.bindings.len() != assign.targets.len() || assign.values.is_empty() {
        return false;
    }
    if !local_decl
        .bindings
        .iter()
        .zip(assign.targets.iter())
        .all(|(binding, target)| local_binding_matches_target(binding.id, target))
    {
        return false;
    }
    if stmt_references_any_binding_in_assign(assign, &local_decl.bindings) {
        // 候选拒绝[SemanticBarrier:Scope]：`local x; x = function() return x end` 合成 initializer 后 closure 捕获点的词法绑定会改变。
        return false;
    }

    let initializer_merge_transaction = match (
        local_decl.initializer_merge_transaction,
        assign.initializer_merge_transaction,
    ) {
        (Some(decl), Some(assign)) if decl == assign => Some(decl),
        (None, None) => None,
        _ => return false,
    };
    if initializer_merge_transaction.is_none()
        && local_decl
            .bindings
            .iter()
            .any(|binding| binding.origin.is_physical_root())
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：空 PhysicalRoot declaration 会先用 nil
        // 清空复用的 VM home；只有 HIR 为这一对最终节点发布的同 token transaction
        // 才能证明这次 initializer merge 不会把旧 root 延长过 RHS 求值。
        return false;
    }

    local_decl.values = std::mem::take(&mut assign.values);
    // certificate 是一次性 rewrite authority；合并完成后不属于新声明的持续事实。
    local_decl.initializer_merge_transaction = None;
    local_decl.initializer_root_profile = None;
    true
}

fn hoisted_temp_bindings(stmt: &AstStmt) -> Option<Vec<super::super::common::AstLocalBinding>> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    if !local_decl.values.is_empty() || local_decl.bindings.is_empty() {
        return None;
    }
    if local_decl
        .bindings
        .iter()
        .any(|binding| binding.attr != AstLocalAttr::None || !is_temp_like_binding(binding.id))
    {
        // 属性声明和非 temp binding 不属于 hoisted-temp 下沉候选。
        return None;
    }
    if local_decl
        .bindings
        .iter()
        .any(|binding| binding.origin.is_debug_hinted())
    {
        // 候选拒绝[SemanticBarrier:DebugScope]：DebugHinted temp 的原声明起点是已保留的
        // source identity，下沉会缩短 debug.getlocal 可见期。
        return None;
    }
    if local_decl
        .bindings
        .iter()
        .any(|binding| binding.origin.is_physical_root())
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot 的空声明在 hoist 点清空旧 VM
        // root；下沉到赋值点会让旧对象跨过中间 GC/弱表观察继续存活。
        return None;
    }
    if local_decl
        .bindings
        .iter()
        .any(|binding| !binding.rewrite_authority.may_move_scope_start())
    {
        // 候选拒绝[LayerBoundary]：hoisted binding 的声明起点由 HIR 冻结，不能下沉。
        return None;
    }
    Some(local_decl.bindings.clone())
}

fn try_sink_hoisted_decl_into_stmt(
    pending: &[super::super::common::AstLocalBinding],
    dependency_universe: &[super::super::common::AstLocalBinding],
    stmt: &mut AstStmt,
    use_index: &BindingUseIndex,
    prior_start: usize,
    target_index: usize,
) -> Option<SinkAttempt> {
    let AstStmt::Assign(assign) = stmt else {
        return None;
    };
    if assign.values.is_empty() || assign.targets.is_empty() || assign.targets.len() > pending.len()
    {
        return None;
    }
    let candidate = &pending[..assign.targets.len()];
    if candidate
        .iter()
        .any(|binding| use_index.count_uses_in_range(prior_start, target_index, binding.id) != 0)
    {
        // 候选拒绝[SemanticBarrier:Scope]：binding 在声明点与赋值点之间已经被读过；下沉后这些读取会落到外层或未声明名字。
        return None;
    }
    if !candidate
        .iter()
        .zip(assign.targets.iter())
        .all(|(binding, target)| local_binding_matches_target(binding.id, target))
    {
        return None;
    }
    if stmt_references_any_binding_in_assign(assign, candidate) {
        // 候选拒绝[SemanticBarrier:Scope]：赋值 RHS 读取候选 binding 时，改成 local initializer 会把读取解析到新声明之前的外层绑定。
        return None;
    }
    let dependencies =
        rhs_dependencies_outside_candidate(use_index, target_index, dependency_universe);
    let merged = AstLocalDecl {
        bindings: candidate.to_vec(),
        values: std::mem::take(&mut assign.values),
        initializer_merge_transaction: None,
        initializer_root_profile: None,
    };
    *stmt = AstStmt::LocalDecl(Box::new(merged));
    Some(SinkAttempt {
        start: 0,
        consumed: candidate.len(),
        dependencies,
    })
}

fn is_temp_like_binding(binding: AstBindingRef) -> bool {
    matches!(
        binding,
        AstBindingRef::Temp(_) | AstBindingRef::SyntheticLocal(_)
    )
}

/// 与 [`try_sink_hoisted_decl_into_stmt`] 类似，但在 `pending` 中任意位置搜索
/// 匹配的 binding，而非仅要求它们位于头部。成功时 attempt 同时携带匹配起点、
/// 消费数量和必须留在原 hoist 点的 RHS 依赖；声明直接安装到原语句。
fn try_sink_hoisted_decl_into_stmt_anywhere(
    pending: &[super::super::common::AstLocalBinding],
    dependency_universe: &[super::super::common::AstLocalBinding],
    stmt: &mut AstStmt,
    use_index: &BindingUseIndex,
    prior_start: usize,
    target_index: usize,
    suffix_start: usize,
) -> Option<SinkAttempt> {
    let AstStmt::Assign(assign) = stmt else {
        return None;
    };
    if assign.values.is_empty() || assign.targets.is_empty() || assign.targets.len() > pending.len()
    {
        return None;
    }
    let target_len = assign.targets.len();
    for start in 0..=pending.len() - target_len {
        let candidate = &pending[start..start + target_len];
        if candidate.iter().any(|binding| {
            use_index.count_uses_in_range(prior_start, target_index, binding.id) != 0
        }) {
            // 候选拒绝[SemanticBarrier:Scope]：候选 binding 在下沉区间已被读取，移动声明会让先前读取失去原 local。
            continue;
        }
        if !candidate
            .iter()
            .zip(assign.targets.iter())
            .all(|(binding, target)| local_binding_matches_target(binding.id, target))
        {
            continue;
        }
        if stmt_references_any_binding_in_assign(assign, candidate) {
            // 候选拒绝[SemanticBarrier:Scope]：RHS 自引用在 local initializer 中解析到外层，不能与后置赋值等同。
            continue;
        }
        // 只有当所有候选 binding 在此语句之后不再被使用时才允许下沉。
        if candidate
            .iter()
            .any(|b| use_index.count_uses_in_suffix(suffix_start, b.id) != 0)
        {
            // 候选拒绝[SemanticBarrier:Scope]：候选在赋值后仍活跃，沉入当前位置会缩窄其作用域并破坏后缀读取。
            continue;
        }
        let dependencies =
            rhs_dependencies_outside_candidate(use_index, target_index, dependency_universe);
        let merged = AstLocalDecl {
            bindings: candidate.to_vec(),
            values: std::mem::take(&mut assign.values),
            initializer_merge_transaction: None,
            initializer_root_profile: None,
        };
        *stmt = AstStmt::LocalDecl(Box::new(merged));
        return Some(SinkAttempt {
            start,
            consumed: candidate.len(),
            dependencies,
        });
    }
    None
}

fn rhs_dependencies_outside_candidate(
    use_index: &BindingUseIndex,
    target_index: usize,
    dependency_universe: &[super::super::common::AstLocalBinding],
) -> Vec<AstBindingRef> {
    // 目标已证明全是普通名字，故该行 Read/Capture 精确等于 RHS 引用；candidate
    // 自引用也已拒绝。当前 Assign 尚未改写，直接消费原索引，不逐 binding 重走 RHS。
    dependency_universe
        .iter()
        .filter(|binding| {
            use_index.count_uses_in_range(target_index, target_index + 1, binding.id) != 0
        })
        .map(|binding| binding.id)
        .collect()
}

fn pin_sink_dependencies(
    remaining: &mut Vec<super::super::common::AstLocalBinding>,
    pinned: &mut Vec<super::super::common::AstLocalBinding>,
    dependencies: &[AstBindingRef],
) {
    pinned.extend(remaining.extract_if(.., |binding| dependencies.contains(&binding.id)));
}

fn stmt_references_any_binding_in_assign(
    assign: &super::super::common::AstAssign,
    bindings: &[super::super::common::AstLocalBinding],
) -> bool {
    let refs = BindingRefSet::from_bindings(bindings);
    assign
        .values
        .iter()
        .any(|value| expr_references_binding_set(value, &refs))
}

fn is_mergeable_adjacent_local_value(expr: &super::super::common::AstExpr) -> bool {
    expr_complexity(expr) <= ADJACENT_LOCAL_VALUE_COMPLEXITY_LIMIT && is_copy_like_expr(expr)
}

fn local_binding_matches_target(binding: AstBindingRef, target: &AstLValue) -> bool {
    matches!(target, AstLValue::Name(name) if binding.matches_name_ref(name))
}

struct ForwardGotoIndex {
    has_forward_goto_past_index: Vec<bool>,
    backward_goto_ranges: Vec<(usize, usize)>,
}

impl ForwardGotoIndex {
    fn new(stmts: &[AstStmt]) -> Self {
        let goto_targets_by_stmt = stmts.iter().map(collect_goto_targets).collect::<Vec<_>>();
        let labels_by_stmt = stmts
            .iter()
            .map(|stmt| match stmt {
                AstStmt::Label(label) => Some(label.id),
                _ => None,
            })
            .collect::<Vec<_>>();
        let label_positions = labels_by_stmt
            .iter()
            .enumerate()
            .filter_map(|(index, label)| label.map(|label| (label, index)))
            .collect::<BTreeMap<_, _>>();
        let backward_goto_ranges = goto_targets_by_stmt
            .iter()
            .enumerate()
            .flat_map(|(goto_index, targets)| {
                let label_positions = &label_positions;
                targets.iter().filter_map(move |target| {
                    let label_index = *label_positions.get(target)?;
                    (label_index < goto_index).then_some((label_index, goto_index))
                })
            })
            .collect();

        let mut future_labels: BTreeSet<AstLabelId> =
            labels_by_stmt.iter().skip(1).flatten().copied().collect();
        let mut prefix_goto_targets = BTreeSet::new();
        let mut matched_forward_targets = 0usize;
        let mut has_forward_goto_past_index = Vec::with_capacity(stmts.len());

        for (index, targets) in goto_targets_by_stmt.iter().enumerate() {
            has_forward_goto_past_index.push(matched_forward_targets > 0);

            for target in targets {
                if prefix_goto_targets.insert(*target) && future_labels.contains(target) {
                    matched_forward_targets += 1;
                }
            }

            if let Some(label) = labels_by_stmt.get(index + 1).and_then(|label| *label)
                && future_labels.remove(&label)
                && prefix_goto_targets.contains(&label)
            {
                matched_forward_targets -= 1;
            }
        }

        Self {
            has_forward_goto_past_index,
            backward_goto_ranges,
        }
    }

    fn has_forward_goto_past_index(&self, index: usize) -> bool {
        self.has_forward_goto_past_index
            .get(index)
            .copied()
            .unwrap_or(false)
    }

    fn move_enters_backward_cycle(&self, from_index: usize, to_index: usize) -> bool {
        self.backward_goto_ranges
            .iter()
            .any(|&(label_index, goto_index)| {
                from_index <= label_index && label_index < to_index && to_index <= goto_index
            })
    }

    fn insertion_enters_backward_cycle(&self, index: usize) -> bool {
        self.backward_goto_ranges
            .iter()
            .any(|&(label_index, goto_index)| label_index < index && index <= goto_index)
    }
}

fn collect_goto_targets(stmt: &AstStmt) -> BTreeSet<AstLabelId> {
    let mut targets = BTreeSet::new();
    any_stmt_structure(stmt, &mut |stmt| {
        if let AstStmt::Goto(goto_stmt) = stmt {
            targets.insert(goto_stmt.target);
        }
        false
    });
    targets
}
