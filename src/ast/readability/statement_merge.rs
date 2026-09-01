//! 这个文件负责把被前层机械拆开的相邻语句重新合并回更像源码的一次声明。
//!
//! 它依赖 binding/use 分析已经给出稳定引用关系，因此这里只合并“明显属于同一段
//! 源码声明”的 local/assign/temp-hoist 形状，而不会越权跨阶段重排有副作用的语句。
//! 这一步的目标是消掉 VM/结构恢复留下的机械拆分，不是随意把多条语句压成一行。
//!
//! 例子：
//! - `local a; a = f()` 会合成 `local a = f()`
//! - `local a = x; local b = y` 在两者确实属于同一组声明且后续使用形状允许时，
//!   会合成 `local a, b = x, y`
//! - 单次使用的独立 local 会留给 `inline-exprs`，不会先被并入后层无法拆开的 multi-local
//! - 提前 hoist 出来的 `local t0; if cond then t0 = x end` 会尽量把 `t0` 下沉回
//!   真正使用它的分支/循环体里
//! - 如果同一条 hoisted 声明里前面的 carried binding 还要跨分支后缀继续活着，
//!   后面的 `staged` 之类一次性临时 binding 仍应允许单独沉回某个分支
//! - 但如果当前位置之前已经有会跳到更后面 label 的 forward goto，
//!   这里会停止继续下沉，避免生成“goto 跳进 local 作用域”的非法 Lua
//! - 如果某个 hoisted temp 在声明点与候选下沉点之间已经被读取过，也不能把它下沉
//!   成后置 `local`，否则 fallback/goto 回边会读到未初始化的局部变量
//! - repeat body 的 until 条件是正文之后的读取，引用到的声明不能沉入更窄的嵌套块

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::super::common::{
    AstBindingRef, AstBlock, AstExpr, AstLValue, AstLabelId, AstLocalAttr, AstLocalBinding,
    AstLocalDecl, AstModule, AstStmt,
};
use super::ReadabilityContext;
use super::binding_flow::{
    BindingRefSet, BindingUseIndex, binding_mentions_in_block, binding_mentions_in_expr,
    block_references_binding_set, expr_references_any_binding, expr_references_binding_set,
    stmt_references_any_binding, stmt_references_binding_set,
};
use super::expr_analysis::{expr_complexity, is_copy_like_expr, is_discard_safe_expr};
use super::visit::{self, AstVisitor};
use super::walk::{self, AstRewritePass, BlockKind};

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
    while let Some(stmt) = old_stmts.pop_front() {
        let Some(next_stmt) = old_stmts.front() else {
            new_stmts.push(stmt);
            continue;
        };

        if let Some(merged) = try_merge_local_decl_with_assign(&stmt, next_stmt) {
            new_stmts.push(AstStmt::LocalDecl(Box::new(merged)));
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
        if bindings
            .iter()
            .any(|binding| binding.origin.is_debug_hinted())
        {
            // 候选拒绝[SemanticBarrier:DebugScope]：`local debug_name; local t` 合并后，
            // 首个 binding 要到第二条声明之后才进入作用域；原第二行的 line hook 本可
            // 通过 debug.getlocal 观察它，合并会丢失这段已保留的源码可见期。
            new_stmts.push(stmt);
            continue;
        }

        let mut merged_bindings = bindings.to_vec();
        let mut consumed = 0;
        for next_bindings in old_stmts.iter().map_while(empty_local_decl_bindings) {
            if next_bindings
                .iter()
                .any(|binding| binding.origin.is_debug_hinted())
            {
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

fn merge_adjacent_single_value_local_decls(
    block: &mut AstBlock,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&old_stmts, trailing_condition);
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
        if binding.origin.is_debug_hinted() {
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
        if binding_is_owned_by_inline_exprs(&use_index, index + 1, binding) {
            // 候选拒绝[LayerBoundary]：单次-use 的独立 local 保持为 inline-exprs
            // candidate；若先并入 multi-local，后层将无法再消费该 binding。
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
            if next_binding.origin.is_debug_hinted() {
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
            if binding_is_owned_by_inline_exprs(&use_index, lookahead + 1, next_binding) {
                // 候选拒绝[LayerBoundary]：单次-use 声明是当前连续 merge run 的分段点；
                // 已形成的前缀仍可合并，该声明及其后缀交给后续扫描与 inline-exprs。
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
            && bindings
                .iter()
                .any(|b| use_index.count_uses_in_suffix(lookahead, b.id) > 1)
        {
            new_stmts.push(AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings,
                values,
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

fn binding_is_owned_by_inline_exprs(
    use_index: &BindingUseIndex,
    suffix_start: usize,
    binding: &AstLocalBinding,
) -> bool {
    super::inline_exprs::local_attr_belongs_to_inline_pipeline(binding.attr)
        && use_index.count_uses_in_suffix(suffix_start, binding.id) == 1
}

fn sink_hoisted_temp_decls(block: &mut AstBlock, trailing_condition: Option<&AstExpr>) -> bool {
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&block.stmts, trailing_condition);
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
                let mut remaining_index = 0;
                while remaining_index < remaining.len() {
                    if stmt_references_any_binding(
                        &block.stmts[lookahead],
                        std::slice::from_ref(&remaining[remaining_index]),
                    ) {
                        pinned.push(remaining.remove(remaining_index));
                    } else {
                        remaining_index += 1;
                    }
                }
                lookahead += 1;
                continue;
            }
            if let Some(attempt) = try_sink_hoisted_decl_into_stmt(
                &remaining,
                &remaining,
                &block.stmts[lookahead],
                &use_index,
                index + 1,
                lookahead,
            ) {
                let consumed = attempt.merged.bindings.len();
                block.stmts[lookahead] = AstStmt::LocalDecl(Box::new(attempt.merged));
                remaining.drain(..consumed);
                pin_sink_dependencies(&mut remaining, &mut pinned, &attempt.dependencies);
                sink_changed = true;
                lookahead += 1;
                continue;
            }
            if let Some(attempt) = try_sink_hoisted_decl_into_nested_stmt_anywhere(
                &remaining,
                &block.stmts[lookahead],
                &use_index,
                lookahead + 1,
            ) {
                block.stmts[lookahead] = attempt.rewritten;
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
                &block.stmts[lookahead],
                &use_index,
                index + 1,
                lookahead,
                lookahead + 1,
            ) {
                let consumed = attempt.merged.bindings.len();
                block.stmts[lookahead] = AstStmt::LocalDecl(Box::new(attempt.merged));
                remaining.drain(attempt.start..attempt.start + consumed);
                pin_sink_dependencies(&mut remaining, &mut pinned, &attempt.dependencies);
                sink_changed = true;
                lookahead += 1;
                continue;
            }
            let remaining_refs = BindingRefSet::from_bindings(&remaining);
            if stmt_references_binding_set(&block.stmts[lookahead], &remaining_refs) {
                // 钉住被引用但无法下沉的 binding：它们的声明必须留在提升位置，
                // 但其他 binding 仍然可能被下沉到后续语句里。
                // 候选拒绝[SemanticBarrier:Scope]：当前语句已经读取却无法成为声明 sink 的 binding 必须继续由 hoisted 声明支配。
                let mut i = 0;
                while i < remaining.len() {
                    if stmt_references_any_binding(
                        &block.stmts[lookahead],
                        std::slice::from_ref(&remaining[i]),
                    ) {
                        pinned.push(remaining.remove(i));
                    } else {
                        i += 1;
                    }
                }
                lookahead += 1;
                continue;
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
        return true;
    }
    false
}

struct NestedSinkAttempt {
    rewritten: AstStmt,
    start: usize,
    consumed: usize,
    dependencies: Vec<AstBindingRef>,
}

struct BlockSinkAttempt {
    consumed: usize,
    dependencies: Vec<AstBindingRef>,
}

struct DirectSinkAttempt {
    start: usize,
    merged: AstLocalDecl,
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

fn try_sink_hoisted_decl_into_nested_stmt_anywhere(
    pending: &[super::super::common::AstLocalBinding],
    stmt: &AstStmt,
    use_index: &BindingUseIndex,
    suffix_start: usize,
) -> Option<NestedSinkAttempt> {
    let owners = NestedSinkOwners::new(stmt)?;

    let mut start = 0usize;
    while start < pending.len() {
        if use_index.count_uses_in_suffix(suffix_start, pending[start].id) != 0 {
            // 候选拒绝[SemanticBarrier:Scope]：binding 在候选嵌套语句之后仍被读取，沉入该子 block 会使后缀读取越出词法作用域。
            start += 1;
            continue;
        }

        let run_start = start;
        let mut run_end = start;
        let mut mentioned_owners = Vec::new();
        while run_end < pending.len()
            && use_index.count_uses_in_suffix(suffix_start, pending[run_end].id) == 0
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
            if let Some((rewritten, attempt)) = try_sink_hoisted_decl_into_nested_stmt(
                &pending[slice_start..slice_end],
                pending,
                stmt,
                use_index,
                suffix_start,
            ) {
                return Some(NestedSinkAttempt {
                    rewritten,
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
    stmt: &AstStmt,
    use_index: &BindingUseIndex,
    suffix_start: usize,
) -> Option<(AstStmt, BlockSinkAttempt)> {
    if !stmt_can_accept_nested_hoisted_sink(stmt) {
        return None;
    }

    let sinkable_len = pending
        .iter()
        .take_while(|binding| use_index.count_uses_in_suffix(suffix_start, binding.id) == 0)
        .count();
    if sinkable_len == 0 {
        // 候选拒绝[SemanticBarrier:Scope]：所有 pending binding 都在 nested stmt 后仍有 use，沉入子 block 会让后缀读取越出作用域。
        return None;
    }
    let sinkable = &pending[..sinkable_len];
    let sinkable_refs = BindingRefSet::from_bindings(sinkable);

    match stmt {
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

            let mut rewritten = stmt.clone();
            let target_block = match &mut rewritten {
                AstStmt::If(if_stmt) if then_refs => &mut if_stmt.then_block,
                AstStmt::If(if_stmt) => if_stmt
                    .else_block
                    .as_mut()
                    .expect("else refs imply else block"),
                _ => unreachable!("rewritten stmt must remain if"),
            };
            let attempt =
                sink_pending_bindings_into_block(target_block, sinkable, dependency_universe);
            (attempt.consumed > 0).then_some((rewritten, attempt))
        }
        AstStmt::While(while_stmt) => {
            if expr_references_binding_set(&while_stmt.cond, &sinkable_refs) {
                // 候选拒绝[SemanticBarrier:Scope]：`while t do ... end` 的条件在 body 外且逐轮先求值，声明不能沉入 body。
                return None;
            }
            let mut rewritten = stmt.clone();
            let AstStmt::While(while_stmt) = &mut rewritten else {
                unreachable!("rewritten stmt must remain while");
            };
            let attempt = sink_pending_bindings_into_block(
                &mut while_stmt.body,
                sinkable,
                dependency_universe,
            );
            (attempt.consumed > 0).then_some((rewritten, attempt))
        }
        AstStmt::Repeat(repeat_stmt) => {
            if expr_references_binding_set(&repeat_stmt.cond, &sinkable_refs) {
                // 候选拒绝[SemanticBarrier:Scope]：`until t` 与 body 共享外层词法域；把 `t` 声明沉入更窄子块会让条件不可见。
                return None;
            }
            let mut rewritten = stmt.clone();
            let AstStmt::Repeat(repeat_stmt) = &mut rewritten else {
                unreachable!("rewritten stmt must remain repeat");
            };
            let attempt = sink_pending_bindings_into_block(
                &mut repeat_stmt.body,
                sinkable,
                dependency_universe,
            );
            (attempt.consumed > 0).then_some((rewritten, attempt))
        }
        AstStmt::NumericFor(numeric_for) => {
            if expr_references_binding_set(&numeric_for.start, &sinkable_refs)
                || expr_references_binding_set(&numeric_for.limit, &sinkable_refs)
                || expr_references_binding_set(&numeric_for.step, &sinkable_refs)
            {
                // 候选拒绝[SemanticBarrier:Scope]：numeric-for header 在循环 binding/body 作用域建立前求值，声明不能沉入 body。
                return None;
            }
            let mut rewritten = stmt.clone();
            let AstStmt::NumericFor(numeric_for) = &mut rewritten else {
                unreachable!("rewritten stmt must remain numeric-for");
            };
            let attempt = sink_pending_bindings_into_block(
                &mut numeric_for.body,
                sinkable,
                dependency_universe,
            );
            (attempt.consumed > 0).then_some((rewritten, attempt))
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
            let mut rewritten = stmt.clone();
            let AstStmt::GenericFor(generic_for) = &mut rewritten else {
                unreachable!("rewritten stmt must remain generic-for");
            };
            let attempt = sink_pending_bindings_into_block(
                &mut generic_for.body,
                sinkable,
                dependency_universe,
            );
            (attempt.consumed > 0).then_some((rewritten, attempt))
        }
        AstStmt::DoBlock(inner) => {
            let mut rewritten = AstBlock {
                stmts: inner.stmts.clone(),
            };
            let attempt =
                sink_pending_bindings_into_block(&mut rewritten, sinkable, dependency_universe);
            (attempt.consumed > 0).then_some((AstStmt::DoBlock(Box::new(rewritten)), attempt))
        }
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
        | AstStmt::Error(_) => None,
    }
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

fn sink_pending_bindings_into_block(
    block: &mut AstBlock,
    pending: &[super::super::common::AstLocalBinding],
    dependency_universe: &[super::super::common::AstLocalBinding],
) -> BlockSinkAttempt {
    let use_index = BindingUseIndex::for_stmts(&block.stmts);
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
            &block.stmts[index],
            &use_index,
            0,
            index,
        ) {
            let merged_len = attempt.merged.bindings.len();
            block.stmts[index] = AstStmt::LocalDecl(Box::new(attempt.merged));
            consumed += merged_len;
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
        if let Some((rewritten, nested_attempt)) = try_sink_hoisted_decl_into_nested_stmt(
            remaining,
            dependency_universe,
            &block.stmts[index],
            &use_index,
            index + 1,
        ) {
            block.stmts[index] = rewritten;
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

fn try_merge_local_decl_with_assign(current: &AstStmt, next: &AstStmt) -> Option<AstLocalDecl> {
    let AstStmt::LocalDecl(local_decl) = current else {
        return None;
    };
    let AstStmt::Assign(assign) = next else {
        return None;
    };
    if !local_decl.values.is_empty() || local_decl.bindings.is_empty() {
        return None;
    }
    if local_decl
        .bindings
        .iter()
        .any(|binding| binding.attr != AstLocalAttr::None)
    {
        // `<const>`/`<close>` local 在目标 Lua 中不可在声明后
        // 普通赋值；该异常 AST pair 不属于 initializer merge 候选。
        return None;
    }
    if local_decl
        .bindings
        .iter()
        .any(|binding| binding.origin.is_debug_hinted())
    {
        // 候选拒绝[SemanticBarrier:DebugScope]：regress_342 中条件调用通过 `debug.getlocal`
        // 观察空声明；合并到 initializer 会把 debug local 的作用域起点后移到调用之后。
        return None;
    }
    if local_decl
        .bindings
        .iter()
        .any(|binding| binding.origin.is_physical_root())
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：空 PhysicalRoot declaration 会先用 nil
        // 清空复用的 VM home；合并成 initializer 会把清空推迟到 RHS 求值之后，
        // RHS 内的 GC/弱表观察可以看到旧对象继续存活（regress_435）。
        return None;
    }
    if local_decl.bindings.len() != assign.targets.len() || assign.values.is_empty() {
        return None;
    }
    if !local_decl
        .bindings
        .iter()
        .zip(assign.targets.iter())
        .all(|(binding, target)| local_binding_matches_target(binding.id, target))
    {
        return None;
    }
    if stmt_references_any_binding_in_assign(assign, &local_decl.bindings) {
        // 候选拒绝[SemanticBarrier:Scope]：`local x; x = function() return x end` 合成 initializer 后 closure 捕获点的词法绑定会改变。
        return None;
    }

    Some(AstLocalDecl {
        bindings: local_decl.bindings.clone(),
        values: assign.values.clone(),
    })
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
    Some(local_decl.bindings.clone())
}

fn try_sink_hoisted_decl_into_stmt(
    pending: &[super::super::common::AstLocalBinding],
    dependency_universe: &[super::super::common::AstLocalBinding],
    stmt: &AstStmt,
    use_index: &BindingUseIndex,
    prior_start: usize,
    target_index: usize,
) -> Option<DirectSinkAttempt> {
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
    Some(DirectSinkAttempt {
        start: 0,
        merged: AstLocalDecl {
            bindings: candidate.to_vec(),
            values: assign.values.clone(),
        },
        dependencies: rhs_dependencies_outside_candidate(assign, dependency_universe, candidate),
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
/// 合并声明和必须留在原 hoist 点的 RHS 依赖。
fn try_sink_hoisted_decl_into_stmt_anywhere(
    pending: &[super::super::common::AstLocalBinding],
    dependency_universe: &[super::super::common::AstLocalBinding],
    stmt: &AstStmt,
    use_index: &BindingUseIndex,
    prior_start: usize,
    target_index: usize,
    suffix_start: usize,
) -> Option<DirectSinkAttempt> {
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
        return Some(DirectSinkAttempt {
            start,
            merged: AstLocalDecl {
                bindings: candidate.to_vec(),
                values: assign.values.clone(),
            },
            dependencies: rhs_dependencies_outside_candidate(
                assign,
                dependency_universe,
                candidate,
            ),
        });
    }
    None
}

fn rhs_dependencies_outside_candidate(
    assign: &super::super::common::AstAssign,
    dependency_universe: &[super::super::common::AstLocalBinding],
    candidate: &[super::super::common::AstLocalBinding],
) -> Vec<AstBindingRef> {
    // candidate 自引用由调用方拒绝；其余 RHS 引用随成功 attempt 返回，并在下一次
    // sink 前固定到原 hoist 点，因而 initializer 的词法解析保持不变。
    dependency_universe
        .iter()
        .filter(|binding| !candidate.iter().any(|item| item.id == binding.id))
        .filter(|binding| {
            stmt_references_any_binding_in_assign(assign, std::slice::from_ref(binding))
        })
        .map(|binding| binding.id)
        .collect()
}

fn pin_sink_dependencies(
    remaining: &mut Vec<super::super::common::AstLocalBinding>,
    pinned: &mut Vec<super::super::common::AstLocalBinding>,
    dependencies: &[AstBindingRef],
) {
    let mut index = 0;
    while index < remaining.len() {
        if dependencies.contains(&remaining[index].id) {
            pinned.push(remaining.remove(index));
        } else {
            index += 1;
        }
    }
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
    let mut visitor = GotoTargetCollector {
        targets: BTreeSet::new(),
    };
    visit::visit_stmt(stmt, &mut visitor);
    visitor.targets
}

struct GotoTargetCollector {
    targets: BTreeSet<AstLabelId>,
}

impl AstVisitor for GotoTargetCollector {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        if let AstStmt::Goto(goto_stmt) = stmt {
            self.targets.insert(goto_stmt.target);
        }
    }

    fn visit_function_expr(&mut self, _function: &super::super::common::AstFunctionExpr) -> bool {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::common::{
        AstAssign, AstCallExpr, AstGlobalName, AstGoto, AstIf, AstLabel, AstLocalOrigin, AstNameRef,
    };
    use crate::hir::{LocalId, TempId};

    fn empty_local(id: usize, origin: AstLocalOrigin) -> AstStmt {
        AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![AstLocalBinding {
                id: AstBindingRef::Local(LocalId(id)),
                attr: AstLocalAttr::None,
                origin,
            }],
            values: Vec::new(),
        }))
    }

    fn temp_decl_with_following_write(origin: AstLocalOrigin) -> AstBlock {
        let binding = AstBindingRef::Temp(TempId(0));
        AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: binding,
                        attr: AstLocalAttr::None,
                        origin,
                    }],
                    values: Vec::new(),
                })),
                AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::Name(binding.to_name_ref())],
                    values: vec![AstExpr::Integer(1)],
                })),
            ],
        }
    }

    fn recovered_temp_decl(binding: AstBindingRef) -> AstStmt {
        AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![AstLocalBinding {
                id: binding,
                attr: AstLocalAttr::None,
                origin: AstLocalOrigin::Recovered,
            }],
            values: Vec::new(),
        }))
    }

    fn temp_write(binding: AstBindingRef) -> AstStmt {
        AstStmt::Assign(Box::new(AstAssign {
            targets: vec![AstLValue::Name(binding.to_name_ref())],
            values: vec![AstExpr::Integer(1)],
        }))
    }

    fn label(id: usize) -> AstStmt {
        AstStmt::Label(Box::new(AstLabel { id: AstLabelId(id) }))
    }

    fn conditional_goto(id: usize) -> AstStmt {
        AstStmt::If(Box::new(AstIf {
            cond: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                text: "again".to_owned(),
            })),
            then_block: AstBlock {
                stmts: vec![AstStmt::Goto(Box::new(AstGoto {
                    target: AstLabelId(id),
                }))],
            },
            else_block: None,
        }))
    }

    #[test]
    fn empty_local_merge_preserves_each_debug_scope_boundary() {
        let debug_first = AstBlock {
            stmts: vec![
                empty_local(0, AstLocalOrigin::DebugHinted),
                empty_local(1, AstLocalOrigin::Recovered),
            ],
        };
        let debug_second = AstBlock {
            stmts: vec![
                empty_local(0, AstLocalOrigin::Recovered),
                empty_local(1, AstLocalOrigin::DebugHinted),
            ],
        };
        let mut recovered = AstBlock {
            stmts: vec![
                empty_local(0, AstLocalOrigin::Recovered),
                empty_local(1, AstLocalOrigin::Recovered),
            ],
        };

        let mut debug_first_after = debug_first.clone();
        let mut debug_second_after = debug_second.clone();
        assert!(!merge_adjacent_empty_local_decls(&mut debug_first_after));
        assert!(!merge_adjacent_empty_local_decls(&mut debug_second_after));
        assert_eq!(debug_first_after, debug_first);
        assert_eq!(debug_second_after, debug_second);

        assert!(merge_adjacent_empty_local_decls(&mut recovered));
        assert_eq!(recovered.stmts.len(), 1);
    }

    #[test]
    fn zero_use_physical_root_tail_remains_a_merge_candidate() {
        let first = AstBindingRef::Local(LocalId(0));
        let retained = AstBindingRef::Local(LocalId(1));
        let input = AstBindingRef::Local(LocalId(2));
        let mut block = AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: first,
                        attr: AstLocalAttr::None,
                        origin: AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Var(input.to_name_ref())],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: retained,
                        attr: AstLocalAttr::None,
                        origin: AstLocalOrigin::PhysicalRoot,
                    }],
                    values: vec![AstExpr::Var(input.to_name_ref())],
                })),
                AstStmt::Return(Box::new(crate::ast::common::AstReturn {
                    values: vec![
                        AstExpr::Var(first.to_name_ref()),
                        AstExpr::Var(first.to_name_ref()),
                    ],
                })),
            ],
        };

        assert!(merge_adjacent_single_value_local_decls(&mut block, None));
        assert_eq!(block.stmts.len(), 2);
        let AstStmt::LocalDecl(decl) = &block.stmts[0] else {
            panic!("adjacent retained locals should merge");
        };
        assert_eq!(decl.bindings.len(), 2);
        assert_eq!(decl.bindings[1].id, retained);
    }

    #[test]
    fn hoisted_temp_sink_preserves_debug_and_physical_root_origins() {
        for origin in [
            AstLocalOrigin::DebugHinted,
            AstLocalOrigin::PhysicalRoot,
            AstLocalOrigin::DebugHintedPhysicalRoot,
        ] {
            let original = temp_decl_with_following_write(origin);
            let mut block = original.clone();
            assert!(!sink_hoisted_temp_decls(&mut block, None));
            assert_eq!(block, original);
        }

        let mut recovered = temp_decl_with_following_write(AstLocalOrigin::Recovered);
        assert!(sink_hoisted_temp_decls(&mut recovered, None));
        assert_eq!(recovered.stmts.len(), 1);
        let AstStmt::LocalDecl(decl) = &recovered.stmts[0] else {
            panic!("recovered hoisted temp should sink into its assignment");
        };
        assert_eq!(decl.values, vec![AstExpr::Integer(1)]);
    }

    #[test]
    fn empty_physical_root_decl_does_not_merge_with_eventful_assignment() {
        let binding = AstBindingRef::Local(LocalId(0));
        let declaration = empty_local(0, AstLocalOrigin::PhysicalRoot);
        let assignment = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![AstLValue::Name(binding.to_name_ref())],
            values: vec![AstExpr::Call(Box::new(AstCallExpr {
                callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                    text: "root_is_dead".to_owned(),
                })),
                args: Vec::new(),
                method_name: None,
            }))],
        }));

        assert!(try_merge_local_decl_with_assign(&declaration, &assignment).is_none());
    }

    #[test]
    fn unrelated_prior_backedge_does_not_disable_hoisted_temp_sink() {
        let binding = AstBindingRef::Temp(TempId(0));
        let mut block = AstBlock {
            stmts: vec![
                label(0),
                conditional_goto(0),
                recovered_temp_decl(binding),
                temp_write(binding),
            ],
        };

        assert!(sink_hoisted_temp_decls(&mut block, None));
        assert!(matches!(
            block.stmts.as_slice(),
            [AstStmt::Label(_), AstStmt::If(_), AstStmt::LocalDecl(decl)]
                if decl.values == vec![AstExpr::Integer(1)]
        ));
    }

    #[test]
    fn hoisted_temp_sink_does_not_enter_existing_backedge_cycle() {
        let binding = AstBindingRef::Temp(TempId(0));
        let original = AstBlock {
            stmts: vec![
                recovered_temp_decl(binding),
                label(0),
                temp_write(binding),
                conditional_goto(0),
            ],
        };
        let mut block = original.clone();

        assert!(!sink_hoisted_temp_decls(&mut block, None));
        assert_eq!(block, original);
    }

    #[test]
    fn hoisted_temp_sink_within_same_backedge_cycle_keeps_cell_epoch() {
        let binding = AstBindingRef::Temp(TempId(0));
        let mut block = AstBlock {
            stmts: vec![
                label(0),
                recovered_temp_decl(binding),
                temp_write(binding),
                conditional_goto(0),
            ],
        };

        assert!(sink_hoisted_temp_decls(&mut block, None));
        assert!(matches!(
            block.stmts.as_slice(),
            [AstStmt::Label(_), AstStmt::LocalDecl(decl), AstStmt::If(_)]
                if decl.values == vec![AstExpr::Integer(1)]
        ));
    }

    #[test]
    fn nested_sink_does_not_create_per_iteration_cell() {
        let binding = AstBindingRef::Temp(TempId(0));
        let original = AstBlock {
            stmts: vec![
                recovered_temp_decl(binding),
                AstStmt::DoBlock(Box::new(AstBlock {
                    stmts: vec![label(0), temp_write(binding), conditional_goto(0)],
                })),
            ],
        };
        let mut block = original.clone();

        assert!(!sink_hoisted_temp_decls(&mut block, None));
        assert_eq!(block, original);
    }

    #[test]
    fn nested_sink_does_not_cross_control_barrier_read() {
        let binding = AstBindingRef::Temp(TempId(0));
        let original = AstBlock {
            stmts: vec![
                recovered_temp_decl(binding),
                AstStmt::DoBlock(Box::new(AstBlock {
                    stmts: vec![
                        AstStmt::Goto(Box::new(AstGoto {
                            target: AstLabelId(0),
                        })),
                        AstStmt::Assign(Box::new(AstAssign {
                            targets: vec![AstLValue::Name(AstNameRef::Global(AstGlobalName {
                                text: "seen".to_owned(),
                            }))],
                            values: vec![AstExpr::Var(binding.to_name_ref())],
                        })),
                        label(0),
                        AstStmt::DoBlock(Box::new(AstBlock {
                            stmts: vec![temp_write(binding)],
                        })),
                    ],
                })),
            ],
        };
        let mut block = original.clone();

        assert!(!sink_hoisted_temp_decls(&mut block, None));
        assert_eq!(block, original);
    }
}
