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
use super::expr_analysis::{expr_complexity, is_copy_like_expr};
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

        let mut merged_bindings = bindings.to_vec();
        let mut consumed = 0;
        for next_bindings in old_stmts.iter().map_while(empty_local_decl_bindings) {
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
    if !local_decl.values.is_empty()
        || local_decl
            .bindings
            .iter()
            .any(|binding| binding.attr != AstLocalAttr::None)
    {
        // 候选拒绝[ProofIncomplete]：非空声明不属于本规则；相邻空属性声明本可保留每个
        // binding 的 attr 且中间无求值事件，当前 blanket gate 仍缺目标语法验证后再放宽。
        return None;
    }
    Some(&local_decl.bindings)
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
        if !is_mergeable_adjacent_local_value(value) {
            // 候选拒绝[PolicyBoundary]：相邻声明合并只接受复杂度不超过 4 的 copy-like RHS，避免把阶段性复杂声明压成难读的并行列表。
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
            // 这里故意只收“连续复制/lookup”式的 local：
            // 目标是把 `local a = x; local b = y; local c = t[k]` 这类明显属于同一段
            // 源码声明的机械拆分重新压回去，而不是把有阶段语义的复杂 local 都并成一行。
            if !is_mergeable_adjacent_local_value(next_value)
                || expr_references_any_binding(next_value, &bindings)
            {
                // 候选拒绝[SemanticBarrier:Scope]：`local a=x; local b=a` 合成并行声明后 RHS 的 `a` 会解析到外层；候选拒绝[PolicyBoundary]：复杂 RHS 受展示预算限制。
                break;
            }
            bindings.push(next_binding.clone());
            values.push(next_value.clone());
            lookahead += 1;
        }

        // 只把多次使用的 binding 纳入合并组；单次使用的 binding 留给 inline_exprs
        // 去内联。否则 `local a = x; local b = t.f; local c = T.K` 中 b/c 只用一次，
        // 却因为 a 多次使用而被一起合并成 multi-local，导致 inline_exprs 无法识别。
        // 为了不破坏声明顺序，从连续序列尾部剥离单次使用的 binding。
        while bindings.len() >= 2
            && use_index.count_uses_in_suffix(lookahead, bindings.last().unwrap().id) <= 1
        {
            // 候选拒绝[LayerBoundary]：尾部单次-use binding 留给 inline-exprs 消费；这是
            // owner 分工而非合并会不等价的证明。
            bindings.pop();
            values.pop();
            lookahead -= 1;
        }

        if bindings.len() >= 2
            && bindings
                .iter()
                .any(|b| use_index.count_uses_in_suffix(lookahead, b.id) > 1)
        {
            // 证明缺陷[PotentialUnsoundness:DebugScope]：顺序声明会让较早 local 在后续 RHS
            // 求值时进入调用者活动局部；合成并行声明后所有 binding 都到 RHS 全部求值后才生效。
            // `debug.getlocal` 可从后续 lookup 的元方法观察该差异；当前 proof 未排除此类事件。
            new_stmts.push(AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings,
                values,
            })));
            changed = true;
            old_stmts.drain(..(lookahead - index - 1));
            index = lookahead;
            continue;
        }

        // 候选拒绝[PolicyBoundary]：不足两个 multi-use binding 时不生成并行声明；该展示
        // 密度门不说明顺序合并存在语义差异。
        new_stmts.push(stmt);
        index += 1;
    }

    block.stmts = new_stmts;
    changed
}

fn sink_hoisted_temp_decls(block: &mut AstBlock, trailing_condition: Option<&AstExpr>) -> bool {
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&block.stmts, trailing_condition);
    let forward_gotos = ForwardGotoIndex::new(&block.stmts);
    if forward_gotos.has_backward_goto {
        // backward goto 把当前 block 变成显式 CFG：hoisted temp 可能是回边上的 phi
        // 槽。把声明沉进任一分支会创建不同的词法 local，破坏 label 后读取的值。
        // 分析停用[SemanticBarrier:ControlFlow]：`::L::; use(t); ...; goto L` 中 hoisted `t` 可能是回边 phi，沉入单一路径会产生不同词法 local。
        return false;
    }
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
            if forward_gotos.has_forward_goto_past_index(lookahead) {
                // 候选拒绝[SemanticBarrier:Scope]：`goto L; local t; ...; ::L:: use(t)` 若把声明沉到 label 前后，会让跳转进入 local 作用域或改变读取绑定。
                lookahead += 1;
                continue;
            }
            if let Some(merged) = try_sink_hoisted_decl_into_stmt(
                &remaining,
                &block.stmts[lookahead],
                &use_index,
                index + 1,
                lookahead,
            ) {
                let consumed = merged.bindings.len();
                block.stmts[lookahead] = AstStmt::LocalDecl(Box::new(merged));
                remaining.drain(..consumed);
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
                sink_changed = true;
                // 不要前进 lookahead：同一条 if / loop 语句可能还有其它分支可以
                // 接收剩余 binding。例如 `local t12, t7; if ... then t12 = A else
                // t7 = B end` —— 第一轮把 t12 沉进 then，第二轮把 t7 沉进 else。
                continue;
            }
            if let Some((start, merged)) = try_sink_hoisted_decl_into_stmt_anywhere(
                &remaining,
                &block.stmts[lookahead],
                &use_index,
                index + 1,
                lookahead,
                lookahead + 1,
            ) {
                let consumed = merged.bindings.len();
                block.stmts[lookahead] = AstStmt::LocalDecl(Box::new(merged));
                remaining.drain(start..start + consumed);
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
            // 候选拒绝[SemanticBarrier:ControlFlow/Scope]：header 或多个 arm 同时 mention 的 binding 没有唯一 nested owner，声明必须留在共同支配点。
            .filter(|(_, owner, _)| *owner != NestedSinkOwner::Blocked)
            .map(|(index, _, end)| (index, end));

        // 对每个真实 mention 起点只尝试 owner 改变前的最大切片。未提及 binding
        // 继续随同该组下沉，以保留并行赋值的声明/RHS 词法边界。
        for (slice_start, slice_end) in candidates {
            if let Some((rewritten, consumed)) = try_sink_hoisted_decl_into_nested_stmt(
                &pending[slice_start..slice_end],
                stmt,
                use_index,
                suffix_start,
            ) {
                return Some(NestedSinkAttempt {
                    rewritten,
                    start: slice_start,
                    consumed,
                });
            }
        }

        start = run_end;
    }

    None
}

fn try_sink_hoisted_decl_into_nested_stmt(
    pending: &[super::super::common::AstLocalBinding],
    stmt: &AstStmt,
    use_index: &BindingUseIndex,
    suffix_start: usize,
) -> Option<(AstStmt, usize)> {
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
            let consumed = sink_pending_bindings_into_block(target_block, sinkable);
            (consumed > 0).then_some((rewritten, consumed))
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
            let consumed = sink_pending_bindings_into_block(&mut while_stmt.body, sinkable);
            (consumed > 0).then_some((rewritten, consumed))
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
            let consumed = sink_pending_bindings_into_block(&mut repeat_stmt.body, sinkable);
            (consumed > 0).then_some((rewritten, consumed))
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
            let consumed = sink_pending_bindings_into_block(&mut numeric_for.body, sinkable);
            (consumed > 0).then_some((rewritten, consumed))
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
            let consumed = sink_pending_bindings_into_block(&mut generic_for.body, sinkable);
            (consumed > 0).then_some((rewritten, consumed))
        }
        AstStmt::DoBlock(inner) => {
            let mut rewritten = AstBlock {
                stmts: inner.stmts.clone(),
            };
            let consumed = sink_pending_bindings_into_block(&mut rewritten, sinkable);
            (consumed > 0).then_some((AstStmt::DoBlock(Box::new(rewritten)), consumed))
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
) -> usize {
    let use_index = BindingUseIndex::for_stmts(&block.stmts);
    let forward_gotos = ForwardGotoIndex::new(&block.stmts);
    let mut consumed = 0usize;
    let mut index = 0usize;
    while index < block.stmts.len() && consumed < pending.len() {
        let remaining = &pending[consumed..];
        if forward_gotos.has_forward_goto_past_index(index) {
            // 候选拒绝[SemanticBarrier:Scope]：已有 forward goto 跨过此点时新增 local 会制造非法的“跳入 local 作用域”。
            index += 1;
            continue;
        }
        if let Some(merged) =
            try_sink_hoisted_decl_into_stmt(remaining, &block.stmts[index], &use_index, 0, index)
        {
            let merged_len = merged.bindings.len();
            block.stmts[index] = AstStmt::LocalDecl(Box::new(merged));
            consumed += merged_len;
            index += 1;
            continue;
        }
        if let Some((rewritten, nested_consumed)) = try_sink_hoisted_decl_into_nested_stmt(
            remaining,
            &block.stmts[index],
            &use_index,
            index + 1,
        ) {
            block.stmts[index] = rewritten;
            consumed += nested_consumed;
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
    consumed
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
    if binding.attr != AstLocalAttr::None {
        // 候选拒绝[ProofIncomplete]：`<close>` 在后续 lookup/call 前的注册时点可被
        // `__close`/GC 观察，但 `<const>` 或无事件后缀存在安全子集；需按 attr 与后续事件拆分。
        return None;
    }
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
        // 候选拒绝[TargetConstraint]：`<const>`/`<close>` local 在目标 Lua 中不可在声明后
        // 普通赋值；该异常 AST 不能用无属性 hoist 规则静默合法化。
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
        return None;
    }
    Some(local_decl.bindings.clone())
}

fn try_sink_hoisted_decl_into_stmt(
    pending: &[super::super::common::AstLocalBinding],
    stmt: &AstStmt,
    use_index: &BindingUseIndex,
    prior_start: usize,
    target_index: usize,
) -> Option<AstLocalDecl> {
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
    if stmt_references_any_binding_in_assign(assign, &pending[assign.targets.len()..]) {
        // 候选拒绝[ProofIncomplete]：剩余 binding 仍由原 hoisted 声明支配，`local a,b;
        // a=b` 下沉为 `local b; local a=b` 等价；当前 gate 未利用这一支配事实。
        return None;
    }
    Some(AstLocalDecl {
        bindings: candidate.to_vec(),
        values: assign.values.clone(),
    })
}

fn is_temp_like_binding(binding: AstBindingRef) -> bool {
    matches!(
        binding,
        AstBindingRef::Temp(_) | AstBindingRef::SyntheticLocal(_)
    )
}

/// 与 [`try_sink_hoisted_decl_into_stmt`] 类似，但在 `pending` 中任意位置搜索
/// 匹配的 binding，而非仅要求它们位于头部。成功时返回 `(start_index, AstLocalDecl)`，
/// 其中 `start_index` 是匹配 binding 在 `pending` 中的起始位置。
fn try_sink_hoisted_decl_into_stmt_anywhere(
    pending: &[super::super::common::AstLocalBinding],
    stmt: &AstStmt,
    use_index: &BindingUseIndex,
    prior_start: usize,
    target_index: usize,
    suffix_start: usize,
) -> Option<(usize, AstLocalDecl)> {
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
        // RHS 不得引用 consumed 切片之后的其他待处理 binding
        // （与前序变体相同的安全检查）。
        let after = &pending[start + target_len..];
        if !after.is_empty() && stmt_references_any_binding_in_assign(assign, after) {
            // 候选拒绝[ProofIncomplete]：切片后的 binding 仍在原 hoisted 声明中，读取解析
            // 不变；应证明声明重建顺序后移除此 gate。
            continue;
        }
        // 同样检查 consumed 切片之前的 binding。
        let before = &pending[..start];
        if !before.is_empty() && stmt_references_any_binding_in_assign(assign, before) {
            // 候选拒绝[ProofIncomplete]：切片前 binding 同样仍由 hoisted 声明支配；
            // `local a,b; b=a` 是安全子集，当前 gate 缺少重建后支配关系证明。
            continue;
        }
        return Some((
            start,
            AstLocalDecl {
                bindings: candidate.to_vec(),
                values: assign.values.clone(),
            },
        ));
    }
    None
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
    has_backward_goto: bool,
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
        let has_backward_goto = goto_targets_by_stmt
            .iter()
            .enumerate()
            .any(|(index, targets)| {
                targets.iter().any(|target| {
                    label_positions
                        .get(target)
                        .is_some_and(|label_index| *label_index < index)
                })
            });

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
            has_backward_goto,
        }
    }

    fn has_forward_goto_past_index(&self, index: usize) -> bool {
        self.has_forward_goto_past_index
            .get(index)
            .copied()
            .unwrap_or(false)
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
