//! 内联由 branch 独占的条件 scratch 并提取 assignment values；依赖纯表达式/使用计数，不负责 break rewrite；例如把临时 local 条件折回 if cond。

use super::*;

pub(super) fn inline_owned_branch_conditions(
    block: &mut HirBlock,
    candidates: &BTreeSet<LocalId>,
    outer_bindings: &dyn BindingProtection,
    captured_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    let mut eligible = candidates
        .iter()
        .copied()
        .filter(|local| {
            let binding = CarryBinding::Local(*local);
            !outer_bindings.contains(&binding) && !captured_bindings.contains(&binding)
        })
        .collect::<BTreeSet<_>>();
    // 候选拒绝[SemanticBarrier:Capture]：outer/captured condition local 可能被分支外或 closure 观察，不能删除 producer identity。
    if eligible.is_empty() {
        return false;
    }

    let mentions = collect_binding_mentions_by_stmt(&block.stmts);
    let mut invalid = BTreeSet::new();
    for (index, stmt_mentions) in mentions.iter().enumerate() {
        for local in stmt_mentions.iter().filter_map(|binding| match binding {
            CarryBinding::Local(local) if eligible.contains(local) => Some(*local),
            CarryBinding::Param(_) | CarryBinding::Local(_) | CarryBinding::Temp(_) => None,
        }) {
            if !condition_scratch_mention_is_owned(&block.stmts, index, local) {
                invalid.insert(local);
            }
        }
    }
    eligible.retain(|local| !invalid.contains(local));
    if eligible.is_empty() {
        return false;
    }

    let mut removed = vec![false; block.stmts.len()];
    let producer_count = block.stmts.len().saturating_sub(1);
    for (index, remove) in removed.iter_mut().enumerate().take(producer_count) {
        let Some((local, value)) = condition_scratch_producer(&block.stmts[index]) else {
            continue;
        };
        if !eligible.contains(&local) || !condition_if_uses_only(&block.stmts[index + 1], local) {
            continue;
        }
        let value = value.clone();
        let HirStmt::If(if_stmt) = &mut block.stmts[index + 1] else {
            continue;
        };
        // 证明缺陷[PotentialPolicyViolation]：此 owner 没有 HandoffIdentityFacts/debug gate；带 debug hint 的 condition local 也会被直接删除。
        if_stmt.cond = value;
        *remove = true;
    }
    let changed = removed.iter().any(|removed| *removed);
    if changed {
        let mut cursor = 0;
        block.stmts.retain(|_| {
            let keep = !removed[cursor];
            cursor += 1;
            keep
        });
    }
    changed
}

pub(super) fn condition_scratch_mention_is_owned(
    stmts: &[HirStmt],
    index: usize,
    local: LocalId,
) -> bool {
    condition_scratch_producer(&stmts[index]).is_some_and(|(binding, _)| {
        binding == local
            && stmts
                .get(index + 1)
                .is_some_and(|stmt| condition_if_uses_only(stmt, local))
    }) || index.checked_sub(1).is_some_and(|producer| {
        condition_scratch_producer(&stmts[producer]).is_some_and(|(binding, _)| {
            binding == local && condition_if_uses_only(&stmts[index], local)
        })
    })
}

pub(super) fn condition_scratch_producer(stmt: &HirStmt) -> Option<(LocalId, &HirExpr)> {
    let (binding, values) = match stmt {
        HirStmt::LocalDecl(local_decl) => {
            let [binding] = local_decl.bindings.as_slice() else {
                return None;
            };
            (*binding, &local_decl.values)
        }
        HirStmt::Assign(assign) => {
            let [HirLValue::Local(binding)] = assign.targets.as_slice() else {
                return None;
            };
            (*binding, &assign.values)
        }
        _ => return None,
    };
    let [value] = values.fixed.as_slice() else {
        return None;
    };
    if values.tail.is_some()
        || collect_binding_mentions_in_expr(value).contains(&CarryBinding::Local(binding))
    {
        // 候选拒绝[SemanticBarrier:Scope]：producer RHS 自读 local 时，内联到 if 后会从声明前/旧 epoch 改为当前 binding 读取。
        // 候选拒绝[ProofIncomplete]：open-tail condition producer 尚未用单值截断事实证明可内联。
        return None;
    }
    Some((binding, value))
}

pub(super) fn condition_if_uses_only(stmt: &HirStmt, local: LocalId) -> bool {
    let HirStmt::If(if_stmt) = stmt else {
        return false;
    };
    if if_stmt.cond != HirExpr::LocalRef(local) {
        return false;
    }
    let binding = CarryBinding::Local(local);
    !binding_is_mentioned_in_stmts(&if_stmt.then_block.stmts, binding)
        && if_stmt
            .else_block
            .as_ref()
            .is_none_or(|block| !binding_is_mentioned_in_stmts(&block.stmts, binding))
}

pub(super) fn collect_fallthrough_assignments(
    block: &HirBlock,
    results: &[CarryBinding],
    exits: &mut Vec<BTreeMap<CarryBinding, HirExpr>>,
) -> Option<bool> {
    let (last, prefix) = block.stmts.split_last()?;
    if bindings_are_mentioned_in_stmts(prefix, results) {
        // 候选拒绝[SemanticBarrier:Lifetime]：fallthrough assignment 前已读写 result 时，整段改名会合并未产出/中间 epoch。
        return None;
    }
    match last {
        HirStmt::Assign(assign) => {
            exits.push(result_assignment_values(assign, results)?);
            Some(true)
        }
        HirStmt::If(if_stmt) => {
            let else_block = if_stmt.else_block.as_ref()?;
            let then_falls = collect_fallthrough_assignments(&if_stmt.then_block, results, exits)?;
            let else_falls = collect_fallthrough_assignments(else_block, results, exits)?;
            Some(then_falls || else_falls)
        }
        HirStmt::Block(block) => collect_fallthrough_assignments(block, results, exits),
        HirStmt::Return(_) | HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_) => Some(false),
        _ => None,
    }
}

pub(super) fn result_assignment_values(
    assign: &HirAssign,
    results: &[CarryBinding],
) -> Option<BTreeMap<CarryBinding, HirExpr>> {
    let values = assignment_values(assign)?;
    let result_values = results
        .iter()
        .map(|result| Some((*result, values.get(result)?.clone())))
        .collect::<Option<BTreeMap<_, _>>>()?;
    (!bindings_are_mentioned_in_exprs(result_values.values(), results)).then_some(result_values)
}

pub(super) fn assignment_values(assign: &HirAssign) -> Option<BTreeMap<CarryBinding, HirExpr>> {
    // 候选拒绝[ProofIncomplete]：open-tail/非等宽 assignment 缺完整 value-pack 与 target 对位事实。
    if assign.values.tail.is_some() || assign.targets.len() != assign.values.fixed.len() {
        return None;
    }
    let mut values = BTreeMap::new();
    for (target, value) in assign.targets.iter().zip(&assign.values.fixed) {
        let Some(binding) = carry_binding_from_lvalue(target) else {
            continue;
        };
        if values.insert(binding, value.clone()).is_some() {
            // 候选拒绝[SemanticBarrier:EvalOrder]：同一 binding 多次出现在并行 targets 时，最后写胜出；Map 合并会丢失位置语义。
            return None;
        }
    }
    Some(values)
}
