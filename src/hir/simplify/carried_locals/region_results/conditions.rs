//! 内联由 branch 独占的条件 scratch 并提取 assignment values；依赖纯表达式/使用计数，不负责 break rewrite；例如把临时 local 条件折回 if cond。

use super::*;

#[derive(Debug, Clone, PartialEq)]
pub(super) enum ExitValue {
    Expr { expr: HirExpr, target: usize },
    TailProjection { projection: usize, target: usize },
}

impl ExitValue {
    pub(super) fn exact_binding(&self) -> Option<CarryBinding> {
        let Self::Expr { expr, .. } = self else {
            return None;
        };
        carry_binding_from_expr(expr)
    }

    pub(super) fn target_index(&self) -> usize {
        match self {
            Self::Expr { target, .. } | Self::TailProjection { target, .. } => *target,
        }
    }
}

pub(super) type ExitValues = BTreeMap<CarryBinding, ExitValue>;

pub(super) fn inline_owned_branch_conditions(
    block: &mut HirBlock,
    candidates: &BTreeSet<LocalId>,
    outer_bindings: &dyn BindingProtection,
    identity_facts: &HandoffIdentityFacts,
) -> bool {
    let mut eligible = candidates
        .iter()
        .copied()
        .filter(|local| {
            let binding = CarryBinding::Local(*local);
            !outer_bindings.contains(&binding) && !identity_facts.contains(*local)
        })
        .collect::<BTreeSet<_>>();
    // 候选拒绝[SemanticBarrier:Scope]：outer condition local 可能被分支外观察，不能删除 producer identity。
    // 候选拒绝[PolicyBoundary]：debug condition local 是项目选择保留的源码身份。
    // 候选拒绝[SemanticBarrier:Scope]：for condition local 每轮重建且只在 loop body
    // 可见；删除 producer 会把 per-iteration binder 改成跨轮值。
    // 所有非 producer/相邻 if-cond mention（包括 closure capture）都会在下面的 ownership
    // scan 中逐点拒绝，不需要 proto-wide capture blanket。
    // 候选拒绝[SemanticBarrier:Lifetime]：内联后删除 physical-root condition producer 会移除其 VM root declaration；lua54_01_close#17 用 __gc + collectgarbage 观察同槽清空前失去 root 的对象提前析构。
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
    let value = match (values.fixed.as_slice(), values.tail.as_ref()) {
        ([value], None) => value,
        ([], Some(tail)) => tail.as_expr(),
        _ => {
            // 候选拒绝[SemanticBarrier:EvalOrder]：scratch 之外的 fixed/tail 表达式也会被求值；只把首值移入 condition 会删掉其求值。
            return None;
        }
    };
    if collect_binding_mentions_in_expr(value).contains(&CarryBinding::Local(binding)) {
        // 候选拒绝[SemanticBarrier:Scope]：producer RHS 自读 local 时，内联到 if 后会从声明前/旧 epoch 改为当前 binding 读取。
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
    exits: &mut Vec<ExitValues>,
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
) -> Option<ExitValues> {
    if assignment_reads_bindings(assign, results) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：fallthrough assignment 的其它 RHS/左值地址也在并行写前读取旧 result，不能随 result 一起改名。
        return None;
    }
    let values = assignment_values(assign);
    results
        .iter()
        .map(|result| values.get(result))
        .collect::<Option<Vec<_>>>()?;
    Some(values)
}

pub(super) fn assignment_values(assign: &HirAssign) -> ExitValues {
    let mut values = ExitValues::new();
    for (index, target) in assign.targets.iter().enumerate() {
        let Some(binding) = carry_binding_from_lvalue(target) else {
            continue;
        };
        let value = if let Some(value) = assign.values.fixed.get(index) {
            ExitValue::Expr {
                expr: value.clone(),
                target: index,
            }
        } else if assign.values.tail.is_some() {
            ExitValue::TailProjection {
                projection: index - assign.values.fixed.len(),
                target: index,
            }
        } else {
            ExitValue::Expr {
                expr: HirExpr::Nil,
                target: index,
            }
        };
        values.insert(binding, value);
    }
    values
}

pub(super) fn assignment_reads_bindings(assign: &HirAssign, bindings: &[CarryBinding]) -> bool {
    bindings_are_mentioned_in_exprs(assign.values.iter(), bindings)
        || assign.targets.iter().any(|target| {
            let HirLValue::TableAccess(access) = target else {
                return false;
            };
            bindings.iter().any(|binding| {
                collect_binding_mentions_in_expr(&access.base).contains(binding)
                    || collect_binding_mentions_in_expr(&access.key).contains(binding)
            })
        })
}
