//! 这个文件负责把 fallback label/goto 区域里“交棒出去的 carried 状态”认回原绑定。
//!
//! 某些 `<close> + goto` 形状因为暂时无法整体结构化，只能先在 HIR 里保留成
//! `assign tX = lY; ... label/goto ...; tX = ...` 这样的状态 temp。语义虽然对，
//! 但它会把本来是同一个源码 local 的身份拆成“两段 binding”，最终长成
//! `local turn = 1; do state = turn; ... state = state + 1 end` 这种机械形状。
//!
//! 这个 pass 只吃两类很窄的 handoff：
//! - 纯别名交棒：`assign tX = lY; ... tX ...`
//! - 多目标纯别名交棒：`assign tA, tB = sA, sB; ... tA/tB ...`
//! - 多目标混合交棒：`assign tA, tB, tC = sA, sB, 0; ... sA, sB = tA, tB`
//! - 更新后交棒：`assign tX = (sY + 1); ... sY = tX`
//! - 显式 `goto/label` mesh 里的边界别名：若多条边界快照把同一组状态 temp 串成一个
//!   等价类，这里会在当前 fallback block 内把它们统一认回同一批 binding
//!
//! 满足这几个条件时，说明这个 block 已经把“后半段状态身份”完全交给了 temp；
//! 这里把它认回原 local，删掉 handoff seed。它不会发明新 local，也不会在原 local
//! 仍然活跃时强行合并两段状态。对于第二类“更新后交棒”，它只在旧 binding 后续不再
//! 被读取、并且后续确实存在 `sY = tX` 这种直接写回时才会把 `tX` 重新折回旧
//! binding，并只裁掉“这次 rewrite 自己制造出来”的 `x = x` seed/self-copy。
//! 像 branch merge 里“沿用当前值”的那一臂，即便在局部重写后暂时长成 `x = x`，
//! 也仍然承载着 preserved-current-value 语义，不能在这里被当成纯噪音吞掉。
//!
//! 例子：
//! - 输入：`local l0 = 1; do t4 = l0; ::L1:: if t4 < 3 then t4 = t4 + 1; goto L1 end end`
//! - 输出：`local l0 = 1; do ::L1:: if l0 < 3 then l0 = l0 + 1; goto L1 end end`
//! - 输入：`assign t8, t9 = t1, t2; ... assign t8, t9 = step(t8), next`
//! - 输出：`... assign t1, t2 = step(t1), next`
//! - 输入：`assign t8, t9, t10 = t1, t2, 0; ... assign t1, t2 = t8, t9`
//! - 输出：`assign t10 = 0; ...`
//! - 输入：`assign t3 = (t24 + 1); if cond(t3) then assign t23, t24 = step(t3), t3 end`
//! - 输出：`assign t24 = (t24 + 1); if cond(t24) then assign t23 = step(t24) end`
//! - 输入：`if cond then assign t10, t11 = t0, t1; goto L2 end; ... ::L2:: assign t2 = t10 + 1`
//! - 输出：`if cond then goto L2 end; ... ::L2:: assign t0 = t0 + 1`

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirProto, HirStmt, LocalId, TempId};

use super::temp_touch::collect_temp_refs_in_stmts;
use super::visit::{HirVisitor, visit_stmts};
use super::walk::{for_each_nested_block_mut, HirRewritePass, rewrite_stmts};

pub(super) fn collapse_carried_local_handoffs_in_proto(proto: &mut HirProto) -> bool {
    collapse_handoffs_recursive(&mut proto.body, &BTreeSet::new())
}

/// 自定义后序遍历：先递归处理子块（同时把外层 temp 引用集传下去），再在当前块做 handoff 折叠。
/// `outer_temps` 包含当前块的所有祖先作用域中引用过的 temp，如果一个 temp 在 `outer_temps` 中，
/// 说明它在当前块外部仍被消费，不能在当前块内被折叠消除。
fn collapse_handoffs_recursive(
    block: &mut HirBlock,
    outer_temps: &BTreeSet<TempId>,
) -> bool {
    let mut changed = false;

    // 为每个嵌套语句预计算"进入该子块时需要保护的 temp 集"。
    // 对于 index 处的语句，保护集 = 继承的 outer_temps ∪ 本块中「其他语句」引用的 temps。
    // 注意不能用 `all - self` 来近似——如果某个 temp 同时出现在当前语句和其他语句中，
    // 差集会把它减掉，导致跨作用域的引用失去保护。这里用前缀+后缀并集来精确计算。
    let per_stmt_temps: Vec<BTreeSet<TempId>> = block
        .stmts
        .iter()
        .map(|stmt| collect_temp_refs_in_stmts(std::slice::from_ref(stmt)))
        .collect();

    // 累积前缀 temp 集合
    let mut prefix_temps = BTreeSet::new();
    // 预计算完整后缀 temp 集合（逐步缩小）
    let mut suffix_temps_vec: Vec<BTreeSet<TempId>> = Vec::with_capacity(per_stmt_temps.len());
    {
        let mut suffix = BTreeSet::new();
        for stmt_temps in per_stmt_temps.iter().rev() {
            suffix_temps_vec.push(suffix.clone());
            suffix.extend(stmt_temps.iter().copied());
        }
        suffix_temps_vec.reverse();
    }

    for (index, _) in per_stmt_temps.iter().enumerate() {
        let child_outer: BTreeSet<TempId> = outer_temps
            .union(&prefix_temps)
            .chain(suffix_temps_vec[index].iter())
            .copied()
            .collect();

        for_each_nested_block_mut(&mut block.stmts[index], &mut |nested_block| {
            changed |= collapse_handoffs_recursive(nested_block, &child_outer);
        });

        prefix_temps.extend(per_stmt_temps[index].iter().copied());
    }

    // 后序：子块都处理完之后，再处理当前块的 handoff
    changed |= collapse_block_handoffs(block, outer_temps);
    changed
}

fn collapse_block_handoffs(block: &mut HirBlock, outer_temps: &BTreeSet<TempId>) -> bool {
    let mut changed = collapse_boundary_alias_classes(block);
    let mut index = 0;

    while index < block.stmts.len() {
        if try_collapse_pure_binding_handoffs(block, index, outer_temps) {
            changed = true;
            continue;
        }
        if try_collapse_single_binding_handoff(block, index, outer_temps) {
            changed = true;
            continue;
        }
        if try_collapse_pure_local_handoff(block, index, outer_temps) {
            changed = true;
            continue;
        }
        if try_collapse_binding_update_handoff(block, index, outer_temps) {
            changed = true;
            index += 1;
            continue;
        }

        index += 1;
    }

    changed
}

fn collapse_boundary_alias_classes(block: &mut HirBlock) -> bool {
    if !block
        .stmts
        .iter()
        .any(|stmt| matches!(stmt, HirStmt::Goto(_) | HirStmt::Label(_)))
    {
        return false;
    }

    let boundary_pairs = collect_boundary_alias_pairs(block);
    if boundary_pairs.len() < 2 {
        return false;
    }

    let mut adjacency = BTreeMap::<CarryBinding, BTreeSet<CarryBinding>>::new();
    for pairs in boundary_pairs {
        for (target, source) in pairs {
            adjacency.entry(target).or_default().insert(source);
            adjacency.entry(source).or_default().insert(target);
        }
    }

    let mut visited = BTreeSet::new();
    let mut rewrites = BTreeMap::new();
    for &binding in adjacency.keys() {
        if !visited.insert(binding) {
            continue;
        }

        let mut stack = vec![binding];
        let mut component = BTreeSet::from([binding]);
        while let Some(current) = stack.pop() {
            let Some(neighbors) = adjacency.get(&current) else {
                continue;
            };
            for &neighbor in neighbors {
                if visited.insert(neighbor) {
                    stack.push(neighbor);
                }
                component.insert(neighbor);
            }
        }

        // 这里只吃“已经被多条边界快照串起来”的 mesh 状态类。
        // 单条 `a = b` 本身既可能是 handoff，也可能只是暂时保留的并行值；
        // 至少需要 3 个成员，才能证明这更像同一槽位在多个 label 入口之间来回交棒。
        if component.len() < 3 {
            continue;
        }

        let canonical = component
            .iter()
            .copied()
            .min_by_key(|binding| binding_canonical_key(*binding))
            .expect("component is non-empty");
        for member in component {
            if member != canonical {
                rewrites.insert(member, canonical);
            }
        }
    }

    if rewrites.is_empty() {
        return false;
    }

    let prunable_bindings = collect_prunable_bindings(rewrites.values().copied());
    let mut pass = BindingClassRewritePass { rewrites };
    if !rewrite_stmts(&mut block.stmts, &mut pass) {
        return false;
    }

    prune_boundary_snapshot_self_assigns(block, &prunable_bindings);
    true
}

fn collect_boundary_alias_pairs(block: &HirBlock) -> Vec<Vec<(CarryBinding, CarryBinding)>> {
    let mut pairs = Vec::new();

    for (index, stmt) in block.stmts.iter().enumerate() {
        if let HirStmt::Assign(assign) = stmt
            && let Some(alias_pairs) =
                top_level_boundary_alias_pairs(assign, block.stmts.get(index + 1))
        {
            pairs.push(alias_pairs);
        }

        let HirStmt::If(if_stmt) = stmt else {
            continue;
        };
        let falls_through_to_label = matches!(block.stmts.get(index + 1), Some(HirStmt::Label(_)));

        if let Some(then_pairs) =
            edge_snapshot_alias_pairs(&if_stmt.then_block, falls_through_to_label)
        {
            pairs.push(then_pairs);
        }
        if let Some(else_block) = &if_stmt.else_block
            && let Some(else_pairs) = edge_snapshot_alias_pairs(else_block, falls_through_to_label)
        {
            pairs.push(else_pairs);
        }
    }

    pairs
}

fn top_level_boundary_alias_pairs(
    assign: &crate::hir::common::HirAssign,
    next_stmt: Option<&HirStmt>,
) -> Option<Vec<(CarryBinding, CarryBinding)>> {
    match next_stmt {
        Some(HirStmt::Goto(_)) | Some(HirStmt::Label(_)) => pure_alias_pairs(assign),
        _ => None,
    }
}

fn edge_snapshot_alias_pairs(
    block: &HirBlock,
    allow_fallthrough_to_label: bool,
) -> Option<Vec<(CarryBinding, CarryBinding)>> {
    match block.stmts.as_slice() {
        [HirStmt::Assign(assign), HirStmt::Goto(_)] => pure_alias_pairs(assign),
        [HirStmt::Assign(assign)] if allow_fallthrough_to_label => pure_alias_pairs(assign),
        _ => None,
    }
}

fn pure_alias_pairs(
    assign: &crate::hir::common::HirAssign,
) -> Option<Vec<(CarryBinding, CarryBinding)>> {
    if assign.targets.is_empty() || assign.targets.len() != assign.values.len() {
        return None;
    }

    let mut seen_targets = BTreeSet::new();
    let mut seen_sources = BTreeSet::new();
    let mut pairs = Vec::with_capacity(assign.targets.len());

    for (target, value) in assign.targets.iter().zip(&assign.values) {
        let target = carry_binding_from_lvalue(target)?;
        let source = carry_binding_from_expr(value)?;
        if !seen_targets.insert(target) || !seen_sources.insert(source) {
            return None;
        }
        pairs.push((target, source));
    }

    Some(pairs)
}

fn binding_canonical_key(binding: CarryBinding) -> (u8, usize) {
    match binding {
        CarryBinding::Local(local) => (0, local.index()),
        CarryBinding::Temp(temp) => (1, temp.index()),
    }
}

fn try_collapse_pure_binding_handoffs(
    block: &mut HirBlock,
    index: usize,
    outer_temps: &BTreeSet<TempId>,
) -> bool {
    let Some(seed) = binding_handoff_seed(&block.stmts[index]) else {
        return false;
    };

    // 如果被折叠的 temp 在外层作用域中仍被引用，不能消除
    if seed
        .rewrites
        .iter()
        .any(|rewrite| outer_temps.contains(&rewrite.from))
    {
        return false;
    }

    let suffix = &block.stmts[index + 1..];
    if suffix.is_empty()
        || seed.rewrites.iter().any(|rewrite| {
            suffix_reads_binding(suffix, rewrite.to)
                || !suffix_writes_binding_only_via_direct_writeback(
                    suffix,
                    rewrite.to,
                    rewrite.from,
                )
                || !suffix_mentions_temp(suffix, rewrite.from)
        })
    {
        return false;
    }

    let mut pass = TempToBindingPass {
        rewrites: seed.rewrites.clone(),
    };
    if !rewrite_stmts(&mut block.stmts[index + 1..], &mut pass) {
        return false;
    }

    if seed.retained_pairs.is_empty() {
        block.stmts.remove(index);
    } else if !rewrite_binding_handoff_seed(&mut block.stmts[index], &seed.retained_pairs) {
        return false;
    }

    prune_redundant_self_assigns_in_stmts(
        &mut block.stmts[index + 1..],
        collect_prunable_bindings(seed.rewrites.iter().map(|rewrite| rewrite.to)),
    );
    prune_empty_assign_stmts(block);
    true
}

fn try_collapse_pure_local_handoff(
    block: &mut HirBlock,
    index: usize,
    outer_temps: &BTreeSet<TempId>,
) -> bool {
    let Some((temp, local)) = local_handoff_seed(&block.stmts[index]) else {
        return false;
    };

    // 如果被折叠的 temp 在外层作用域中仍被引用，不能消除
    if outer_temps.contains(&temp) {
        return false;
    }

    let suffix = &block.stmts[index + 1..];
    if suffix.is_empty()
        || suffix_mentions_local(suffix, local)
        || !suffix_mentions_temp(suffix, temp)
    {
        return false;
    }

    let mut pass = TempToLocalPass { temp, local };
    if !rewrite_stmts(&mut block.stmts[index + 1..], &mut pass) {
        return false;
    }

    block.stmts.remove(index);
    true
}

fn try_collapse_single_binding_handoff(
    block: &mut HirBlock,
    index: usize,
    outer_temps: &BTreeSet<TempId>,
) -> bool {
    let Some((temp, binding)) = single_binding_handoff_seed(&block.stmts[index]) else {
        return false;
    };

    // 如果被折叠的 temp 在外层作用域中仍被引用，不能消除
    if outer_temps.contains(&temp) {
        return false;
    }

    let suffix = &block.stmts[index + 1..];
    if suffix.is_empty()
        || suffix_mentions_binding(suffix, binding)
        || !suffix_mentions_temp(suffix, temp)
    {
        return false;
    }

    let rewritten = match binding {
        CarryBinding::Local(local) => {
            let mut pass = TempToLocalPass { temp, local };
            rewrite_stmts(&mut block.stmts[index + 1..], &mut pass)
        }
        CarryBinding::Temp(to) => {
            let mut pass = TempToTempPass { from: temp, to };
            rewrite_stmts(&mut block.stmts[index + 1..], &mut pass)
        }
    };
    if !rewritten {
        return false;
    }

    block.stmts.remove(index);
    true
}

fn try_collapse_binding_update_handoff(
    block: &mut HirBlock,
    index: usize,
    outer_temps: &BTreeSet<TempId>,
) -> bool {
    let Some((target_temp, carried)) = update_handoff_seed(&block.stmts[index]) else {
        return false;
    };

    // 如果被折叠的 temp 在外层作用域中仍被引用，不能消除
    if outer_temps.contains(&target_temp) {
        return false;
    }

    let suffix = &block.stmts[index + 1..];
    if suffix.is_empty()
        || suffix_reads_binding(suffix, carried)
        || !suffix_contains_direct_writeback(suffix, carried, target_temp)
        || !suffix_mentions_temp(suffix, target_temp)
    {
        return false;
    }

    let rewritten = match carried {
        CarryBinding::Local(local) => {
            let mut pass = TempToLocalPass {
                temp: target_temp,
                local,
            };
            rewrite_stmts(&mut block.stmts[index + 1..], &mut pass)
        }
        CarryBinding::Temp(temp) => {
            let mut pass = TempToTempPass {
                from: target_temp,
                to: temp,
            };
            rewrite_stmts(&mut block.stmts[index + 1..], &mut pass)
        }
    };
    if !rewritten {
        return false;
    }
    if !rewrite_update_handoff_seed(&mut block.stmts[index], carried) {
        return false;
    }

    rewrite_stmts(
        &mut block.stmts[index + 1..],
        &mut RedundantSelfAssignPrunePass::for_bindings([carried]),
    );
    prune_empty_assign_stmts(block);
    true
}

#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
enum CarryBinding {
    Local(LocalId),
    Temp(TempId),
}

fn carry_binding_from_expr(expr: &HirExpr) -> Option<CarryBinding> {
    match expr {
        HirExpr::LocalRef(local) => Some(CarryBinding::Local(*local)),
        HirExpr::TempRef(temp) => Some(CarryBinding::Temp(*temp)),
        _ => None,
    }
}

fn carry_binding_from_lvalue(lvalue: &HirLValue) -> Option<CarryBinding> {
    match lvalue {
        HirLValue::Local(local) => Some(CarryBinding::Local(*local)),
        HirLValue::Temp(temp) => Some(CarryBinding::Temp(*temp)),
        HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => None,
    }
}

fn carry_binding_expr(binding: CarryBinding) -> HirExpr {
    match binding {
        CarryBinding::Local(local) => HirExpr::LocalRef(local),
        CarryBinding::Temp(temp) => HirExpr::TempRef(temp),
    }
}

fn carry_binding_lvalue(binding: CarryBinding) -> HirLValue {
    match binding {
        CarryBinding::Local(local) => HirLValue::Local(local),
        CarryBinding::Temp(temp) => HirLValue::Temp(temp),
    }
}

#[derive(Clone, Copy)]
struct TempBindingRewrite {
    from: TempId,
    to: CarryBinding,
}

struct BindingClassRewritePass {
    rewrites: BTreeMap<CarryBinding, CarryBinding>,
}

impl BindingClassRewritePass {
    fn rewrite_binding(&self, binding: CarryBinding) -> Option<CarryBinding> {
        self.rewrites.get(&binding).copied()
    }
}

impl HirRewritePass for BindingClassRewritePass {
    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        let Some(binding) = carry_binding_from_expr(expr) else {
            return false;
        };
        let Some(rewrite) = self.rewrite_binding(binding) else {
            return false;
        };
        *expr = carry_binding_expr(rewrite);
        true
    }

    fn rewrite_lvalue(&mut self, lvalue: &mut HirLValue) -> bool {
        let Some(binding) = carry_binding_from_lvalue(lvalue) else {
            return false;
        };
        let Some(rewrite) = self.rewrite_binding(binding) else {
            return false;
        };
        *lvalue = carry_binding_lvalue(rewrite);
        true
    }
}

struct BindingHandoffSeed {
    rewrites: Vec<TempBindingRewrite>,
    retained_pairs: Vec<(HirLValue, HirExpr)>,
}

fn binding_handoff_seed(stmt: &HirStmt) -> Option<BindingHandoffSeed> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    if assign.targets.len() < 2 || assign.targets.len() != assign.values.len() {
        return None;
    }

    let mut seen_targets = std::collections::BTreeSet::new();
    let mut seen_bindings = std::collections::BTreeSet::new();
    let mut rewrites = Vec::with_capacity(assign.targets.len());
    let mut retained_pairs = Vec::new();
    for (target, value) in assign.targets.iter().zip(&assign.values) {
        let rewrite = match (target, value) {
            (HirLValue::Temp(target_temp), HirExpr::LocalRef(local)) => Some(TempBindingRewrite {
                from: *target_temp,
                to: CarryBinding::Local(*local),
            }),
            (HirLValue::Temp(target_temp), HirExpr::TempRef(temp)) => Some(TempBindingRewrite {
                from: *target_temp,
                to: CarryBinding::Temp(*temp),
            }),
            _ => None,
        };
        let Some(rewrite) = rewrite else {
            retained_pairs.push((target.clone(), value.clone()));
            continue;
        };
        if !seen_targets.insert(rewrite.from) || !seen_bindings.insert(rewrite.to) {
            return None;
        }
        rewrites.push(rewrite);
    }
    if rewrites.is_empty() {
        return None;
    }
    Some(BindingHandoffSeed {
        rewrites,
        retained_pairs,
    })
}

fn rewrite_binding_handoff_seed(
    stmt: &mut HirStmt,
    retained_pairs: &[(HirLValue, HirExpr)],
) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    assign.targets = retained_pairs
        .iter()
        .map(|(target, _)| target.clone())
        .collect();
    assign.values = retained_pairs
        .iter()
        .map(|(_, value)| value.clone())
        .collect();
    true
}

fn update_handoff_seed(stmt: &HirStmt) -> Option<(TempId, CarryBinding)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Temp(target_temp)] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.as_slice() else {
        return None;
    };
    // `assign tX = lY` 这种纯别名交棒应继续走旧分支；这里只有“先算一个 next 状态，
    // 再把后半段身份完全交给它”的形状才应该继续往下看。
    if matches!(value, HirExpr::LocalRef(_) | HirExpr::TempRef(_)) {
        return None;
    }
    let mut collector = BindingReadCollector::default();
    collector.collect_expr(value);
    let [carried] = collector.reads.as_slice() else {
        return None;
    };
    match carried {
        CarryBinding::Temp(temp) if *temp == *target_temp => None,
        _ => Some((*target_temp, *carried)),
    }
}

fn rewrite_update_handoff_seed(stmt: &mut HirStmt, carried: CarryBinding) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    let [target] = assign.targets.as_mut_slice() else {
        return false;
    };
    *target = match carried {
        CarryBinding::Local(local) => HirLValue::Local(local),
        CarryBinding::Temp(temp) => HirLValue::Temp(temp),
    };
    true
}

fn suffix_reads_binding(stmts: &[HirStmt], binding: CarryBinding) -> bool {
    let mut collector = BindingReadCollector::default();
    collector.collect_stmts(stmts);
    collector.reads.contains(&binding)
}

fn suffix_contains_direct_writeback(
    stmts: &[HirStmt],
    binding: CarryBinding,
    target_temp: TempId,
) -> bool {
    let mut collector = DirectWritebackCollector {
        binding,
        target_temp,
        found: false,
    };
    visit_stmts(stmts, &mut collector);
    collector.found
}

fn suffix_writes_binding_only_via_direct_writeback(
    stmts: &[HirStmt],
    binding: CarryBinding,
    target_temp: TempId,
) -> bool {
    stmts
        .iter()
        .all(|stmt| stmt_writes_binding_only_via_direct_writeback(stmt, binding, target_temp))
}

fn stmt_writes_binding_only_via_direct_writeback(
    stmt: &HirStmt,
    binding: CarryBinding,
    target_temp: TempId,
) -> bool {
    match stmt {
        HirStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .zip(&assign.values)
                .all(|(target, value)| {
                    !binding_matches_lvalue(target, binding)
                        || matches_direct_writeback_pair(target, value, binding, target_temp)
                })
        }
        HirStmt::If(if_stmt) => {
            suffix_writes_binding_only_via_direct_writeback(
                &if_stmt.then_block.stmts,
                binding,
                target_temp,
            ) && if_stmt.else_block.as_ref().is_none_or(|else_block| {
                suffix_writes_binding_only_via_direct_writeback(
                    &else_block.stmts,
                    binding,
                    target_temp,
                )
            })
        }
        HirStmt::While(while_stmt) => suffix_writes_binding_only_via_direct_writeback(
            &while_stmt.body.stmts,
            binding,
            target_temp,
        ),
        HirStmt::Repeat(repeat_stmt) => suffix_writes_binding_only_via_direct_writeback(
            &repeat_stmt.body.stmts,
            binding,
            target_temp,
        ),
        HirStmt::NumericFor(numeric_for) => suffix_writes_binding_only_via_direct_writeback(
            &numeric_for.body.stmts,
            binding,
            target_temp,
        ),
        HirStmt::GenericFor(generic_for) => suffix_writes_binding_only_via_direct_writeback(
            &generic_for.body.stmts,
            binding,
            target_temp,
        ),
        HirStmt::Block(block) => {
            suffix_writes_binding_only_via_direct_writeback(&block.stmts, binding, target_temp)
        }
        HirStmt::Unstructured(unstructured) => suffix_writes_binding_only_via_direct_writeback(
            &unstructured.body.stmts,
            binding,
            target_temp,
        ),
        HirStmt::LocalDecl(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => true,
    }
}

fn binding_matches_lvalue(lvalue: &HirLValue, binding: CarryBinding) -> bool {
    match (binding, lvalue) {
        (CarryBinding::Local(binding), HirLValue::Local(local)) => binding == *local,
        (CarryBinding::Temp(binding), HirLValue::Temp(temp)) => binding == *temp,
        _ => false,
    }
}

#[derive(Default)]
struct BindingReadCollector {
    reads: Vec<CarryBinding>,
}

impl BindingReadCollector {
    fn collect_stmts(&mut self, stmts: &[HirStmt]) {
        visit_stmts(stmts, self);
    }

    fn collect_expr(&mut self, expr: &HirExpr) {
        super::visit::visit_expr(expr, self);
    }
}

impl HirVisitor for BindingReadCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        let binding = match expr {
            HirExpr::LocalRef(local) => Some(CarryBinding::Local(*local)),
            HirExpr::TempRef(temp) => Some(CarryBinding::Temp(*temp)),
            _ => None,
        };
        if let Some(binding) = binding
            && !self.reads.contains(&binding)
        {
            self.reads.push(binding);
        }
    }
}

struct DirectWritebackCollector {
    binding: CarryBinding,
    target_temp: TempId,
    found: bool,
}

impl HirVisitor for DirectWritebackCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        let HirStmt::Assign(assign) = stmt else {
            return;
        };
        self.found |= assign
            .targets
            .iter()
            .zip(&assign.values)
            .any(|(target, value)| {
                matches_direct_writeback_pair(target, value, self.binding, self.target_temp)
            });
    }
}

fn prune_redundant_self_assign_components_in_stmt(
    stmt: &mut HirStmt,
    prunable_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    if assign.targets.len() != assign.values.len() {
        return false;
    }

    let mut rewritten = Vec::with_capacity(assign.targets.len());
    for (target, value) in assign
        .targets
        .iter()
        .cloned()
        .zip(assign.values.iter().cloned())
    {
        if !matches_redundant_self_assign_pair(&target, &value, prunable_bindings) {
            rewritten.push((target, value));
        }
    }

    if rewritten.len() == assign.targets.len() {
        return false;
    }

    assign.targets = rewritten.iter().map(|(target, _)| target.clone()).collect();
    assign.values = rewritten.into_iter().map(|(_, value)| value).collect();
    true
}

fn matches_redundant_self_assign_pair(
    target: &HirLValue,
    value: &HirExpr,
    prunable_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    redundant_self_assign_binding(target, value)
        .is_some_and(|binding| prunable_bindings.contains(&binding))
}

fn redundant_self_assign_binding(target: &HirLValue, value: &HirExpr) -> Option<CarryBinding> {
    match (target, value) {
        (HirLValue::Temp(target), HirExpr::TempRef(value)) if target == value => {
            Some(CarryBinding::Temp(*target))
        }
        (HirLValue::Local(target), HirExpr::LocalRef(value)) if target == value => {
            Some(CarryBinding::Local(*target))
        }
        _ => None,
    }
}

struct RedundantSelfAssignPrunePass {
    prunable_bindings: BTreeSet<CarryBinding>,
}

impl RedundantSelfAssignPrunePass {
    fn for_bindings(bindings: impl IntoIterator<Item = CarryBinding>) -> Self {
        Self {
            prunable_bindings: collect_prunable_bindings(bindings),
        }
    }
}

impl HirRewritePass for RedundantSelfAssignPrunePass {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let original_len = block.stmts.len();
        block.stmts.retain(|stmt| !is_empty_assign_stmt(stmt));
        block.stmts.len() != original_len
    }

    fn rewrite_stmt(&mut self, stmt: &mut HirStmt) -> bool {
        prune_redundant_self_assign_components_in_stmt(stmt, &self.prunable_bindings)
    }
}

fn is_empty_assign_stmt(stmt: &HirStmt) -> bool {
    matches!(stmt, HirStmt::Assign(assign) if assign.targets.is_empty())
}

fn prune_empty_assign_stmts(block: &mut HirBlock) -> bool {
    let original_len = block.stmts.len();
    block.stmts.retain(|stmt| !is_empty_assign_stmt(stmt));
    block.stmts.len() != original_len
}

fn prune_redundant_self_assigns_in_stmts(
    stmts: &mut [HirStmt],
    prunable_bindings: BTreeSet<CarryBinding>,
) -> bool {
    if prunable_bindings.is_empty() {
        return false;
    }
    let mut pass = RedundantSelfAssignPrunePass { prunable_bindings };
    rewrite_stmts(stmts, &mut pass)
}

fn collect_prunable_bindings(
    bindings: impl IntoIterator<Item = CarryBinding>,
) -> BTreeSet<CarryBinding> {
    bindings.into_iter().collect()
}

fn prune_boundary_snapshot_self_assigns(
    block: &mut HirBlock,
    prunable_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    if prunable_bindings.is_empty() {
        return false;
    }
    let mut changed = false;

    for index in 0..block.stmts.len() {
        let top_level_boundary_snapshot = matches!(
            block.stmts.get(index + 1),
            Some(HirStmt::Goto(_) | HirStmt::Label(_))
        );
        let falls_through_to_label = matches!(block.stmts.get(index + 1), Some(HirStmt::Label(_)));

        match &mut block.stmts[index] {
            stmt @ HirStmt::Assign(_) if top_level_boundary_snapshot => {
                changed |= prune_redundant_self_assign_components_in_stmt(stmt, prunable_bindings);
            }
            HirStmt::If(if_stmt) => {
                changed |= prune_edge_snapshot_self_assigns(
                    &mut if_stmt.then_block,
                    falls_through_to_label,
                    prunable_bindings,
                );
                if let Some(else_block) = &mut if_stmt.else_block {
                    changed |= prune_edge_snapshot_self_assigns(
                        else_block,
                        falls_through_to_label,
                        prunable_bindings,
                    );
                }
            }
            _ => {}
        }
    }

    changed |= prune_empty_assign_stmts(block);
    changed
}

fn prune_edge_snapshot_self_assigns(
    block: &mut HirBlock,
    allow_fallthrough_to_label: bool,
    prunable_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    let mut changed = match block.stmts.as_mut_slice() {
        [stmt @ HirStmt::Assign(_), HirStmt::Goto(_)] => {
            prune_redundant_self_assign_components_in_stmt(stmt, prunable_bindings)
        }
        [stmt @ HirStmt::Assign(_)] if allow_fallthrough_to_label => {
            prune_redundant_self_assign_components_in_stmt(stmt, prunable_bindings)
        }
        _ => false,
    };
    changed |= prune_empty_assign_stmts(block);
    changed
}

fn matches_direct_writeback_pair(
    target: &HirLValue,
    value: &HirExpr,
    binding: CarryBinding,
    target_temp: TempId,
) -> bool {
    matches!(value, HirExpr::TempRef(temp) if *temp == target_temp)
        && match (binding, target) {
            (CarryBinding::Local(binding), HirLValue::Local(target)) => binding == *target,
            (CarryBinding::Temp(binding), HirLValue::Temp(target)) => binding == *target,
            _ => false,
        }
}

struct TempToTempPass {
    from: TempId,
    to: TempId,
}

impl HirRewritePass for TempToTempPass {
    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        let HirExpr::TempRef(temp) = expr else {
            return false;
        };
        if *temp != self.from {
            return false;
        }
        *expr = HirExpr::TempRef(self.to);
        true
    }

    fn rewrite_lvalue(&mut self, lvalue: &mut HirLValue) -> bool {
        let HirLValue::Temp(temp) = lvalue else {
            return false;
        };
        if *temp != self.from {
            return false;
        }
        *lvalue = HirLValue::Temp(self.to);
        true
    }
}

struct TempToBindingPass {
    rewrites: Vec<TempBindingRewrite>,
}

impl TempToBindingPass {
    fn binding_for_temp(&self, temp: TempId) -> Option<CarryBinding> {
        self.rewrites
            .iter()
            .find_map(|rewrite| (rewrite.from == temp).then_some(rewrite.to))
    }
}

impl HirRewritePass for TempToBindingPass {
    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        let HirExpr::TempRef(temp) = expr else {
            return false;
        };
        let Some(binding) = self.binding_for_temp(*temp) else {
            return false;
        };
        *expr = match binding {
            CarryBinding::Local(local) => HirExpr::LocalRef(local),
            CarryBinding::Temp(temp) => HirExpr::TempRef(temp),
        };
        true
    }

    fn rewrite_lvalue(&mut self, lvalue: &mut HirLValue) -> bool {
        let HirLValue::Temp(temp) = lvalue else {
            return false;
        };
        let Some(binding) = self.binding_for_temp(*temp) else {
            return false;
        };
        *lvalue = match binding {
            CarryBinding::Local(local) => HirLValue::Local(local),
            CarryBinding::Temp(temp) => HirLValue::Temp(temp),
        };
        true
    }
}

fn local_handoff_seed(stmt: &HirStmt) -> Option<(TempId, LocalId)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Temp(temp)] = assign.targets.as_slice() else {
        return None;
    };
    let [HirExpr::LocalRef(local)] = assign.values.as_slice() else {
        return None;
    };
    Some((*temp, *local))
}

fn single_binding_handoff_seed(stmt: &HirStmt) -> Option<(TempId, CarryBinding)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Temp(temp)] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.as_slice() else {
        return None;
    };
    let binding = match value {
        HirExpr::LocalRef(local) => CarryBinding::Local(*local),
        HirExpr::TempRef(source) => CarryBinding::Temp(*source),
        _ => return None,
    };
    Some((*temp, binding))
}

fn suffix_mentions_local(stmts: &[HirStmt], local: LocalId) -> bool {
    let mut collector = LocalMentionCollector {
        local,
        mentioned: false,
    };
    visit_stmts(stmts, &mut collector);
    collector.mentioned
}

fn suffix_mentions_binding(stmts: &[HirStmt], binding: CarryBinding) -> bool {
    let mut collector = BindingMentionCollector {
        binding,
        mentioned: false,
    };
    visit_stmts(stmts, &mut collector);
    collector.mentioned
}

fn suffix_mentions_temp(stmts: &[HirStmt], temp: TempId) -> bool {
    let mut collector = TempMentionCollector {
        temp,
        mentioned: false,
    };
    visit_stmts(stmts, &mut collector);
    collector.mentioned
}

struct TempToLocalPass {
    temp: TempId,
    local: LocalId,
}

impl HirRewritePass for TempToLocalPass {
    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        let HirExpr::TempRef(temp) = expr else {
            return false;
        };
        if *temp != self.temp {
            return false;
        }
        *expr = HirExpr::LocalRef(self.local);
        true
    }

    fn rewrite_lvalue(&mut self, lvalue: &mut HirLValue) -> bool {
        let HirLValue::Temp(temp) = lvalue else {
            return false;
        };
        if *temp != self.temp {
            return false;
        }
        *lvalue = HirLValue::Local(self.local);
        true
    }
}

#[derive(Clone, Copy)]
struct BindingMentionCollector {
    binding: CarryBinding,
    mentioned: bool,
}

impl HirVisitor for BindingMentionCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        let binding = match expr {
            HirExpr::LocalRef(local) => Some(CarryBinding::Local(*local)),
            HirExpr::TempRef(temp) => Some(CarryBinding::Temp(*temp)),
            _ => None,
        };
        if binding == Some(self.binding) {
            self.mentioned = true;
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if binding_matches_lvalue(lvalue, self.binding) {
            self.mentioned = true;
        }
    }
}

struct LocalMentionCollector {
    local: LocalId,
    mentioned: bool,
}

impl HirVisitor for LocalMentionCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.mentioned |= matches!(expr, HirExpr::LocalRef(local) if *local == self.local);
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.mentioned |= matches!(lvalue, HirLValue::Local(local) if *local == self.local);
    }
}

struct TempMentionCollector {
    temp: TempId,
    mentioned: bool,
}

impl HirVisitor for TempMentionCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.mentioned |= matches!(expr, HirExpr::TempRef(temp) if *temp == self.temp);
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.mentioned |= matches!(lvalue, HirLValue::Temp(temp) if *temp == self.temp);
    }
}

#[cfg(test)]
mod tests;
