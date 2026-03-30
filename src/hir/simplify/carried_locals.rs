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
//! - 更新后交棒：`assign tX = (sY + 1); ... sY = tX`
//!
//! 满足这几个条件时，说明这个 block 已经把“后半段状态身份”完全交给了 temp；
//! 这里把它认回原 local，删掉 handoff seed。它不会发明新 local，也不会在原 local
//! 仍然活跃时强行合并两段状态。对于第二类“更新后交棒”，它只在旧 binding 后续不再
//! 被读取、并且后续确实存在 `sY = tX` 这种直接写回时才会把 `tX` 重新折回旧
//! binding，并顺手裁掉改写后形成的 `x = x` 冗余赋值分量。
//!
//! 例子：
//! - 输入：`local l0 = 1; do t4 = l0; ::L1:: if t4 < 3 then t4 = t4 + 1; goto L1 end end`
//! - 输出：`local l0 = 1; do ::L1:: if l0 < 3 then l0 = l0 + 1; goto L1 end end`
//! - 输入：`assign t8, t9 = t1, t2; ... assign t8, t9 = step(t8), next`
//! - 输出：`... assign t1, t2 = step(t1), next`
//! - 输入：`assign t3 = (t24 + 1); if cond(t3) then assign t23, t24 = step(t3), t3 end`
//! - 输出：`assign t24 = (t24 + 1); if cond(t24) then assign t23 = step(t24) end`

use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirProto, HirStmt, LocalId, TempId};

use super::visit::{HirVisitor, visit_stmts};
use super::walk::{HirRewritePass, rewrite_proto, rewrite_stmts};

pub(super) fn collapse_carried_local_handoffs_in_proto(proto: &mut HirProto) -> bool {
    rewrite_proto(proto, &mut CarriedLocalPass)
}

struct CarriedLocalPass;

impl HirRewritePass for CarriedLocalPass {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        collapse_block_handoffs(block)
    }
}

fn collapse_block_handoffs(block: &mut HirBlock) -> bool {
    let mut changed = false;
    let mut index = 0;

    while index < block.stmts.len() {
        if try_collapse_pure_binding_handoffs(block, index) {
            changed = true;
            continue;
        }
        if try_collapse_pure_local_handoff(block, index) {
            changed = true;
            continue;
        }
        if try_collapse_binding_update_handoff(block, index) {
            changed = true;
            index += 1;
            continue;
        }

        index += 1;
    }

    changed
}

fn try_collapse_pure_binding_handoffs(block: &mut HirBlock, index: usize) -> bool {
    let Some(rewrites) = pure_binding_handoff_seed(&block.stmts[index]) else {
        return false;
    };

    let suffix = &block.stmts[index + 1..];
    if suffix.is_empty()
        || rewrites.iter().any(|rewrite| {
            suffix_mentions_binding(suffix, rewrite.to)
                || !suffix_mentions_temp(suffix, rewrite.from)
        })
    {
        return false;
    }

    let mut pass = TempToBindingPass { rewrites };
    if !rewrite_stmts(&mut block.stmts[index + 1..], &mut pass) {
        return false;
    }

    block.stmts.remove(index);
    true
}

fn try_collapse_pure_local_handoff(block: &mut HirBlock, index: usize) -> bool {
    let Some((temp, local)) = local_handoff_seed(&block.stmts[index]) else {
        return false;
    };

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

fn try_collapse_binding_update_handoff(block: &mut HirBlock, index: usize) -> bool {
    let Some((target_temp, carried)) = update_handoff_seed(&block.stmts[index]) else {
        return false;
    };

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

    prune_redundant_self_assign_components_in_stmt(&mut block.stmts[index]);
    rewrite_stmts(
        &mut block.stmts[index + 1..],
        &mut RedundantSelfAssignPrunePass,
    );
    prune_empty_assign_stmts(block);
    true
}

#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
enum CarryBinding {
    Local(LocalId),
    Temp(TempId),
}

#[derive(Clone, Copy)]
struct TempBindingRewrite {
    from: TempId,
    to: CarryBinding,
}

fn pure_binding_handoff_seed(stmt: &HirStmt) -> Option<Vec<TempBindingRewrite>> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    if assign.targets.len() < 2 || assign.targets.len() != assign.values.len() {
        return None;
    }

    let mut seen_targets = std::collections::BTreeSet::new();
    let mut seen_bindings = std::collections::BTreeSet::new();
    let mut rewrites = Vec::with_capacity(assign.targets.len());
    for (target, value) in assign.targets.iter().zip(&assign.values) {
        let HirLValue::Temp(target_temp) = target else {
            return None;
        };
        let binding = match value {
            HirExpr::LocalRef(local) => CarryBinding::Local(*local),
            HirExpr::TempRef(temp) => CarryBinding::Temp(*temp),
            _ => return None,
        };
        if !seen_targets.insert(*target_temp) || !seen_bindings.insert(binding) {
            return None;
        }
        rewrites.push(TempBindingRewrite {
            from: *target_temp,
            to: binding,
        });
    }
    Some(rewrites)
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

fn prune_redundant_self_assign_components_in_stmt(stmt: &mut HirStmt) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };

    let mut rewritten = Vec::with_capacity(assign.targets.len());
    for (target, value) in assign
        .targets
        .iter()
        .cloned()
        .zip(assign.values.iter().cloned())
    {
        if !is_redundant_self_assign_pair(&target, &value) {
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

fn is_redundant_self_assign_pair(target: &HirLValue, value: &HirExpr) -> bool {
    match (target, value) {
        (HirLValue::Temp(target), HirExpr::TempRef(value)) => target == value,
        (HirLValue::Local(target), HirExpr::LocalRef(value)) => target == value,
        _ => false,
    }
}

struct RedundantSelfAssignPrunePass;

impl HirRewritePass for RedundantSelfAssignPrunePass {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let original_len = block.stmts.len();
        block.stmts.retain(|stmt| !is_empty_assign_stmt(stmt));
        block.stmts.len() != original_len
    }

    fn rewrite_stmt(&mut self, stmt: &mut HirStmt) -> bool {
        prune_redundant_self_assign_components_in_stmt(stmt)
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

struct BindingMentionCollector {
    binding: CarryBinding,
    mentioned: bool,
}

impl HirVisitor for BindingMentionCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.mentioned |= match (self.binding, expr) {
            (CarryBinding::Local(binding), HirExpr::LocalRef(local)) => binding == *local,
            (CarryBinding::Temp(binding), HirExpr::TempRef(temp)) => binding == *temp,
            _ => false,
        };
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.mentioned |= match (self.binding, lvalue) {
            (CarryBinding::Local(binding), HirLValue::Local(local)) => binding == *local,
            (CarryBinding::Temp(binding), HirLValue::Temp(temp)) => binding == *temp,
            _ => false,
        };
    }
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
