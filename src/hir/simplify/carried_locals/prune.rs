//! carried-local 收敛后的冗余赋值裁剪。
//!
//! handoff owner 在主模块里完成语义判断；这个模块只删除已经由 owner 或局部控制流证明
//! 无效的复制。除了单目标 `x = x`、空 assign、直接 binding 的整句 `x, y = x, y`，
//! 还收回分支 arm 中“支配初值之后没有任何 binding 写入”的 `target = temp` 快照：
//! `local target = temp; if cond then target = temp end` 变成只保留初值声明。
//! 分支规则要求 temp 全 proto 单写、target 无 debug/capture/TBC/for/物理 root 身份，
//! 并在每个 arm 独立维护已证明的 `(local -> temp)` 状态；它不会跨未知控制合并猜测。
//! 多目标赋值仍不拆分，因为其中的单个 `x = x` 可能承载其它 RHS 的并行快照。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirLValue, HirProto, HirStmt, LocalId, TempId,
};

use super::super::mention::{
    collect_temp_write_counts, stmts_captured_locals, stmts_protected_locals,
    stmts_reference_captured_bindings, stmts_to_be_closed_temps, stmts_value_captured_bindings,
};
use super::super::visit::{HirVisitor, visit_stmts};
use super::super::walk::{HirRewritePass, rewrite_stmts};
use super::binding::{
    CarryBinding, carry_binding_from_expr, carry_binding_from_lvalue, single_binding_copy,
};

pub(super) struct RedundantSelfAssignPrunePass {
    prunable_bindings: BTreeSet<CarryBinding>,
}

impl RedundantSelfAssignPrunePass {
    pub(super) fn for_bindings(bindings: impl IntoIterator<Item = CarryBinding>) -> Self {
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
        prune_redundant_self_assign_stmt(stmt, &self.prunable_bindings)
    }
}

pub(super) fn prune_empty_assign_stmts(block: &mut HirBlock) -> bool {
    let original_len = block.stmts.len();
    block.stmts.retain(|stmt| !is_empty_assign_stmt(stmt));
    block.stmts.len() != original_len
}

pub(super) fn prune_redundant_copy_stmts(block: &mut HirBlock) -> bool {
    let original = std::mem::take(&mut block.stmts);
    let mut rewritten = Vec::<HirStmt>::with_capacity(original.len());
    let mut changed = false;

    for stmt in original {
        let copy = single_binding_copy(&stmt);
        let redundant_parallel = matches!(
            &stmt,
            HirStmt::Assign(assign) if redundant_parallel_self_copy(assign)
        );
        if copy.is_some_and(|(target, source)| target == source)
            || redundant_parallel
            || rewritten
                .last()
                .and_then(single_binding_copy)
                .zip(copy)
                .is_some_and(|((first_target, first_source), (target, source))| {
                    first_target != first_source && first_target == source && first_source == target
                })
        {
            changed = true;
        } else {
            rewritten.push(stmt);
        }
    }

    block.stmts = rewritten;
    changed
}

pub(super) fn prune_redundant_branch_state_copies(proto: &mut HirProto) -> bool {
    let reference_captured = stmts_reference_captured_bindings(&proto.body.stmts);
    let value_captured = stmts_value_captured_bindings(&proto.body.stmts);
    let mut captured_locals = stmts_captured_locals(&proto.body.stmts);
    captured_locals.extend(value_captured.locals.iter().copied());
    let mut captured_temps = reference_captured.temps;
    captured_temps.extend(value_captured.temps.iter().copied());
    let protected_locals = stmts_protected_locals(&proto.body.stmts);
    let closed_temps = stmts_to_be_closed_temps(&proto.body.stmts);
    let debug_locals = proto
        .locals
        .iter()
        .copied()
        .zip(&proto.local_debug_hints)
        .filter_map(|(local, hint)| hint.is_some().then_some(local))
        .collect();
    let temp_write_counts = collect_temp_write_counts(proto);
    let facts = BranchStateCopyFacts {
        captured_locals: &captured_locals,
        captured_temps: &captured_temps,
        protected_locals: &protected_locals,
        closed_temps: &closed_temps,
        debug_locals: &debug_locals,
        debug_temps: &proto.temp_debug_locals,
        physical_root_locals: &proto.physical_root_locals,
        temp_write_counts: &temp_write_counts,
    };
    let (changed, _) = rewrite_branch_state_block(&mut proto.body, &facts, BTreeMap::new(), false);
    changed
}

struct BranchStateCopyFacts<'a> {
    captured_locals: &'a BTreeSet<LocalId>,
    captured_temps: &'a BTreeSet<TempId>,
    protected_locals: &'a BTreeSet<LocalId>,
    closed_temps: &'a BTreeSet<TempId>,
    debug_locals: &'a BTreeSet<LocalId>,
    debug_temps: &'a [Option<String>],
    physical_root_locals: &'a BTreeSet<LocalId>,
    temp_write_counts: &'a BTreeMap<TempId, usize>,
}

fn rewrite_branch_state_block(
    block: &mut HirBlock,
    facts: &BranchStateCopyFacts<'_>,
    mut known: BTreeMap<LocalId, TempId>,
    allow_prune: bool,
) -> (bool, BTreeMap<LocalId, TempId>) {
    let mut changed = false;
    let mut index = 0;
    while index < block.stmts.len() {
        match &mut block.stmts[index] {
            HirStmt::If(if_stmt) => {
                let incoming = known.clone();
                let (then_changed, then_known) = rewrite_branch_state_block(
                    &mut if_stmt.then_block,
                    facts,
                    incoming.clone(),
                    true,
                );
                let (else_changed, else_known) = if let Some(else_block) = &mut if_stmt.else_block {
                    rewrite_branch_state_block(else_block, facts, incoming, true)
                } else {
                    (false, incoming)
                };
                changed |= then_changed || else_changed;
                known = intersect_known_states(then_known, else_known);
            }
            HirStmt::Block(nested) => {
                let declared = declared_locals(nested);
                let (nested_changed, nested_known) =
                    rewrite_branch_state_block(nested, facts, known.clone(), allow_prune);
                changed |= nested_changed;
                known = nested_known;
                for local in declared {
                    known.remove(&local);
                }
            }
            HirStmt::While(while_stmt) => {
                // 证明缺陷[PotentialUnsoundness:ControlFlow]：这里只把首轮入口 known 带进循环；`local l=t; while c do l=t; use(l); l=u end` 的恢复写在第二轮仍必需，却会被删。
                let (body_changed, _) =
                    rewrite_branch_state_block(&mut while_stmt.body, facts, known.clone(), true);
                changed |= body_changed;
                invalidate_written_locals(&mut known, &while_stmt.body);
            }
            HirStmt::Repeat(repeat_stmt) => {
                // 证明缺陷[PotentialUnsoundness:ControlFlow]：repeat 回边没有参与 known fixed-point，首轮前成立的 local=temp 不能证明每轮入口仍成立。
                let (body_changed, _) =
                    rewrite_branch_state_block(&mut repeat_stmt.body, facts, known.clone(), true);
                changed |= body_changed;
                invalidate_written_locals(&mut known, &repeat_stmt.body);
            }
            HirStmt::NumericFor(for_stmt) => {
                // 证明缺陷[PotentialUnsoundness:ControlFlow]：numeric-for body 的 known 仅来自循环外，未与上一轮 body exit 相交便会提交删除。
                let (body_changed, _) =
                    rewrite_branch_state_block(&mut for_stmt.body, facts, known.clone(), true);
                changed |= body_changed;
                invalidate_written_locals(&mut known, &for_stmt.body);
                known.remove(&for_stmt.binding);
            }
            HirStmt::GenericFor(for_stmt) => {
                // 证明缺陷[PotentialUnsoundness:ControlFlow]：generic-for body 的跨迭代 local 状态未建模，入口 duplicate-copy 删除缺少回边证明。
                let (body_changed, _) =
                    rewrite_branch_state_block(&mut for_stmt.body, facts, known.clone(), true);
                changed |= body_changed;
                invalidate_written_locals(&mut known, &for_stmt.body);
                for binding in &for_stmt.bindings {
                    known.remove(binding);
                }
            }
            stmt => {
                if allow_prune
                    && direct_local_temp_copy(stmt).is_some_and(|(local, temp)| {
                        known.get(&local) == Some(&temp) && facts.can_remove(local, temp)
                    })
                {
                    block.stmts.remove(index);
                    changed = true;
                    continue;
                }
                update_known_state(stmt, &mut known);
                if matches!(
                    stmt,
                    HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_) | HirStmt::Label(_)
                ) {
                    known.clear();
                }
            }
        }
        index += 1;
    }
    (changed, known)
}

impl BranchStateCopyFacts<'_> {
    fn can_remove(&self, local: LocalId, temp: TempId) -> bool {
        // 候选拒绝[SemanticBarrier:Capture]：local/temp 被闭包捕获时，删写会让闭包继续观察旧 cell/value。
        // 候选拒绝[SemanticBarrier:Lifetime]：TBC/protected/physical-root 或 temp 非单写时，删除快照会改变资源/值 epoch 的可观察存活期。
        // 候选拒绝[LayerBoundary]：debug local/temp 的源码身份由 locals/source owner 保留。
        !self.captured_locals.contains(&local)
            && !self.captured_temps.contains(&temp)
            && !self.protected_locals.contains(&local)
            && !self.closed_temps.contains(&temp)
            && !self.debug_locals.contains(&local)
            && self
                .debug_temps
                .get(temp.index())
                .is_none_or(Option::is_none)
            && !self.physical_root_locals.contains(&local)
            && self.temp_write_counts.get(&temp).copied() == Some(1)
    }
}

fn direct_local_temp_copy(stmt: &HirStmt) -> Option<(LocalId, TempId)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let ([HirLValue::Local(local)], [HirExpr::TempRef(temp)], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    Some((*local, *temp))
}

fn direct_local_temp_decl(stmt: &HirStmt) -> Option<(LocalId, TempId)> {
    let HirStmt::LocalDecl(decl) = stmt else {
        return None;
    };
    let ([local], [HirExpr::TempRef(temp)], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    Some((*local, *temp))
}

fn update_known_state(stmt: &HirStmt, known: &mut BTreeMap<LocalId, TempId>) {
    if let Some((local, temp)) =
        direct_local_temp_copy(stmt).or_else(|| direct_local_temp_decl(stmt))
    {
        known.insert(local, temp);
        return;
    }
    let mut writes = LocalWriteCollector::default();
    visit_stmts(std::slice::from_ref(stmt), &mut writes);
    for local in writes.locals {
        known.remove(&local);
    }
}

fn invalidate_written_locals(known: &mut BTreeMap<LocalId, TempId>, body: &HirBlock) {
    let mut writes = LocalWriteCollector::default();
    visit_stmts(&body.stmts, &mut writes);
    for local in writes.locals {
        known.remove(&local);
    }
}

fn intersect_known_states(
    mut left: BTreeMap<LocalId, TempId>,
    right: BTreeMap<LocalId, TempId>,
) -> BTreeMap<LocalId, TempId> {
    left.retain(|local, temp| right.get(local) == Some(temp));
    left
}

fn declared_locals(block: &HirBlock) -> BTreeSet<LocalId> {
    let mut declarations = LocalDeclCollector::default();
    visit_stmts(&block.stmts, &mut declarations);
    declarations.locals
}

#[derive(Default)]
struct LocalDeclCollector {
    locals: BTreeSet<LocalId>,
}

impl HirVisitor for LocalDeclCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        if let HirStmt::LocalDecl(decl) = stmt {
            self.locals.extend(decl.bindings.iter().copied());
        }
    }
}

#[derive(Default)]
struct LocalWriteCollector {
    locals: BTreeSet<LocalId>,
}

impl HirVisitor for LocalWriteCollector {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let HirLValue::Local(local) = lvalue {
            self.locals.insert(*local);
        }
    }
}

fn redundant_parallel_self_copy(assign: &HirAssign) -> bool {
    // 候选拒绝[ProofIncomplete]：非等宽或 open-tail 并行赋值不能由逐 pair 自复制证明覆盖；需完整 value-pack 对位事实。
    if assign.values.tail.is_some()
        || assign.targets.len() < 2
        || assign.targets.len() != assign.values.fixed.len()
    {
        return false;
    }
    let mut targets = BTreeSet::new();
    assign
        .targets
        .iter()
        .zip(&assign.values.fixed)
        .all(|(target, value)| {
            let Some(target) = carry_binding_from_lvalue(target) else {
                return false;
            };
            let Some(value) = carry_binding_from_expr(value) else {
                return false;
            };
            target == value && targets.insert(target)
        })
}

pub(super) fn prune_redundant_self_assigns_in_stmts(
    stmts: &mut [HirStmt],
    prunable_bindings: BTreeSet<CarryBinding>,
) -> bool {
    if prunable_bindings.is_empty() {
        return false;
    }
    let mut pass = RedundantSelfAssignPrunePass { prunable_bindings };
    rewrite_stmts(stmts, &mut pass)
}

pub(super) fn collect_prunable_bindings(
    bindings: impl IntoIterator<Item = CarryBinding>,
) -> BTreeSet<CarryBinding> {
    bindings.into_iter().collect()
}

fn prune_redundant_self_assign_stmt(
    stmt: &mut HirStmt,
    prunable_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    let ([target], [value], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return false;
    };
    if !matches_redundant_self_assign_pair(target, value, prunable_bindings) {
        return false;
    }

    assign.targets.clear();
    assign.values.fixed.clear();
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
        (HirLValue::Param(target), HirExpr::ParamRef(value)) if target == value => {
            Some(CarryBinding::Param(*target))
        }
        (HirLValue::Temp(target), HirExpr::TempRef(value)) if target == value => {
            Some(CarryBinding::Temp(*target))
        }
        (HirLValue::Local(target), HirExpr::LocalRef(value)) if target == value => {
            Some(CarryBinding::Local(*target))
        }
        _ => None,
    }
}

fn is_empty_assign_stmt(stmt: &HirStmt) -> bool {
    matches!(stmt, HirStmt::Assign(assign) if assign.targets.is_empty())
}
