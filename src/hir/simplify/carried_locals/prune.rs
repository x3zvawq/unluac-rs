//! carried-local 收敛后的冗余赋值裁剪。
//!
//! handoff owner 在主模块里完成语义判断；这个模块只删除已经由 owner 或局部控制流证明
//! 无效的复制。除了单目标 `x = x`、空 assign、直接 binding 的整句 `x, y = x, y`，
//! 还收回分支 arm 中“支配初值之后没有任何 binding 写入”的 `target = temp` 快照：
//! `local target = temp; if cond then target = temp end` 变成只保留初值声明。
//! 分支规则在每个 arm 独立维护已证明的 `(local -> temp)` 状态，并让循环入口状态收敛到
//! 首轮入口与所有自然/continue 回边的交集；它不会跨未知 goto 或 reference capture 猜测。
//! 多目标赋值默认仍不拆分；唯一例外是这里证明过的 dead loop-carrier mirror 分量：
//! 被删 RHS 只能是纯 `LocalRef`，且目标 temp 的每一次写都必须属于同一 active-for、
//! same-exact-home 删除事务，因此不会留下旧值写而改变并行求值、副作用或 GC root 行为。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirAssign, HirBlock, HirCallExpr, HirExpr, HirLValue, HirProto, HirStmt, LocalId, TempId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::ProtoPromotionFacts;

use super::super::mention::stmts_reference_captured_bindings;
use super::super::temp_touch::collect_temp_reads_in_proto;
use super::super::visit::{HirVisitor, visit_block, visit_expr, visit_stmts};
use super::super::walk::{HirRewritePass, rewrite_stmts};
use super::binding::{
    CarryBinding, binding_home_slot, carry_binding_from_expr, carry_binding_from_lvalue,
    single_binding_copy,
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

pub(super) fn prune_redundant_branch_state_copies(
    proto: &mut HirProto,
    safety: HirExprSafety,
) -> bool {
    let reference_captured = stmts_reference_captured_bindings(&proto.body.stmts);
    let debug_locals = proto
        .locals
        .iter()
        .copied()
        .zip(&proto.local_debug_hints)
        .filter_map(|(local, hint)| hint.is_some().then_some(local))
        .collect();
    let facts = BranchStateCopyFacts {
        reference_captured_locals: &reference_captured.locals,
        reference_captured_temps: &reference_captured.temps,
        debug_locals: &debug_locals,
        debug_temps: &proto.temp_debug_locals,
        safety,
    };
    let (changed, _) = rewrite_branch_state_block(&mut proto.body, &facts, BTreeMap::new(), false);
    changed
}

pub(super) fn prune_dead_for_binding_temp_mirrors(
    proto: &mut HirProto,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    let live_reads = collect_temp_reads_in_proto(proto);
    let write_audit = collect_temp_write_audit_in_proto(proto, promotion_facts);
    let debug_temps = proto
        .temp_debug_locals
        .iter()
        .map(Option::is_some)
        .collect::<Vec<_>>();
    prune_dead_for_binding_temp_mirrors_in_block(
        &mut proto.body,
        &live_reads,
        &write_audit,
        &debug_temps,
        &BTreeSet::new(),
        promotion_facts,
    )
}

fn prune_dead_for_binding_temp_mirrors_in_block(
    block: &mut HirBlock,
    live_reads: &BTreeSet<TempId>,
    write_audit: &TempWriteAudit,
    debug_temps: &[bool],
    active_for_bindings: &BTreeSet<LocalId>,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    let mut changed = false;
    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());

    for mut stmt in old_stmts {
        let nested_changed = match &mut stmt {
            HirStmt::NumericFor(numeric_for) => {
                let mut child_for_bindings = active_for_bindings.clone();
                child_for_bindings.insert(numeric_for.binding);
                prune_dead_for_binding_temp_mirrors_in_block(
                    &mut numeric_for.body,
                    live_reads,
                    write_audit,
                    debug_temps,
                    &child_for_bindings,
                    promotion_facts,
                )
            }
            HirStmt::GenericFor(generic_for) => {
                let mut child_for_bindings = active_for_bindings.clone();
                child_for_bindings.extend(generic_for.bindings.iter().copied());
                prune_dead_for_binding_temp_mirrors_in_block(
                    &mut generic_for.body,
                    live_reads,
                    write_audit,
                    debug_temps,
                    &child_for_bindings,
                    promotion_facts,
                )
            }
            HirStmt::If(if_stmt) => {
                prune_dead_for_binding_temp_mirrors_in_block(
                    &mut if_stmt.then_block,
                    live_reads,
                    write_audit,
                    debug_temps,
                    active_for_bindings,
                    promotion_facts,
                ) | if_stmt.else_block.as_mut().is_some_and(|else_block| {
                    prune_dead_for_binding_temp_mirrors_in_block(
                        else_block,
                        live_reads,
                        write_audit,
                        debug_temps,
                        active_for_bindings,
                        promotion_facts,
                    )
                })
            }
            HirStmt::While(while_stmt) => prune_dead_for_binding_temp_mirrors_in_block(
                &mut while_stmt.body,
                live_reads,
                write_audit,
                debug_temps,
                active_for_bindings,
                promotion_facts,
            ),
            HirStmt::Repeat(repeat_stmt) => prune_dead_for_binding_temp_mirrors_in_block(
                &mut repeat_stmt.body,
                live_reads,
                write_audit,
                debug_temps,
                active_for_bindings,
                promotion_facts,
            ),
            HirStmt::Block(inner) => prune_dead_for_binding_temp_mirrors_in_block(
                inner,
                live_reads,
                write_audit,
                debug_temps,
                active_for_bindings,
                promotion_facts,
            ),
            HirStmt::LocalDecl(_)
            | HirStmt::GlobalDecl(_)
            | HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Return(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => false,
        };
        changed |= nested_changed;
        if prune_dead_for_binding_temp_mirror_components(
            &mut stmt,
            live_reads,
            write_audit,
            debug_temps,
            active_for_bindings,
            promotion_facts,
        ) {
            changed = true;
            if is_empty_assign_stmt(&stmt) {
                continue;
            }
        }
        new_stmts.push(stmt);
    }

    block.stmts = new_stmts;
    changed
}

fn prune_dead_for_binding_temp_mirror_components(
    stmt: &mut HirStmt,
    live_reads: &BTreeSet<TempId>,
    write_audit: &TempWriteAudit,
    debug_temps: &[bool],
    active_for_bindings: &BTreeSet<LocalId>,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    if assign.values.tail.is_some() || assign.targets.len() != assign.values.fixed.len() {
        return false;
    }

    let mut changed = false;
    let old_targets = std::mem::take(&mut assign.targets);
    let old_values = std::mem::take(&mut assign.values.fixed);
    let mut new_targets = Vec::with_capacity(old_targets.len());
    let mut new_values = Vec::with_capacity(old_values.len());

    for (target, value) in old_targets.into_iter().zip(old_values) {
        // 逐对移除是安全的：被删 RHS 只是纯 LocalRef，target temp 又已证明无读者，
        // 因此不会改变其余并行分量的求值、副作用或相互可见顺序。
        if dead_for_binding_temp_mirror_can_be_pruned(
            &target,
            &value,
            live_reads,
            write_audit,
            debug_temps,
            active_for_bindings,
            promotion_facts,
        ) {
            changed = true;
            continue;
        }
        new_targets.push(target);
        new_values.push(value);
    }

    assign.targets = new_targets;
    assign.values.fixed = new_values;
    changed
}

fn dead_for_binding_temp_mirror_can_be_pruned(
    target: &HirLValue,
    value: &HirExpr,
    live_reads: &BTreeSet<TempId>,
    write_audit: &TempWriteAudit,
    debug_temps: &[bool],
    active_for_bindings: &BTreeSet<LocalId>,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    let (HirLValue::Temp(temp), HirExpr::LocalRef(local)) = (target, value) else {
        return false;
    };
    if !active_for_bindings.contains(local) || !promotion_facts.is_loop_carrier_temp(*temp) {
        return false;
    }
    if live_reads.contains(temp) {
        // 候选拒绝[SemanticBarrier:ValueFlow]：`t = binding; return t` 若删 mirror 会让后续读取失去该值定义。
        return false;
    }
    if debug_temps.get(temp.index()).copied().unwrap_or(false) {
        // 候选拒绝[PolicyBoundary]：zero-read debug temp 仍是项目选择保留的源码 identity。
        return false;
    }
    if write_audit.has_surviving_write(*temp) {
        // 候选拒绝[SemanticBarrier:Lifetime]：`t=A; for binding=B do t=binding; GC end` 若只删 mirror，会让 A 多活并改变终结时机。
        return false;
    }
    if write_audit.has_unproven_write(*temp) {
        // 候选拒绝[ProofIncomplete]：至少一次写缺少 fixed-arity 对位或 trusted exact-home，无法证明该 temp 的所有写都由本事务删除。
        return false;
    }

    write_audit.all_writes_are_prunable_mirrors(*temp)
}

#[derive(Default)]
struct TempWriteAudit {
    all_prunable_writes: BTreeSet<TempId>,
    surviving_writes: BTreeSet<TempId>,
    unproven_writes: BTreeSet<TempId>,
}

impl TempWriteAudit {
    fn note_write(&mut self, temp: TempId, disposition: MirrorWriteDisposition) {
        match disposition {
            MirrorWriteDisposition::Prunable => {
                self.all_prunable_writes.insert(temp);
            }
            MirrorWriteDisposition::Survives => {
                self.surviving_writes.insert(temp);
            }
            MirrorWriteDisposition::ProofIncomplete => {
                self.unproven_writes.insert(temp);
            }
        }
    }

    fn all_writes_are_prunable_mirrors(&self, temp: TempId) -> bool {
        self.all_prunable_writes.contains(&temp)
            && !self.has_surviving_write(temp)
            && !self.has_unproven_write(temp)
    }

    fn has_surviving_write(&self, temp: TempId) -> bool {
        self.surviving_writes.contains(&temp)
    }

    fn has_unproven_write(&self, temp: TempId) -> bool {
        self.unproven_writes.contains(&temp)
    }
}

#[derive(Clone, Copy)]
enum MirrorWriteDisposition {
    Prunable,
    Survives,
    ProofIncomplete,
}

fn collect_temp_write_audit_in_proto(
    proto: &HirProto,
    promotion_facts: &ProtoPromotionFacts,
) -> TempWriteAudit {
    let mut audit = TempWriteAudit::default();
    collect_temp_write_audit_in_block(&proto.body, promotion_facts, &BTreeSet::new(), &mut audit);
    audit
}

fn collect_temp_write_audit_in_block(
    block: &HirBlock,
    promotion_facts: &ProtoPromotionFacts,
    active_for_bindings: &BTreeSet<LocalId>,
    audit: &mut TempWriteAudit,
) {
    for stmt in &block.stmts {
        match stmt {
            HirStmt::Assign(assign) => {
                note_assign_writes(assign, promotion_facts, active_for_bindings, audit)
            }
            HirStmt::NumericFor(numeric_for) => {
                let mut child_for_bindings = active_for_bindings.clone();
                child_for_bindings.insert(numeric_for.binding);
                collect_temp_write_audit_in_block(
                    &numeric_for.body,
                    promotion_facts,
                    &child_for_bindings,
                    audit,
                );
            }
            HirStmt::GenericFor(generic_for) => {
                let mut child_for_bindings = active_for_bindings.clone();
                child_for_bindings.extend(generic_for.bindings.iter().copied());
                collect_temp_write_audit_in_block(
                    &generic_for.body,
                    promotion_facts,
                    &child_for_bindings,
                    audit,
                );
            }
            HirStmt::If(if_stmt) => {
                collect_temp_write_audit_in_block(
                    &if_stmt.then_block,
                    promotion_facts,
                    active_for_bindings,
                    audit,
                );
                if let Some(else_block) = &if_stmt.else_block {
                    collect_temp_write_audit_in_block(
                        else_block,
                        promotion_facts,
                        active_for_bindings,
                        audit,
                    );
                }
            }
            HirStmt::While(while_stmt) => {
                collect_temp_write_audit_in_block(
                    &while_stmt.body,
                    promotion_facts,
                    active_for_bindings,
                    audit,
                );
            }
            HirStmt::Repeat(repeat_stmt) => {
                collect_temp_write_audit_in_block(
                    &repeat_stmt.body,
                    promotion_facts,
                    active_for_bindings,
                    audit,
                );
            }
            HirStmt::Block(inner) => {
                collect_temp_write_audit_in_block(
                    inner,
                    promotion_facts,
                    active_for_bindings,
                    audit,
                );
            }
            HirStmt::LocalDecl(_)
            | HirStmt::GlobalDecl(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Return(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => {}
        }
    }
}

fn note_assign_writes(
    assign: &HirAssign,
    promotion_facts: &ProtoPromotionFacts,
    active_for_bindings: &BTreeSet<LocalId>,
    audit: &mut TempWriteAudit,
) {
    if assign.values.tail.is_some() || assign.targets.len() != assign.values.fixed.len() {
        for target in &assign.targets {
            if let HirLValue::Temp(temp) = target {
                audit.note_write(*temp, MirrorWriteDisposition::ProofIncomplete);
            }
        }
        return;
    }

    for (target, value) in assign.targets.iter().zip(&assign.values.fixed) {
        let HirLValue::Temp(temp) = target else {
            continue;
        };
        let disposition =
            mirror_write_disposition(target, value, active_for_bindings, promotion_facts);
        audit.note_write(*temp, disposition);
    }
}

fn mirror_write_disposition(
    target: &HirLValue,
    value: &HirExpr,
    active_for_bindings: &BTreeSet<LocalId>,
    promotion_facts: &ProtoPromotionFacts,
) -> MirrorWriteDisposition {
    let (HirLValue::Temp(temp), HirExpr::LocalRef(local)) = (target, value) else {
        return MirrorWriteDisposition::Survives;
    };
    if !active_for_bindings.contains(local) || !promotion_facts.is_loop_carrier_temp(*temp) {
        return MirrorWriteDisposition::Survives;
    }
    let (Some(target), Some(source)) = (
        carry_binding_from_lvalue(target),
        carry_binding_from_expr(value),
    ) else {
        return MirrorWriteDisposition::ProofIncomplete;
    };
    match (
        binding_home_slot(target, promotion_facts),
        binding_home_slot(source, promotion_facts),
    ) {
        (Some(target), Some(source)) if target == source => MirrorWriteDisposition::Prunable,
        (Some(_), Some(_)) => MirrorWriteDisposition::Survives,
        _ => MirrorWriteDisposition::ProofIncomplete,
    }
}

struct BranchStateCopyFacts<'a> {
    reference_captured_locals: &'a BTreeSet<LocalId>,
    reference_captured_temps: &'a BTreeSet<TempId>,
    debug_locals: &'a BTreeSet<LocalId>,
    debug_temps: &'a [Option<String>],
    safety: HirExprSafety,
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
                invalidate_capture_writes_from_expr(&mut known, &if_stmt.cond, facts);
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
                invalidate_capture_writes_from_expr(&mut known, &while_stmt.cond, facts);
                let loop_entry = stable_loop_entry(
                    &while_stmt.body,
                    &known,
                    facts,
                    expr_may_execute_user_code(&while_stmt.cond, facts.safety),
                );
                let (body_changed, _) =
                    rewrite_branch_state_block(&mut while_stmt.body, facts, loop_entry, true);
                changed |= body_changed;
                invalidate_written_bindings(&mut known, &while_stmt.body);
                invalidate_capture_writes_from_block(&mut known, &while_stmt.body, facts);
                invalidate_capture_writes_from_expr(&mut known, &while_stmt.cond, facts);
            }
            HirStmt::Repeat(repeat_stmt) => {
                let loop_entry = stable_loop_entry(
                    &repeat_stmt.body,
                    &known,
                    facts,
                    expr_may_execute_user_code(&repeat_stmt.cond, facts.safety),
                );
                let (body_changed, _) =
                    rewrite_branch_state_block(&mut repeat_stmt.body, facts, loop_entry, true);
                changed |= body_changed;
                invalidate_written_bindings(&mut known, &repeat_stmt.body);
                invalidate_capture_writes_from_block(&mut known, &repeat_stmt.body, facts);
                invalidate_capture_writes_from_expr(&mut known, &repeat_stmt.cond, facts);
            }
            HirStmt::NumericFor(for_stmt) => {
                for expr in [&for_stmt.start, &for_stmt.limit, &for_stmt.step] {
                    invalidate_capture_writes_from_expr(&mut known, expr, facts);
                }
                let mut initial_entry = known.clone();
                initial_entry.remove(&for_stmt.binding);
                let loop_entry = stable_loop_entry(&for_stmt.body, &initial_entry, facts, false);
                let (body_changed, _) =
                    rewrite_branch_state_block(&mut for_stmt.body, facts, loop_entry, true);
                changed |= body_changed;
                invalidate_written_bindings(&mut known, &for_stmt.body);
                invalidate_capture_writes_from_block(&mut known, &for_stmt.body, facts);
                known.remove(&for_stmt.binding);
            }
            HirStmt::GenericFor(for_stmt) => {
                invalidate_reference_captured_state(&mut known, facts);
                let mut initial_entry = known.clone();
                for binding in &for_stmt.bindings {
                    initial_entry.remove(binding);
                }
                let loop_entry = stable_loop_entry(&for_stmt.body, &initial_entry, facts, true);
                let (body_changed, _) =
                    rewrite_branch_state_block(&mut for_stmt.body, facts, loop_entry, true);
                changed |= body_changed;
                invalidate_written_bindings(&mut known, &for_stmt.body);
                invalidate_reference_captured_state(&mut known, facts);
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
                update_known_state(stmt, &mut known, facts);
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
        // 候选拒绝[PolicyBoundary]：retain-debug 模式保留源码 local/temp 的显式写入位置与值 epoch，不把它压成支配声明（regress_336 retain-debug）。
        !self.debug_locals.contains(&local)
            && self
                .debug_temps
                .get(temp.index())
                .is_none_or(Option::is_none)
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

fn update_known_state(
    stmt: &HirStmt,
    known: &mut BTreeMap<LocalId, TempId>,
    facts: &BranchStateCopyFacts<'_>,
) {
    invalidate_capture_writes_from_stmt(known, stmt, facts);
    if let Some((local, temp)) =
        direct_local_temp_copy(stmt).or_else(|| direct_local_temp_decl(stmt))
    {
        known.insert(local, temp);
        return;
    }
    let mut writes = BindingWriteCollector::default();
    visit_stmts(std::slice::from_ref(stmt), &mut writes);
    invalidate_known_state(known, &writes);
}

/// 循环体里的删除必须在首轮入口和每一条实际回边上都成立。这里对有限的
/// `(local -> temp)` must-state 做单调递减迭代；goto 会把回边降到 unknown，nested loop
/// 则只按其完整写集失效当前关系，不把内层 continue 错认成外层回边。
fn stable_loop_entry(
    body: &HirBlock,
    initial: &BTreeMap<LocalId, TempId>,
    facts: &BranchStateCopyFacts<'_>,
    backedge_may_execute_user_code: bool,
) -> BTreeMap<LocalId, TempId> {
    let mut entry = initial.clone();
    loop {
        let mut flow = analyze_loop_flow(body, entry.clone(), facts);
        if backedge_may_execute_user_code {
            invalidate_optional_reference_captured_state(&mut flow.fallthrough, facts);
            invalidate_optional_reference_captured_state(&mut flow.backedges, facts);
        }
        let Some(backedge) = merge_known_paths(flow.fallthrough, flow.backedges) else {
            return entry;
        };
        let next = intersect_known_states(initial.clone(), backedge);
        if next == entry {
            return entry;
        }
        entry = next;
    }
}

struct LoopFlow {
    fallthrough: Option<BTreeMap<LocalId, TempId>>,
    backedges: Option<BTreeMap<LocalId, TempId>>,
}

fn analyze_loop_flow(
    block: &HirBlock,
    initial: BTreeMap<LocalId, TempId>,
    facts: &BranchStateCopyFacts<'_>,
) -> LoopFlow {
    let mut flow = LoopFlow {
        fallthrough: Some(initial),
        backedges: None,
    };
    for stmt in &block.stmts {
        let Some(mut known) = flow.fallthrough.take() else {
            if matches!(stmt, HirStmt::Label(_)) {
                // 未解析 goto 可能从任意前驱进入 label；空集表示没有可复用的 must-state。
                flow.fallthrough = Some(BTreeMap::new());
            }
            continue;
        };
        match stmt {
            HirStmt::If(if_stmt) => {
                invalidate_capture_writes_from_expr(&mut known, &if_stmt.cond, facts);
                let then_flow = analyze_loop_flow(&if_stmt.then_block, known.clone(), facts);
                let else_flow = if let Some(else_block) = &if_stmt.else_block {
                    analyze_loop_flow(else_block, known, facts)
                } else {
                    LoopFlow {
                        fallthrough: Some(known),
                        backedges: None,
                    }
                };
                flow.fallthrough = merge_known_paths(then_flow.fallthrough, else_flow.fallthrough);
                flow.backedges = merge_known_paths(
                    flow.backedges,
                    merge_known_paths(then_flow.backedges, else_flow.backedges),
                );
            }
            HirStmt::Block(nested) => {
                let declared = declared_locals(nested);
                let mut nested_flow = analyze_loop_flow(nested, known, facts);
                remove_known_locals(&mut nested_flow.fallthrough, &declared);
                remove_known_locals(&mut nested_flow.backedges, &declared);
                flow.fallthrough = nested_flow.fallthrough;
                flow.backedges = merge_known_paths(flow.backedges, nested_flow.backedges);
            }
            HirStmt::While(while_stmt) => {
                invalidate_capture_writes_from_expr(&mut known, &while_stmt.cond, facts);
                invalidate_capture_writes_from_block(&mut known, &while_stmt.body, facts);
                invalidate_written_bindings(&mut known, &while_stmt.body);
                flow.fallthrough = Some(known);
            }
            HirStmt::Repeat(repeat_stmt) => {
                invalidate_capture_writes_from_block(&mut known, &repeat_stmt.body, facts);
                invalidate_capture_writes_from_expr(&mut known, &repeat_stmt.cond, facts);
                invalidate_written_bindings(&mut known, &repeat_stmt.body);
                flow.fallthrough = Some(known);
            }
            HirStmt::NumericFor(for_stmt) => {
                for expr in [&for_stmt.start, &for_stmt.limit, &for_stmt.step] {
                    invalidate_capture_writes_from_expr(&mut known, expr, facts);
                }
                invalidate_capture_writes_from_block(&mut known, &for_stmt.body, facts);
                invalidate_written_bindings(&mut known, &for_stmt.body);
                known.remove(&for_stmt.binding);
                flow.fallthrough = Some(known);
            }
            HirStmt::GenericFor(for_stmt) => {
                invalidate_reference_captured_state(&mut known, facts);
                invalidate_written_bindings(&mut known, &for_stmt.body);
                for binding in &for_stmt.bindings {
                    known.remove(binding);
                }
                flow.fallthrough = Some(known);
            }
            HirStmt::Continue => {
                flow.backedges = merge_known_paths(flow.backedges, Some(known));
            }
            HirStmt::Break | HirStmt::Return(_) => {}
            HirStmt::Goto(_) => {
                // 非结构跳转不携带当前树遍历的 must-state；清空关系后，label 后的复制会
                // 重新建立自己的状态，不会沿错误的词法前驱继承证明。
                flow.backedges = Some(BTreeMap::new());
            }
            HirStmt::Label(_) => {
                known.clear();
                flow.fallthrough = Some(known);
            }
            stmt => {
                update_known_state(stmt, &mut known, facts);
                flow.fallthrough = Some(known);
            }
        }
    }
    flow
}

fn merge_known_paths(
    left: Option<BTreeMap<LocalId, TempId>>,
    right: Option<BTreeMap<LocalId, TempId>>,
) -> Option<BTreeMap<LocalId, TempId>> {
    match (left, right) {
        (Some(left), Some(right)) => Some(intersect_known_states(left, right)),
        (Some(known), None) | (None, Some(known)) => Some(known),
        (None, None) => None,
    }
}

fn remove_known_locals(known: &mut Option<BTreeMap<LocalId, TempId>>, locals: &BTreeSet<LocalId>) {
    if let Some(known) = known {
        for local in locals {
            known.remove(local);
        }
    }
}

fn invalidate_known_state(known: &mut BTreeMap<LocalId, TempId>, writes: &BindingWriteCollector) {
    for local in &writes.locals {
        known.remove(local);
    }
    known.retain(|_, temp| !writes.temps.contains(temp));
}

fn invalidate_capture_writes_from_stmt(
    known: &mut BTreeMap<LocalId, TempId>,
    stmt: &HirStmt,
    facts: &BranchStateCopyFacts<'_>,
) {
    let mut effects = UserCodeEffectCollector::new(facts.safety);
    visit_stmts(std::slice::from_ref(stmt), &mut effects);
    if effects.found {
        invalidate_reference_captured_state(known, facts);
    }
}

fn invalidate_capture_writes_from_block(
    known: &mut BTreeMap<LocalId, TempId>,
    block: &HirBlock,
    facts: &BranchStateCopyFacts<'_>,
) {
    let mut effects = UserCodeEffectCollector::new(facts.safety);
    visit_block(block, &mut effects);
    if effects.found {
        invalidate_reference_captured_state(known, facts);
    }
}

fn invalidate_capture_writes_from_expr(
    known: &mut BTreeMap<LocalId, TempId>,
    expr: &HirExpr,
    facts: &BranchStateCopyFacts<'_>,
) {
    if expr_may_execute_user_code(expr, facts.safety) {
        invalidate_reference_captured_state(known, facts);
    }
}

fn expr_may_execute_user_code(expr: &HirExpr, safety: HirExprSafety) -> bool {
    let mut effects = UserCodeEffectCollector::new(safety);
    visit_expr(expr, &mut effects);
    effects.found
}

fn invalidate_reference_captured_state(
    known: &mut BTreeMap<LocalId, TempId>,
    facts: &BranchStateCopyFacts<'_>,
) {
    known.retain(|local, temp| {
        !facts.reference_captured_locals.contains(local)
            && !facts.reference_captured_temps.contains(temp)
    });
}

fn invalidate_optional_reference_captured_state(
    known: &mut Option<BTreeMap<LocalId, TempId>>,
    facts: &BranchStateCopyFacts<'_>,
) {
    if let Some(known) = known {
        invalidate_reference_captured_state(known, facts);
    }
}

fn invalidate_written_bindings(known: &mut BTreeMap<LocalId, TempId>, body: &HirBlock) {
    let mut writes = BindingWriteCollector::default();
    visit_stmts(&body.stmts, &mut writes);
    invalidate_known_state(known, &writes);
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
struct BindingWriteCollector {
    locals: BTreeSet<LocalId>,
    temps: BTreeSet<TempId>,
}

impl HirVisitor for BindingWriteCollector {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        match lvalue {
            HirLValue::Local(local) => {
                self.locals.insert(*local);
            }
            HirLValue::Temp(temp) => {
                self.temps.insert(*temp);
            }
            HirLValue::Param(_)
            | HirLValue::Upvalue(_)
            | HirLValue::Global(_)
            | HirLValue::TableAccess(_) => {}
        }
    }
}

struct UserCodeEffectCollector {
    found: bool,
    safety: HirExprSafety,
}

impl UserCodeEffectCollector {
    fn new(safety: HirExprSafety) -> Self {
        Self {
            found: false,
            safety,
        }
    }
}

impl HirVisitor for UserCodeEffectCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.found |= matches!(stmt, HirStmt::GlobalDecl(_) | HirStmt::Close(_));
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        // Allocation, dynamic access, calls and metamethod-capable expressions can run GC or
        // user code that mutates a captured binding. Reuse the shared dialect-aware boundary so
        // branch-state facts cannot survive an event omitted by a second ad-hoc classifier.
        self.found |= !self.safety.is_discard_safe_without_residual(expr);
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.found |= matches!(lvalue, HirLValue::Global(_) | HirLValue::TableAccess(_));
    }

    fn visit_call(&mut self, _call: &HirCallExpr) {
        self.found = true;
    }
}

fn redundant_parallel_self_copy(assign: &HirAssign) -> bool {
    if assign.targets.len() < 2 {
        return false;
    }
    if assign.values.tail.is_some() || assign.targets.len() != assign.values.fixed.len() {
        return false;
    }
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
            target == value
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
