//! carried-local 收敛后的冗余赋值裁剪。
//!
//! handoff owner 在主模块里完成语义判断；这个模块只删除已经由 owner 或局部控制流证明
//! 无效的复制。除了单目标 `x = x`、空 assign、直接 binding 的整句 `x, y = x, y`，
//! 还收回分支 arm 中“支配初值之后没有任何 binding 写入”的 `target = temp` 快照：
//! `local target = temp; if cond then target = temp end` 变成只保留初值声明。
//! 分支规则在每个 arm 独立维护已证明的 `(local -> temp)` 状态，并让循环入口状态收敛到
//! 首轮入口与所有自然/continue 回边的交集；它不会跨未知 goto 或 reference capture 猜测。
//! debug 身份直接查询 proto 的 canonical 映射；删除已证明的重复写不更新状态，语句列表
//! 按原顺序传播事实并只压缩一次，避免每个重复写都搬移整个尾部。相邻复制裁剪也保留
//! 上一条存活语句的已分类关系；删除项不改变邻接事实，非复制语句则清空它。
//! 多目标赋值默认仍不拆分；唯一例外是这里证明过的 dead loop-carrier mirror 分量：
//! 被删 RHS 只能是纯 `LocalRef`，且目标 temp 的每一次写都必须属于同一 active-for、
//! same-sole-possible-home 删除事务，因此不会留下旧值写而改变并行求值、副作用或 GC root 行为。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirLValue, HirProto, HirStmt, LocalId, TempId,
};
use crate::hir::expr_safety::{HirEvalEffects, HirExprSafety};
use crate::hir::promotion::ProtoPromotionFacts;

use super::super::mention::stmts_reference_captured_bindings;
use super::super::temp_touch::collect_temp_reads_in_proto;
use super::super::walk::{HirRewritePass, rewrite_stmts};
use super::binding::{
    CarryBinding, carry_binding_from_expr, carry_binding_from_lvalue, single_binding_copy,
};
use crate::hir::visit::{HirVisitor, visit_block, visit_stmt_structure, visit_stmts};

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

pub(super) fn prune_redundant_copy_stmts(
    block: &mut HirBlock,
    preserved_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    let mut previous_copy = None;
    let mut changed = false;

    block.stmts.retain(|stmt| {
        let copy = single_binding_copy(stmt);
        let redundant_parallel = matches!(
            stmt,
            HirStmt::Assign(assign)
                if redundant_parallel_self_copy(assign)
                    && !assign_targets_preserved_binding(assign, preserved_bindings)
        );
        if copy.is_some_and(|(target, source)| {
            target == source && !preserved_bindings.contains(&target)
        }) || redundant_parallel
            || previous_copy.zip(copy).is_some_and(
                |((first_target, first_source), (target, source))| {
                    first_target != first_source
                        && first_target == source
                        && first_source == target
                        && !preserved_bindings.contains(&target)
                },
            )
        {
            changed = true;
            false
        } else {
            previous_copy = copy;
            true
        }
    });
    changed
}

pub(super) fn prune_redundant_branch_state_copies(
    proto: &mut HirProto,
    safety: HirExprSafety,
    preserved_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    let reference_captured = stmts_reference_captured_bindings(&proto.body.stmts);
    let facts = BranchStateCopyFacts {
        reference_captured_locals: &reference_captured.locals,
        reference_captured_temps: &reference_captured.temps,
        debug_locals: &proto.local_debug_hints,
        debug_temps: &proto.temp_debug_locals,
        preserved_bindings,
        safety,
    };
    let (changed, _) = rewrite_branch_state_block(&mut proto.body, &facts, BTreeMap::new(), false);
    changed
}

pub(super) fn prune_dead_for_binding_temp_mirrors(
    proto: &mut HirProto,
    promotion_facts: &ProtoPromotionFacts,
    preserved_bindings: &BTreeSet<CarryBinding>,
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
        preserved_bindings,
        &BTreeSet::new(),
        promotion_facts,
    )
}

fn prune_dead_for_binding_temp_mirrors_in_block(
    block: &mut HirBlock,
    live_reads: &BTreeSet<TempId>,
    write_audit: &TempWriteAudit,
    debug_temps: &[bool],
    preserved_bindings: &BTreeSet<CarryBinding>,
    active_for_bindings: &BTreeSet<LocalId>,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    let mut changed = false;
    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());

    for mut stmt in old_stmts {
        let nested_changed = match &mut stmt {
            HirStmt::LocalRootRelease(_) => false,
            HirStmt::NumericFor(numeric_for) => {
                let mut child_for_bindings = active_for_bindings.clone();
                child_for_bindings.insert(numeric_for.binding);
                prune_dead_for_binding_temp_mirrors_in_block(
                    &mut numeric_for.body,
                    live_reads,
                    write_audit,
                    debug_temps,
                    preserved_bindings,
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
                    preserved_bindings,
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
                    preserved_bindings,
                    active_for_bindings,
                    promotion_facts,
                ) | if_stmt.else_block.as_mut().is_some_and(|else_block| {
                    prune_dead_for_binding_temp_mirrors_in_block(
                        else_block,
                        live_reads,
                        write_audit,
                        debug_temps,
                        preserved_bindings,
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
                preserved_bindings,
                active_for_bindings,
                promotion_facts,
            ),
            HirStmt::Repeat(repeat_stmt) => prune_dead_for_binding_temp_mirrors_in_block(
                &mut repeat_stmt.body,
                live_reads,
                write_audit,
                debug_temps,
                preserved_bindings,
                active_for_bindings,
                promotion_facts,
            ),
            HirStmt::Block(inner) => prune_dead_for_binding_temp_mirrors_in_block(
                inner,
                live_reads,
                write_audit,
                debug_temps,
                preserved_bindings,
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
            preserved_bindings,
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
    preserved_bindings: &BTreeSet<CarryBinding>,
    active_for_bindings: &BTreeSet<LocalId>,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    let facts = DeadForBindingMirrorFacts {
        live_reads,
        write_audit,
        debug_temps,
        preserved_bindings,
        active_for_bindings,
        promotion_facts,
    };
    let mut changed = false;
    let old_targets = std::mem::take(&mut assign.targets);
    let old_values = std::mem::take(&mut assign.values.fixed);
    let mut new_targets = Vec::with_capacity(old_targets.len());
    let mut new_values = Vec::with_capacity(old_values.len());
    let mut removed_pairs = Vec::new();
    let mut targets = old_targets.into_iter();
    let mut values = old_values.into_iter();

    loop {
        let Some(target) = targets.next() else {
            new_values.extend(values);
            break;
        };
        let Some(value) = values.next() else {
            new_targets.push(target);
            new_targets.extend(targets);
            break;
        };
        // 逐对移除是安全的：被删 RHS 只是纯 LocalRef，target temp 又已证明无读者，
        // 因此不会改变其余并行分量的求值、副作用或相互可见顺序。fixed pair 与
        // target 同时缩短后，后续 fixed/open-tail 的投影位置保持不变。
        if dead_for_binding_temp_mirror_can_be_pruned(&target, &value, &facts) {
            changed = true;
            removed_pairs.push((target, value));
            continue;
        }
        new_targets.push(target);
        new_values.push(value);
    }

    if changed && new_targets.is_empty() && (!new_values.is_empty() || assign.values.tail.is_some())
    {
        // 零 target assign 会由后续空赋值裁剪整句；若值包仍有额外 fixed/open tail，
        // 删除最后一个 mirror 会连带丢失这些表达式的求值。此时保持原赋值。
        assign.targets = removed_pairs
            .iter()
            .map(|(target, _)| target.clone())
            .collect();
        assign.values.fixed = removed_pairs
            .into_iter()
            .map(|(_, value)| value)
            .chain(new_values)
            .collect();
        return false;
    }

    assign.targets = new_targets;
    assign.values.fixed = new_values;
    if changed {
        assign.generic_for_initializer_producer = None;
    }
    changed
}

struct DeadForBindingMirrorFacts<'a> {
    live_reads: &'a BTreeSet<TempId>,
    write_audit: &'a TempWriteAudit,
    debug_temps: &'a [bool],
    preserved_bindings: &'a BTreeSet<CarryBinding>,
    active_for_bindings: &'a BTreeSet<LocalId>,
    promotion_facts: &'a ProtoPromotionFacts,
}

fn dead_for_binding_temp_mirror_can_be_pruned(
    target: &HirLValue,
    value: &HirExpr,
    facts: &DeadForBindingMirrorFacts<'_>,
) -> bool {
    let (HirLValue::Temp(temp), HirExpr::LocalRef(local)) = (target, value) else {
        return false;
    };
    if !facts.active_for_bindings.contains(local)
        || !facts.promotion_facts.is_loop_carrier_temp(*temp)
    {
        return false;
    }
    if facts.live_reads.contains(temp) {
        // 候选拒绝[SemanticBarrier:ValueFlow]：`t = binding; return t` 若删 mirror 会让后续读取失去该值定义。
        return false;
    }
    if facts
        .preserved_bindings
        .contains(&CarryBinding::Temp(*temp))
    {
        // 候选拒绝[LayerBoundary]：该 temp 写入已由上游 HIR 证明必须保留；即使它在
        // 当前 for mirror 审计中无读取，也不能把另一事务的负向结论洗掉。
        return false;
    }
    if facts
        .debug_temps
        .get(temp.index())
        .copied()
        .unwrap_or(false)
    {
        // 候选拒绝[PolicyBoundary]：zero-read debug temp 仍是项目选择保留的源码 identity。
        return false;
    }
    if facts.write_audit.has_surviving_write(*temp) {
        // 候选拒绝[SemanticBarrier:Lifetime]：regress_347 的 `t=A; for binding=B do t=binding; GC end`
        // 若任一写不是同一唯一可能 home 的 no-op，删 mirror 会让 A 多活并改变弱表/终结观察。
        return false;
    }

    facts.write_audit.all_writes_are_prunable_mirrors(*temp)
}

#[derive(Default)]
struct TempWriteAudit {
    all_prunable_writes: BTreeSet<TempId>,
    surviving_writes: BTreeSet<TempId>,
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
        }
    }

    fn all_writes_are_prunable_mirrors(&self, temp: TempId) -> bool {
        self.all_prunable_writes.contains(&temp) && !self.has_surviving_write(temp)
    }

    fn has_surviving_write(&self, temp: TempId) -> bool {
        self.surviving_writes.contains(&temp)
    }
}

#[derive(Clone, Copy)]
enum MirrorWriteDisposition {
    Prunable,
    Survives,
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
            HirStmt::LocalRootRelease(_) => {}
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
    for (index, target) in assign.targets.iter().enumerate() {
        let HirLValue::Temp(temp) = target else {
            continue;
        };
        let Some(value) = assign.values.fixed.get(index) else {
            // 候选拒绝[SemanticBarrier:ValueArity]：该 target 从 open tail 或 closed nil
            // padding 取值，不是显式 `LocalRef(for_binding)` mirror；写入必须保留。
            audit.note_write(*temp, MirrorWriteDisposition::Survives);
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
    let Some(target_home) = promotion_facts.home_slot(*temp) else {
        return MirrorWriteDisposition::Survives;
    };
    let Some(source_homes) = promotion_facts.possible_local_home_slots(*local) else {
        return MirrorWriteDisposition::Survives;
    };
    if source_homes.len() == 1 && source_homes.contains(&target_home) {
        // LValue 的 raw home 不随 binding rewrite 改变；RHS 即使失去 trusted provenance，
        // 完整可能集合仍为同一单槽时，每条路径上的写都只是该物理 cell 自写回。
        MirrorWriteDisposition::Prunable
    } else {
        MirrorWriteDisposition::Survives
    }
}

struct BranchStateCopyFacts<'a> {
    reference_captured_locals: &'a BTreeSet<LocalId>,
    reference_captured_temps: &'a BTreeSet<TempId>,
    debug_locals: &'a [Option<String>],
    debug_temps: &'a [Option<String>],
    preserved_bindings: &'a BTreeSet<CarryBinding>,
    safety: HirExprSafety,
}

fn rewrite_branch_state_block(
    block: &mut HirBlock,
    facts: &BranchStateCopyFacts<'_>,
    mut known: BTreeMap<LocalId, TempId>,
    allow_prune: bool,
) -> (bool, BTreeMap<LocalId, TempId>) {
    let mut changed = false;
    block.stmts.retain_mut(|stmt| {
        match stmt {
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
                    !facts
                        .safety
                        .is_discard_safe_without_residual(&while_stmt.cond),
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
                    !facts
                        .safety
                        .is_discard_safe_without_residual(&repeat_stmt.cond),
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
                    changed = true;
                    return false;
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
        true
    });
    (changed, known)
}

impl BranchStateCopyFacts<'_> {
    fn can_remove(&self, local: LocalId, temp: TempId) -> bool {
        // 候选拒绝[PolicyBoundary]：retain-debug 模式保留源码 local/temp 的显式写入位置与值 epoch，不把它压成支配声明（regress_336 retain-debug）。
        self.debug_locals
            .get(local.index())
            .is_none_or(Option::is_none)
            && self
                .debug_temps
                .get(temp.index())
                .is_none_or(Option::is_none)
            && !self
                .preserved_bindings
                .contains(&CarryBinding::Local(local))
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
    let mut effects = HirEvalEffects::new(facts.safety, |_| false);
    visit_stmts(std::slice::from_ref(stmt), &mut effects);
    if effects.found() {
        invalidate_reference_captured_state(known, facts);
    }
}

fn invalidate_capture_writes_from_block(
    known: &mut BTreeMap<LocalId, TempId>,
    block: &HirBlock,
    facts: &BranchStateCopyFacts<'_>,
) {
    let mut effects = HirEvalEffects::new(facts.safety, |_| false);
    visit_block(block, &mut effects);
    if effects.found() {
        invalidate_reference_captured_state(known, facts);
    }
}

fn invalidate_capture_writes_from_expr(
    known: &mut BTreeMap<LocalId, TempId>,
    expr: &HirExpr,
    facts: &BranchStateCopyFacts<'_>,
) {
    if !facts.safety.is_discard_safe_without_residual(expr) {
        invalidate_reference_captured_state(known, facts);
    }
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
    let mut locals = BTreeSet::new();
    for stmt in &block.stmts {
        visit_stmt_structure(stmt, &mut |stmt| {
            if let HirStmt::LocalDecl(decl) = stmt {
                locals.extend(decl.bindings.iter().copied());
            }
        });
    }
    locals
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

fn assign_targets_preserved_binding(
    assign: &HirAssign,
    preserved_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    assign
        .targets
        .iter()
        .filter_map(carry_binding_from_lvalue)
        .any(|binding| preserved_bindings.contains(&binding))
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
    assign.generic_for_initializer_producer = None;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::common::{HirPackTail, HirValuePack};
    use crate::hir::promotion::HomeSlotKey;

    fn mirror_facts(temp: TempId, local: LocalId) -> ProtoPromotionFacts {
        let mut facts = ProtoPromotionFacts::default();
        let home = HomeSlotKey::new(0, 0);
        facts.record_temp_home_slot_for_test(temp, home);
        facts.record_local_home_slot(local, home);
        facts.record_loop_carrier_temp_for_test(temp);
        facts
    }

    fn prunable_audit(temp: TempId) -> TempWriteAudit {
        let mut audit = TempWriteAudit::default();
        audit.note_write(temp, MirrorWriteDisposition::Prunable);
        audit
    }

    #[test]
    fn dead_mirror_accepts_invalidated_single_home_provenance() {
        let mirror = TempId(0);
        let binding = LocalId(0);
        let mut facts = mirror_facts(mirror, binding);
        facts.record_temp_home_merge(mirror, Some(BTreeSet::new()));
        facts.record_local_home_merge(binding, Some(BTreeSet::new()));

        assert_eq!(facts.trusted_temp_home_slot(mirror), None);
        assert_eq!(facts.trusted_local_home_slot(binding), None);
        assert!(matches!(
            mirror_write_disposition(
                &HirLValue::Temp(mirror),
                &HirExpr::LocalRef(binding),
                &BTreeSet::from([binding]),
                &facts,
            ),
            MirrorWriteDisposition::Prunable
        ));
        let live_reads = BTreeSet::new();
        let audit = prunable_audit(mirror);
        let preserved_bindings = BTreeSet::from([CarryBinding::Temp(mirror)]);
        let active_for_bindings = BTreeSet::from([binding]);
        let mirror_facts = DeadForBindingMirrorFacts {
            live_reads: &live_reads,
            write_audit: &audit,
            debug_temps: &[false],
            preserved_bindings: &preserved_bindings,
            active_for_bindings: &active_for_bindings,
            promotion_facts: &facts,
        };
        assert!(!dead_for_binding_temp_mirror_can_be_pruned(
            &HirLValue::Temp(mirror),
            &HirExpr::LocalRef(binding),
            &mirror_facts,
        ));
    }

    #[test]
    fn dead_mirror_rejects_multi_home_source_lifetime_change() {
        let mirror = TempId(0);
        let binding = LocalId(0);
        let mut facts = mirror_facts(mirror, binding);
        facts.record_local_home_merge(binding, Some(BTreeSet::from([HomeSlotKey::new(1, 0)])));

        assert!(matches!(
            mirror_write_disposition(
                &HirLValue::Temp(mirror),
                &HirExpr::LocalRef(binding),
                &BTreeSet::from([binding]),
                &facts,
            ),
            MirrorWriteDisposition::Survives
        ));
    }

    #[test]
    fn dead_mirror_component_preserves_open_tail_projection() {
        let mirror = TempId(0);
        let tail_target = TempId(1);
        let binding = LocalId(0);
        let tail = HirPackTail::open(HirExpr::VarArg);
        let mut stmt = HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(mirror), HirLValue::Temp(tail_target)],
            values: HirValuePack::expanding(vec![HirExpr::LocalRef(binding)], tail.clone()),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }));
        let facts = mirror_facts(mirror, binding);

        assert!(prune_dead_for_binding_temp_mirror_components(
            &mut stmt,
            &BTreeSet::new(),
            &prunable_audit(mirror),
            &[false, false],
            &BTreeSet::new(),
            &BTreeSet::from([binding]),
            &facts,
        ));

        assert_eq!(
            stmt,
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(tail_target)],
                values: HirValuePack::expanding(Vec::new(), tail),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            }))
        );
    }

    #[test]
    fn last_dead_mirror_keeps_residual_open_tail_evaluation() {
        let mirror = TempId(0);
        let binding = LocalId(0);
        let mut stmt = HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(mirror)],
            values: HirValuePack::expanding(
                vec![HirExpr::LocalRef(binding)],
                HirPackTail::open(HirExpr::VarArg),
            ),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }));
        let before = stmt.clone();
        let facts = mirror_facts(mirror, binding);

        assert!(!prune_dead_for_binding_temp_mirror_components(
            &mut stmt,
            &BTreeSet::new(),
            &prunable_audit(mirror),
            &[false],
            &BTreeSet::new(),
            &BTreeSet::from([binding]),
            &facts,
        ));
        assert_eq!(stmt, before);
    }
}
