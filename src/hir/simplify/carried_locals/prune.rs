//! 删除 carried-local 收敛后已证明冗余的赋值。
//!
//! 消费交接 owner 的身份和路径证明，保留仍承担物理写入责任的操作。

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
    call_preparations: &BTreeSet<(CarryBinding, CarryBinding)>,
    reference_captured: &BTreeSet<CarryBinding>,
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
                        // 候选拒绝[LayerBoundary]：前次 CALL 写回后的反向 COPY 仍是下次
                        // callee/SELF 的原准备事件，由完整调用帧消费，不能仅据同值裁剪。
                        && !call_preparations.contains(&(target, source))
                        // 捕获 cell 的回读可开启新的赋值快照；同值不授权把它并回
                        // 前一次 CALL 结果，否则后续帧失去独立消费这两个版本的边界。
                        && !reference_captured.contains(&source)
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

/// 原同槽 COPY 已完成写入时，把合流身份接回该写点；不把逻辑转移推迟到计算之后。
pub(super) fn restore_phi_copy_writes(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
) -> bool {
    use super::super::mention::{BindingReadCollector, stmts_captured_locals};
    use crate::hir::common::HirBinding;
    let mut read_temps = BTreeSet::new();
    visit_stmts(
        &proto.body.stmts,
        &mut BindingReadCollector(|binding| {
            if let HirBinding::Temp(temp) = binding {
                read_temps.insert(temp);
            }
        }),
    );
    let captured = stmts_captured_locals(&proto.body.stmts);
    struct Restore<'a> {
        facts: &'a mut ProtoPromotionFacts,
        read: &'a BTreeSet<TempId>,
        captured: &'a BTreeSet<LocalId>,
        debug: &'a [Option<String>],
        debug_scopes: &'a [Option<usize>],
        merges: Vec<(TempId, LocalId)>,
    }
    impl HirRewritePass for Restore<'_> {
        fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
            let Some(HirStmt::Assign(phi)) = block.stmts.last() else {
                return false;
            };
            if !phi.is_phi_transfer
                || phi.values.tail.is_some()
                || phi.targets.len() != phi.values.fixed.len()
            {
                return false;
            }
            let mut candidates = BTreeMap::new();
            let targets = phi
                .targets
                .iter()
                .filter_map(|target| match target {
                    HirLValue::Local(local) => Some(*local),
                    _ => None,
                })
                .collect::<BTreeSet<_>>();
            for (component, (target, source)) in
                phi.targets.iter().zip(&phi.values.fixed).enumerate()
            {
                let HirLValue::Local(target) = target else {
                    continue;
                };
                let Some(source @ (HirBinding::Local(_) | HirBinding::Param(_))) =
                    HirBinding::from_expr(source)
                else {
                    continue;
                };
                if self.captured.contains(target)
                    || matches!(source, HirBinding::Local(local) if targets.contains(&local))
                {
                    continue;
                }
                if let Some(home) = self.facts.trusted_local_home_slot(*target) {
                    candidates.insert(home, (component, *target, source));
                }
            }
            if candidates.is_empty() {
                return false;
            }
            // phi 持有 canonical producer，原 MOVE 则可能读取它的另一份低槽副本。
            // 只在同一顺序区间跟踪未捕获 local 的当前值版本；写入立即换版本，
            // 因而不能把曾经同值、后来已被覆盖的 binding 当作原 COPY 的来源。
            let suffix = block.stmts[..block.stmts.len() - 1]
                .iter()
                .rposition(|stmt| {
                    matches!(
                        stmt,
                        HirStmt::Block(_)
                            | HirStmt::If(_)
                            | HirStmt::While(_)
                            | HirStmt::Repeat(_)
                            | HirStmt::NumericFor(_)
                            | HirStmt::GenericFor(_)
                            | HirStmt::Goto(_)
                            | HirStmt::Label(_)
                            | HirStmt::Break
                            | HirStmt::Continue
                            | HirStmt::Return(_)
                    )
                })
                .map_or(0, |index| index + 1);
            let mut versions = BTreeMap::new();
            let mut next_version = 0usize;
            let mut copy_versions = Vec::new();
            for (index, stmt) in block
                .stmts
                .iter()
                .enumerate()
                .take(block.stmts.len() - 1)
                .skip(suffix)
            {
                let source = single_binding_copy(stmt).and_then(|(target, source)| {
                    let CarryBinding::Local(source) = source else {
                        return None;
                    };
                    if self.captured.contains(&source) {
                        return None;
                    }
                    let version = *versions.entry(source).or_insert_with(|| {
                        next_version += 1;
                        next_version
                    });
                    Some((target, version))
                });
                let mut writes = BindingWriteCollector::default();
                visit_stmts(std::slice::from_ref(stmt), &mut writes);
                if let HirStmt::LocalDecl(decl) = stmt {
                    writes.locals.extend(decl.bindings.iter().copied());
                }
                for local in writes.locals {
                    let version = source
                        .filter(|(target, _)| *target == CarryBinding::Local(local))
                        .map_or_else(
                            || {
                                next_version += 1;
                                next_version
                            },
                            |(_, version)| version,
                        );
                    versions.insert(local, version);
                }
                if let Some((CarryBinding::Temp(temp), version)) = source {
                    copy_versions.push((index, temp, version));
                }
            }
            let equivalent_copies = copy_versions
                .into_iter()
                .filter_map(|(index, temp, version)| {
                    let home = self.facts.trusted_temp_home_slot(temp)?;
                    let (_, _, HirBinding::Local(expected)) = candidates.get(&home)? else {
                        return None;
                    };
                    (!self.captured.contains(expected) && versions.get(expected) == Some(&version))
                        .then_some(index)
                })
                .collect::<BTreeSet<_>>();
            let mut touched = BTreeSet::new();
            let mut written = BTreeSet::new();
            let mut replacements = Vec::new();
            for (index, stmt) in block
                .stmts
                .iter()
                .enumerate()
                .take(block.stmts.len() - 1)
                .skip(suffix)
                .rev()
            {
                if let Some((temp, value)) = stmt.scalar_temp_assignment()
                    && let Some(source @ (HirBinding::Local(_) | HirBinding::Param(_))) =
                        HirBinding::from_expr(value)
                    && !self.read.contains(&temp)
                    && self.debug.get(temp.index()).is_none_or(Option::is_none)
                    && self
                        .debug_scopes
                        .get(temp.index())
                        .is_none_or(Option::is_none)
                    && let Some(home) = self.facts.trusted_temp_home_slot(temp)
                    && let Some(&(component, target, expected)) = candidates.get(&home)
                    && match expected {
                        HirBinding::Local(_) => {
                            source == expected || equivalent_copies.contains(&index)
                        }
                        // canonical phi 已绕过高槽 COPY；用原 SSA 的只读参数身份认回
                        // 这次写，将目标接回 phi local，保留当前 RHS 与原覆盖位置。
                        HirBinding::Param(param) => {
                            self.facts.readonly_parameter_copy(temp) == Some(param)
                        }
                        _ => false,
                    }
                    && !touched.contains(&target)
                    && !matches!(source, HirBinding::Local(local) if written.contains(&local))
                    && matches!(stmt, HirStmt::Assign(copy)
                        if !copy.is_phi_transfer
                            && copy.initializer_merge_transaction.is_none()
                            && copy.generic_for_initializer_producer.is_none()
                            && copy.generic_for_dispatch_release.is_none()
                            && copy.method_rewrite_transaction.is_none())
                {
                    replacements.push((index, component, temp, target));
                    candidates.remove(&home);
                    written.insert(target);
                }
                let mut collector = (
                    BindingReadCollector(|binding| {
                        if let HirBinding::Local(local) = binding {
                            touched.insert(local);
                        }
                    }),
                    BindingWriteCollector::default(),
                );
                visit_stmts(std::slice::from_ref(stmt), &mut collector);
                let (_, writes) = collector;
                touched.extend(writes.locals.iter().copied());
                written.extend(writes.locals);
                if let HirStmt::LocalDecl(decl) = stmt {
                    touched.extend(decl.bindings.iter().copied());
                    written.extend(decl.bindings.iter().copied());
                }
            }
            if replacements.is_empty() {
                return false;
            }
            let mut removed = BTreeSet::new();
            for (index, component, temp, target) in replacements {
                let HirStmt::Assign(copy) = &mut block.stmts[index] else {
                    unreachable!()
                };
                copy.targets[0] = HirLValue::Local(target);
                self.facts.record_temp_to_local_merge(temp, target);
                self.merges.push((temp, target));
                removed.insert(component);
            }
            let Some(HirStmt::Assign(phi)) = block.stmts.last_mut() else {
                unreachable!()
            };
            let mut component = 0;
            phi.targets.retain(|_| {
                let keep = !removed.contains(&component);
                component += 1;
                keep
            });
            component = 0;
            phi.values.fixed.retain(|_| {
                let keep = !removed.contains(&component);
                component += 1;
                keep
            });
            if phi.targets.is_empty() {
                block.stmts.pop();
            }
            true
        }
    }
    let mut restore = Restore {
        facts,
        read: &read_temps,
        captured: &captured,
        debug: &proto.temp_debug_locals,
        debug_scopes: &proto.temp_debug_scopes,
        merges: Vec::new(),
    };
    let changed = super::super::walk::rewrite_block(&mut proto.body, &mut restore);
    for (temp, local) in restore.merges {
        proto.inline_dispositions.promote_temp_to_local(temp, local);
        if proto.physical_root_temps.contains(&temp) {
            proto.physical_root_locals.insert(local);
        }
    }
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
        || !(facts.promotion_facts.is_loop_carrier_temp(*temp)
            || facts.promotion_facts.is_phi_carrier_temp(*temp))
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
    if !active_for_bindings.contains(local)
        || !(promotion_facts.is_loop_carrier_temp(*temp)
            || promotion_facts.is_phi_carrier_temp(*temp))
    {
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
    mut known: BTreeMap<LocalId, CarryBinding>,
    allow_prune: bool,
) -> (bool, BTreeMap<LocalId, CarryBinding>) {
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
                known.retain(|local, source| !declared.contains(local)
                    && !matches!(source, CarryBinding::Local(source) if declared.contains(source)));
            }
            HirStmt::While(while_stmt) => {
                invalidate_capture_writes_from_expr(&mut known, &while_stmt.cond, facts);
                let loop_entry = stable_loop_entry(
                    &while_stmt.body,
                    &known,
                    facts,
                    facts.safety.may_observe_gc_roots(&while_stmt.cond),
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
                    facts.safety.may_observe_gc_roots(&repeat_stmt.cond),
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
                    && direct_local_binding_copy(stmt).is_some_and(|(local, temp)| {
                        known.get(&local) == Some(&temp) && facts.can_remove(stmt, local, temp)
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
    fn can_remove(&self, stmt: &HirStmt, local: LocalId, source: CarryBinding) -> bool {
        if matches!(stmt, HirStmt::Assign(assign) if assign.is_phi_transfer) {
            // 合流转移没有独立的 VM 写事件；已建立且未失效的同值关系足以删除
            // 重复转移。仍保留目标声明、原初始化和 PhysicalFramePrefix 身份。
            return true;
        }
        let CarryBinding::Temp(temp) = source else {
            // 原 local/param COPY 不由路径同值证明删除，留给其完整帧 owner。
            return false;
        };
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

fn direct_local_binding_copy(stmt: &HirStmt) -> Option<(LocalId, CarryBinding)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let ([HirLValue::Local(local)], [value], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    Some((*local, carry_binding_from_expr(value)?))
}

fn direct_local_binding_decl(stmt: &HirStmt) -> Option<(LocalId, CarryBinding)> {
    let HirStmt::LocalDecl(decl) = stmt else {
        return None;
    };
    let ([local], [value], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    Some((*local, carry_binding_from_expr(value)?))
}

fn update_known_state(
    stmt: &HirStmt,
    known: &mut BTreeMap<LocalId, CarryBinding>,
    facts: &BranchStateCopyFacts<'_>,
) {
    invalidate_capture_writes_from_stmt(known, stmt, facts);
    let copy = direct_local_binding_copy(stmt).or_else(|| direct_local_binding_decl(stmt));
    let mut writes = BindingWriteCollector::default();
    visit_stmts(std::slice::from_ref(stmt), &mut writes);
    invalidate_known_state(known, &writes);
    if let Some((local, source)) = copy {
        known.insert(local, source);
    }
}

/// 循环体里的删除必须在首轮入口和每一条实际回边上都成立。这里对有限的
/// `(local -> binding)` must-state 做单调递减迭代；goto 会把回边降到 unknown，nested loop
/// 则只按其完整写集失效当前关系，不把内层 continue 错认成外层回边。
fn stable_loop_entry(
    body: &HirBlock,
    initial: &BTreeMap<LocalId, CarryBinding>,
    facts: &BranchStateCopyFacts<'_>,
    backedge_may_execute_user_code: bool,
) -> BTreeMap<LocalId, CarryBinding> {
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
    fallthrough: Option<BTreeMap<LocalId, CarryBinding>>,
    backedges: Option<BTreeMap<LocalId, CarryBinding>>,
}

fn analyze_loop_flow(
    block: &HirBlock,
    initial: BTreeMap<LocalId, CarryBinding>,
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
    left: Option<BTreeMap<LocalId, CarryBinding>>,
    right: Option<BTreeMap<LocalId, CarryBinding>>,
) -> Option<BTreeMap<LocalId, CarryBinding>> {
    match (left, right) {
        (Some(left), Some(right)) => Some(intersect_known_states(left, right)),
        (Some(known), None) | (None, Some(known)) => Some(known),
        (None, None) => None,
    }
}

fn remove_known_locals(
    known: &mut Option<BTreeMap<LocalId, CarryBinding>>,
    locals: &BTreeSet<LocalId>,
) {
    if let Some(known) = known {
        known.retain(|local, source| {
            !locals.contains(local)
                && !matches!(source, CarryBinding::Local(source) if locals.contains(source))
        });
    }
}

fn invalidate_known_state(
    known: &mut BTreeMap<LocalId, CarryBinding>,
    writes: &BindingWriteCollector,
) {
    for local in &writes.locals {
        known.remove(local);
    }
    known.retain(|_, source| match source {
        CarryBinding::Local(local) => !writes.locals.contains(local),
        CarryBinding::Temp(temp) => !writes.temps.contains(temp),
        CarryBinding::Param(param) => !writes.params.contains(param),
    });
}

fn invalidate_capture_writes_from_stmt(
    known: &mut BTreeMap<LocalId, CarryBinding>,
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
    known: &mut BTreeMap<LocalId, CarryBinding>,
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
    known: &mut BTreeMap<LocalId, CarryBinding>,
    expr: &HirExpr,
    facts: &BranchStateCopyFacts<'_>,
) {
    if facts.safety.may_observe_gc_roots(expr) {
        invalidate_reference_captured_state(known, facts);
    }
}

fn invalidate_reference_captured_state(
    known: &mut BTreeMap<LocalId, CarryBinding>,
    facts: &BranchStateCopyFacts<'_>,
) {
    known.retain(|local, temp| {
        !facts.reference_captured_locals.contains(local)
            && match temp {
                CarryBinding::Local(source) => !facts.reference_captured_locals.contains(source),
                CarryBinding::Temp(source) => !facts.reference_captured_temps.contains(source),
                CarryBinding::Param(_) => false,
            }
    });
}

fn invalidate_optional_reference_captured_state(
    known: &mut Option<BTreeMap<LocalId, CarryBinding>>,
    facts: &BranchStateCopyFacts<'_>,
) {
    if let Some(known) = known {
        invalidate_reference_captured_state(known, facts);
    }
}

fn invalidate_written_bindings(known: &mut BTreeMap<LocalId, CarryBinding>, body: &HirBlock) {
    let mut writes = BindingWriteCollector::default();
    visit_stmts(&body.stmts, &mut writes);
    invalidate_known_state(known, &writes);
}

fn intersect_known_states(
    mut left: BTreeMap<LocalId, CarryBinding>,
    right: BTreeMap<LocalId, CarryBinding>,
) -> BTreeMap<LocalId, CarryBinding> {
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
    params: BTreeSet<crate::hir::common::ParamId>,
    locals: BTreeSet<LocalId>,
    temps: BTreeSet<TempId>,
}

impl HirVisitor<'_> for BindingWriteCollector {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        match lvalue {
            HirLValue::Local(local) => {
                self.locals.insert(*local);
            }
            HirLValue::Temp(temp) => {
                self.temps.insert(*temp);
            }
            HirLValue::Param(param) => {
                self.params.insert(*param);
            }
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => {}
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
