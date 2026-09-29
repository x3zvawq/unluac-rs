//! 恢复原 nil 批次与合流声明的初始化归属，保留绑定和物理根。
//! 消费原批次、精确 home 与当前声明边界，不跨求值或回边移动初始化。

use super::*;
use crate::hir::common::{HirInlineDisposition, HirInlineRetentionReason, HirValuePack};
use crate::hir::simplify::mention::stmts_mentioned_locals;
use crate::hir::simplify::walk::{HirRewritePass, rewrite_proto};

pub(super) fn restore(proto: &mut HirProto, facts: &mut ProtoPromotionFacts) -> bool {
    let mut mentioned = stmts_mentioned_locals(&proto.body.stmts);
    mentioned.extend((0..proto.local_count).map(LocalId).filter(|local| {
        matches!(proto.inline_dispositions.local(*local), HirInlineDisposition::Preserve(reasons)
            if reasons.iter().any(|reason| *reason != HirInlineRetentionReason::PhysicalFramePrefix))
    }));
    let debug = proto
        .local_debug_hints
        .iter()
        .enumerate()
        .filter_map(|(index, hint)| hint.is_some().then_some(LocalId(index)))
        .chain(
            proto
                .local_debug_scopes
                .iter()
                .enumerate()
                .filter_map(|(index, scope)| scope.is_some().then_some(LocalId(index))),
        )
        .collect();
    let mut pass = Restore {
        facts,
        mentioned,
        debug,
        nil_groups: facts
            .nil_write_groups()
            .filter_map(|temps| {
                temps
                    .iter()
                    .map(|&temp| {
                        let local = facts.promoted_local_for_temp(temp)?;
                        let home = facts.trusted_temp_home_slot(temp)?;
                        (Some(home) == facts.trusted_local_home_slot(local)).then_some(local)
                    })
                    .collect::<Option<Vec<_>>>()
            })
            .collect(),
        merges: Vec::new(),
    };
    let changed = rewrite_proto(proto, &mut pass);
    for (seed, target) in pass.merges {
        // 声明仍在原 NIL 写点，保活约束随同一个 home 的身份一起转移。
        if proto.physical_root_locals.remove(&seed) {
            proto.physical_root_locals.insert(target);
        }
        if let HirInlineDisposition::Preserve(reasons) =
            proto.inline_dispositions.local(seed).clone()
        {
            for reason in reasons {
                proto.inline_dispositions.preserve_local(target, reason);
            }
        }
        let homes = facts
            .supplemental_local_definition_write_homes(seed)
            .into_owned();
        facts.merge_local_definition_write_homes(target, homes);
    }
    changed
}

struct Restore<'a> {
    facts: &'a ProtoPromotionFacts,
    mentioned: BTreeSet<LocalId>,
    debug: BTreeSet<LocalId>,
    nil_groups: BTreeSet<Vec<LocalId>>,
    merges: Vec<(LocalId, LocalId)>,
}

impl Restore<'_> {
    fn restore_single_pass_initializers(&self, block: &mut HirBlock) -> bool {
        let mut declarations = Vec::new();
        let mut bindings = Vec::new();
        let mut changed = false;
        for index in 0..block.stmts.len() {
            match &mut block.stmts[index] {
                HirStmt::LocalDecl(decl)
                    if decl.values.is_empty()
                        && decl.initializer_merge_transaction.is_none()
                        && decl
                            .bindings
                            .iter()
                            .all(|local| !self.debug.contains(local)) =>
                {
                    declarations.push(index);
                    bindings.extend(decl.bindings.iter().copied());
                    continue;
                }
                HirStmt::Repeat(repeat)
                    if !repeat.preserves_condition
                        && matches!(repeat.cond, HirExpr::Boolean(true))
                        && !bindings.is_empty()
                        && self.nil_groups.contains(&bindings) =>
                {
                    if let Some(HirStmt::Assign(assign)) = repeat.body.stmts.first()
                        && assign.initializer_merge_transaction.is_none()
                        && assign.generic_for_initializer_producer.is_none()
                        && assign.root_release.is_none()
                        && assign.method_rewrite_transaction.is_none()
                        && assign.parallel_nil_frame.is_none()
                        && assign.targets.len() == bindings.len()
                        && assign
                            .targets
                            .iter()
                            .zip(&bindings)
                            .all(|(target, local)| *target == HirLValue::Local(*local))
                        && assign.values.tail.is_none()
                        && assign.values.fixed.len() == bindings.len()
                        && assign
                            .values
                            .fixed
                            .iter()
                            .all(|value| matches!(value, HirExpr::Nil))
                    {
                        // 壳入口没有求值，首条原 LOADNIL 恰好初始化紧邻的空声明。
                        // 同一绑定、槽序及原 nil 批次均已确认；把初始化交回声明，
                        // 不跨任何原操作，也不把会再次执行的循环体写移到循环外。
                        repeat.body.stmts.remove(0);
                        for &declaration in &declarations {
                            let HirStmt::LocalDecl(decl) = &mut block.stmts[declaration] else {
                                unreachable!()
                            };
                            decl.values =
                                HirValuePack::fixed(vec![HirExpr::Nil; decl.bindings.len()]);
                        }
                        changed = true;
                    }
                }
                _ => {}
            }
            declarations.clear();
            bindings.clear();
        }
        changed
    }
}

impl HirRewritePass for Restore<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let initializers_changed = self.restore_single_pass_initializers(block);
        let mut seeds = BTreeMap::new();
        let mut replacements = Vec::new();
        let mut removed = BTreeSet::new();
        let mut assigned = BTreeSet::new();
        for (index, stmt) in block.stmts.iter().enumerate() {
            // 同块高槽调用可以跨过低槽 nil 声明：不移动初始化或 COPY，只恢复
            // 被 SSA 拆开的同一源码槽。控制路径、未知调用布局和同槽写则终止候选。
            if !matches!(
                stmt,
                HirStmt::LocalDecl(_) | HirStmt::Assign(_) | HirStmt::CallStmt(_)
            ) {
                seeds.clear();
                continue;
            }
            struct Calls<'a> {
                facts: &'a ProtoPromotionFacts,
                floor: Option<usize>,
            }
            impl crate::hir::visit::HirVisitor<'_> for Calls<'_> {
                fn visit_call(&mut self, call: &crate::hir::common::HirCallExpr) {
                    let floor = self
                        .facts
                        .native_call_layout(call)
                        .map_or(0, |layout| layout.home.slot());
                    self.floor = Some(self.floor.map_or(floor, |old| old.min(floor)));
                }
            }
            let mut calls = Calls {
                facts: self.facts,
                floor: None,
            };
            crate::hir::visit::visit_stmts(std::slice::from_ref(stmt), &mut calls);
            if let Some(floor) = calls.floor {
                drop(seeds.split_off(&crate::hir::promotion::HomeSlotKey::new(floor, 0)));
            }
            let HirStmt::LocalDecl(decl) = stmt else {
                crate::hir::visit::visit_stmt_header(
                    stmt,
                    &mut crate::hir::simplify::mention::BindingWriteCollector(|binding| {
                        let homes = match binding {
                            crate::hir::common::HirBinding::Local(local) => {
                                self.facts.complete_local_definition_write_homes(local)
                            }
                            crate::hir::common::HirBinding::Temp(temp) => {
                                self.facts.complete_temp_definition_write_homes(temp)
                            }
                            _ => return,
                        };
                        for home in homes.iter() {
                            seeds.remove(home);
                        }
                    }),
                );
                continue;
            };
            let [local] = decl.bindings.as_slice() else {
                for local in &decl.bindings {
                    for home in self
                        .facts
                        .complete_local_definition_write_homes(*local)
                        .iter()
                    {
                        seeds.remove(home);
                    }
                }
                continue;
            };
            let Some(home) = self.facts.trusted_local_home_slot(*local) else {
                seeds.clear();
                continue;
            };
            if decl.initializer_merge_transaction.is_some() || self.debug.contains(local) {
                seeds.clear();
                continue;
            }
            if decl.values.tail.is_none() && decl.values.fixed == [HirExpr::Nil] {
                seeds.remove(&home);
                if !self.mentioned.contains(local) {
                    seeds.insert(home, (index, *local));
                }
            } else if decl.values.is_empty()
                || matches!(
                    (decl.values.fixed.as_slice(), &decl.values.tail),
                    ([HirExpr::LocalRef(_) | HirExpr::ParamRef(_)], None)
                ) && self
                    .facts
                    .complete_local_definition_write_homes(*local)
                    .iter()
                    .copied()
                    .eq([home])
            {
                if let Some((seed_index, seed)) = seeds.remove(&home) {
                    replacements.push((seed_index, *local));
                    if decl.values.is_empty() {
                        removed.insert(index);
                    } else {
                        assigned.insert(index);
                    }
                    self.merges.push((seed, *local));
                }
            } else {
                for home in self
                    .facts
                    .complete_local_definition_write_homes(*local)
                    .iter()
                {
                    seeds.remove(home);
                }
            }
        }
        for (index, target) in replacements {
            let HirStmt::LocalDecl(decl) = &mut block.stmts[index] else {
                unreachable!()
            };
            decl.bindings[0] = target;
        }
        for index in &assigned {
            let HirStmt::LocalDecl(decl) = &mut block.stmts[*index] else {
                unreachable!()
            };
            block.stmts[*index] = HirStmt::Assign(Box::new(HirAssign {
                luau_function_declaration: false,
                targets: decl
                    .bindings
                    .iter()
                    .copied()
                    .map(HirLValue::Local)
                    .collect(),
                values: std::mem::take(&mut decl.values),
                luau_compound_global: false,
                upvalue_write_source: None,
                is_phi_transfer: false,
                parallel_nil_frame: None,
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                root_release: None,
                method_rewrite_transaction: None,
            }));
        }
        let mut index = 0;
        block.stmts.retain(|_| {
            let keep = !removed.contains(&index);
            index += 1;
            keep
        });
        initializers_changed || !removed.is_empty() || !assigned.is_empty()
    }
}
