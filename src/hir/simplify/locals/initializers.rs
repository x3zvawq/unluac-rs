//! 恢复结构入口、原 nil 批次与合流声明的初始化归属，保留绑定和物理根。
//! 消费原 Def、精确 home 与当前声明边界，不跨求值或回边移动初始化。

use super::*;
use crate::hir::common::{
    HirInlineDisposition, HirInlineRetentionReason, HirOperationSources, HirValuePack,
};
use crate::hir::simplify::mention::stmts_mentioned_locals;
use crate::hir::simplify::walk::{HirRewritePass, rewrite_proto};

/// 单次结构壳没有入口求值；在 Temp 身份仍可核验时，将首写交回外层声明 owner。
pub(super) fn restore_single_pass_entries(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
) -> bool {
    // 候选拒绝[ProofIncomplete:Scope]：显式跳转仍需原声明域的入口证明，不能由词法首写代替。
    if proto.body.stmts.iter().any(stmt_has_label_or_goto) {
        return false;
    }
    struct Entries<'a> {
        facts: &'a ProtoPromotionFacts,
        debug_names: &'a [Option<String>],
        debug_scopes: &'a [Option<usize>],
    }
    impl Entries<'_> {
        fn is_initializer(&self, stmt: &HirStmt) -> bool {
            let Some((temp, value)) = stmt.scalar_temp_assignment() else {
                return false;
            };
            let HirStmt::Assign(assign) = stmt else {
                unreachable!()
            };
            // 候选接受[NoOpScopeProof]：只越过无求值的结构入口，原写及顺序完整保留。
            // 旧物理槽可能含入口残值，不能将移动原写误作删除 Entry(nil) 覆盖。
            // 候选拒绝[ProofIncomplete:Identity]：捕获定义或已失效 home 缺少独立声明域证明。
            self.facts.temp_definition_is_uncaptured(temp)
                // 候选拒绝[PolicyBoundary]：debug 声明入口由 Bindings 的源码窗口持有。
                && self.debug_names[temp.index()].is_none()
                && self.debug_scopes[temp.index()].is_none()
                // 候选拒绝[LayerBoundary]：边转移、源码帧和根释放仍交各自的原子事务 owner 消费。
                && !assign.is_phi_transfer
                && assign.initializer_merge_transaction.is_none()
                && assign.generic_for_initializer_producer.is_none()
                && assign.root_release.is_none()
                && assign.method_rewrite_transaction.is_none()
                && assign.parallel_nil_frame.is_none()
                && matches!(
                    value,
                    HirExpr::Nil
                        | HirExpr::Boolean(_)
                        | HirExpr::Integer(_)
                        | HirExpr::Number(_)
                        | HirExpr::String(_)
                )
        }

        fn block(&self, block: &mut HirBlock, mut prefix: Option<&mut Vec<HirStmt>>) -> bool {
            let mut changed = false;
            let mut output = Vec::with_capacity(block.stmts.len());
            for mut stmt in std::mem::take(&mut block.stmts) {
                if let Some(destination) = prefix.as_deref_mut()
                    && self.is_initializer(&stmt)
                {
                    destination.push(stmt);
                    changed = true;
                    continue;
                }
                if let HirStmt::Repeat(repeat) = &mut stmt
                    && !repeat.preserves_condition
                    && matches!(repeat.cond, HirExpr::Boolean(true))
                {
                    // 嵌套首段直接写入同一外层缓冲，不逐层复制/重扫已移动的初始化序列。
                    let destination = prefix.as_deref_mut().unwrap_or(&mut output);
                    changed |= self.block(&mut repeat.body, Some(destination));
                } else {
                    crate::hir::simplify::walk::for_each_nested_block_mut(
                        &mut stmt,
                        &mut |child| {
                            changed |= self.block(child, None);
                        },
                    );
                }
                // 任何原语句都会结束外层首段；后续单次壳仅向自己的相邻位置移交。
                prefix = None;
                output.push(stmt);
            }
            block.stmts = output;
            changed
        }
    }
    Entries {
        facts,
        debug_names: &proto.temp_debug_locals,
        debug_scopes: &proto.temp_debug_scopes,
    }
    .block(&mut proto.body, None)
}

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
    fn owns_empty_table_initializer(&self, bindings: &[LocalId], values: &[HirExpr]) -> bool {
        let ([local], [HirExpr::TableConstructor(table)]) = (bindings, values) else {
            return false;
        };
        let HirOperationSources::Single(source) = table.sources else {
            return false;
        };
        // 空表没有依赖壳内声明的字段求值；原分配仍写入壳外已经持有的同一绑定。
        table.fields.is_empty()
            && table.trailing_multivalue.is_none()
            && self
                .facts
                .operation_result_temp(source)
                .and_then(|temp| self.facts.promoted_local_for_temp(temp))
                == Some(*local)
            && self
                .facts
                .allocation_result_home(table)
                .is_some_and(|home| self.facts.trusted_local_home_slot(*local) == Some(home))
    }

    fn restore_adjacent_initializers(&self, block: &mut HirBlock) -> bool {
        let mut declarations = Vec::new();
        let mut bindings = Vec::new();
        let mut changed = false;
        let mut removed = BTreeSet::new();
        for index in 0..block.stmts.len() {
            match &mut block.stmts[index] {
                HirStmt::LocalDecl(decl)
                    if decl.values.is_empty()
                        && decl.initializer_merge_transaction.is_none()
                        && decl.generic_for_initializer_producer.is_none()
                        && decl
                            .bindings
                            .iter()
                            .all(|local| !self.debug.contains(local)) =>
                {
                    declarations.push(index);
                    bindings.extend(decl.bindings.iter().copied());
                    continue;
                }
                HirStmt::Assign(assign)
                    if !bindings.is_empty()
                        && self.nil_groups.contains(&bindings)
                        && assign.initializer_merge_transaction.is_none()
                        && assign.generic_for_initializer_producer.is_none()
                        && assign.root_release.is_none()
                        && assign.method_rewrite_transaction.is_none()
                        && assign.parallel_nil_frame.is_none()
                        && !assign.is_phi_transfer
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
                            .all(|value| matches!(value, HirExpr::Nil)) =>
                {
                    // 构造器退休后恢复的空声明仍属于原 LOADNIL 批次；相邻空声明
                    // 没有求值，整批原位归还初始化，避免 AST 再拆成逐槽 nil 赋值。
                    let values = std::mem::take(&mut assign.values);
                    block.stmts[declarations[0]] = HirStmt::LocalDecl(Box::new(HirLocalDecl {
                        bindings: std::mem::take(&mut bindings),
                        values,
                        initializer_merge_transaction: None,
                        generic_for_initializer_producer: None,
                    }));
                    removed.extend(declarations.iter().skip(1).copied());
                    removed.insert(index);
                    changed = true;
                }
                HirStmt::Repeat(repeat)
                    if !repeat.preserves_condition
                        && matches!(repeat.cond, HirExpr::Boolean(true))
                        && !bindings.is_empty() =>
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
                        && (self.nil_groups.contains(&bindings)
                            && assign
                                .values
                                .fixed
                                .iter()
                                .all(|value| matches!(value, HirExpr::Nil))
                            || self.owns_empty_table_initializer(&bindings, &assign.values.fixed))
                    {
                        // 空声明已在壳外持有同一绑定；合并初始化不扩展分配的词法寿命。
                        // 原 nil 批次或单次空表分配都在首写处，越过无求值入口不改变顺序。
                        let HirStmt::Assign(assign) = repeat.body.stmts.remove(0) else {
                            unreachable!()
                        };
                        let mut values = assign.values.fixed.into_iter();
                        for &declaration in &declarations {
                            let HirStmt::LocalDecl(decl) = &mut block.stmts[declaration] else {
                                unreachable!()
                            };
                            decl.values = HirValuePack::fixed(
                                values.by_ref().take(decl.bindings.len()).collect(),
                            );
                        }
                        changed = true;
                    }
                }
                _ => {}
            }
            declarations.clear();
            bindings.clear();
        }
        let mut index = 0;
        block.stmts.retain(|_| {
            let keep = !removed.contains(&index);
            index += 1;
            keep
        });
        changed
    }
}

impl HirRewritePass for Restore<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let initializers_changed = self.restore_adjacent_initializers(block);
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
