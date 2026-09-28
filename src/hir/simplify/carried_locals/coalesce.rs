//! 在共享 HIR 控制流上合并不干扰的同槽 carrier。
//!
//! 消费 Promotion 身份与当前活跃性，保留源码声明和资源边界后提交绑定复用。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirAssign, HirBinding, HirBlock, HirCallExpr, HirExpr, HirLValue, HirProto, HirStmt, LocalId,
    TempId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};
use crate::hir::visit::{self, HirVisitor};

use super::super::lexical_cfg::{HirFlowGraph, HirFlowNodeKind};
use super::super::mention::{BindingReadCollector, BindingWriteCollector};
use super::super::temp_touch::collect_temp_reads_in_proto;
use super::super::walk::rewrite_proto;
use super::HandoffIdentityFacts;
use super::binding::{
    BindingClassRewritePass, CarryBinding, binding_home_slot, carry_binding_from_capture,
    carry_binding_from_expr, carry_binding_from_lvalue,
};

pub(super) fn coalesce_disjoint_temps(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
    identity: &HandoffIdentityFacts,
    safety: HirExprSafety,
    dialect: crate::decompile::DecompileDialect,
) -> bool {
    let mut blocked = BTreeSet::new();
    for binding in identity
        .reference_captured
        .iter()
        .chain(&identity.to_be_closed)
    {
        let homes = match *binding {
            CarryBinding::Param(param) => facts.complete_param_home_slots(param),
            CarryBinding::Local(local) => facts.complete_local_home_slots(local),
            CarryBinding::Temp(temp) => facts.complete_temp_home_slots(temp),
        };
        blocked.extend(homes.iter().copied());
    }
    let mut groups = BTreeMap::<HomeSlotKey, Vec<CarryBinding>>::new();
    // 值决策折叠后，根块中已有声明与后续同槽逻辑更新可能各自提升为 Local。
    // 更新不必紧邻或读取旧值；声明仍支配整个根块后缀，旧快照能否共存由下方
    // 整图干扰证明判断。不把声明前的 Temp 归入后置 owner，也不删除原初始化。
    let mut local_updates = BTreeMap::new();
    let mut definition_preserving_updates = BTreeSet::new();
    let mut empty_carried = BTreeSet::new();
    let mut initialized_owners = BTreeMap::new();
    let mut copy_owners = BTreeMap::new();
    let mut preceding_reads = BTreeSet::new();
    let carrier_locals = (0..proto.temp_count)
        .map(TempId)
        .filter(|&temp| facts.is_loop_carrier_temp(temp) || facts.is_phi_carrier_temp(temp))
        .filter_map(|temp| facts.promoted_local_for_temp(temp))
        .collect::<BTreeSet<_>>();
    for stmt in &proto.body.stmts {
        // 根块的声明支配其后控制语句内的低槽写回。只收集原高槽 COPY，
        // 不把子块的新计算或同槽分配猜成外层变量；旧值干扰仍由整图活跃性核对。
        visit::for_each_nested_block(stmt, &mut |block| {
            for child in &block.stmts {
                visit::visit_stmt_structure(child, &mut |child| {
                    let HirStmt::LocalDecl(decl) = child else {
                        return;
                    };
                    let ([target], [value], None) = (
                        decl.bindings.as_slice(),
                        decl.values.fixed.as_slice(),
                        &decl.values.tail,
                    ) else {
                        return;
                    };
                    if let HirExpr::TableAccess(access) = value
                        && decl.initializer_merge_transaction.is_none()
                        && let Some(home) = facts.trusted_local_home_slot(*target)
                        && let Some(&seed) = copy_owners.get(&home)
                        && facts.table_read_result_local(access) == Some(*target)
                        && facts.table_read_result_home(access) == Some(home)
                        && seed != *target
                    {
                        // 原 GETTABLE 覆盖根块中已声明的 carrier；保留计算位置，
                        // 只恢复这次写回身份。旧值快照与协议干扰继续由整图证明排除。
                        local_updates.insert(*target, (seed, home));
                        definition_preserving_updates.insert(*target);
                    }
                    let HirExpr::LocalRef(source) = value else {
                        return;
                    };
                    if decl.initializer_merge_transaction.is_none()
                        && let Some(home) = facts.trusted_local_home_slot(*target)
                        && let Some(&seed) = copy_owners.get(&home)
                        && seed != *target
                        && preceding_reads.contains(&seed)
                        && facts
                            .trusted_local_home_slot(*source)
                            .is_some_and(|source| source.slot() > home.slot())
                    {
                        local_updates.insert(*target, (seed, home));
                    }
                });
            }
        });
        visit::visit_stmts(
            std::slice::from_ref(stmt),
            &mut BindingReadCollector(|binding| {
                if let crate::hir::common::HirBinding::Local(local) = binding {
                    preceding_reads.insert(local);
                }
            }),
        );
        let HirStmt::LocalDecl(update) = stmt else {
            continue;
        };
        for &local in &update.bindings {
            if let Some(home) = facts.trusted_local_home_slot(local) {
                copy_owners.insert(home, local);
            }
        }
        let [target] = update.bindings.as_slice() else {
            continue;
        };
        let Some(home) = facts.trusted_local_home_slot(*target) else {
            continue;
        };
        if update.values.is_empty() {
            // 已有声明后的原地更新不结束其词法域；后置 phi 空声明仍可认回它。
            // 只收集明确的 carrier，首次有效写和旧值干扰仍由整图证明核对。
            if carrier_locals.contains(target)
                && update.initializer_merge_transaction.is_none()
                && let Some(&(seed, _)) = initialized_owners.get(&home)
                && seed != *target
                && preceding_reads.contains(&seed)
            {
                local_updates.insert(*target, (seed, home));
                empty_carried.insert(*target);
            }
            continue;
        }
        let ([value], None) = (update.values.fixed.as_slice(), &update.values.tail) else {
            continue;
        };
        let (seed, preserve_unread_initializer) = *initialized_owners.entry(home).or_insert((
            *target,
            !matches!(value, HirExpr::Nil | HirExpr::Boolean(_)),
        ));
        if seed != *target
            // 未被读取的 nil/Boolean seed 可能只是 Decision 的准备写，不能因合并
            // 赋予它永久声明身份，阻断完整返回或 Boolean initializer 的原帧恢复。
            && (preserve_unread_initializer || preceding_reads.contains(&seed))
            && update.initializer_merge_transaction.is_none()
            && (matches!(value, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))
                // for preheader 的调用可能夹在 seed 与合成 carrier COPY 之间。
                // 声明位置不动；同槽初始化的归属仍由下方整图干扰与协议边界证明。
                || matches!(value, HirExpr::LocalRef(source)
                    if *source == seed && carrier_locals.contains(target)))
        {
            local_updates.insert(*target, (seed, home));
        }
    }
    // 子块中的 seed 同样支配其词法后缀；for 的 iterator 准备可夹在 seed
    // 与 carrier COPY 之间，因此不能只识别相邻声明。只收集本块已声明的同槽
    // 身份，捕获、协议及旧值快照仍交给下面统一的整图证明。
    let mut scoped_updates = Vec::new();
    let mut scoped_temps = BTreeMap::new();
    let mut phi_inputs = BTreeSet::new();
    let mut literal_writes = BTreeSet::new();
    let temp_reads = collect_temp_reads_in_proto(proto);
    ScopedCarrierDeclarations {
        facts,
        updates: &mut scoped_updates,
        temp_owners: &mut scoped_temps,
        phi_inputs: &mut phi_inputs,
        literal_writes: &mut literal_writes,
        candidate: |seed, target, empty| {
            if carrier_locals.contains(&target)
                && let Some(home) = facts.trusted_local_home_slot(seed)
                && facts.trusted_local_home_slot(target) == Some(home)
            {
                local_updates.insert(target, (seed, home));
                if empty {
                    empty_carried.insert(target);
                }
            }
        },
    }
    .block(&proto.body, &mut BTreeMap::new());
    // Boolean initializer 的入口写由完整值帧消费；不能先接到前一代 local，
    // 否则它会反过来阻止前一帧退休其 scratch 声明。
    let mut pending_value_locals = BTreeSet::new();
    for (initial, _, _, _) in facts.boolean_value_prewrites() {
        literal_writes.remove(&initial);
        pending_value_locals.extend(facts.promoted_local_for_temp(initial));
    }
    // PUC/JIT 回调还可经 debug.setlocal 改写非捕获值；显式写分析不覆盖该入口。
    let inert = (dialect == crate::decompile::DecompileDialect::Luau
        && (scoped_updates.iter().any(|&(_, _, inert_only)| inert_only)
            || literal_writes.iter().any(|temp| {
                !temp_reads.contains(temp) && scoped_temps.get(temp).is_some_and(Option::is_some)
            })))
    .then(|| super::super::object_flow::gc_inert_bindings(proto, safety));
    for (seed, target, inert_only) in scoped_updates {
        // 低槽 COPY 合并可能改变后续临时帧覆盖的根；只有两代都是非资源值时，
        // 才能在保留原写入的前提下交给普通活跃性证明。
        if inert_only
            && (pending_value_locals.contains(&target)
                || !inert.as_ref().is_some_and(|bindings| {
                    bindings.contains(&HirBinding::Local(seed))
                        && bindings.contains(&HirBinding::Local(target))
                }))
        {
            continue;
        }
        local_updates.insert(target, (seed, facts.trusted_local_home_slot(seed).unwrap()));
        definition_preserving_updates.insert(target);
    }
    // 入口直线声明支配后面的整个函数体，可作为跨 goto carrier 的词法 owner。
    // Temp 只认回此前缀中的 owner。根块逻辑更新的 Local 交接另行收集；loop-carrier
    // 及分支 phi 提升生成的空声明则须由下方整图活跃性证明首次有效写支配所有读取。
    let mut preceding_temp_homes = BTreeSet::new();
    for stmt in &proto.body.stmts {
        let HirStmt::LocalDecl(decl) = stmt else {
            if let Some((temp, value)) = stmt.scalar_temp_assignment()
                && matches!(
                    value,
                    HirExpr::Nil
                        | HirExpr::Boolean(_)
                        | HirExpr::Integer(_)
                        | HirExpr::Number(_)
                        | HirExpr::String(_)
                )
                && let Some(home) = facts.trusted_temp_home_slot(temp)
            {
                // 尚未提升的字面量 seed 也属于直线入口；其 home 不能认回后置声明，
                // 否则该 temp 的前置写会被改成声明之前对 local 的访问。
                preceding_temp_homes.insert(home);
                continue;
            }
            break;
        };
        for &local in &decl.bindings {
            if let Some(home) = facts.trusted_local_home_slot(local)
                && !blocked.contains(&home)
                && !preceding_temp_homes.contains(&home)
                && proto
                    .local_debug_scopes
                    .get(local.index())
                    .is_none_or(Option::is_none)
            {
                let group = groups.entry(home).or_default();
                let synthetic = !group.is_empty()
                    && decl.values.is_empty()
                    && decl.initializer_merge_transaction.is_none()
                    && carrier_locals.contains(&local);
                if synthetic {
                    empty_carried.insert(local);
                } else if !group.is_empty() && !local_updates.contains_key(&local) {
                    blocked.insert(home);
                }
                group.push(CarryBinding::Local(local));
            }
        }
    }
    let mut local_only_homes = BTreeSet::new();
    let mut grouped_locals = groups.values().flatten().copied().collect::<BTreeSet<_>>();
    // 分支 carrier 的入口也可能位于循环体内。相邻声明保证 seed 与 carrier
    // 具有同一词法后缀；seed 参与第一条更新的 RHS 并不是快照干扰，是否能共用
    // 身份仍由下面一次整图活跃性证明。不同子块的 owner 不按同槽强行合并。
    visit::visit_proto(
        proto,
        &mut AdjacentCarrierSeeds(|seed, carried| {
            if !carrier_locals.contains(&carried) {
                return;
            }
            let Some(home) = facts.trusted_local_home_slot(seed) else {
                return;
            };
            if facts.trusted_local_home_slot(carried) != Some(home) || blocked.contains(&home) {
                return;
            }
            let group = groups.entry(home).or_insert_with(|| {
                local_only_homes.insert(home);
                vec![CarryBinding::Local(seed)]
            });
            if group.first() != Some(&CarryBinding::Local(seed)) {
                blocked.insert(home);
                return;
            }
            // 根块前缀可能已经收集了这对 Local；它与子块候选拥有相同的成员边界，
            // 不因先进入 groups 就把后续同槽 CALL 参数的独立 Def 纳入归并。
            local_only_homes.insert(home);
            if grouped_locals.insert(CarryBinding::Local(carried)) {
                group.push(CarryBinding::Local(carried));
            }
            empty_carried.insert(carried);
        }),
    );
    for (&target, &(seed, home)) in &local_updates {
        if blocked.contains(&home) {
            continue;
        }
        let group = groups.entry(home).or_insert_with(|| {
            local_only_homes.insert(home);
            vec![CarryBinding::Local(seed)]
        });
        if group.first() != Some(&CarryBinding::Local(seed)) {
            blocked.insert(home);
        } else if grouped_locals.insert(CarryBinding::Local(target)) {
            group.push(CarryBinding::Local(target));
        }
        local_only_homes.insert(home);
    }
    // 显式 phi 写回将循环/分支 Temp 连到既有声明；同槽本身不构成身份。
    // 每次读写都必须处于同一声明的词法后缀，随后仍由整图活跃性排除快照干扰。
    let mut definition_preserving_temps = BTreeSet::new();
    for (temp, owner) in scoped_temps {
        let Some(owner) = owner else { continue };
        let inert_write = literal_writes.contains(&temp)
            && !temp_reads.contains(&temp)
            && inert.as_ref().is_some_and(|bindings| {
                bindings.contains(&HirBinding::Temp(temp))
                    && bindings.contains(&HirBinding::Local(owner))
            });
        if !phi_inputs.contains(&temp) && !inert_write {
            continue;
        }
        let home = facts.trusted_local_home_slot(owner).unwrap();
        let group = groups
            .entry(home)
            .or_insert_with(|| vec![CarryBinding::Local(owner)]);
        if group.first() == Some(&CarryBinding::Local(owner)) {
            group.push(CarryBinding::Temp(temp));
            definition_preserving_temps.insert(temp);
            local_only_homes.insert(home);
        } else {
            blocked.insert(home);
        }
    }
    let scoped_groups = groups
        .iter()
        .filter(|(home, _)| local_only_homes.contains(home))
        .map(|(&home, group)| (home, group.iter().copied().collect::<BTreeSet<_>>()))
        .collect::<BTreeMap<_, _>>();
    for &local in identity.debug.iter().chain(&identity.for_bindings) {
        // 源码身份只保护候选成员；已退出的 for/debug 声明复用同槽，不应封锁
        // 另一组 Local 的归并。引用捕获/TBC 的 may-alias 保护仍按整个 home 生效。
        block_binding_homes(
            CarryBinding::Local(local),
            facts,
            &scoped_groups,
            &mut blocked,
        );
    }
    // ByValue 捕获也冻结来源身份；合并后的后续写会迫使 Lua 编译器改成引用
    // 捕获，使旧闭包观察新值。GC-inert 只证明值域，不能替代这份快照义务。
    for &binding in &identity.value_captured {
        block_binding_homes(binding, facts, &scoped_groups, &mut blocked);
    }
    // 原 GETTABLE 写回和合流空声明都只认回已声明 carrier；不移除实际定义或
    // 求值，按 source/Def 索引的准备协议仍有效。空声明的首次有效写另经 CFG 验证。
    let definition_preserving_homes = scoped_groups
        .iter()
        .filter_map(|(&home, locals)| {
            (locals.len() > 1
                && locals
                    .iter()
                    .filter(|local| groups[&home].first() != Some(*local))
                    .all(|binding| match binding {
                        CarryBinding::Local(local) => {
                            definition_preserving_updates.contains(local)
                                || empty_carried.contains(local)
                        }
                        CarryBinding::Temp(temp) => definition_preserving_temps.contains(temp),
                        CarryBinding::Param(_) => false,
                    }))
            .then_some(home)
        })
        .collect::<BTreeSet<_>>();
    let retained_entry_local = |local| {
        facts.trusted_local_home_slot(local).is_some_and(|home| {
            groups
                .get(&home)
                .is_some_and(|bindings| bindings.first() == Some(&CarryBinding::Local(local)))
        })
    };

    for &binding in &identity.preserved {
        if let CarryBinding::Temp(temp) = binding
            && facts
                .promoted_local_for_temp(temp)
                .and_then(|local| facts.trusted_local_home_slot(local))
                .is_some_and(|home| definition_preserving_homes.contains(&home))
            && matches!(proto.inline_dispositions.temp(temp),
                crate::hir::common::HirInlineDisposition::Preserve(reasons)
                if reasons.iter().all(|reason| *reason == crate::hir::common::HirInlineRetentionReason::PhysicalFramePrefix))
        {
            continue;
        }
        if let CarryBinding::Local(local) = binding
            && (retained_entry_local(local)
                || facts
                    .trusted_local_home_slot(local)
                    .is_some_and(|home| definition_preserving_homes.contains(&home)))
            && facts
                .trusted_local_home_slot(local)
                .is_some_and(|home| scoped_groups.contains_key(&home))
            && matches!(proto.inline_dispositions.local(local),
                crate::hir::common::HirInlineDisposition::Preserve(reasons)
                if reasons.iter().all(|reason| *reason == crate::hir::common::HirInlineRetentionReason::PhysicalFramePrefix))
        {
            // owner 的声明及原槽保持不动，后续同槽 COPY 不破坏前缀保留义务。
            continue;
        }
        block_binding_homes(binding, facts, &scoped_groups, &mut blocked);
    }

    visit::visit_proto(
        proto,
        &mut ProtocolHomes {
            facts,
            scoped_groups: &scoped_groups,
            definition_preserving_homes: &definition_preserving_homes,
            blocked: &mut blocked,
        },
    );

    for &binding in &identity.physical_roots {
        let local = match binding {
            CarryBinding::Local(local) => Some(local),
            CarryBinding::Temp(temp) => facts.promoted_local_for_temp(temp),
            CarryBinding::Param(_) => None,
        };
        if local.is_some_and(|local| {
            (retained_entry_local(local)
                || facts
                    .trusted_local_home_slot(local)
                    .is_some_and(|home| definition_preserving_homes.contains(&home)))
                && binding_home_slot(binding, facts) == facts.trusted_local_home_slot(local)
        }) {
            // 候选接受[RootOwnerPreserved]：入口声明、初始化及 root 标记均留在原处；
            // 只把同一精确 home 的后续写认回该 owner。下方活跃性仍须证明没有旧值
            // 快照与新值同时被读取，不能把任意物理根移入另一个 carrier。
            continue;
        }
        block_binding_homes(binding, facts, &scoped_groups, &mut blocked);
    }

    for temp in (0..proto.temp_count).map(TempId) {
        // scope-end producer 或 COPY 的旧根已提升为保留的入口 local 时，
        // 合并只让同槽 phi 写回该 owner，原声明与覆盖点均不动；不能让已退出
        // HIR 的旧 Temp 身份封锁整个 home。其它 endpoint 仍是根生命周期屏障。
        let retained_root = facts
            .promoted_local_for_temp(temp)
            .is_some_and(retained_entry_local);
        if (facts.is_scope_end_copy_root_temp(temp) || facts.is_copy_root_endpoint(temp, |_| true))
            && !retained_root
            && !facts
                .trusted_temp_home_slot(temp)
                .is_some_and(|home| definition_preserving_homes.contains(&home))
            || proto
                .temp_debug_locals
                .get(temp.index())
                .is_some_and(Option::is_some)
        {
            block_binding_homes(
                CarryBinding::Temp(temp),
                facts,
                &scoped_groups,
                &mut blocked,
            );
        }
    }

    // 无读者的写入留给 dead-temps；吸收到活跃 carrier 会使它们失去独立死写身份。
    for temp in temp_reads {
        if let Some(home) = facts.trusted_temp_home_slot(temp)
            && !blocked.contains(&home)
            && !local_only_homes.contains(&home)
        {
            groups
                .entry(home)
                .or_default()
                .push(CarryBinding::Temp(temp));
        }
    }
    groups.retain(|_, temps| temps.len() > 1);
    if groups.is_empty() {
        return false;
    }
    let homes = groups
        .iter()
        .flat_map(|(&home, temps)| temps.iter().map(move |&temp| (temp, home)))
        .collect::<BTreeMap<_, _>>();
    let Ok(graph) = HirFlowGraph::for_proto(&proto.body, safety) else {
        return false;
    };
    let events = graph
        .nodes()
        .iter()
        .map(|node| {
            let mut event = BindingEvent::default();
            node.kind().visit_evaluation(&mut (
                BindingReadCollector(|binding| {
                    if let Some(binding) = carry_binding_from_capture(binding) {
                        event.reads.insert(binding);
                    }
                }),
                BindingWriteCollector(|binding| {
                    if let Some(binding) = carry_binding_from_capture(binding) {
                        event.writes.insert(binding);
                    }
                }),
            ));
            if let HirFlowNodeKind::Stmt(HirStmt::LocalDecl(decl)) = node.kind()
                && decl.values.is_empty()
            {
                event.empty_carried.extend(
                    decl.bindings
                        .iter()
                        .filter(|local| empty_carried.contains(local))
                        .copied(),
                );
                for &local in &event.empty_carried {
                    event.writes.remove(&CarryBinding::Local(local));
                }
            }
            if matches!(node.kind(), HirFlowNodeKind::UnknownControl) {
                event.reads.extend(homes.keys().copied());
            }
            event.reads.retain(|temp| homes.contains_key(temp));
            event.writes.retain(|temp| homes.contains_key(temp));
            event
        })
        .collect::<Vec<_>>();

    graph.solve_backward(BTreeSet::new(), union_bindings, |id, _, live| {
        let event = &events[id.index()];
        for &local in &event.empty_carried {
            let binding = CarryBinding::Local(local);
            if live.contains(&binding)
                && let Some(&home) = homes.get(&binding)
            {
                // 候选拒绝[SemanticBarrier:ReadBeforeWrite]：删掉合成空声明后，
                // 这条路径会在真正写入 carrier 前读取 seed 的旧值，不能合并。
                blocked.insert(home);
            }
        }
        // 定义与其它 live-out 同时存在；并行写入也不能合成重复 lvalue。
        note_interference(
            live.iter().chain(&event.writes).copied(),
            &homes,
            &mut blocked,
        );
        live.retain(|temp| !event.writes.contains(temp));
        live.extend(&event.reads);
        note_interference(live.iter().copied(), &homes, &mut blocked);
    });
    let rewrites = groups
        .into_iter()
        .filter(|(home, _)| !blocked.contains(home))
        .flat_map(|(_, temps)| {
            let target = temps[0];
            temps
                .into_iter()
                .skip(1)
                .map(move |binding| (binding, target))
        })
        .collect::<BTreeMap<_, _>>();
    if rewrites.is_empty() {
        return false;
    }
    remove_coalesced_carrier_declarations(&mut proto.body, &empty_carried, &rewrites);
    restore_local_update_assignments(&mut proto.body, &local_updates, &rewrites);
    prune_entry_carrier_seeds(proto, &rewrites, facts, identity);
    let merged_locals = rewrites
        .keys()
        .chain(rewrites.values())
        .filter_map(|binding| binding.local())
        .collect::<BTreeSet<_>>();
    let mut merged: BTreeSet<_> = rewrites
        .keys()
        .chain(rewrites.values())
        .filter_map(|binding| {
            if let CarryBinding::Temp(temp) = binding {
                Some(*temp)
            } else {
                None
            }
        })
        .collect();
    let mut local_bindings = Vec::new();
    for temp in (0..proto.temp_count).map(TempId) {
        if let Some(local) = facts.promoted_local_for_temp(temp)
            && merged_locals.contains(&local)
        {
            merged.insert(temp);
            let binding = CarryBinding::Local(local);
            if let CarryBinding::Local(target) = rewrites.get(&binding).copied().unwrap_or(binding)
            {
                local_bindings.push((temp, target));
            }
        }
    }
    local_bindings.extend(rewrites.iter().filter_map(|(source, target)| {
        if let (CarryBinding::Temp(temp), CarryBinding::Local(local)) = (*source, *target) {
            Some((temp, local))
        } else {
            None
        }
    }));
    merged.retain(|temp| {
        !facts
            .trusted_temp_home_slot(*temp)
            .is_some_and(|home| definition_preserving_homes.contains(&home))
    });
    facts.retire_coalesced_definition_facts(&merged);
    // 独占 producer 的证书须退休，原 Def 落在哪个 Local 的身份映射则随改写保留。
    // 完整帧仍按具体 source site、值版本和写域验证，不能把身份合并误作原操作消失。
    for (temp, local) in local_bindings {
        facts.record_temp_local_binding(temp, local);
    }
    facts.rewrite_copy_assignment_bindings(|binding| {
        use crate::hir::common::HirBinding;
        let source = match binding {
            HirBinding::Temp(temp) => CarryBinding::Temp(temp),
            HirBinding::Local(local) => CarryBinding::Local(local),
            HirBinding::Param(param) => CarryBinding::Param(param),
            HirBinding::Upvalue(_) => return binding,
        };
        match rewrites.get(&source).copied().unwrap_or(source) {
            CarryBinding::Temp(temp) => HirBinding::Temp(temp),
            CarryBinding::Local(local) => HirBinding::Local(local),
            CarryBinding::Param(param) => HirBinding::Param(param),
        }
    });
    rewrite_proto(
        proto,
        &mut BindingClassRewritePass {
            rewrites,
            promotion_facts: facts,
        },
    )
}

struct ScopedCarrierDeclarations<'a, F> {
    facts: &'a ProtoPromotionFacts,
    updates: &'a mut Vec<(LocalId, LocalId, bool)>,
    temp_owners: &'a mut BTreeMap<TempId, Option<LocalId>>,
    phi_inputs: &'a mut BTreeSet<TempId>,
    literal_writes: &'a mut BTreeSet<TempId>,
    candidate: F,
}

impl<F: FnMut(LocalId, LocalId, bool)> ScopedCarrierDeclarations<'_, F> {
    fn block(&mut self, block: &HirBlock, owners: &mut BTreeMap<HomeSlotKey, LocalId>) {
        let mut previous = Vec::new();
        for stmt in &block.stmts {
            let mut touches = BTreeSet::new();
            visit::visit_stmt_header(
                stmt,
                &mut BindingReadCollector(|binding| {
                    if let crate::hir::common::HirBinding::Temp(temp) = binding {
                        touches.insert(temp);
                    }
                }),
            );
            visit::visit_stmt_header(
                stmt,
                &mut BindingWriteCollector(|binding| {
                    if let crate::hir::common::HirBinding::Temp(temp) = binding {
                        touches.insert(temp);
                    }
                }),
            );
            for temp in touches {
                let owner = self
                    .facts
                    .trusted_temp_home_slot(temp)
                    .and_then(|home| owners.get(&home).copied());
                self.temp_owners
                    .entry(temp)
                    .and_modify(|old| {
                        if *old != owner {
                            *old = None;
                        }
                    })
                    .or_insert(owner);
            }
            if let HirStmt::Assign(assign) = stmt
                && assign.is_phi_transfer
                && assign.values.tail.is_none()
            {
                for (target, value) in assign.targets.iter().zip(&assign.values.fixed) {
                    if let (HirLValue::Local(local), HirExpr::TempRef(temp)) = (target, value)
                        && self
                            .facts
                            .trusted_local_home_slot(*local)
                            .is_some_and(|home| {
                                self.facts.trusted_temp_home_slot(*temp) == Some(home)
                                    && owners.get(&home) == Some(local)
                            })
                    {
                        self.phi_inputs.insert(*temp);
                    }
                }
            }
            // 原低槽未读标量覆盖仍须发出；两代值都 GC-inert 时可认回已有
            // owner，保留写入位置。其它无读 Temp 留给源码帧恢复独立声明。
            if let Some((temp, HirExpr::Boolean(_) | HirExpr::Integer(_) | HirExpr::Number(_))) =
                stmt.scalar_temp_assignment()
            {
                self.literal_writes.insert(temp);
            }
            if let HirStmt::LocalDecl(decl) = stmt
                && decl.initializer_merge_transaction.is_none()
            {
                if let ([target], [HirExpr::LocalRef(source)], None) = (
                    decl.bindings.as_slice(),
                    decl.values.fixed.as_slice(),
                    &decl.values.tail,
                ) && self
                    .facts
                    .trusted_local_home_slot(*source)
                    .is_some_and(|home| owners.get(&home) == Some(source))
                {
                    (self.candidate)(*source, *target, false);
                }
                if let ([target], [value], None) = (
                    decl.bindings.as_slice(),
                    decl.values.fixed.as_slice(),
                    &decl.values.tail,
                ) && let Some(home) = self.facts.trusted_local_home_slot(*target)
                    && let Some(&seed) = owners.get(&home)
                    && seed != *target
                {
                    let high_copy = matches!(value, HirExpr::LocalRef(source)
                        if self.facts.trusted_local_home_slot(*source)
                            .is_some_and(|input| input.slot() > home.slot()));
                    let binding_copy = matches!(value, HirExpr::LocalRef(_) | HirExpr::ParamRef(_));
                    let mut reads_seed = false;
                    if matches!(value, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)) {
                        visit::visit_expr(
                            value,
                            &mut BindingReadCollector(|binding| {
                                reads_seed |=
                                    binding == crate::hir::common::HirBinding::Local(seed);
                            }),
                        );
                    }
                    let literal = matches!(
                        value,
                        HirExpr::Boolean(_)
                            | HirExpr::Integer(_)
                            | HirExpr::Number(_)
                            | HirExpr::String(_)
                    );
                    if binding_copy || reads_seed || literal {
                        self.updates
                            .push((seed, *target, !high_copy && !reads_seed));
                    }
                }
                for &target in &decl.bindings {
                    let Some(home) = self.facts.trusted_local_home_slot(target) else {
                        continue;
                    };
                    if decl.values.is_empty() {
                        if let Some(&seed) = owners.get(&home) {
                            (self.candidate)(seed, target, true);
                        }
                    } else {
                        previous.push((home, owners.insert(home, target)));
                    }
                }
            }
            if let HirStmt::LocalRootRelease(local) = stmt
                && let Some(home) = self.facts.trusted_local_home_slot(*local)
            {
                previous.push((home, owners.remove(&home)));
            }
            if matches!(stmt, HirStmt::Goto(_) | HirStmt::Label(_)) {
                break;
            }
            visit::for_each_nested_block(stmt, &mut |child| self.block(child, owners));
        }
        // 外层声明支配子块，兄弟分支的局部 owner 则不能沿 DFS 泄漏。
        for (home, old) in previous.into_iter().rev() {
            if let Some(local) = old {
                owners.insert(home, local);
            } else {
                owners.remove(&home);
            }
        }
    }
}

struct AdjacentCarrierSeeds<F>(F);

impl<'hir, F: FnMut(LocalId, LocalId)> HirVisitor<'hir> for AdjacentCarrierSeeds<F> {
    fn visit_block(&mut self, block: &HirBlock) {
        use super::super::local_shapes::{
            empty_single_local_decl_binding, initialized_single_local_decl,
        };

        for pair in block.stmts.windows(2) {
            if pair.iter().any(|stmt| {
                matches!(stmt, HirStmt::LocalDecl(decl) if decl.initializer_merge_transaction.is_some())
            }) {
                // 候选拒绝[LayerBoundary]：尚未提交的整组初始化不能拆走其中的声明。
                continue;
            }
            if let Some((seed, _)) = initialized_single_local_decl(&pair[0])
                && let Some(carried) = empty_single_local_decl_binding(&pair[1])
            {
                (self.0)(seed, carried);
            }
        }
    }
}

fn remove_coalesced_carrier_declarations(
    block: &mut HirBlock,
    empty_carried: &BTreeSet<LocalId>,
    rewrites: &BTreeMap<CarryBinding, CarryBinding>,
) {
    block.stmts.retain_mut(|stmt| {
        super::super::walk::for_each_nested_block_mut(stmt, &mut |child| {
            remove_coalesced_carrier_declarations(child, empty_carried, rewrites);
        });
        if let HirStmt::LocalDecl(decl) = stmt
            && decl.values.is_empty()
        {
            decl.bindings.retain(|local| {
                !empty_carried.contains(local)
                    || !rewrites.contains_key(&CarryBinding::Local(*local))
            });
            return !decl.bindings.is_empty();
        }
        true
    });
}

fn restore_local_update_assignments(
    block: &mut HirBlock,
    local_updates: &BTreeMap<LocalId, (LocalId, HomeSlotKey)>,
    rewrites: &BTreeMap<CarryBinding, CarryBinding>,
) {
    for stmt in &mut block.stmts {
        super::super::walk::for_each_nested_block_mut(stmt, &mut |child| {
            restore_local_update_assignments(child, local_updates, rewrites);
        });
        let HirStmt::LocalDecl(decl) = stmt else {
            continue;
        };
        let [local] = decl.bindings.as_slice() else {
            continue;
        };
        if local_updates.contains_key(local)
            && let Some(&CarryBinding::Local(target)) = rewrites.get(&CarryBinding::Local(*local))
        {
            *stmt = HirStmt::Assign(Box::new(HirAssign {
                luau_function_declaration: false,
                luau_compound_global: false,
                upvalue_write_source: None,
                is_phi_transfer: false,
                parallel_nil_frame: None,
                targets: vec![HirLValue::Local(target)],
                values: std::mem::take(&mut decl.values),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                generic_for_dispatch_release: None,
                method_rewrite_transaction: None,
            }));
        }
    }
}

/// 合并入口 local 后，原 loop phi seed 可能重复该 local 的初始化。
/// 只删除已证明同槽的合成写；版本号保留两端在直线前缀中的真实覆写关系。
fn prune_entry_carrier_seeds(
    proto: &mut HirProto,
    rewrites: &BTreeMap<CarryBinding, CarryBinding>,
    facts: &ProtoPromotionFacts,
    identity: &HandoffIdentityFacts,
) {
    let mut versions = BTreeMap::<CarryBinding, usize>::new();
    let mut seeds = BTreeMap::new();
    for (index, stmt) in proto.body.stmts.iter_mut().enumerate() {
        if !matches!(
            stmt,
            HirStmt::LocalDecl(_) | HirStmt::Assign(_) | HirStmt::CallStmt(_)
        ) {
            break;
        }
        if let HirStmt::Assign(assign) = stmt
            && assign.values.tail.is_none()
            && assign.initializer_merge_transaction.is_none()
            && assign.generic_for_initializer_producer.is_none()
            && assign.generic_for_dispatch_release.is_none()
            && assign.method_rewrite_transaction.is_none()
            && assign.targets.len() == assign.values.fixed.len()
            && assign.values.fixed.iter().all(|value| {
                carry_binding_from_expr(value).is_some()
                    || matches!(
                        value,
                        HirExpr::Nil
                            | HirExpr::Boolean(_)
                            | HirExpr::Integer(_)
                            | HirExpr::Number(_)
                    )
            })
            && assign
                .targets
                .iter()
                .all(|target| carry_binding_from_lvalue(target).is_some())
        {
            let mut keep = Vec::with_capacity(assign.targets.len());
            for (target, value) in assign.targets.iter().zip(&assign.values.fixed) {
                let redundant = (|| {
                    let HirLValue::Temp(temp) = target else {
                        return None;
                    };
                    if !facts.is_loop_carrier_temp(*temp) {
                        return None;
                    }
                    let owner = *rewrites.get(&CarryBinding::Temp(*temp))?;
                    let source = carry_binding_from_expr(value)?;
                    let &(seed_source, owner_version, source_version) = seeds.get(&owner)?;
                    Some(
                        source == seed_source
                            && versions.get(&owner).copied().unwrap_or(0) == owner_version
                            && versions.get(&source).copied().unwrap_or(0) == source_version,
                    )
                })()
                .unwrap_or(false);
                keep.push(!redundant);
            }
            // 整组 RHS 均无求值事件，两个源身份均未捕获；其它直接左值的
            // 提交不能产生可观察回调，也没有调用帧或分配槽因缩短值包而移位。
            let mut cursor = 0;
            assign.targets.retain(|_| {
                let retained = keep[cursor];
                cursor += 1;
                retained
            });
            let mut cursor = 0;
            assign.values.fixed.retain(|_| {
                let retained = keep[cursor];
                cursor += 1;
                retained
            });
        }
        let declaration = match stmt {
            HirStmt::LocalDecl(decl) if decl.values.tail.is_none() => decl
                .bindings
                .iter()
                .zip(&decl.values.fixed)
                .filter_map(|(&local, value)| {
                    Some((CarryBinding::Local(local), carry_binding_from_expr(value)?))
                })
                .filter(|(target, source)| {
                    !identity.reference_captured.contains(target)
                        && !identity.reference_captured.contains(source)
                })
                .collect::<Vec<_>>(),
            _ => Vec::new(),
        };
        visit::visit_stmts(
            std::slice::from_ref(stmt),
            &mut BindingWriteCollector(|binding| {
                if let Some(binding) = carry_binding_from_capture(binding) {
                    versions.insert(binding, index + 1);
                    if let Some(&target) = rewrites.get(&binding) {
                        versions.insert(target, index + 1);
                    }
                }
            }),
        );
        for (target, source) in declaration {
            seeds.insert(
                target,
                (
                    source,
                    index + 1,
                    versions.get(&source).copied().unwrap_or(0),
                ),
            );
        }
    }
    proto.body.stmts.retain(|stmt| !matches!(stmt, HirStmt::Assign(assign) if assign.targets.is_empty() && assign.values.is_empty()));
}

/// 纯 Local 交接不退休同槽的其它 Def；后续 CALL 参数或早先的 scratch
/// 恰好复用同一槽时，其协议不是本次候选的成员，不能据此封锁整个 home。
fn block_binding_homes(
    binding: CarryBinding,
    facts: &ProtoPromotionFacts,
    scoped_groups: &BTreeMap<HomeSlotKey, BTreeSet<CarryBinding>>,
    blocked: &mut BTreeSet<HomeSlotKey>,
) {
    let (homes, local) = match binding {
        CarryBinding::Param(param) => (facts.complete_param_home_slots(param), None),
        CarryBinding::Local(local) => (facts.complete_local_home_slots(local), Some(local)),
        CarryBinding::Temp(temp) => (
            facts.complete_temp_home_slots(temp),
            facts.promoted_local_for_temp(temp),
        ),
    };
    blocked.extend(homes.iter().copied().filter(|home| {
        scoped_groups.get(home).is_none_or(|group| {
            group.contains(&binding)
                || local.is_some_and(|local| group.contains(&CarryBinding::Local(local)))
        })
    }));
}

struct ProtocolHomes<'a> {
    facts: &'a ProtoPromotionFacts,
    scoped_groups: &'a BTreeMap<HomeSlotKey, BTreeSet<CarryBinding>>,
    definition_preserving_homes: &'a BTreeSet<HomeSlotKey>,
    blocked: &'a mut BTreeSet<HomeSlotKey>,
}

impl ProtocolHomes<'_> {
    fn protect(&mut self, temp: TempId) {
        if self
            .facts
            .promoted_local_for_temp(temp)
            .and_then(|local| self.facts.trusted_local_home_slot(local))
            .is_some_and(|home| self.definition_preserving_homes.contains(&home))
        {
            return;
        }
        block_binding_homes(
            CarryBinding::Temp(temp),
            self.facts,
            self.scoped_groups,
            self.blocked,
        );
    }
}

impl HirVisitor<'_> for ProtocolHomes<'_> {
    fn visit_call(&mut self, call: &HirCallExpr) {
        if let Some(frame) = self.facts.native_call_frame(call)
            && let HirExpr::LocalRef(local) = call.callee
            && self.facts.promoted_local_for_temp(frame.callee) == Some(local)
            && self.facts.trusted_local_home_slot(local) == Some(frame.home)
        {
            // 尚在原准备槽的 callee 依赖独立 producer 身份；待完整调用消费后再合并。
            // 已恢复成低槽源变量的读取不再消费该证书，不阻止它后面的同槽交接。
            self.protect(frame.callee);
        }
        // 已树化的 Boolean 参数也持有原 producer 协议，未必仍出现在 argument_roots。
        // 合并其 Local 会退休比较写回/FASTCALL 证书；先由完整调用 owner 消费该参数。
        for index in 0..call.args.fixed.len() {
            if let Some(producer) = self.facts.call_argument_value(call, index) {
                self.protect(producer);
            }
        }
        for root in &call.argument_roots {
            self.protect(root.producer);
        }
    }

    fn visit_stmt(&mut self, stmt: &HirStmt) {
        if matches!(stmt, HirStmt::TableSetList(_)) {
            // 候选拒绝[LayerBoundary]：未完成的 SETLIST 仍消费原 buffer Def。
            // 此时即使值不干扰，合并并退休来源也会让构造器失去槽布局证明；
            // 待完整构造帧消费该协议后，再合并后续逻辑值的源码 owner。
            visit::visit_stmts(
                std::slice::from_ref(stmt),
                &mut BindingReadCollector(|binding| {
                    if let Some(binding) = carry_binding_from_capture(binding)
                        && binding_home_slot(binding, self.facts)
                            .is_none_or(|home| !self.definition_preserving_homes.contains(&home))
                    {
                        block_binding_homes(binding, self.facts, self.scoped_groups, self.blocked);
                    }
                }),
            );
        }
        if let HirStmt::LocalRootRelease(local) = stmt {
            // 候选拒绝[SemanticBarrier:Scope]：入口 root 的源码 owner 在此退出，
            // 后续同槽值已属于另一声明帧；不能因入口声明支配它就重新延长旧 owner。
            self.blocked
                .extend(self.facts.complete_local_home_slots(*local).iter().copied());
        }
        if let HirStmt::GenericFor(for_stmt) = stmt {
            for &temp in &for_stmt.initializer_roots {
                self.protect(temp);
            }
            for result in &for_stmt.dispatch_results {
                self.protect(result.result_def);
            }
        }
        if let HirStmt::Assign(assign) = stmt
            && (assign.method_rewrite_transaction.is_some()
                || assign.generic_for_initializer_producer.is_some())
        {
            // 固定宽度 iterator 初始化须整组消费；只把其中一个结果认回先前
            // callee 会拆散 producer/iterator 配对，后续完整帧便无法恢复循环头。
            for target in &assign.targets {
                if let HirLValue::Temp(temp) = target {
                    self.protect(*temp);
                }
            }
        }
    }
}

#[derive(Default)]
struct BindingEvent {
    reads: BTreeSet<CarryBinding>,
    writes: BTreeSet<CarryBinding>,
    empty_carried: BTreeSet<crate::hir::common::LocalId>,
}

fn union_bindings(current: &mut BTreeSet<CarryBinding>, incoming: &BTreeSet<CarryBinding>) -> bool {
    let before = current.len();
    current.extend(incoming);
    before != current.len()
}

fn note_interference(
    live: impl IntoIterator<Item = CarryBinding>,
    homes: &BTreeMap<CarryBinding, HomeSlotKey>,
    blocked: &mut BTreeSet<HomeSlotKey>,
) {
    let mut seen = BTreeMap::new();
    for temp in live {
        let home = homes[&temp];
        if let Some(previous) = seen.insert(home, temp)
            && previous != temp
        {
            blocked.insert(home);
        }
    }
}
