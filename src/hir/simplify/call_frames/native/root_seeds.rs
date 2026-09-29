//! 将合成副本根的入口初始化交回消费其全部退休事件的原帧事务。
//!
//! lowering 提供初始化来源；native preview 恢复实际 COPY 声明并核对完整源码前缀。

use super::*;

pub(super) fn attach(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    plans: &mut Vec<Plan>,
    stmt_count: usize,
) {
    let handoffs = facts
        .copy_root_seed_handoffs()
        .filter_map(|(holder, source)| {
            Some((
                facts.promoted_local_for_temp(holder)?,
                facts.promoted_local_for_temp(source)?,
            ))
        })
        .collect::<BTreeMap<_, _>>();
    let seeds = facts
        .copy_root_seed_locals()
        .chain(handoffs.keys().copied())
        .collect::<BTreeSet<_>>();
    if seeds.is_empty() {
        return;
    }
    let root_bindings = proto
        .body
        .stmts
        .iter()
        .filter_map(|stmt| {
            let HirStmt::LocalDecl(decl) = stmt else {
                return None;
            };
            (!decl.bindings.is_empty()
                && decl.initializer_merge_transaction.is_none()
                && decl.values.tail.is_none()
                && decl.values.fixed.len() == decl.bindings.len()
                && decl
                    .values
                    .fixed
                    .iter()
                    .all(|value| matches!(value, HirExpr::Nil))
                && decl.bindings.iter().all(|local| {
                    seeds.contains(local)
                        && proto.local_debug_hints[local.index()].is_none()
                        && proto.local_debug_scopes[local.index()].is_none()
                }))
            .then_some(decl.bindings.as_slice())
        })
        .flatten()
        .copied()
        .collect::<BTreeSet<_>>();
    let mut consumed = vec![None; stmt_count];
    let mut retained = BTreeSet::new();
    for (owner, plan) in plans.iter().enumerate() {
        retained.insert(plan.sink);
        retained.extend(plan.retained_copies.iter().map(|(index, _)| *index));
        for &index in &plan.removed {
            consumed[index] = Some(owner);
        }
    }
    let mut obligations = BTreeMap::<usize, BTreeSet<LocalId>>::new();
    let mut accepted_holders = BTreeSet::new();
    let mut owners = BTreeMap::<LocalId, Option<usize>>::new();
    let mut declarations = Vec::new();
    let mut declaration_counts = BTreeMap::<LocalId, usize>::new();
    let mut holder_writes = BTreeMap::<LocalId, Vec<usize>>::new();
    let mut retirement_statements = BTreeMap::<LocalId, BTreeSet<usize>>::new();
    let mut handoff_statements = BTreeMap::<LocalId, Vec<usize>>::new();
    let mut pending_handoff = None;
    let mut unexpected_holders = BTreeSet::new();
    prefix::coordinates::visit(&proto.body, &mut 0, &mut |index, kind, stmt| {
        if kind != PointKind::Statement {
            pending_handoff = None;
            return;
        }
        if let Some((previous, holder, source)) = pending_handoff.take()
            && index == previous + 1
            && matches!(stmt, HirStmt::LocalRootRelease(local) if *local == source)
        {
            handoff_statements
                .entry(holder)
                .or_default()
                .extend([previous, index]);
        }
        if let HirStmt::Assign(assign) = stmt
            && assign.root_release.is_none()
            && let [HirLValue::Local(holder)] = assign.targets.as_slice()
            && let Some(&source) = handoffs.get(holder)
            && assign.values.tail.is_none()
            && assign.values.fixed.as_slice() == [HirExpr::LocalRef(source)]
        {
            pending_handoff = Some((index, *holder, source));
        }
        // holder 只能承担已有的交接与退休，不能借当前形状消费另一个用途的身份。
        let mut mentions = (
            BindingReadCollector(|binding| {
                if let HirBinding::Local(local) = binding
                    && handoffs.contains_key(&local)
                {
                    unexpected_holders.insert(local);
                }
            }),
            BindingWriteCollector(|binding| {
                if let HirBinding::Local(local) = binding
                    && handoffs.contains_key(&local)
                {
                    holder_writes.entry(local).or_default().push(index);
                }
            }),
        );
        crate::hir::visit::visit_stmt_header(stmt, &mut mentions);
        if let HirStmt::LocalDecl(decl) = stmt {
            for local in &decl.bindings {
                if root_bindings.contains(local) {
                    *declaration_counts.entry(*local).or_default() += 1;
                }
            }
        }
        if let HirStmt::LocalDecl(decl) = stmt
            && decl
                .bindings
                .iter()
                .all(|local| root_bindings.contains(local))
            && !decl.bindings.is_empty()
            && decl.initializer_merge_transaction.is_none()
            && decl.values.tail.is_none()
            && decl.values.fixed.len() == decl.bindings.len()
            && decl
                .values
                .fixed
                .iter()
                .all(|value| matches!(value, HirExpr::Nil))
        {
            declarations.push((index, decl.bindings.clone()));
        }
        let HirStmt::Assign(assign) = stmt else {
            return;
        };
        let Some(crate::hir::common::HirRootRelease::CopyOverwrite { released, .. }) =
            &assign.root_release
        else {
            return;
        };
        for temp in released {
            let Some(local) = facts
                .promoted_local_for_temp(*temp)
                .filter(|local| seeds.contains(local))
            else {
                continue;
            };
            retirement_statements
                .entry(local)
                .or_default()
                .insert(index);
            let owner = consumed[index];
            if handoffs.contains_key(&local)
                && let Some(owner) = owner
            {
                obligations.entry(owner).or_default().insert(local);
            }
            owners
                .entry(local)
                .and_modify(|current| {
                    if *current != owner {
                        *current = None;
                    }
                })
                .or_insert(owner);
        }
    });
    for (declaration, bindings) in declarations {
        if consumed[declaration].is_some()
            || retained.contains(&declaration)
            || bindings
                .iter()
                .any(|local| declaration_counts.get(local) != Some(&1))
        {
            // 候选拒绝[ProofIncomplete]：seed 必须仍是该身份唯一、尚未被其它帧认领的入口声明。
            continue;
        }
        let Some(Some(owner)) = owners.get(&bindings[0]).copied() else {
            continue;
        };
        if !bindings
            .iter()
            .all(|local| owners.get(local) == Some(&Some(owner)))
        {
            // 候选拒绝[ProofIncomplete]：一个声明组的所有退休须由同一完整帧消费，
            // 不把尚未原子化的跨事务依赖藏进可单独撤回的计划。
            continue;
        }
        if bindings.iter().any(|local| {
            handoffs.contains_key(local)
                && (unexpected_holders.contains(local)
                    || handoff_statements
                        .get(local)
                        .is_none_or(|statements| statements.len() != 2)
                    || handoff_statements[local]
                        .iter()
                        .any(|&index| consumed[index].is_some() || retained.contains(&index))
                    || holder_writes.get(local).is_some_and(|writes| {
                        writes.iter().any(|index| {
                            *index != declaration
                                && !handoff_statements[local].contains(index)
                                && !retirement_statements[local].contains(index)
                        })
                    }))
        }) {
            // 候选拒绝[ProofIncomplete]：词法 holder 的唯一交接及紧邻清槽必须仍完整可消费。
            continue;
        }
        for local in &bindings {
            if let Some(statements) = handoff_statements.get(local) {
                accepted_holders.insert(*local);
                plans[owner].removed.extend(statements);
                // 原 COPY 槽继续保活，由已签证的覆盖帧接替 scope 末端的合成清槽。
                // 仅此事务的 release 可以不退休 source binding；其它清槽仍走普通预览。
                plans[owner].replayed_effects.push(statements[1]);
            }
        }
        // 候选接受[BindingIdentityProof]：只有 lowering 的合成 nil 可以随退休事务
        // 消费。preview 仍须在原 COPY 处恢复声明，并验证所有读取、后缀帧与回边布局；
        // 任一失败会连同入口初始化一起撤回，不提前删除保活责任。
        plans[owner].removed.push(declaration);
    }
    let mut owner = 0;
    plans.retain(|_| {
        // 候选拒绝[ProofIncomplete]：builder 只认领了原覆盖，holder 的入口和
        // 作用域交接尚未获证时必须撤回整个帧，不能单独删除 nil 退休。
        let keep = obligations
            .get(&owner)
            .is_none_or(|roots| roots.is_subset(&accepted_holders));
        owner += 1;
        keep
    });
}
