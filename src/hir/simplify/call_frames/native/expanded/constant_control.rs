//! 将常量控制选出的完整状态轨迹恢复为必须重新内联的调用。
//! 原输入分配、初始化、算术写回和低槽 COPY 一起配对，后缀身份由 native 事务验证。

use super::super::assignments::plain_copy;
use super::*;
use crate::hir::luau_inlining::constant_control::{Action, Template};
use crate::hir::luau_inlining::small_integer;

pub(super) fn plans(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    templates: &[Option<Template>],
) -> Vec<Plan> {
    let mut indexed = BTreeMap::new();
    for callee in context
        .expanded_callees
        .into_iter()
        .flat_map(|items| items.values())
    {
        if let HirLuauInliningBody::ConstantControl { template, .. } = callee.body
            && let Some(body) = &templates[template]
        {
            indexed
                .entry((body.trace.actions.clone(), body.trace.returned[0]))
                .and_modify(|known| *known = None)
                .or_insert(Some(callee));
        }
    }
    if indexed.is_empty() {
        return Vec::new();
    }
    let copies = facts
        .result_copy_frames()
        .filter_map(|copy| Some((facts.promoted_local_for_temp(copy.target)?, copy)))
        .fold(BTreeMap::new(), |mut map, (local, copy)| {
            map.entry(local)
                .and_modify(|known| *known = None)
                .or_insert(Some(copy));
            map
        });
    let mut plans = Vec::new();
    let mut index = 0;
    let statements = &context.proto.body.stmts;
    while index < statements.len() {
        let start = index;
        index += 1;
        let Some((input, HirExpr::TableConstructor(table))) = scalar_local(&statements[start])
        else {
            continue;
        };
        let crate::hir::common::HirOperationSources::Single(allocation) = table.sources else {
            continue;
        };
        let Some(home) = facts.allocation_result_home(table) else {
            continue;
        };
        let Some(base) = home
            .slot()
            .checked_sub(1)
            .map(|slot| HomeSlotKey::new(slot, 0))
        else {
            continue;
        };
        if home != HomeSlotKey::new(base.slot() + 1, 0)
            || !table.fields.is_empty()
            || table.trailing_multivalue.is_some()
            || !table.matches_allocation_capacity(0)
            || facts.trusted_local_home_slot(input) != Some(home)
            || !facts.allocation_result_reference_unaliased(table)
            || context.proto.local_debug_hints[input.index()].is_some()
            || context.proto.local_debug_scopes[input.index()].is_some()
        {
            continue;
        }
        let mut states = BTreeMap::new();
        let mut actions = Vec::new();
        let mut updates = Vec::new();
        let mut copied = None;
        while let Some(stmt) = statements.get(index) {
            if let Some((target, HirExpr::LocalRef(source))) = scalar_local(stmt)
                && facts.trusted_local_home_slot(target) == Some(base)
            {
                let candidate = (|| {
                    let copy = *copies.get(&target)?.as_ref()?;
                    let state = *states.get(&HirBinding::Local(*source))?;
                    if !matches!(stmt, HirStmt::LocalDecl(_))
                        || copy.target_home != base
                        || facts.promoted_local_for_temp(copy.source?) != Some(*source)
                        || facts.trusted_local_home_slot(*source) != Some(copy.source_home)
                        || context.proto.local_debug_hints[target.index()].is_some()
                        || context.proto.local_debug_scopes[target.index()].is_some()
                    {
                        return None;
                    }
                    Some((target, state))
                })();
                copied = candidate;
                break;
            }
            let next_home = HomeSlotKey::new(home.slot() + 1 + states.len(), 0);
            if let Some((binding, value)) = super::super::super::scalar_binding(stmt)
                && let Some(value) = small_integer(value)
            {
                let valid = match binding {
                    HirBinding::Local(local) => {
                        matches!(stmt, HirStmt::LocalDecl(_))
                            && facts.trusted_local_home_slot(local) == Some(next_home)
                            && context.proto.local_debug_hints[local.index()].is_none()
                            && context.proto.local_debug_scopes[local.index()].is_none()
                    }
                    HirBinding::Temp(temp) => {
                        facts.trusted_temp_home_slot(temp) == Some(next_home)
                            && facts.unread_literal_initializer(temp).is_some()
                            && facts.temp_definition_reference_unaliased(temp)
                            && context.proto.temp_debug_locals[temp.index()].is_none()
                            && context.proto.temp_debug_scopes[temp.index()].is_none()
                    }
                    _ => false,
                };
                if !valid || !plain_copy(stmt) || states.contains_key(&binding) {
                    break;
                }
                states.insert(binding, states.len());
                actions.push(Action::Initialize(value));
                index += 1;
                continue;
            }
            let update = (|| {
                let (local, HirExpr::Binary(binary)) = scalar_local(stmt)? else {
                    return None;
                };
                let state = *states.get(&HirBinding::Local(local))?;
                let output = HomeSlotKey::new(home.slot() + 1 + state, 0);
                if !plain_copy(stmt)
                    || !matches!(stmt, HirStmt::Assign(_))
                    || binary.lhs != HirExpr::LocalRef(local)
                    || !repeat_prefix::update_layout(binary, facts, output)
                    || facts.trusted_local_home_slot(local) != Some(output)
                {
                    return None;
                }
                Some(Action::Update {
                    state,
                    op: binary.op,
                    value: small_integer(&binary.rhs)?,
                })
            })();
            let Some(update) = update else { break };
            actions.push(update);
            updates.push(index);
            index += 1;
        }
        let Some((result, returned)) = copied else {
            continue;
        };
        let Some(Some(callee)) = indexed.get(&(actions, returned)) else {
            continue;
        };
        let HirLuauInliningBody::ConstantControl {
            parameters,
            truth_mask,
            ..
        } = callee.body
        else {
            unreachable!()
        };
        // 候选拒绝[ProofIncomplete:Frame]：整段须属于同一闭包之后的匿名高槽准备，
        // 不借当前常量值跨过原观察、capture 或未匹配操作。
        if start <= callee.declaration
            || allocation.proto != callee.creation.proto
            || (base.slot()..home.slot() + 1 + states.len()).any(|slot| {
                let home = HomeSlotKey::new(slot, 0);
                context.barred.contains(&home) || context.closed.contains(&home)
            })
        {
            continue;
        }
        let mut args = (0..parameters - 1)
            .map(|bit| HirExpr::Boolean(truth_mask & (1 << bit) != 0))
            .collect::<Vec<_>>();
        args.push(HirExpr::TableConstructor(table.clone()));
        let mut plan = factories::invocation(callee, allocation, base, result, start, index);
        plan.values = vec![factories::factory_call(
            callee.local,
            Some(allocation),
            args.into(),
        )]
        .into();
        plan.replayed_effects = updates;
        plans.push(plan);
        index += 1;
    }
    plans
}
