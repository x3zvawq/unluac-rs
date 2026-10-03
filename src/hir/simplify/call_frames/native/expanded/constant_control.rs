//! 将常量控制选出的完整状态轨迹恢复为必须重新内联的调用。
//! 原输入分配、初始化、算术写回和低槽 COPY 一起配对，后缀身份由 native 事务验证。

use super::super::assignments::plain_copy;
use super::*;
use crate::hir::luau_inlining::constant_control::{Action, Template};
use crate::hir::luau_inlining::small_integer;

pub(in crate::hir::simplify::call_frames) struct Frames<'a> {
    indexed: BTreeMap<(Vec<Action>, usize), Option<Specialization<'a>>>,
    copies: BTreeMap<TempId, Option<crate::hir::promotion::ImmediateMoveWrite>>,
}

#[derive(Clone, Copy)]
struct Specialization<'a> {
    callee: &'a Callee,
    mask: u8,
}

pub(super) fn frames<'a>(
    callees: &'a Callees,
    facts: &ProtoPromotionFacts,
    templates: &[Option<Template>],
) -> Frames<'a> {
    let mut indexed = BTreeMap::new();
    for callee in callees.values() {
        if let HirLuauInliningBody::ConstantControl { template, .. } = callee.body
            && let Some(body) = &templates[template]
        {
            for (trace, &mask) in &body.traces {
                // 调用帧只接收一个结果，但函数可以声明多个返回值；完整操作轨迹
                // 仍保留其它状态的初始化和更新，源码的固定单值语境负责截断返回。
                indexed
                    .entry((trace.actions.clone(), trace.returned[0]))
                    .and_modify(|known: &mut Option<Specialization<'a>>| {
                        if known
                            .as_ref()
                            .is_some_and(|known| known.callee.local != callee.local)
                        {
                            *known = None;
                        }
                    })
                    .or_insert(Some(Specialization { callee, mask }));
            }
        }
    }
    let copies = facts
        .result_copy_frames()
        .fold(BTreeMap::new(), |mut map, copy| {
            map.entry(copy.target)
                .and_modify(|known| *known = None)
                .or_insert(Some(*copy));
            map
        });
    Frames { indexed, copies }
}

pub(super) fn plans(context: NativeFrameContext<'_>, facts: &ProtoPromotionFacts) -> Vec<Plan> {
    let Some(frames) = context.constant_controls else {
        return Vec::new();
    };
    let indexed = &frames.indexed;
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
        let Some(Some(Specialization { callee, mask })) = indexed.get(&(actions, returned)) else {
            continue;
        };
        let HirLuauInliningBody::ConstantControl { parameters, .. } = callee.body else {
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
            .map(|bit| HirExpr::Boolean(*mask & (1 << bit) != 0))
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

impl FrameBuilder<'_> {
    pub(in crate::hir::simplify::call_frames) fn has_constant_control(
        &self,
        result: TempId,
    ) -> bool {
        self.native
            .and_then(|context| context.constant_controls)
            .is_some_and(|frames| {
                !frames.indexed.is_empty()
                    && frames
                        .copies
                        .get(&result)
                        .and_then(Option::as_ref)
                        .is_some_and(|copy| {
                            copy.source_home == HomeSlotKey::new(copy.target_home.slot() + 2, 0)
                        })
            })
    }

    pub(in crate::hir::simplify::call_frames) fn expanded_constant_control(
        &mut self,
        expr: &HirExpr,
        before: usize,
        slot: usize,
        result: TempId,
    ) -> Option<HirExpr> {
        let context = self.native?;
        let frames = context.constant_controls?;
        let copy = frames.copies.get(&result)?.as_ref()?;
        let state_home = HomeSlotKey::new(slot + 2, 0);
        if copy.target_home != HomeSlotKey::new(slot, 0)
            || copy.source_home != state_home
            || !self.facts.temp_definition_is_uncaptured(result)
            || context.proto.temp_debug_locals[result.index()].is_some()
            || context.proto.temp_debug_scopes[result.index()].is_some()
        {
            return None;
        }
        let mut value = expr;
        let mut updates = Vec::new();
        let mut expected = copy.source?;
        while let HirExpr::Binary(binary) = value {
            // 候选搜索裁剪[ResourceLimit]：与函数轨迹共享 256 条操作上限，沿左链单次遍历。
            if updates.len() >= 256 {
                return None;
            }
            let site = binary.source_site?;
            let layout = self.facts.native_binary_layout(binary)?;
            let (input, home) = self
                .facts
                .binary_operand_preparation(binary, 0, &binary.lhs)?;
            if self.facts.operation_result_temp(site) != Some(expected)
                || self.facts.operation_result_home(site) != Some(state_home)
                || layout.lhs != Some(state_home)
                || layout.rhs.is_some()
                || home != state_home
                || !self.facts.operation_result_reference_unaliased(site)
                || !self.facts.temp_definition_is_uncaptured(expected)
                || context.proto.temp_debug_locals[expected.index()].is_some()
                || context.proto.temp_debug_scopes[expected.index()].is_some()
            {
                return None;
            }
            updates.push(Action::Update {
                state: 0,
                op: binary.op,
                value: small_integer(&binary.rhs)?,
            });
            expected = input;
            value = &binary.lhs;
        }
        if updates.is_empty() && self.facts.result_copy_literal(result, value) != Some(expected) {
            return None;
        }
        if !self.facts.temp_definition_is_uncaptured(expected)
            || context.proto.temp_debug_locals[expected.index()].is_some()
            || context.proto.temp_debug_scopes[expected.index()].is_some()
        {
            return None;
        }
        updates.push(Action::Initialize(small_integer(value)?));
        updates.reverse();
        let &Specialization { callee, mask } = frames.indexed.get(&(updates, 0))?.as_ref()?;
        let HirLuauInliningBody::ConstantControl { parameters, .. } = callee.body else {
            return None;
        };
        let at = self.next_event;
        let (binding, HirExpr::TableConstructor(table)) = scalar_binding(self.run.get(at)?)? else {
            return None;
        };
        let crate::hir::common::HirOperationSources::Single(allocation) = table.sources else {
            return None;
        };
        let input = self.facts.operation_result_temp(allocation)?;
        let input_home = HomeSlotKey::new(slot + 1, 0);
        // 候选拒绝[ProofIncomplete:Frame]：消失的调用仍须重放完整空表实参；
        // 事件游标不允许跨过额外写入，参数槽与状态槽共同确定这次展开帧。
        if at >= before
            || !plain_copy(self.run[at])
            || callee.creation.proto != allocation.proto
            || callee.creation.instr >= allocation.instr
            || !table.fields.is_empty()
            || table.trailing_multivalue.is_some()
            || !table.matches_allocation_capacity(0)
            || self.facts.allocation_result_home(table) != Some(input_home)
            || !self.facts.allocation_result_reference_unaliased(table)
            || (slot..=slot + 2).any(|slot| {
                let home = HomeSlotKey::new(slot, 0);
                context.barred.contains(&home) || context.closed.contains(&home)
            })
        {
            return None;
        }
        let argument = match binding {
            HirBinding::Local(local)
                if self.facts.promoted_local_for_temp(input) == Some(local) =>
            {
                HirExpr::LocalRef(local)
            }
            HirBinding::Temp(temp) if temp == input => HirExpr::TempRef(temp),
            _ => return None,
        };
        let argument = self.expr(
            &argument,
            before,
            input_home.slot(),
            None,
            false,
            true,
            Some(input),
        )?;
        let mut args = (0..parameters - 1)
            .map(|bit| HirExpr::Boolean(mask & (1 << bit) != 0))
            .collect::<Vec<_>>();
        args.push(argument);
        Some(factories::factory_call(
            callee.local,
            Some(allocation),
            args.into(),
        ))
    }
}
