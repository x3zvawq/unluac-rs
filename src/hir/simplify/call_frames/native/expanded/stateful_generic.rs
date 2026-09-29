//! 配对常量真分支展开的状态查找循环与低槽结果 COPY。
//! 模板、原查表/迭代帧及当前绑定共同签证，提交仍由完整后缀前缀验证负责。

use super::*;
use crate::hir::common::{
    HirBinaryOpKind, HirOperationSources, HirTableAccess, HirUnaryOpKind, ParamId,
};

fn negated_lookup(expr: &HirExpr) -> Option<&HirTableAccess> {
    let HirExpr::Unary(not) = expr else {
        return None;
    };
    if not.op != HirUnaryOpKind::Not || not.source_site.is_some() {
        return None;
    }
    let HirExpr::TableAccess(access) = &not.expr else {
        return None;
    };
    Some(access)
}

fn iteration(stmt: &HirStmt, iterator: &HirExpr, facts: &ProtoPromotionFacts, base: usize) -> bool {
    let HirStmt::GenericFor(for_) = stmt else {
        return false;
    };
    let Some(frame) = facts.generic_for_body_frame(for_) else {
        return false;
    };
    for_.iterator.fixed.as_slice() == std::slice::from_ref(iterator)
        && for_.iterator.tail.is_none()
        && for_.bindings.len() == 2
        && matches!(for_.body.stmts.as_slice(), [HirStmt::Break])
        && frame
            .initializers
            .iter()
            .copied()
            .eq((base..base + 3).map(|slot| HomeSlotKey::new(slot, 0)))
        && frame.controls == frame.initializers
        && frame
            .bindings
            .iter()
            .copied()
            .eq((base + 3..base + 5).map(|slot| HomeSlotKey::new(slot, 0)))
        && frame.binding_padding == 0
}

pub(super) fn body_key(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
) -> Option<(HirLuauInliningBody, crate::LuaString)> {
    if proto.params.len() != 4
        || proto.signature.is_vararg
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [
        first @ HirStmt::LocalDecl(_),
        HirStmt::While(loop_),
        HirStmt::Return(ret),
    ] = proto.body.stmts.as_slice()
    else {
        return None;
    };

    let (state, initial) = scalar_local(first)?;
    let initial = repeat_prefix::integer(initial)?;
    let condition = negated_lookup(&loop_.cond)?;
    let HirExpr::String(field) = &condition.key else {
        return None;
    };
    let [HirStmt::If(branch)] = loop_.body.stmts.as_slice() else {
        return None;
    };
    let [HirStmt::If(probe)] = branch.then_block.stmts.as_slice() else {
        return None;
    };
    let lookup = negated_lookup(&probe.cond)?;
    let [for_] = probe.then_block.stmts.as_slice() else {
        return None;
    };
    let [update] = branch.else_block.as_ref()?.stmts.as_slice() else {
        return None;
    };
    let (target, HirExpr::Binary(add)) = scalar_local(update)? else {
        return None;
    };
    let increment = repeat_prefix::integer(&add.rhs)?;

    if facts.trusted_local_home_slot(state) != Some(HomeSlotKey::new(4, 0))
        || !lookup_layout(
            condition,
            facts,
            HomeSlotKey::new(1, 0),
            None,
            HomeSlotKey::new(5, 0),
        )
        || !lookup_layout(
            lookup,
            facts,
            HomeSlotKey::new(2, 0),
            Some(HomeSlotKey::new(4, 0)),
            HomeSlotKey::new(5, 0),
        )
        || condition.base != HirExpr::ParamRef(ParamId(1))
        || branch.cond != HirExpr::ParamRef(ParamId(0))
        || lookup.base != HirExpr::ParamRef(ParamId(2))
        || lookup.key != HirExpr::LocalRef(state)
        || probe.else_block.is_some()
        || !iteration(for_, &HirExpr::ParamRef(ParamId(3)), facts, 5)
        || target != state
        || add.op != HirBinaryOpKind::Add
        || add.lhs != HirExpr::LocalRef(state)
        || !repeat_prefix::update_layout(add, facts, HomeSlotKey::new(4, 0))
        || ret.values.fixed.as_slice() != [HirExpr::LocalRef(state)]
        || ret.values.tail.is_some()
        || i16::try_from(initial).is_err()
        || i16::try_from(increment).is_err()
    {
        return None;
    }
    Some((
        HirLuauInliningBody::StatefulGenericWhile {
            template: proto.id.index(),
            initial,
            increment,
        },
        field.clone(),
    ))
}

fn lookup_layout(
    access: &HirTableAccess,
    facts: &ProtoPromotionFacts,
    base: HomeSlotKey,
    key: Option<HomeSlotKey>,
    result: HomeSlotKey,
) -> bool {
    facts
        .native_table_read_layout(access)
        .is_some_and(|layout| layout.base == base && layout.key == key)
        && facts.table_read_result_home(access) == Some(result)
        && matches!(access.sources, HirOperationSources::Single(source) if facts.operation_result_reference_unaliased(source))
}

pub(super) fn plans(context: NativeFrameContext<'_>, facts: &ProtoPromotionFacts) -> Vec<Plan> {
    let Some(callees) = context.expanded_callees else {
        return Vec::new();
    };
    let mut templates = BTreeMap::new();
    for callee in callees.values() {
        if let HirLuauInliningBody::StatefulGenericWhile { initial, .. } = callee.body {
            templates
                .entry((callee.field.clone(), initial))
                .and_modify(|old| *old = None)
                .or_insert(Some(callee));
        }
    }

    if templates.is_empty() {
        return Vec::new();
    }
    let mut reads = BTreeMap::new();
    let mut writes = BTreeMap::new();
    let mut collectors = (
        CaptureCollector::new(HirCaptureMode::ByReference),
        (
            BindingReadCollector(|binding| {
                if let HirBinding::Local(local) = binding {
                    *reads.entry(local).or_insert(0) += 1;
                }
            }),
            BindingWriteCollector(|binding| {
                if let HirBinding::Local(local) = binding {
                    *writes.entry(local).or_insert(0) += 1;
                }
            }),
        ),
    );
    visit_stmts(&context.proto.body.stmts, &mut collectors);
    let (reference_captures, _) = collectors;
    let mut plans = Vec::new();
    for (start, window) in context.proto.body.stmts.windows(4).enumerate() {
        let paired = (|| {
            let [
                table_stmt @ HirStmt::LocalDecl(_),
                state_stmt @ HirStmt::LocalDecl(_),
                HirStmt::While(loop_),
                last @ HirStmt::LocalDecl(_),
            ] = window
            else {
                return None;
            };
            let (table_local, HirExpr::TableConstructor(table)) = scalar_local(table_stmt)? else {
                return None;
            };
            let (state, initial_expr) = scalar_local(state_stmt)?;
            let initial = repeat_prefix::integer(initial_expr)?;
            let (result, returned) = scalar_local(last)?;
            let condition = negated_lookup(&loop_.cond)?;
            let (HirExpr::LocalRef(argument), HirExpr::String(field)) =
                (&condition.base, &condition.key)
            else {
                return None;
            };
            let callee = templates.get(&(field.clone(), initial))?.as_ref()?;
            let [HirStmt::If(branch)] = loop_.body.stmts.as_slice() else {
                return None;
            };
            let lookup = negated_lookup(&branch.cond)?;
            let [for_stmt @ HirStmt::GenericFor(for_)] = branch.then_block.stmts.as_slice() else {
                return None;
            };
            let [HirExpr::LocalRef(iterator)] = for_.iterator.fixed.as_slice() else {
                return None;
            };
            let base = facts.trusted_local_home_slot(result)?;
            let table_home = HomeSlotKey::new(base.slot() + 1, 0);
            let state_home = HomeSlotKey::new(base.slot() + 2, 0);
            let scratch = HomeSlotKey::new(base.slot() + 3, 0);
            let argument_home = facts.trusted_local_home_slot(*argument)?;
            let iterator_home = facts.trusted_local_home_slot(*iterator)?;

            let (state_temp, key_home) = facts.table_read_key_value(lookup)?;

            let copy = facts.value_result_copy(state_temp)?;
            let HirOperationSources::Single(source) = table.sources else {
                return None;
            };

            if start <= callee.declaration || base != HomeSlotKey::new(base.slot(), 0)
                || !table.fields.is_empty() || table.trailing_multivalue.is_some() || !table.matches_allocation_capacity(0)
                || !matches!(table.allocation, crate::hir::HirTableAllocation::Luau(_))
                || facts.allocation_result_home(table) != Some(table_home)
                || facts.trusted_local_home_slot(table_local) != Some(table_home)
                || facts.trusted_local_home_slot(state) != Some(state_home)
                || key_home != state_home || facts.promoted_local_for_temp(state_temp) != Some(state)
                || copy.source != Some(state_temp) || copy.source_home != state_home || copy.target_home != base
                || facts.promoted_local_for_temp(copy.target) != Some(result)
                || *returned != HirExpr::LocalRef(state)
                || branch.else_block.is_some() || lookup.base != HirExpr::LocalRef(table_local)
                || lookup.key != HirExpr::LocalRef(state)
                || !lookup_layout(condition, facts, argument_home, None, scratch)
                || !lookup_layout(lookup, facts, table_home, Some(state_home), scratch)
                || !iteration(for_stmt, &HirExpr::LocalRef(*iterator), facts, scratch.slot())
                || reads.get(&state) != Some(&2) || writes.get(&state) != Some(&1)
                || [*argument, *iterator].iter().any(|local| writes.get(local) != Some(&1) || reference_captures.bindings.locals.contains(local) || !facts.local_definitions_reference_unaliased(*local))
                || argument_home.slot() >= base.slot() || iterator_home.slot() >= base.slot()
                // 低槽只读实参保持原绑定；状态读计数包含 capture，两个原读取之外不得逃逸。
                || !facts.temp_definition_reference_unaliased(state_temp)
                || [base, table_home].iter().any(|home| context.barred.contains(home))
                || [base, table_home, state_home, argument_home, iterator_home].iter().any(|home| context.closed.contains(home))
                // 候选拒绝[ProofIncomplete:Scope]：匿名输入区才有当前完整的参数替换证书。
                || [table_local, state, result].iter().any(|local| context.proto.local_debug_scopes[local.index()].is_some() || context.proto.local_debug_hints[local.index()].is_some())
            {
                return None;
            }
            let mut plan = factories::invocation(callee, source, base, result, start, start + 3);
            plan.values = vec![factories::factory_call(
                callee.local,
                Some(source),
                vec![
                    HirExpr::Boolean(true),
                    HirExpr::LocalRef(*argument),
                    HirExpr::TableConstructor(table.clone()),
                    HirExpr::LocalRef(*iterator),
                ]
                .into(),
            )]
            .into();
            plan.replayed_effects.push(start + 2);
            Some(plan)
        })();
        plans.extend(paired);
    }
    plans
}
