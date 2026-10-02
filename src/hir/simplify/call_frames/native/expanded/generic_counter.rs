//! 将常量短路参数展开的 generic-for 计数帧接回现存函数。
//! 逐项核对循环模板、原迭代槽及低槽返回，完整观察调用与后缀仍由共享前缀事务提交。

use super::repeat_prefix::{integer, observation, update_layout};
use super::*;
use crate::hir::common::{HirBinaryExpr, HirBinaryOpKind, HirGenericFor, ParamId};

fn add(stmt: &HirStmt, state: LocalId) -> Option<&HirBinaryExpr> {
    let (target, HirExpr::Binary(add)) = scalar_local(stmt)? else {
        return None;
    };
    (target == state && add.op == HirBinaryOpKind::Add && add.lhs == HirExpr::LocalRef(state))
        .then_some(add)
}

fn iteration(
    for_: &HirGenericFor,
    input: &HirExpr,
    facts: &ProtoPromotionFacts,
    base: usize,
) -> bool {
    let Some(frame) = facts.generic_for_body_frame(for_) else {
        return false;
    };
    for_.iterator.fixed.as_slice() == std::slice::from_ref(input)
        && for_.iterator.tail.is_none()
        && for_.bindings.len() == 2
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

fn and_parameters(expr: &HirExpr) -> bool {
    matches!(expr, HirExpr::LogicalAnd(and) if and.lhs == HirExpr::ParamRef(ParamId(0)) && and.rhs == HirExpr::ParamRef(ParamId(1)))
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
    let [first, HirStmt::GenericFor(for_), HirStmt::Return(ret)] = proto.body.stmts.as_slice()
    else {
        return None;
    };
    let (state, initial) = scalar_local(first)?;
    let initial = integer(initial)?;
    let home = HomeSlotKey::new(4, 0);
    let [HirStmt::If(branch), tail] = for_.body.stmts.as_slice() else {
        return None;
    };
    let increment = integer(&add(tail, state)?.rhs)?;
    let valid_add = |stmt: &HirStmt| {
        add(stmt, state).is_some_and(|add| {
            integer(&add.rhs) == Some(increment) && update_layout(add, facts, home)
        })
    };
    if facts.trusted_local_home_slot(state) != Some(home)
        || !iteration(for_, &HirExpr::ParamRef(ParamId(3)), facts, 5)
        || branch.cond != HirExpr::ParamRef(ParamId(0))
        || !valid_add(tail)
        || ret.values.fixed.as_slice() != [HirExpr::LocalRef(state)]
        || ret.values.tail.is_some()
        || ret.pending_cleanup_source.is_some()
        || i16::try_from(initial).is_err()
        || i16::try_from(increment).is_err()
    {
        return None;
    }
    let (steps, remainder) = branch.then_block.stmts.as_chunks::<2>();
    if steps.is_empty() || !remainder.is_empty() {
        return None;
    }
    for [update, repeat] in steps {
        let HirStmt::Repeat(repeat) = repeat else {
            return None;
        };
        if !valid_add(update)
            || repeat.cond != HirExpr::ParamRef(ParamId(1))
            || !matches!(repeat.body.stmts.as_slice(), [update] if valid_add(update))
        {
            return None;
        }
    }
    let [HirStmt::If(skip), HirStmt::If(update), HirStmt::If(stop)] =
        branch.else_block.as_ref()?.stmts.as_slice()
    else {
        return None;
    };
    let HirExpr::LogicalAnd(condition) = &skip.cond else {
        return None;
    };
    let (left, left_not) = synthetic_not_subject(&condition.lhs);
    let (right, right_not) = synthetic_not_subject(&condition.rhs);
    let [call, HirStmt::If(exit)] = stop.then_block.stmts.as_slice() else {
        return None;
    };
    let HirExpr::TableAccess(lookup) = &exit.cond else {
        return None;
    };
    if left != &HirExpr::ParamRef(ParamId(0))
        || right != &HirExpr::ParamRef(ParamId(2))
        || left_not != 1
        || right_not != 1
        || skip.else_block.is_some()
        || !matches!(skip.then_block.stmts.as_slice(), [step, HirStmt::Continue] if valid_add(step))
        || !and_parameters(&update.cond)
        || update.else_block.is_some()
        || !matches!(update.then_block.stmts.as_slice(), [step] if valid_add(step))
        || !and_parameters(&stop.cond)
        || stop.else_block.is_some()
        || observation(call, state).is_none()
        || lookup.base != HirExpr::ParamRef(ParamId(3))
        || lookup.key != HirExpr::LocalRef(state)
        || exit.else_block.is_some()
        || !matches!(exit.then_block.stmts.as_slice(), [HirStmt::Break])
    {
        return None;
    }
    Some((
        HirLuauInliningBody::GenericCounter {
            template: proto.id.index(),
            initial,
            increment,
            repeats: steps.len(),
        },
        "".into(),
    ))
}

pub(super) fn plans(context: NativeFrameContext<'_>, facts: &ProtoPromotionFacts) -> Vec<Plan> {
    let mut templates = BTreeMap::new();
    for callee in context
        .expanded_callees
        .into_iter()
        .flat_map(|items| items.values())
    {
        if let HirLuauInliningBody::GenericCounter {
            initial, increment, ..
        } = callee.body
        {
            templates
                .entry((initial, increment))
                .and_modify(|entry| *entry = None)
                .or_insert(Some(callee));
        }
    }
    if templates.is_empty() {
        return Vec::new();
    }
    let mut plans = Vec::new();
    for (sink, stmt) in context.proto.body.stmts.iter().enumerate() {
        let candidate = (|| {
            let HirStmt::CallStmt(statement) = stmt else {
                return None;
            };
            let call = &statement.call;
            let frame = facts.native_call_frame(call)?;
            let count = call.args.fixed.len().checked_sub(1)?;
            if count == 0
                || call.args.tail.is_some()
                || frame.results != Some(ResultPack::Ignore)
                || !frame.arguments_unaliased
                || call.fastcall.is_some()
            {
                return None;
            }
            let start = sink.checked_sub(count.checked_mul(4)?.checked_add(2)?)?;
            let stmts = &context.proto.body.stmts;
            let prefix = [&stmts[start], &stmts[start + 1]];
            let mut builder = frame_builder(
                context,
                &prefix,
                facts,
                DecompileDialect::Luau,
                frame.home.slot(),
            )?;
            let callee = builder.expr(
                &call.callee,
                prefix.len(),
                frame.home.slot(),
                None,
                true,
                false,
                Some(frame.callee),
            )?;
            if !matches!(&callee, HirExpr::GlobalRef(name) if name.key.as_utf8() == Some("print")) {
                return None;
            }
            let label = builder.expr(
                &call.args.fixed[0],
                prefix.len(),
                frame.home.slot() + 1,
                None,
                false,
                true,
                facts.call_argument_value(call, 0),
            )?;
            if !matches!(label, HirExpr::String(_))
                || builder.first_event != Some(0)
                || builder.next_event != prefix.len()
            {
                return None;
            }
            let mut args = vec![label];
            let mut replayed = Vec::new();
            for (offset, chunk) in stmts[start + 2..sink].as_chunks::<4>().0.iter().enumerate() {
                let (input, table @ HirExpr::TableConstructor(constructor)) =
                    scalar_local(&chunk[0])?
                else {
                    return None;
                };
                let (state, initial) = scalar_local(&chunk[1])?;
                let HirStmt::GenericFor(for_) = &chunk[2] else {
                    return None;
                };
                let [update] = for_.body.stmts.as_slice() else {
                    return None;
                };
                let update = add(update, state)?;
                let (result, returned) = scalar_local(&chunk[3])?;
                let callee = *templates
                    .get(&(integer(initial)?, integer(&update.rhs)?))?
                    .as_ref()?;
                let base = HomeSlotKey::new(frame.home.slot() + 2 + offset, 0);
                let input_home = HomeSlotKey::new(base.slot() + 1, 0);
                let state_home = HomeSlotKey::new(base.slot() + 2, 0);
                if start <= callee.declaration
                    || returned != &HirExpr::LocalRef(state)
                    || call.args.fixed[offset + 1] != HirExpr::LocalRef(result)
                    || facts.trusted_local_home_slot(result) != Some(base)
                    || facts.trusted_local_home_slot(input) != Some(input_home)
                    || facts.trusted_local_home_slot(state) != Some(state_home)
                    || facts.allocation_result_home(constructor) != Some(input_home)
                    || !facts.allocation_result_reference_unaliased(constructor)
                    || !update_layout(update, facts, state_home)
                    || !iteration(for_, &HirExpr::LocalRef(input), facts, base.slot() + 3)
                    || [input, state, result].iter().any(|local| {
                        context.proto.local_debug_hints[local.index()].is_some()
                            || context.proto.local_debug_scopes[local.index()].is_some()
                    })
                    || (base.slot()..base.slot() + 8).any(|slot| {
                        let home = HomeSlotKey::new(slot, 0);
                        context.barred.contains(&home) || context.closed.contains(&home)
                    })
                {
                    return None;
                }
                let mut builder =
                    frame_builder(context, &[], facts, DecompileDialect::Luau, base.slot())?;
                let argument =
                    builder.expr(table, 0, input_home.slot(), None, false, true, None)?;
                args.push(factories::factory_call(
                    callee.local,
                    Some(update.source_site?),
                    vec![
                        HirExpr::Boolean(false),
                        HirExpr::Boolean(true),
                        HirExpr::Boolean(false),
                        argument,
                    ]
                    .into(),
                ));
                replayed.push(start + 2 + offset * 4 + 2);
            }
            let mut restored = call.clone();
            restored.callee = callee;
            restored.args = args.into();
            Some(Plan {
                prefix_at_sink: false,
                luau_function_declaration: false,
                start,
                sink,
                base: frame.home,
                values: vec![HirExpr::Call(Box::new(restored))].into(),
                result_locals: Vec::new(),
                assignment_targets: Vec::new(),
                luau_compound_global: false,
                indexed_target: None,
                continuing_root: None,
                retained_copies: Vec::new(),
                replayed_effects: replayed,
                removed: (start..sink).collect(),
            })
        })();
        plans.extend(candidate);
    }
    plans
}
