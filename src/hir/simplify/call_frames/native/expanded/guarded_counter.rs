//! 恢复条件计数循环的成组结果声明。
//! 原更新、观察、比较、返回 COPY 及共同 scratch 起点一起签证，后缀仍由整批源码帧验证。

use super::super::assignments::plain_copy;
use super::*;
use crate::hir::common::{HirBinaryExpr, HirBinaryOpKind, HirSourceSite};
use crate::hir::luau_inlining::{CounterLoopKind, GuardedCounterTemplate, small_integer};

pub(super) struct Recovered {
    pub plans: Vec<Plan>,
    pub result_slots: BTreeMap<HirSourceSite, usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Profile {
    kind: CounterLoopKind,
    decrement: i64,
    bound: i64,
    stop: Option<i64>,
    label: Option<crate::LuaString>,
}

fn initializer(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::Assign(assign) => {
            // 循环入口的 phi transfer 仍是同槽初值写入，整个循环随之原样重放；
            // 不借此删除跨槽 transfer 或其它尚未消费的事务。
            assign.initializer_merge_transaction.is_none()
                && assign.generic_for_initializer_producer.is_none()
                && assign.root_release.is_none()
                && assign.method_rewrite_transaction.is_none()
                && assign.parallel_nil_frame.is_none()
        }
        other => plain_copy(other),
    }
}

fn compare(
    expr: &HirExpr,
    op: HirBinaryOpKind,
    state: LocalId,
    facts: &ProtoPromotionFacts,
) -> Option<i64> {
    let HirExpr::Binary(binary) = expr else {
        return None;
    };
    let home = facts.trusted_local_home_slot(state)?;
    let layout = facts.native_binary_layout(binary)?;
    if binary.op != op
        || binary.lhs != HirExpr::LocalRef(state)
        || layout.lhs != Some(home)
        || facts.direct_binary_operand_home(binary, 0) != Some(home)
    {
        return None;
    }
    if let Some(rhs) = layout.rhs
        && (rhs != HomeSlotKey::new(home.slot() + 1, 0)
            || facts.binary_operand_preparation(binary, 1, &binary.rhs)?.1 != rhs)
    {
        return None;
    }
    small_integer(&binary.rhs)
}

fn observation(
    stmt: &HirStmt,
    state: LocalId,
    facts: &ProtoPromotionFacts,
    context: NativeFrameContext<'_>,
    producer: HirSourceSite,
) -> Option<crate::LuaString> {
    let HirStmt::CallStmt(statement) = stmt else {
        return None;
    };
    let call = &statement.call;
    let [HirExpr::String(label), value] = call.args.fixed.as_slice() else {
        return None;
    };
    let home = facts.trusted_local_home_slot(state)?;
    let frame = facts.native_call_frame(call)?;
    if *value != HirExpr::LocalRef(state)
        || call.args.tail.is_some()
        || call.fastcall.is_some()
        || call.is_method()
        || !matches!(&call.callee,HirExpr::GlobalRef(global) if global.key.as_utf8()==Some("print"))
        || frame.home != HomeSlotKey::new(home.slot() + 1, 0)
        || frame.results != Some(ResultPack::Ignore)
        || !frame.arguments_unaliased
        || facts
            .call_state_writeback_copy(call, 1, producer)
            .is_none_or(|copy| {
                copy.source_home != home || copy.target_home != HomeSlotKey::new(home.slot() + 3, 0)
            })
    {
        return None;
    }
    let mut builder = frame_builder(context, &[], facts, DecompileDialect::Luau, home.slot() + 1)?;
    builder.call(call, 0, home.slot() + 1, false, CallWidth::Ignore)?;
    Some(label.clone())
}

fn profile<'a>(
    stmt: &'a HirStmt,
    state: LocalId,
    facts: &ProtoPromotionFacts,
    context: NativeFrameContext<'_>,
) -> Option<(Profile, &'a HirBinaryExpr)> {
    let (kind, condition, body) = match stmt {
        HirStmt::While(loop_) => (CounterLoopKind::While, &loop_.cond, &loop_.body),
        HirStmt::Repeat(loop_) => (CounterLoopKind::Repeat, &loop_.cond, &loop_.body),
        _ => return None,
    };
    let (update, rest) = body.stmts.split_first()?;
    let (target, HirExpr::Binary(binary)) = scalar_local(update)? else {
        return None;
    };
    let home = facts.trusted_local_home_slot(state)?;
    if target != state
        || binary.op != HirBinaryOpKind::Sub
        || binary.lhs != HirExpr::LocalRef(state)
        || !repeat_prefix::update_layout(binary, facts, home)
    {
        return None;
    }
    let (label, rest) = if rest
        .first()
        .is_some_and(|stmt| matches!(stmt, HirStmt::CallStmt(_)))
    {
        (
            Some(observation(
                &rest[0],
                state,
                facts,
                context,
                binary.source_site?,
            )?),
            &rest[1..],
        )
    } else {
        (None, rest)
    };
    let (bound, stop) = match kind {
        CounterLoopKind::While => {
            let bound = compare(condition, HirBinaryOpKind::Gt, state, facts)?;
            let stop = match rest {
                [] => None,
                [HirStmt::If(exit)]
                    if matches!(exit.then_block.stmts.as_slice(), [HirStmt::Break])
                        && exit
                            .else_block
                            .as_ref()
                            .is_none_or(|other| other.stmts.is_empty()) =>
                {
                    Some(compare(&exit.cond, HirBinaryOpKind::Eq, state, facts)?)
                }
                _ => return None,
            };
            (bound, stop)
        }
        CounterLoopKind::Repeat => {
            if !rest.is_empty() {
                return None;
            }
            if let HirExpr::LogicalOr(condition) = condition {
                (
                    compare(&condition.rhs, HirBinaryOpKind::Le, state, facts)?,
                    Some(compare(&condition.lhs, HirBinaryOpKind::Eq, state, facts)?),
                )
            } else {
                (compare(condition, HirBinaryOpKind::Le, state, facts)?, None)
            }
        }
    };
    if label.is_some() && stop.is_none() {
        return None;
    }
    Some((
        Profile {
            kind,
            decrement: small_integer(&binary.rhs)?,
            bound,
            stop,
            label,
        },
        binary,
    ))
}

pub(super) fn plans(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    templates: &[Option<GuardedCounterTemplate>],
) -> Recovered {
    let mut recovered = Recovered {
        plans: Vec::new(),
        result_slots: BTreeMap::new(),
    };
    let mut profiles = BTreeMap::new();
    for callee in context
        .expanded_callees
        .into_iter()
        .flat_map(|callees| callees.values())
    {
        let HirLuauInliningBody::GuardedCounter { template } = callee.body else {
            continue;
        };
        let Some(body) = templates[template].as_ref() else {
            continue;
        };
        for (a, b) in [(false, false), (true, false), (true, true)] {
            let key = Profile {
                kind: body.kind,
                decrement: body.decrement,
                bound: body.bound,
                stop: (!b).then_some(body.stop),
                label: (!a).then(|| body.label.clone()),
            };
            profiles
                .entry(key)
                .and_modify(|known| *known = None)
                .or_insert(Some((callee, a, b)));
        }
    }
    if profiles.is_empty() {
        return recovered;
    }
    let copies = facts
        .state_copy_frames()
        .filter_map(|copy| Some((facts.promoted_local_for_temp(copy.target)?, copy)))
        .fold(BTreeMap::new(), |mut map, (local, copy)| {
            map.entry(local)
                .and_modify(|known| *known = None)
                .or_insert(Some(copy));
            map
        });
    let stmts = &context.proto.body.stmts;
    let mut start = 0;
    while start + 2 < stmts.len() {
        let candidate = (|| {
            let (state, initial) = scalar_local(&stmts[start])?;
            small_integer(initial)?;
            let home = facts.trusted_local_home_slot(state)?;
            let (first_result, _) = scalar_local(&stmts[start + 2])?;
            let first = *copies.get(&first_result)?.as_ref()?;
            let base = first.target_home;
            let width = home.slot().checked_sub(base.slot())?;
            if width == 0
                || width > 255
                || first.source_home != home
                || base != HomeSlotKey::new(base.slot(), 0)
                || home != HomeSlotKey::new(home.slot(), 0)
            {
                return None;
            }
            let end = start.checked_add(width.checked_mul(3)?)?;
            let group = stmts.get(start..end)?;
            let mut values = Vec::with_capacity(width);
            let mut results = Vec::with_capacity(width);
            let mut slots = Vec::with_capacity(width);
            for (offset, triple) in group.as_chunks::<3>().0.iter().enumerate() {
                let (current, initial) = scalar_local(&triple[0])?;
                let (result, value) = scalar_local(&triple[2])?;
                let copy = *copies.get(&result)?.as_ref()?;
                let (key, binary) = profile(&triple[1], current, facts, context)?;
                let (callee, a, b) = *profiles.get(&key)?.as_ref()?;
                let site = binary.source_site?;
                if *value != HirExpr::LocalRef(current)
                    || copy
                        .source
                        .and_then(|source| facts.promoted_local_for_temp(source))
                        != Some(current)
                    || facts.trusted_local_home_slot(current) != Some(home)
                    || copy.source_home != home
                    || copy.target_home != HomeSlotKey::new(base.slot() + offset, 0)
                    || facts.trusted_local_home_slot(result) != Some(copy.target_home)
                    || !initializer(&triple[0])
                    || !plain_copy(&triple[2])
                    || small_integer(initial).is_none()
                    || callee.declaration >= start
                    || !facts.local_definitions_reference_unaliased(current)
                    || [current, result].into_iter().any(|local| {
                        context.proto.local_debug_hints[local.index()].is_some()
                            || context.proto.local_debug_scopes[local.index()].is_some()
                    })
                {
                    return None;
                }
                values.push(factories::factory_call(
                    callee.local,
                    Some(site),
                    vec![HirExpr::Boolean(a), HirExpr::Boolean(b), initial.clone()].into(),
                ));
                results.push(result);
                slots.push((site, copy.target_home.slot()));
            }
            if (base.slot()..=home.slot() + 3).any(|slot| {
                let home = HomeSlotKey::new(slot, 0);
                context.closed.contains(&home) || context.barred.contains(&home)
            }) {
                return None;
            }
            Some((
                end,
                slots,
                Plan {
                    prefix_at_sink: false,
                    luau_function_declaration: false,
                    start,
                    sink: end - 1,
                    base,
                    values: values.into(),
                    result_locals: results,
                    assignment_targets: Vec::new(),
                    luau_compound_global: false,
                    indexed_target: None,
                    continuing_root: None,
                    retained_copies: Vec::new(),
                    replayed_effects: (start + 1..end).step_by(3).collect(),
                    removed: (start..end - 1).collect(),
                },
            ))
        })();
        if let Some((end, slots, plan)) = candidate {
            recovered.result_slots.extend(slots);
            recovered.plans.push(plan);
            start = end;
        } else {
            start += 1;
        }
    }
    recovered
}
