//! 配对 Boolean 条件计数 repeat 的完整展开体与原返回 COPY。
//! 模板保留原操作，caller 仅恢复能由高槽求值、低槽写回共同证明的常量调用。

use super::repeat_prefix::{integer, update_layout};
use super::*;
use crate::hir::common::{HirBinaryExpr, HirBinaryOpKind, ParamId};

fn add(stmt: &HirStmt, state: LocalId) -> Option<&HirBinaryExpr> {
    let (target, HirExpr::Binary(binary)) = scalar_local(stmt)? else {
        return None;
    };
    (target == state && binary.op == HirBinaryOpKind::Add && binary.lhs == HirExpr::LocalRef(state))
        .then_some(binary)
}

fn comparison(expr: &HirExpr, state: LocalId) -> Option<&HirBinaryExpr> {
    let HirExpr::Binary(binary) = expr else {
        return None;
    };
    (binary.op == HirBinaryOpKind::Gt && binary.lhs == HirExpr::LocalRef(state)).then_some(binary)
}

fn conjunction(expr: &HirExpr, left: usize, right: usize) -> bool {
    matches!(expr, HirExpr::LogicalAnd(and)
        if and.lhs == HirExpr::ParamRef(ParamId(left))
            && and.rhs == HirExpr::ParamRef(ParamId(right)))
}

pub(super) fn body_key(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
) -> Option<(HirLuauInliningBody, crate::LuaString)> {
    if proto.params.len() != 3
        || proto.signature.is_vararg
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [first, HirStmt::Repeat(loop_), HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let (state, initial) = scalar_local(first)?;
    let [update] = loop_.body.stmts.as_slice() else {
        return None;
    };
    let update = add(update, state)?;
    let HirExpr::LogicalOr(outer) = &loop_.cond else {
        return None;
    };
    let HirExpr::LogicalOr(inner) = &outer.rhs else {
        return None;
    };
    let limit = comparison(&inner.rhs, state)?;
    if !conjunction(&outer.lhs, 1, 0)
        || !conjunction(&inner.lhs, 1, 2)
        || ret.values.fixed.as_slice() != [HirExpr::LocalRef(state)]
        || ret.values.tail.is_some()
        || ret.pending_cleanup_source.is_some()
        || facts.trusted_local_home_slot(state) != Some(HomeSlotKey::new(3, 0))
        || !update_layout(update, facts, HomeSlotKey::new(3, 0))
    {
        return None;
    }
    Some((
        HirLuauInliningBody::CounterRepeat {
            template: proto.id.index(),
            initial: integer(initial)?,
            increment: integer(&update.rhs)?,
            limit: integer(&limit.rhs)?,
        },
        "".into(),
    ))
}

pub(super) fn plans(context: NativeFrameContext<'_>, facts: &ProtoPromotionFacts) -> Vec<Plan> {
    let mut loops = BTreeMap::new();
    let mut singles = BTreeMap::new();
    for callee in context
        .expanded_callees
        .into_iter()
        .flat_map(|items| items.values())
    {
        if let HirLuauInliningBody::CounterRepeat {
            initial,
            increment,
            limit,
            ..
        } = callee.body
        {
            loops
                .entry((initial, increment, limit))
                .and_modify(|v| *v = None)
                .or_insert(Some(callee));
            singles
                .entry((initial, increment))
                .and_modify(|v| *v = None)
                .or_insert(Some(callee));
        }
    }
    if loops.is_empty() {
        return Vec::new();
    }
    let mut reads = BTreeMap::new();
    let mut writes = BTreeMap::new();
    visit_stmts(
        &context.proto.body.stmts,
        &mut (
            BindingReadCollector(|binding| *reads.entry(binding).or_insert(0) += 1),
            BindingWriteCollector(|binding| *writes.entry(binding).or_insert(0) += 1),
        ),
    );
    let mut plans = Vec::new();
    for (sink, stmt) in context.proto.body.stmts.iter().enumerate() {
        let candidate = (|| {
            let (result, value) = scalar_local(stmt)?;
            if !matches!(stmt, HirStmt::LocalDecl(decl) if decl.initializer_merge_transaction.is_none())
            {
                return None;
            }
            let base = facts.trusted_local_home_slot(result)?;
            let home = HomeSlotKey::new(base.slot() + 1, 0);
            let (callee, start, site, once) = match value {
                HirExpr::LocalRef(state) => {
                    let start = sink.checked_sub(2)?;
                    let (input, initial) = scalar_local(&context.proto.body.stmts[start])?;
                    let HirStmt::Repeat(loop_) = &context.proto.body.stmts[start + 1] else {
                        return None;
                    };
                    let [update] = loop_.body.stmts.as_slice() else {
                        return None;
                    };
                    let update = add(update, *state)?;
                    let limit = comparison(&loop_.cond, *state)?;
                    let key = (
                        integer(initial)?,
                        integer(&update.rhs)?,
                        integer(&limit.rhs)?,
                    );
                    let callee = *loops.get(&key)?.as_ref()?;
                    let layout = facts.native_binary_layout(limit)?;
                    // 候选拒绝[ProofIncomplete:Frame]：循环状态只能由本次初始化、更新和 COPY 使用；尾比较的高槽 LOAD 也必须保持。
                    if input != *state
                        || facts.trusted_local_home_slot(*state) != Some(home)
                        || !update_layout(update, facts, home)
                        || reads.get(&HirBinding::Local(*state)) != Some(&3)
                        || writes.get(&HirBinding::Local(*state)) != Some(&2)
                        || layout.lhs != Some(home)
                        || facts.direct_binary_operand_home(limit, 0) != Some(home)
                        || facts
                            .binary_operand_preparation(limit, 1, &limit.rhs)
                            .map(|(_, slot)| slot)
                            != Some(HomeSlotKey::new(home.slot() + 1, 0))
                        || context.proto.local_debug_hints[state.index()].is_some()
                        || context.proto.local_debug_scopes[state.index()].is_some()
                    {
                        return None;
                    }
                    (callee, start, update.source_site?, false)
                }
                HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Add => {
                    let callee = *singles
                        .get(&(integer(&binary.lhs)?, integer(&binary.rhs)?))?
                        .as_ref()?;
                    let site = binary.source_site?;
                    let producer = facts.operation_result_temp(site)?;
                    // 提前退出可跨基本块到达返回 COPY；消费 Promotion 的唯一入口证明，
                    // 不沿任意控制边追别名，也不把仅同槽的值视为同一写回。
                    let copy = match facts.trusted_immediate_moves(producer)? {
                        [copy] => copy,
                        [] => facts.value_result_copy(producer)?,
                        _ => return None,
                    };
                    let layout = facts.native_binary_layout(binary)?;
                    if layout.lhs != Some(home)
                        || layout.rhs.is_some()
                        || facts
                            .binary_operand_preparation(binary, 0, &binary.lhs)
                            .map(|(_, slot)| slot)
                            != Some(home)
                        || facts.operation_result_home(site) != Some(home)
                        || copy.source != Some(producer)
                        || copy.source_home != home
                        || copy.target_home != base
                        || facts.promoted_local_for_temp(copy.target) != Some(result)
                        || !facts.operation_result_reference_unaliased(site)
                    {
                        return None;
                    }
                    (callee, sink, site, true)
                }
                _ => return None,
            };
            if start <= callee.declaration
                || site.proto != callee.creation.proto
                || base != HomeSlotKey::new(base.slot(), 0)
                || [base, home]
                    .iter()
                    .any(|slot| context.barred.contains(slot) || context.closed.contains(slot))
                || context.proto.local_debug_hints[result.index()].is_some()
                || context.proto.local_debug_scopes[result.index()].is_some()
            {
                return None;
            }
            let mut plan = factories::invocation(callee, site, base, result, start, sink);
            plan.values = vec![factories::factory_call(
                callee.local,
                Some(site),
                vec![
                    HirExpr::Boolean(false),
                    HirExpr::Boolean(once),
                    HirExpr::Boolean(once),
                ]
                .into(),
            )]
            .into();
            if !once {
                plan.replayed_effects.push(start + 1);
            }
            Some(plan)
        })();
        plans.extend(candidate);
    }
    plans
}
