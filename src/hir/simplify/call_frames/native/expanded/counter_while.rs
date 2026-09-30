//! 配对常量参数展开的计数循环、原返回 COPY 与外层比较调用。
//!
//! 现存函数提供控制结构；逐次更新及退出比较保持原位，Generate 再验证调用必须内联。

use super::repeat_prefix::{integer, observation, update_layout};
use super::*;
use crate::hir::common::{HirBinaryOpKind, ParamId};

fn update(stmt: &HirStmt, local: LocalId) -> Option<&crate::hir::HirBinaryExpr> {
    let (target, HirExpr::Binary(binary)) = scalar_local(stmt)? else {
        return None;
    };
    (target == local && binary.op == HirBinaryOpKind::Add && binary.lhs == HirExpr::LocalRef(local))
        .then_some(binary)
}

fn limit(expr: &HirExpr, local: LocalId) -> Option<i64> {
    let HirExpr::Binary(binary) = expr else {
        return None;
    };
    (binary.op == HirBinaryOpKind::Gt && binary.lhs == HirExpr::LocalRef(local))
        .then(|| integer(&binary.rhs))
        .flatten()
}

fn break_only(block: &HirBlock) -> bool {
    matches!(block.stmts.as_slice(), [HirStmt::Break])
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
    let [first, HirStmt::While(loop_), HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let (local, initial) = scalar_local(first)?;
    let initial = integer(initial)?;
    let home = HomeSlotKey::new(4, 0);
    if facts.trusted_local_home_slot(local) != Some(home)
        || loop_.cond != HirExpr::ParamRef(ParamId(0))
        || ret.values.fixed.as_slice() != [HirExpr::LocalRef(local)]
        || ret.values.tail.is_some()
    {
        return None;
    }
    let [assign, HirStmt::If(exit), HirStmt::Repeat(repeat)] = loop_.body.stmts.as_slice() else {
        return None;
    };
    let add = update(assign, local)?;
    let increment = integer(&add.rhs)?;
    let limit = limit(&exit.cond, local)?;
    if !update_layout(add, facts, home)
        || !break_only(&exit.then_block)
        || exit.else_block.is_some()
    {
        return None;
    }
    let HirExpr::LogicalOr(condition) = &repeat.cond else {
        return None;
    };
    let HirExpr::TableAccess(access) = &condition.rhs else {
        return None;
    };
    if condition.lhs != HirExpr::ParamRef(ParamId(0))
        || access.base != HirExpr::ParamRef(ParamId(3))
        || access.key != HirExpr::LocalRef(local)
    {
        return None;
    }
    let [HirStmt::If(branch)] = repeat.body.stmts.as_slice() else {
        return None;
    };
    let [HirStmt::If(inner), call] = branch.then_block.stmts.as_slice() else {
        return None;
    };
    if branch.cond != HirExpr::ParamRef(ParamId(1))
        || !matches!(
            branch.else_block.as_ref()?.stmts.as_slice(),
            [HirStmt::Continue]
        )
        || inner.cond != HirExpr::ParamRef(ParamId(2))
        || !break_only(&inner.then_block)
        || inner.else_block.is_some()
        || observation(call, local).is_none()
    {
        return None;
    }
    Some((
        HirLuauInliningBody::CounterWhile {
            template: proto.id.index(),
            initial,
            increment,
            limit,
        },
        "".into(),
    ))
}

pub(super) fn plans(context: NativeFrameContext<'_>, facts: &ProtoPromotionFacts) -> Vec<Plan> {
    let Some(callees) = context.expanded_callees else {
        return Vec::new();
    };
    let mut templates = BTreeMap::new();
    let mut initials = BTreeMap::new();
    for callee in callees.values() {
        if let HirLuauInliningBody::CounterWhile {
            initial,
            increment,
            limit,
            ..
        } = callee.body
        {
            templates
                .entry((initial, increment, limit))
                .and_modify(|v| *v = None)
                .or_insert(Some(callee));
            initials
                .entry(initial)
                .and_modify(|v| *v = None)
                .or_insert(Some(callee));
        }
    }
    let mut plans = Vec::new();
    for sink in 3..context.proto.body.stmts.len() {
        let candidate = (|| {
            let stmts = &context.proto.body.stmts;
            let HirStmt::CallStmt(statement) = &stmts[sink] else {
                return None;
            };
            let call = &statement.call;
            let frame = facts.native_fastcall_frame(call)?;
            let (callee_local, global @ HirExpr::GlobalRef(name)) = scalar_local(&stmts[sink - 1])?
            else {
                return None;
            };
            let (boolean, HirExpr::Binary(compare)) = scalar_local(&stmts[sink - 2])? else {
                return None;
            };
            let base = frame.home;
            let result_home = HomeSlotKey::new(base.slot() + 2, 0);
            let state_home = HomeSlotKey::new(base.slot() + 3, 0);
            let copy = facts.binary_operand_copy(compare, 0)?;
            let result = copy.target;
            let source = copy.source?;
            if name.key.as_utf8() != Some("assert")
                || call.callee != HirExpr::LocalRef(callee_local)
                || call.args.fixed.as_slice() != [HirExpr::LocalRef(boolean)]
                || call.args.tail.is_some()
                || !call
                    .fastcall
                    .is_some_and(|f| f.builtin() == 1 && f.fixed_is_direct(0))
                || frame.results != Some(ResultPack::Ignore)
                || !frame.arguments_unaliased
                || facts.comparison_result_temp(compare) != facts.call_argument_value(call, 0)
                || facts.trusted_temp_home_slot(result) != Some(result_home)
                || facts.trusted_temp_home_slot(source) != Some(state_home)
                || facts.native_binary_layout(compare)?.rhs.is_some()
                || compare.op != HirBinaryOpKind::Eq
                || integer(&compare.rhs).is_none()
                || (base.slot()..=state_home.slot()).any(|slot| {
                    let home = HomeSlotKey::new(slot, 0);
                    context.barred.contains(&home) || context.closed.contains(&home)
                })
                || facts.boolean_argument_prewrite(call, 0).is_some()
            {
                return None;
            }
            let mut builder =
                frame_builder(context, &[], facts, DecompileDialect::Luau, base.slot())?;
            if builder.expr(
                global,
                0,
                base.slot(),
                None,
                true,
                false,
                Some(frame.callee),
            )? != *global
            {
                return None;
            }
            let mut before = sink - 3;
            let mut value = &compare.lhs;
            if let Some((target, copied @ HirExpr::LocalRef(_))) = scalar_local(&stmts[before])
                && *value == HirExpr::LocalRef(target)
            {
                value = copied;
                before = before.checked_sub(1)?;
            }
            let (start, callee, active, site, replayed) =
                if let HirStmt::Repeat(repeat) = &stmts[before] {
                    let first = before.checked_sub(1)?;
                    let (state, initial) = scalar_local(&stmts[first])?;
                    let [assign] = repeat.body.stmts.as_slice() else {
                        return None;
                    };
                    let add = update(assign, state)?;
                    let key = (
                        integer(initial)?,
                        integer(&add.rhs)?,
                        limit(&repeat.cond, state)?,
                    );
                    let callee = *templates.get(&key)?.as_ref()?;
                    let HirExpr::Binary(condition) = &repeat.cond else {
                        return None;
                    };
                    let layout = facts.native_binary_layout(condition)?;
                    if *value != HirExpr::LocalRef(state)
                        || facts.promoted_local_for_temp(source) != Some(state)
                        || facts.trusted_local_home_slot(state) != Some(state_home)
                        || !update_layout(add, facts, state_home)
                        || layout.lhs != Some(state_home)
                        || facts.direct_binary_operand_home(condition, 0) != Some(state_home)
                        || facts
                            .binary_operand_preparation(condition, 1, &condition.rhs)
                            .map(|(_, home)| home)
                            != Some(HomeSlotKey::new(state_home.slot() + 1, 0))
                    {
                        return None;
                    }
                    (first, callee, true, add.source_site?, vec![before])
                } else {
                    let (local, literal) = scalar_local(&stmts[before])?;
                    let initial = integer(literal)?;
                    let callee = *initials.get(&initial)?.as_ref()?;
                    if *value != HirExpr::LocalRef(local)
                        || !facts.binary_copy_preparation(compare, 0, literal)
                    {
                        return None;
                    }
                    (before, callee, false, compare.source_site?, Vec::new())
                };
            if start <= callee.declaration {
                return None;
            }
            let mut restored = call.clone();
            restored.callee = global.clone();
            let mut compare = compare.as_ref().clone();
            compare.lhs = factories::factory_call(
                callee.local,
                Some(site),
                vec![
                    HirExpr::Boolean(active),
                    HirExpr::Boolean(false),
                    HirExpr::Boolean(false),
                    HirExpr::Nil,
                ]
                .into(),
            );
            restored.args = vec![HirExpr::Binary(Box::new(compare))].into();
            Some(Plan {
                prefix_at_sink: false,
                luau_function_declaration: false,
                start,
                sink,
                base,
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
