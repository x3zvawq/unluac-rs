//! 将 Boolean 清零计数循环及只读条件为假的残留测试恢复为完整调用。
//! 匹配原高槽参数、计数更新和低槽 COPY；原检查必须由同一内联合同重发。

use super::super::assignments::plain_copy;
use super::*;
use crate::hir::luau_inlining::{ResetCounterTemplate, small_integer};

pub(super) fn plans(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    templates: &[Option<ResetCounterTemplate>],
) -> Vec<Plan> {
    let mut callees = BTreeMap::new();
    for callee in context
        .expanded_callees
        .into_iter()
        .flat_map(|map| map.values())
    {
        if let HirLuauInliningBody::ResetCounter { template } = callee.body
            && let Some(body) = templates[template]
        {
            for key in [(body.initial, Some(body.increment)), (body.initial, None)] {
                callees
                    .entry(key)
                    .and_modify(|entry| *entry = None)
                    .or_insert(Some(callee));
            }
        }
    }
    if callees.is_empty() {
        return Vec::new();
    }
    let copies = facts
        .copy_binding_frames()
        .filter_map(|copy| {
            let (HirBinding::Local(source), HirBinding::Local(target)) = (copy.source, copy.target)
            else {
                return None;
            };
            Some(((source, target), copy))
        })
        .fold(BTreeMap::new(), |mut map, (key, copy)| {
            map.entry(key)
                .and_modify(|entry| *entry = None)
                .or_insert(Some(copy));
            map
        });
    let stmts = &context.proto.body.stmts;
    let uses = value_uses::ValueUses::new(context.proto);
    let root = uses.tree.block(uses.tree.root_block());
    let positions = root
        .iter()
        .map(|id| uses.points[id.index()].0)
        .collect::<Vec<_>>();
    let mut definitions = BTreeMap::<LocalId, Vec<usize>>::new();
    for (index, stmt) in stmts.iter().enumerate() {
        if let HirStmt::LocalDecl(decl) = stmt {
            for &local in &decl.bindings {
                definitions.entry(local).or_default().push(index);
            }
        } else if let Some((local, _)) = scalar_local(stmt) {
            definitions.entry(local).or_default().push(index);
        }
    }
    let mut plans = Vec::new();
    for control in 1..stmts.len().saturating_sub(1) {
        if !matches!(stmts[control], HirStmt::While(_) | HirStmt::If(_)) {
            continue;
        }
        let candidate = (|| {
            let (result, HirExpr::LocalRef(state)) = scalar_local(&stmts[control + 1])? else {
                return None;
            };
            let copy = *copies.get(&(*state, result))?.as_ref()?;
            let base = copy.target_home.slot();
            let home = |offset| HomeSlotKey::new(base + offset, 0);
            if copy.target_home != home(0)
                || copy.source_home != home(3)
                || !plain_copy(&stmts[control + 1])
            {
                return None;
            }
            let mut prepared = Vec::new();
            let mut start = control;
            while prepared.len() < 3 && start > 0 {
                start -= 1;
                if !plain_copy(&stmts[start]) {
                    return None;
                }
                if let HirStmt::LocalDecl(decl) = &stmts[start] {
                    if decl.values.tail.is_some()
                        || decl.bindings.len() != decl.values.fixed.len()
                        || decl.bindings.len() + prepared.len() > 3
                    {
                        return None;
                    }
                    prepared.extend(decl.bindings.iter().copied().zip(&decl.values.fixed).rev());
                } else {
                    prepared.push(scalar_local(&stmts[start])?);
                }
            }
            prepared.reverse();
            let [
                (left, HirExpr::Boolean(a)),
                (right, HirExpr::Boolean(b)),
                (count, initial),
            ] = prepared.as_slice()
            else {
                return None;
            };
            if count != state {
                return None;
            }
            let value = |local| HirExpr::LocalRef(local);
            let (active, increment, replay) = match &stmts[control] {
                HirStmt::While(loop_) => {
                    let HirExpr::LogicalOr(or) = &loop_.cond else {
                        return None;
                    };
                    let [update, reset_left, reset_right] = loop_.body.stmts.as_slice() else {
                        return None;
                    };
                    let (target, HirExpr::Binary(add)) = scalar_local(update)? else {
                        return None;
                    };
                    if or.lhs != value(*left)
                        || or.rhs != value(*right)
                        || target != *state
                        || add.op != crate::hir::HirBinaryOpKind::Add
                        || add.lhs != value(*state)
                        || !repeat_prefix::update_layout(add, facts, home(3))
                        || scalar_local(reset_left) != Some((*left, &HirExpr::Boolean(false)))
                        || scalar_local(reset_right) != Some((*right, &HirExpr::Boolean(false)))
                        || ![update, reset_left, reset_right]
                            .into_iter()
                            .all(plain_copy)
                    {
                        return None;
                    }
                    (true, Some(small_integer(&add.rhs)?), vec![control])
                }
                HirStmt::If(branch) => {
                    let HirExpr::LogicalAnd(and) = &branch.cond else {
                        return None;
                    };
                    let HirExpr::Unary(not) = &and.lhs else {
                        return None;
                    };
                    if not.op != crate::hir::HirUnaryOpKind::Not
                        || not.expr != value(*left)
                        || and.rhs != value(*right)
                        || !branch.preserves_empty_test
                        || !branch.then_block.stmts.is_empty()
                        || branch
                            .else_block
                            .as_ref()
                            .is_some_and(|block| !block.stmts.is_empty())
                    {
                        return None;
                    }
                    (false, None, vec![control])
                }
                _ => return None,
            };
            let callee = *callees
                .get(&(small_integer(initial)?, increment))?
                .as_ref()?;
            let source = copy.site;
            if callee.creation.instr >= source.instr
                || [(*left, 1), (*right, 2), (*state, 3), (result, 0)]
                    .into_iter()
                    .any(|(local, offset)| {
                        facts.trusted_local_home_slot(local) != Some(home(offset))
                            || context.proto.local_debug_hints[local.index()].is_some()
                            || context.proto.local_debug_scopes[local.index()].is_some()
                    })
                || (base..=base + 3).any(|slot| {
                    context.closed.contains(&HomeSlotKey::new(slot, 0))
                        || context.barred.contains(&HomeSlotKey::new(slot, 0))
                })
            {
                return None;
            }
            // 原参数状态只退休到下一次无条件覆盖；其 RHS 仍可读旧值，须一起检查。
            // 其它帧再次使用同一 Local 的新版本不属于本次参数。
            if [*left, *right, *state].into_iter().any(|local| {
                let end = definitions
                    .get(&local)
                    .and_then(|sites| {
                        sites.get(sites.partition_point(|&index| index <= control + 1))
                    })
                    .map_or(uses.count, |&index| positions[index] + 1);
                uses.reads(local, positions[control + 1] + 1, end) != 0
            }) {
                return None;
            }
            let mut plan =
                factories::invocation(callee, source, home(0), result, start, control + 1);
            plan.values = vec![factories::factory_call(
                callee.local,
                Some(source),
                vec![
                    HirExpr::Boolean(*a),
                    HirExpr::Boolean(*b),
                    HirExpr::Boolean(active),
                ]
                .into(),
            )]
            .into();
            plan.replayed_effects = replay;
            Some(plan)
        })();
        plans.extend(candidate);
    }
    plans
}
