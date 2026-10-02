//! 配对单次 repeat 查表检查和低槽常量返回，保留原检查及结果写入。
//! 函数体限定控制路径，构造与查表消费原帧事实；提交使用完整后缀事务。

use super::*;
use crate::hir::common::{HirOperationSources, ParamId};
use crate::hir::luau_inlining::small_integer;

fn lookup_exit(branch: &crate::hir::common::HirIf) -> Option<&crate::hir::common::HirTableAccess> {
    let (value, negated) = synthetic_not_subject(&branch.cond);
    let HirExpr::TableAccess(lookup) = value else {
        return None;
    };
    let (exit, empty) = if negated % 2 == 1 {
        (branch.else_block.as_ref()?, Some(&branch.then_block))
    } else {
        (&branch.then_block, branch.else_block.as_ref())
    };
    (matches!(exit.stmts.as_slice(), [HirStmt::Break])
        && empty.is_none_or(|block| block.stmts.is_empty()))
    .then_some(lookup)
}

fn guarded_lookup(block: &HirBlock) -> Option<&crate::hir::common::HirTableAccess> {
    match block.stmts.as_slice() {
        [HirStmt::If(guard), HirStmt::If(test)] => {
            let (value, negated) = synthetic_not_subject(&guard.cond);
            (value == &HirExpr::ParamRef(ParamId(0))
                && negated % 2 == 1
                && matches!(guard.then_block.stmts.as_slice(), [HirStmt::Continue])
                && guard
                    .else_block
                    .as_ref()
                    .is_none_or(|block| block.stmts.is_empty()))
            .then_some(())?;
            lookup_exit(test)
        }
        [HirStmt::If(guard)] => {
            // 同一原控制关系可恢复为 continue guard 或单臂嵌套；不依赖多余 JMP 是否存在。
            let (value, negated) = synthetic_not_subject(&guard.cond);
            if value == &HirExpr::ParamRef(ParamId(0)) {
                let (selected, empty) = if negated % 2 == 1 {
                    (guard.else_block.as_ref()?, Some(&guard.then_block))
                } else {
                    (&guard.then_block, guard.else_block.as_ref())
                };
                if empty.is_some_and(|block| !block.stmts.is_empty()) {
                    return None;
                }
                let [HirStmt::If(test)] = selected.stmts.as_slice() else {
                    return None;
                };
                lookup_exit(test)
            } else {
                let HirExpr::LogicalAnd(and) = &guard.cond else {
                    return None;
                };
                let HirExpr::TableAccess(lookup) = &and.rhs else {
                    return None;
                };
                (and.lhs == HirExpr::ParamRef(ParamId(0))
                    && matches!(guard.then_block.stmts.as_slice(), [HirStmt::Break])
                    && guard
                        .else_block
                        .as_ref()
                        .is_none_or(|block| block.stmts.is_empty()))
                .then_some(lookup)
            }
        }
        _ => None,
    }
}

pub(super) fn body_key(proto: &HirProto) -> Option<(HirLuauInliningBody, crate::LuaString)> {
    if proto.params.as_slice() != [ParamId(0), ParamId(1)]
        || proto.signature.is_vararg
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [HirStmt::Repeat(loop_), HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let lookup = guarded_lookup(&loop_.body)?;
    let [value] = ret.values.fixed.as_slice() else {
        return None;
    };
    if loop_.cond != HirExpr::ParamRef(ParamId(0))
        || lookup.base != HirExpr::ParamRef(ParamId(1))
        || ret.values.tail.is_some()
        || ret.pending_cleanup_source.is_some()
    {
        return None;
    }
    Some((
        HirLuauInliningBody::RepeatLookup {
            template: proto.id.index(),
            key: small_integer(&lookup.key)?,
            result: small_integer(value)?,
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
        if let HirLuauInliningBody::RepeatLookup { key, result, .. } = callee.body {
            templates
                .entry((key, result))
                .and_modify(|entry| *entry = None)
                .or_insert(Some(callee));
        }
    }
    if templates.is_empty() {
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
    for (start, window) in context.proto.body.stmts.windows(3).enumerate() {
        let candidate = (|| {
            let [
                first @ HirStmt::LocalDecl(_),
                HirStmt::If(branch),
                last @ HirStmt::LocalDecl(_),
            ] = window
            else {
                return None;
            };
            let (input, value @ HirExpr::TableConstructor(table)) = scalar_local(first)? else {
                return None;
            };
            let (result, returned) = scalar_local(last)?;
            let (condition, _) = synthetic_not_subject(&branch.cond);
            let HirExpr::TableAccess(lookup) = condition else {
                return None;
            };
            let key = small_integer(&lookup.key)?;
            let callee = *templates.get(&(key, small_integer(returned)?))?.as_ref()?;
            let base = facts.trusted_local_home_slot(result)?;
            let home = facts.trusted_local_home_slot(input)?;
            let HirOperationSources::Single(source) = lookup.sources else {
                return None;
            };
            let layout = facts.native_table_read_layout(lookup)?;
            // 候选拒绝[ProofIncomplete:Frame]：只接受原高槽构造、单次查表和独立低槽写回；不猜 debug 归属。
            if start <= callee.declaration
                || source.proto != callee.creation.proto
                || lookup.base != HirExpr::LocalRef(input)
                || !branch.then_block.stmts.is_empty()
                || branch
                    .else_block
                    .as_ref()
                    .is_some_and(|block| !block.stmts.is_empty())
                || reads.get(&HirBinding::Local(input)) != Some(&1)
                || writes.get(&HirBinding::Local(input)) != Some(&1)
                || base != HomeSlotKey::new(base.slot(), 0)
                || home != HomeSlotKey::new(base.slot() + 1, 0)
                || facts.allocation_result_home(table) != Some(home)
                || !facts.allocation_result_reference_unaliased(table)
                || layout.base != home
                || layout.key != Some(HomeSlotKey::new(base.slot() + 3, 0))
                || facts.table_read_result_home(lookup)
                    != Some(HomeSlotKey::new(base.slot() + 2, 0))
                || [base, home]
                    .iter()
                    .any(|slot| context.closed.contains(slot) || context.barred.contains(slot))
                || [input, result].iter().any(|id| {
                    context.proto.local_debug_scopes[id.index()].is_some()
                        || context.proto.local_debug_hints[id.index()].is_some()
                })
            {
                return None;
            }
            let mut builder =
                frame_builder(context, &[], facts, DecompileDialect::Luau, base.slot())?;
            let value = builder.expr(value, 0, home.slot(), None, false, true, None)?;
            let mut plan = factories::invocation(callee, source, base, result, start, start + 2);
            plan.values = vec![factories::factory_call(
                callee.local,
                Some(source),
                vec![HirExpr::Boolean(true), value].into(),
            )]
            .into();
            plan.replayed_effects.push(start + 1);
            Some(plan)
        })();
        plans.extend(candidate);
    }
    plans
}
