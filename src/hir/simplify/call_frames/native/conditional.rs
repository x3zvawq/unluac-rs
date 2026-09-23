//! 在原共同结果帧中恢复 Luau 条件选值，避免合流 carrier 抬高调用的源码前缀。
//! 分支内的准备事件由 FrameBuilder 消费，整个选择及后继条件由同一 native preview 提交。

use super::*;
use crate::hir::common::{
    HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirDecisionTestSource,
};
use crate::hir::visit::for_each_nested_block;

pub(super) fn collect(context: NativeFrameContext<'_>, facts: &ProtoPromotionFacts) -> Vec<Plan> {
    let mut reads = BTreeMap::new();
    visit_stmts(
        &context.proto.body.stmts,
        &mut BindingReadCollector(|binding| {
            if let HirBinding::Local(local) = binding {
                *reads.entry(local).or_insert(0usize) += 1;
            }
        }),
    );
    let original_nil = facts
        .nil_write_groups()
        .flat_map(|group| {
            group
                .iter()
                .filter_map(|temp| facts.promoted_local_for_temp(*temp))
        })
        .collect();
    let mut plans = Vec::new();
    collect_block(
        context,
        facts,
        &context.proto.body,
        &reads,
        &original_nil,
        &mut 0,
        &mut plans,
    );
    plans
}

fn collect_block(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    block: &HirBlock,
    reads: &BTreeMap<LocalId, usize>,
    original_nil: &BTreeSet<LocalId>,
    cursor: &mut usize,
    plans: &mut Vec<Plan>,
) {
    let mut starts = Vec::with_capacity(block.stmts.len());
    for stmt in &block.stmts {
        starts.push(*cursor);
        *cursor += 1;
        for_each_nested_block(stmt, &mut |child| {
            collect_block(context, facts, child, reads, original_nil, cursor, plans);
        });
        if matches!(stmt, HirStmt::Repeat(_)) {
            *cursor += 1;
        }
    }
    for (index, window) in block.stmts.windows(3).enumerate() {
        if let Some(mut plan) = condition_plan(context, facts, window, reads, original_nil) {
            plan.start = starts[index];
            plan.sink = starts[index + 2];
            plan.removed = (plan.start..plan.sink).collect();
            // 两臂的原 CALL、COPY 与 TEST 在表达式中重发；声明身份仍由 preview 退休。
            plan.replayed_effects.push(starts[index + 1]);
            let mut arm_cursor = starts[index + 1] + 1;
            for_each_nested_block(&window[1], &mut |arm| {
                prefix::coordinates::visit(arm, &mut arm_cursor, &mut |id, kind, stmt| {
                    if kind == PointKind::Statement && !matches!(stmt, HirStmt::LocalDecl(_)) {
                        plan.replayed_effects.push(id);
                    }
                })
            });
            plans.push(plan);
        }
    }
    for (index, window) in block.stmts.windows(2).enumerate() {
        if let Some(mut plan) = initializer_plan(context, facts, window, original_nil) {
            plan.start = starts[index];
            plan.sink = plan.start;
            let end = starts.get(index + 2).copied().unwrap_or(*cursor);
            plan.removed = (starts[index + 1]..end).collect();
            // 两臂只有已树化的结果写，声明本身留在原词法位置。
            plan.replayed_effects.clone_from(&plan.removed);
            plans.push(plan);
        }
    }
}

fn initializer_plan(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    window: &[HirStmt],
    original_nil: &BTreeSet<LocalId>,
) -> Option<Plan> {
    let [HirStmt::LocalDecl(decl), HirStmt::If(select)] = window else {
        return None;
    };
    let [result] = decl.bindings.as_slice() else {
        return None;
    };
    let base = facts.trusted_local_home_slot(*result)?;
    if !decl.values.is_empty()
        || decl.initializer_merge_transaction.is_some()
        || original_nil.contains(result)
        || select.preserves_empty_test
        || context.barred.contains(&base)
        || context.closed.contains(&base)
    {
        return None;
    }
    if let Some(scope) = context.proto.local_debug_scopes[result.index()] {
        let initializer = context.proto.debug_scopes[scope]?.initializer_phi?;
        // 原来已生效的空声明仍独立保留；只有 scope 自身从该合流结果开始才恢复 initializer。
        if facts.promoted_local_for_temp(initializer) != Some(*result)
            || facts.trusted_temp_home_slot(initializer) != Some(base)
        {
            return None;
        }
    }
    let test_home = match &select.cond {
        HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local),
        HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param),
        _ => None,
    }?;
    if test_home.slot() >= base.slot() {
        return None;
    }
    let arm = |block: &HirBlock| {
        let [HirStmt::Assign(assign)] = block.stmts.as_slice() else {
            return None;
        };
        let ([HirLValue::Local(target)], [value], None) = (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail,
        ) else {
            return None;
        };
        if target != result {
            return None;
        }
        let mut builder = frame_builder(context, &[], facts, DecompileDialect::Luau, base.slot())?;
        // 已树化 RHS 仍核对原 CALL/短路结果槽；不依据赋值外形猜测原初始化帧。
        if matches!(value, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)) {
            builder.luau_logical_value(value, 0, base)
        } else {
            builder.expr(value, 0, base.slot(), None, false, true, None)
        }
    };
    let value = native_value(
        &select.cond,
        arm(&select.then_block)?,
        arm(select.else_block.as_ref()?)?,
    );
    let mut plan = value_plan(base, value);
    plan.result_locals.push(*result);
    Some(plan)
}

fn condition_plan(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    window: &[HirStmt],
    reads: &BTreeMap<LocalId, usize>,
    original_nil: &BTreeSet<LocalId>,
) -> Option<Plan> {
    let [
        HirStmt::LocalDecl(decl),
        HirStmt::If(select),
        HirStmt::If(consumer),
    ] = window
    else {
        return None;
    };
    let [result] = decl.bindings.as_slice() else {
        return None;
    };
    let base = facts.trusted_local_home_slot(*result)?;
    if !removable_empty_declaration(context.proto, original_nil, decl)
        || reads.get(result) != Some(&1)
        || consumer.cond != HirExpr::LocalRef(*result)
        || select.preserves_empty_test
        || context.barred.contains(&base)
        || context.closed.contains(&base)
    {
        return None;
    }
    let test_home = match &select.cond {
        HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local),
        HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param),
        _ => None,
    }?;
    if test_home.slot() >= base.slot() {
        // ProofIncomplete：有准备事件的条件须与两臂共同证明 scratch，不能复制原 test。
        return None;
    }
    let truthy = value_arm(context, facts, &select.then_block, *result, base)?;
    let falsy = value_arm(context, facts, select.else_block.as_ref()?, *result, base)?;
    Some(value_plan(base, native_value(&select.cond, truthy, falsy)))
}

fn native_value(condition: &HirExpr, truthy: HirExpr, falsy: HirExpr) -> HirExpr {
    HirExpr::Decision(Box::new(HirDecisionExpr {
        entry: HirDecisionNodeRef(0),
        nodes: vec![HirDecisionNode {
            id: HirDecisionNodeRef(0),
            test: condition.clone(),
            test_source: HirDecisionTestSource::Predicate,
            truthy: HirDecisionTarget::Expr(truthy),
            falsy: HirDecisionTarget::Expr(falsy),
        }],
        emit_as_luau_if: true,
    }))
}

fn value_plan(base: HomeSlotKey, value: HirExpr) -> Plan {
    Plan {
        start: 0,
        sink: 0,
        base,
        values: vec![value].into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    }
}

fn value_arm(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    block: &HirBlock,
    result: LocalId,
    base: HomeSlotKey,
) -> Option<HirExpr> {
    let (last, preparation) = block.stmts.split_last()?;
    let HirStmt::Assign(phi) = last else {
        return None;
    };
    let ([HirLValue::Local(target)], [HirExpr::LocalRef(source)], None) = (
        phi.targets.as_slice(),
        phi.values.fixed.as_slice(),
        &phi.values.tail,
    ) else {
        return None;
    };
    if *target != result
        || !phi.is_phi_transfer
        || facts.trusted_local_home_slot(*source) != Some(base)
    {
        return None;
    }
    let run = preparation.iter().collect::<Vec<_>>();
    let mut builder = frame_builder(context, &run, facts, DecompileDialect::Luau, base.slot())?;
    let value = builder.expr(
        &HirExpr::LocalRef(*source),
        run.len(),
        base.slot(),
        None,
        false,
        true,
        None,
    )?;
    // 只提交完整分支帧；多余写入、独立 debug 身份或没有被消费的事件都留在原控制树。
    (builder.first_event == Some(0) && builder.next_event == run.len()).then_some(value)
}
