//! 在原结果帧中恢复查表短路值、Boolean 物化、调用条件参数与 Luau 条件选值。
//! 分支内的准备事件由 FrameBuilder 消费，整个选择及后继条件由同一 native preview 提交。

use super::assignments::plain_copy;
use super::*;
use crate::hir::common::{
    HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirDecisionTestSource,
};
use crate::hir::visit::for_each_nested_block;

/// 仅在原结果槽内重发整棵值图，不把“允许控制极性恢复”误作单个旧根已结束。
pub(super) fn lookup_value_plans(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> (Vec<Plan>, usize) {
    let mut plans = Vec::new();
    let mut count = 0;
    prefix::coordinates::visit(&context.proto.body, &mut count, &mut |index, kind, stmt| {
        if kind != PointKind::Statement {
            return;
        }
        let HirStmt::LocalDecl(decl) = stmt else {
            return;
        };
        let ([local], [HirExpr::Decision(decision)], None) = (
            decl.bindings.as_slice(),
            decl.values.fixed.as_slice(),
            &decl.values.tail,
        ) else {
            return;
        };
        let Some(home) = facts.trusted_local_home_slot(*local) else {
            return;
        };
        if decision.emit_as_luau_if
            || decl.initializer_merge_transaction.is_some()
            || context.barred.contains(&home)
            || context.closed.contains(&home)
        {
            return;
        }
        let Some(mut builder) = frame_builder(context, &[], facts, dialect, home.slot()) else {
            return;
        };
        let valid_value = |value: &HirExpr, builder: &mut FrameBuilder<'_>| {
            match value {
                HirExpr::Boolean(_) => true,
                HirExpr::TableAccess(access) => {
                    let Some(layout) = facts.native_table_read_layout(access) else {
                        return false;
                    };
                    // 所有动态读取在同一结果槽写回，base 保持在声明前缀中；
                    // 不引入高槽准备，不在下一次 GETTABLE 的回调之前清除旧结果。
                    facts.table_read_result_home(access) == Some(home)
                        && layout.key.is_none()
                        && layout.base.slot() < home.slot()
                        && facts.table_read_base_home(access) == Some(layout.base)
                        && builder
                            .expr(value, 0, home.slot(), None, false, true, None)
                            .is_some()
                }
                _ => false,
            }
        };
        if !decision.nodes.iter().all(|node| {
            matches!(node.test, HirExpr::TableAccess(_))
                && valid_value(&node.test, &mut builder)
                && [&node.truthy, &node.falsy]
                    .iter()
                    .all(|target| match target {
                        HirDecisionTarget::Expr(value) => valid_value(value, &mut builder),
                        HirDecisionTarget::CurrentValue | HirDecisionTarget::Node(_) => true,
                    })
        }) {
            return;
        }
        let Some(value) = super::super::super::decision::collapse_value_decision_expr(
            &crate::hir::decision::analyze_decision(decision),
            crate::hir::expr_safety::HirExprSafety::for_dialect(dialect),
            |_| true,
        ) else {
            return;
        };
        // 图归约不复制共享求值；原生 initializer 的前缀及后继声明义务仍由整批 preview 验证。
        plans.push(Plan {
            prefix_at_sink: false,
            luau_function_declaration: false,
            start: index,
            sink: index,
            base: home,
            values: vec![value].into(),
            result_locals: vec![*local],
            assignment_targets: Vec::new(),
            luau_compound_global: false,
            indexed_target: None,
            continuing_root: None,
            retained_copies: Vec::new(),
            replayed_effects: Vec::new(),
            removed: Vec::new(),
        });
    });
    (plans, count)
}

pub(super) fn collect(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> Vec<Plan> {
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
        dialect,
        &context.proto.body,
        &reads,
        &original_nil,
        &mut 0,
        &mut plans,
    );
    plans
}

#[expect(
    clippy::too_many_arguments,
    reason = "共享事实与 DFS 坐标贯穿同一次条件帧收集"
)]
fn collect_block(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
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
            collect_block(
                context,
                facts,
                dialect,
                child,
                reads,
                original_nil,
                cursor,
                plans,
            );
        });
        if matches!(stmt, HirStmt::Repeat(_)) {
            *cursor += 1;
        }
    }
    for (index, window) in block.stmts.windows(3).enumerate() {
        if dialect == DecompileDialect::Luau
            && let Some(mut plan) = boolean_return_plan(context, facts, window)
        {
            plan.start = starts[index];
            plan.sink = starts[index + 2];
            plan.removed = (plan.start..plan.sink).collect();
            // 原 TEST 由短路树重发；准备声明和合流写仍参与 missing epoch 检查。
            plan.replayed_effects.push(starts[index + 1]);
            let mut cursor = starts[index + 1] + 1;
            for_each_nested_block(&window[1], &mut |arm| {
                prefix::coordinates::visit(arm, &mut cursor, &mut |id, _, stmt| {
                    if matches!(stmt, HirStmt::If(_)) {
                        plan.replayed_effects.push(id);
                    }
                });
            });
            plans.push(plan);
        }
        if let Some(mut plan) = short_circuit_argument_plan(context, facts, dialect, window) {
            plan.start = starts[index];
            plan.sink = starts[index + 2];
            plan.removed = (plan.start..plan.sink).collect();
            // 控制头由参数值树重发；两臂的准备与结果写仍登记退休 epoch，
            // 后继读取不能借此次调用继续使用已被消费的旧合流值。
            plan.replayed_effects.push(starts[index + 1]);
            plans.push(plan);
        }
        if dialect == DecompileDialect::Luau
            && let Some(mut plan) = condition_plan(context, facts, window, reads, original_nil)
        {
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
    if dialect == DecompileDialect::Luau {
        let mut floor = 0;
        for (index, stmt) in block.stmts.iter().enumerate() {
            if let HirStmt::If(select) = stmt
                && let Some(HirStmt::CallStmt(sink)) = block.stmts.get(index + 1)
                && let Some(mut plan) = boolean_call_plan(
                    context,
                    facts,
                    &block.stmts[floor..index],
                    select,
                    &sink.call,
                )
            {
                plan.start = starts[floor + plan.start];
                plan.sink = starts[index + 1];
                plan.removed = (plan.start..plan.sink).collect();
                plan.replayed_effects.push(starts[index]);
                let mut cursor = starts[index] + 1;
                for_each_nested_block(stmt, &mut |arm| {
                    prefix::coordinates::visit(arm, &mut cursor, &mut |id, kind, stmt| {
                        if kind == PointKind::Statement && matches!(stmt, HirStmt::If(_)) {
                            plan.replayed_effects.push(id);
                        }
                    });
                });
                plans.push(plan);
            }
            if !matches!(stmt, HirStmt::LocalDecl(_) | HirStmt::Assign(_)) {
                floor = index + 1;
            }
        }
    }
    let mut preparation_start = 0;
    for (index, window) in block.stmts.windows(2).enumerate() {
        if index > 0
            && !matches!(
                block.stmts[index - 1],
                HirStmt::Assign(_) | HirStmt::LocalDecl(_)
            )
        {
            preparation_start = index;
        }
        let preparation = &block.stmts[preparation_start..index];
        if let Some(mut plan) =
            initializer_plan(context, facts, dialect, preparation, window, original_nil)
        {
            plan.start = starts[preparation_start + plan.start];
            plan.sink = starts[index];
            let end = starts.get(index + 2).copied().unwrap_or(*cursor);
            plan.removed = (plan.start..end).filter(|id| *id != plan.sink).collect();
            // 两臂只有已树化的结果写，声明本身留在原词法位置。
            plan.replayed_effects = (starts[index + 1]..end).collect();
            plans.push(plan);
            preparation_start = index + 1;
        }
    }
}

/// 入口 Boolean、分支内准备与单值 RETURN 共用原结果身份；一次消费整条短路链。
fn boolean_return_plan(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    window: &[HirStmt],
) -> Option<Plan> {
    let [initial_stmt, HirStmt::If(select), HirStmt::Return(ret)] = window else {
        return None;
    };
    let (target, HirExpr::Boolean(initial_value)) = scalar_local(initial_stmt)? else {
        return None;
    };
    let result = facts.fixed_return_input(ret, 0)?;
    let (initial, _, home, original) = facts.boolean_value_prewrite(result)?;
    if !matches!(initial_stmt, HirStmt::LocalDecl(_))
        || !plain_copy(initial_stmt)
        || ret.values.tail.is_some()
        || ret.values.fixed.as_slice() != [HirExpr::LocalRef(target)]
        || *initial_value != original
        || facts.promoted_local_for_temp(initial) != Some(target)
        || facts.promoted_local_for_temp(result) != Some(target)
        || facts.trusted_local_home_slot(target) != Some(home)
        || context.barred.contains(&home)
        || context.closed.contains(&home)
        || context.proto.local_debug_hints[target.index()].is_some()
        || context.proto.local_debug_scopes[target.index()].is_some()
        || context
            .proto
            .inline_dispositions
            .local(target)
            .must_preserve()
        || select.preserves_empty_test
        || !crate::hir::value_facts::value_facts(&select.cond).is_boolean()
    {
        // 候选拒绝[ProofIncomplete]：必须是同一原预写/返回结果，独立源码声明不可退休。
        return None;
    }
    let value = prepared_boolean_value(context, facts, select, target, home, original, result)?;
    let mut builder = frame_builder(context, &[], facts, DecompileDialect::Luau, home.slot())?;
    let value = builder.luau_logical_value(&value, 0, home, None)?;
    Some(value_plan(home, value))
}

fn prepared_boolean_value(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    select: &crate::hir::common::HirIf,
    target: LocalId,
    home: HomeSlotKey,
    original: bool,
    result: TempId,
) -> Option<HirExpr> {
    let (selected, inverted) = if select.then_block.stmts.is_empty() {
        (select.else_block.as_ref()?, true)
    } else if select
        .else_block
        .as_ref()
        .is_none_or(|arm| arm.stmts.is_empty())
    {
        (&select.then_block, false)
    } else {
        return None;
    };
    let condition = select.cond.clone();
    let condition = if original ^ inverted {
        condition.negate()
    } else {
        condition
    };
    let value = prepared_boolean_arm(context, facts, selected, target, home, result)?;
    let logical = Box::new(crate::hir::common::HirLogicalExpr {
        lhs: condition,
        rhs: value,
        preserves_boolean_prewrite: false,
    });
    let value = if original {
        HirExpr::LogicalOr(logical)
    } else {
        HirExpr::LogicalAnd(logical)
    };
    // 外层 RETURN/CALL 一次核对完整值树；递归层只核对自己的准备，不重复扫描已恢复的后缀。
    Some(value)
}

/// 普通 CALL 的 callee、Boolean 预写和条件域一并重放；不把参数预写移到 callee 之前。
fn boolean_call_plan(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    preparation: &[HirStmt],
    select: &crate::hir::common::HirIf,
    call: &HirCallExpr,
) -> Option<Plan> {
    let ([HirExpr::LocalRef(target)], None) = (call.args.fixed.as_slice(), &call.args.tail) else {
        return None;
    };
    let prewrite = facts.boolean_argument_prewrite(call, 0)?;
    let frame = facts.native_call_frame(call)?;
    if call.fastcall.is_some()
        || call.method != HirMethodCall::None
        || facts.promoted_local_for_temp(prewrite.initial) != Some(*target)
        || facts.promoted_local_for_temp(prewrite.result) != Some(*target)
        || !prewrite.reference_uncaptured
        || !frame.arguments_unaliased
        || frame.results != Some(ResultPack::Ignore)
        || prewrite.home.slot() != frame.home.slot() + 1
        || facts.trusted_local_home_slot(*target) != Some(prewrite.home)
        || context.closed.contains(&prewrite.home)
        || context.proto.local_debug_hints[target.index()].is_some()
        || context.proto.local_debug_scopes[target.index()].is_some()
        || select.preserves_empty_test
        || !crate::hir::value_facts::value_facts(&select.cond).is_boolean()
    {
        return None;
    }
    let value = prepared_boolean_value(
        context,
        facts,
        select,
        *target,
        prewrite.home,
        prewrite.initial_value,
        prewrite.result,
    )?;
    let mut rebuilt = call.clone();
    rebuilt.args.fixed[0] = value;
    let run = preparation.iter().collect::<Vec<_>>();
    let mut builder = frame_builder(
        context,
        &run,
        facts,
        DecompileDialect::Luau,
        frame.home.slot(),
    )?;
    let rebuilt = builder.call(
        &rebuilt,
        run.len(),
        frame.home.slot(),
        true,
        CallWidth::Ignore,
    )?;
    if builder.next_event != run.len() {
        return None;
    }
    let mut plan = value_plan(frame.home, HirExpr::Call(Box::new(rebuilt)));
    plan.start = builder.first_event?;
    Some(plan)
}

fn prepared_boolean_arm(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    block: &HirBlock,
    target: LocalId,
    home: HomeSlotKey,
    result: TempId,
) -> Option<HirExpr> {
    if let [initial, HirStmt::If(select)] = block.stmts.as_slice()
        && !select.preserves_empty_test
        && let HirExpr::Binary(condition) = &select.cond
        && let Some((producer, value)) = condition
            .source_site
            .and_then(|site| facts.boolean_branch_prewrite(result, site))
        && scalar_local(initial) == Some((target, &HirExpr::Boolean(value)))
        && plain_copy(initial)
        && facts.promoted_local_for_temp(producer) == Some(target)
        && facts.trusted_local_home_slot(target) == Some(home)
    {
        return prepared_boolean_value(context, facts, select, target, home, value, result);
    }
    let (last, preparation) = block.stmts.split_last()?;
    if !preparation
        .iter()
        .all(|stmt| scalar_local(stmt).is_some() && plain_copy(stmt))
    {
        // 候选拒绝[SemanticBarrier:EvalOrder]：准备区必须完整地进入当前路径的表达式。
        return None;
    }
    let result_value = |stmt: &HirStmt| {
        matches!(stmt, HirStmt::Assign(assign)
            if assign.initializer_merge_transaction.is_none()
                && assign.generic_for_initializer_producer.is_none()
                && assign.root_release.is_none()
                && assign.method_rewrite_transaction.is_none())
            && scalar_local(stmt).is_some_and(|(local, _)| local == target)
    };
    let run = preparation.iter().collect::<Vec<_>>();
    let mut builder = frame_builder(context, &run, facts, DecompileDialect::Luau, home.slot())?;
    builder.boolean_frame = Some(home);
    let (value, continuation) = match last {
        HirStmt::If(select) if !select.preserves_empty_test => {
            let skipped = |block: &HirBlock| {
                matches!(block.stmts.as_slice(), [stmt]
                if result_value(stmt) && scalar_local(stmt).is_some_and(|(_, value)| *value == select.cond))
            };
            let (continuation, and) = if skipped(select.else_block.as_ref()?) {
                (&select.then_block, true)
            } else if skipped(&select.then_block) {
                (select.else_block.as_ref()?, false)
            } else {
                return None;
            };
            (&select.cond, Some((continuation, and)))
        }
        stmt if result_value(stmt) => (scalar_local(stmt)?.1, None),
        _ => return None,
    };
    let value = builder.expr(value, run.len(), home.slot(), None, false, true, None)?;
    if builder.first_event != (!run.is_empty()).then_some(0) || builder.next_event != run.len() {
        return None;
    }
    if let Some((continuation, and)) = continuation {
        let rhs = prepared_boolean_arm(context, facts, continuation, target, home, result)?;
        let logical = Box::new(crate::hir::common::HirLogicalExpr {
            lhs: value,
            rhs,
            preserves_boolean_prewrite: false,
        });
        Some(if and {
            HirExpr::LogicalAnd(logical)
        } else {
            HirExpr::LogicalOr(logical)
        })
    } else {
        Some(value)
    }
}

/// callee 已先准备、条件两臂共同写入原参数槽；整帧消费分支结果而不创建独立声明。
fn short_circuit_argument_plan(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    window: &[HirStmt],
) -> Option<Plan> {
    let [
        preparation,
        HirStmt::If(select),
        HirStmt::CallStmt(consumer),
    ] = window
    else {
        return None;
    };
    // 候选拒绝[TargetConstraint]：此处核对 JIT 的单参数结果槽与帧空洞；
    // Luau 的预写和其它 VM 的条件物化继续由各自的完整协议消费。
    if dialect != DecompileDialect::Luajit || select.preserves_empty_test {
        return None;
    }
    let call = &consumer.call;
    let ([HirExpr::LocalRef(result)], None) = (call.args.fixed.as_slice(), &call.args.tail) else {
        return None;
    };
    let frame = facts.native_call_frame(call)?;
    let original = facts.call_argument_value(call, 0)?;
    let home = facts.trusted_temp_home_slot(original)?;
    // 候选拒绝[ProofIncomplete]：参数必须仍是原合流身份，不能从同槽的另一个值版本推断。
    if !facts.is_phi_carrier_temp(original)
        || facts.promoted_local_for_temp(original) != Some(*result)
        || facts.trusted_local_home_slot(*result) != Some(home)
        || !frame.arguments_unaliased
        || context.barred.contains(&home)
        || context.closed.contains(&home)
        || context.proto.local_debug_hints[result.index()].is_some()
        || context.proto.local_debug_scopes[result.index()].is_some()
        || matches!(context.proto.inline_dispositions.local(*result),
            crate::hir::common::HirInlineDisposition::Preserve(reasons)
                if reasons.iter().any(|reason| *reason != HirInlineRetentionReason::PhysicalFramePrefix))
    {
        return None;
    }
    fn result_value(stmt: &HirStmt, result: LocalId) -> Option<&HirExpr> {
        let HirStmt::Assign(assign) = stmt else {
            return None;
        };
        let (local, value) = scalar_local(stmt)?;
        // 两臂末端是 Structure 的合流转交，表达式中仍重发原 producer；
        // 不把写入已有源码变量的普通赋值当成可退休的参数结果。
        (local == result
            && assign.is_phi_transfer
            && assign.initializer_merge_transaction.is_none()
            && assign.generic_for_initializer_producer.is_none()
            && assign.root_release.is_none()
            && assign.method_rewrite_transaction.is_none())
        .then_some(value)
    }
    let false_arm = |block: &HirBlock| matches!(block.stmts.as_slice(), [stmt] if result_value(stmt, *result) == Some(&HirExpr::Boolean(false)));
    let (selected, inverted) = if false_arm(&select.then_block) {
        (select.else_block.as_ref()?, true)
    } else if false_arm(select.else_block.as_ref()?) {
        (&select.then_block, false)
    } else {
        return None;
    };
    let (last, arm_preparation) = selected.stmts.split_last()?;
    let value = result_value(last, *result)?;
    // 候选拒绝[ProofIncomplete]：值臂只接同一次单结果 CALL；额外控制或独立写不能被树化掉。
    if !matches!(value, HirExpr::Call(_))
        || !arm_preparation
            .iter()
            .all(|stmt| scalar_local(stmt).is_some() && plain_copy(stmt))
        || !crate::hir::value_facts::value_facts(&select.cond).is_boolean()
    {
        return None;
    }
    let run = arm_preparation.iter().collect::<Vec<_>>();
    let mut arm = frame_builder(context, &run, facts, dialect, frame.home.slot())?;
    let value = arm.expr(value, run.len(), home.slot(), None, false, true, None)?;
    if arm.first_event != (!run.is_empty()).then_some(0) || arm.next_event != run.len() {
        // 候选拒绝[SemanticBarrier:EvalOrder]：每条分支内准备都必须按原顺序由结果表达式消费。
        return None;
    }
    let (condition, not_depth) = synthetic_not_subject(&select.cond);
    let condition = if (not_depth % 2 != 0) ^ inverted {
        condition.clone().negate()
    } else {
        condition.clone()
    };
    let mut rebuilt = call.clone();
    rebuilt.args.fixed[0] = HirExpr::LogicalAnd(Box::new(crate::hir::common::HirLogicalExpr {
        preserves_boolean_prewrite: false,
        lhs: condition,
        rhs: value,
    }));
    let run = [preparation];
    let mut builder = frame_builder(context, &run, facts, dialect, frame.home.slot())?;
    builder.boolean_frame = Some(home);
    let rebuilt = builder.call(
        &rebuilt,
        run.len(),
        frame.home.slot(),
        true,
        CallWidth::Ignore,
    )?;
    if builder.first_event != Some(0) || builder.next_event != run.len() {
        // 候选拒绝[ProofIncomplete]：callee 准备必须属于同一原帧，不能遗留独立声明或跳过事件。
        return None;
    }
    Some(value_plan(frame.home, HirExpr::Call(Box::new(rebuilt))))
}

fn initializer_plan(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    preparation: &[HirStmt],
    window: &[HirStmt],
    original_nil: &BTreeSet<LocalId>,
) -> Option<Plan> {
    let [previous, HirStmt::If(select)] = window else {
        return None;
    };
    let (result, empty, declaration) = match previous {
        HirStmt::LocalDecl(decl)
            if decl.bindings.len() == 1 && decl.initializer_merge_transaction.is_none() =>
        {
            (decl.bindings[0], decl.values.is_empty(), true)
        }
        HirStmt::Assign(assign) if assign.initializer_merge_transaction.is_none() => {
            let (local, _) = scalar_local(previous)?;
            (local, false, false)
        }
        _ => return None,
    };
    let result = &result;
    let base = facts.trusted_local_home_slot(*result)?;
    if original_nil.contains(result)
        || select.preserves_empty_test
        || context.barred.contains(&base)
        || context.closed.contains(&base)
    {
        return None;
    }
    if declaration && let Some(scope) = context.proto.local_debug_scopes[result.index()] {
        let initializer = context.proto.debug_scopes[scope]?.initializer_phi?;
        // 原来已生效的空声明仍独立保留；只有 scope 自身从该合流结果开始才恢复 initializer。
        if facts.promoted_local_for_temp(initializer) != Some(*result)
            || facts.trusted_temp_home_slot(initializer) != Some(base)
        {
            return None;
        }
    }
    // 原比较与 Boolean 合流在同一结果槽重发，声明身份保持不动。
    // 与普通 boolean-shells 不同，这里由完整帧预览核对 operand scratch 和后缀根。
    if let HirExpr::Binary(binary) = &select.cond
        && let Some(temp) = facts.comparison_result_temp(binary)
        && facts.promoted_local_for_temp(temp) == Some(*result)
        && facts.trusted_temp_home_slot(temp) == Some(base)
    {
        let boolean_arm = |block: &HirBlock| {
            let [HirStmt::Assign(assign)] = block.stmts.as_slice() else {
                return None;
            };
            match (
                assign.targets.as_slice(),
                assign.values.fixed.as_slice(),
                &assign.values.tail,
            ) {
                ([HirLValue::Local(target)], [HirExpr::Boolean(value)], None)
                    if target == result =>
                {
                    Some(*value)
                }
                _ => None,
            }
        };
        if boolean_arm(&select.then_block) == Some(true)
            && boolean_arm(select.else_block.as_ref()?) == Some(false)
        {
            let mut run = preparation.iter().collect::<Vec<_>>();
            if !empty {
                run.push(previous);
            }
            let mut builder = frame_builder(context, &run, facts, dialect, base.slot())?;
            let value = builder.expr(
                &select.cond,
                run.len(),
                base.slot(),
                None,
                false,
                true,
                None,
            )?;
            if (builder.first_event.is_some() || !empty) && builder.next_event != run.len() {
                return None;
            }
            let mut plan = value_plan(base, value);
            plan.start = builder.first_event.unwrap_or(run.len());
            if declaration {
                plan.result_locals.push(*result);
            } else {
                plan.assignment_targets.push(HirLValue::Local(*result));
            }
            return Some(plan);
        }
    }
    if dialect != DecompileDialect::Luau || !empty {
        return None;
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
            builder.luau_logical_value(value, 0, base, None)
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
    plan.start = preparation.len();
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
        source_result: None,
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
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: 0,
        sink: 0,
        base,
        values: vec![value].into(),
        result_locals: Vec::new(),
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
