//! 配对数值 repeat 的原计数轨迹和完整观察调用帧。
//! 模板只导航候选，原 COPY、循环协议、输入分配与操作 home 共同签证。

use super::super::assignments::plain_copy;
use super::*;
use crate::hir::common::{HirBinaryExpr, HirBinaryOpKind, HirSourceSite};
use crate::hir::luau_inlining::{NumericRepeatTemplate, small_integer};

pub(super) struct Recovered {
    /// 根块序号，交由 expanded 的统一转换发布为 DFS 坐标。
    pub plans: Vec<Plan>,
    /// 已使用 ValueUses 当前快照的 DFS 坐标，包含各层比较调用。
    pub nested_plans: Vec<Plan>,
    /// 来自原返回 COPY 的低槽，不从恢复后表达式的位置推算。
    pub result_slots: BTreeMap<HirSourceSite, usize>,
}

fn chain(expr: &HirExpr) -> Option<(i64, Vec<i64>, &HirBinaryExpr)> {
    let HirExpr::Binary(last) = expr else {
        return None;
    };
    let mut current = expr;
    let mut updates = Vec::new();
    while let HirExpr::Binary(binary) = current {
        if binary.op != HirBinaryOpKind::Add || binary.source_site.is_none() || updates.len() >= 50
        {
            // 候选搜索裁剪[ResourceLimit]：pinned 编译器最多展开25轮，每轮两次更新。
            return None;
        }
        updates.push(small_integer(&binary.rhs)?);
        current = &binary.lhs;
    }
    updates.reverse();
    Some((small_integer(current)?, updates, last))
}

fn chain_layout(mut expr: &HirExpr, facts: &ProtoPromotionFacts, home: HomeSlotKey) -> Option<()> {
    // 这里重放写回同一状态的原 ADD 序列，不把它作为可被 O2 折叠的
    // 常量表达式签证；每一条输入仍由原 use→Def 与准备指令连接。
    while let HirExpr::Binary(binary) = expr {
        let site = binary.source_site?;
        let layout = facts.native_binary_layout(binary)?;
        let (_, input_home) = facts.binary_operand_preparation(binary, 0, &binary.lhs)?;
        if layout.lhs != Some(home)
            || layout.rhs.is_some()
            || input_home != home
            || facts.operation_result_home(site) != Some(home)
            || !facts.operation_result_reference_unaliased(site)
            || !facts.temp_definition_is_uncaptured(facts.operation_result_temp(site)?)
        {
            // 候选拒绝[ProofIncomplete]：链中任一原输入、结果槽或捕获身份未被签证。
            return None;
        }
        expr = &binary.lhs;
    }
    Some(())
}

fn lookup_loop<'a>(
    loop_: &'a crate::hir::HirNumericFor,
    state: LocalId,
    input: LocalId,
    facts: &ProtoPromotionFacts,
) -> Option<&'a HirBinaryExpr> {
    let home = facts.trusted_local_home_slot(state)?;
    let input_home = facts.trusted_local_home_slot(input)?;
    let [update, HirStmt::If(branch)] = loop_.body.stmts.as_slice() else {
        return None;
    };
    let (target, HirExpr::Binary(binary)) = scalar_local(update)? else {
        return None;
    };
    let HirExpr::TableAccess(access) = &branch.cond else {
        return None;
    };
    let crate::hir::common::HirOperationSources::Single(read) = access.sources else {
        return None;
    };
    let layout = facts.native_table_read_layout(access)?;
    let result_home = HomeSlotKey::new(home.slot() + 4, 0);
    let frame = facts.numeric_for_body_frame(loop_)?;
    if target != state
        || binary.op != HirBinaryOpKind::Add
        || binary.lhs != HirExpr::LocalRef(state)
        || !repeat_prefix::update_layout(binary, facts, home)
        || access.base != HirExpr::LocalRef(input)
        || access.key != HirExpr::LocalRef(state)
        || layout.base != input_home
        || layout.key != Some(home)
        || facts.table_read_result_home(access) != Some(result_home)
        || !matches!(branch.then_block.stmts.as_slice(), [HirStmt::Continue])
        || branch
            .else_block
            .as_ref()
            .is_some_and(|block| !block.stmts.is_empty())
        || branch
            .predicate_source
            .and_then(|site| facts.original_truthy_input(site))
            != Some((facts.operation_result_temp(read)?, result_home))
        || frame.controls_len != 2
        || frame.binding_slot != home.slot() + 3
        || frame.controls != [1, 2, 3].map(|offset| HomeSlotKey::new(home.slot() + offset, 0))
    {
        // 候选拒绝[ProofIncomplete]：索引结果的 TEST、数值循环协议与原计数更新未形成同一帧。
        return None;
    }
    Some(binary)
}

pub(super) fn plans(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    templates: &[Option<NumericRepeatTemplate>],
) -> Recovered {
    let mut result = Recovered {
        plans: Vec::new(),
        nested_plans: Vec::new(),
        result_slots: BTreeMap::new(),
    };
    let mut unrolled = BTreeMap::new();
    let mut loops = BTreeMap::new();
    for callee in context
        .expanded_callees
        .into_iter()
        .flat_map(|items| items.values())
    {
        let HirLuauInliningBody::NumericRepeat { template } = callee.body else {
            continue;
        };
        let Some(shape) = templates[template] else {
            continue;
        };
        if let Some(count) = crate::hir::luau_loop_cost::trips(shape.start, shape.limit, shape.step)
            && (1..=25).contains(&count)
        {
            let updates = (0..count)
                .flat_map(|_| [shape.increment, shape.tail_increment])
                .collect::<Vec<_>>();
            unrolled
                .entry((shape.initial, updates))
                .and_modify(|known| *known = None)
                .or_insert(Some(callee));
        }
        loops
            .entry((
                shape.initial,
                shape.start,
                shape.limit,
                shape.step,
                shape.increment,
            ))
            .and_modify(|known| *known = None)
            .or_insert(Some(callee));
    }
    if unrolled.is_empty() && loops.is_empty() {
        return result;
    }
    let mut captured = CaptureCollector::new(HirCaptureMode::ByValue);
    crate::hir::visit::visit_stmts(&context.proto.body.stmts, &mut captured);
    let mut references = CaptureCollector::new(HirCaptureMode::ByReference);
    crate::hir::visit::visit_stmts(&context.proto.body.stmts, &mut references);
    captured
        .bindings
        .locals
        .extend(references.bindings.locals.iter().copied());
    captured
        .bindings
        .temps
        .extend(references.bindings.temps.iter().copied());
    let copies = facts
        .result_copy_frames()
        .fold(BTreeMap::new(), |mut copies, copy| {
            copies
                .entry(copy.target)
                .and_modify(|known| *known = None)
                .or_insert(Some(copy));
            copies
        });
    let stmts = &context.proto.body.stmts;
    for (sink, stmt) in stmts.iter().enumerate() {
        let candidate = (|| {
            let HirStmt::CallStmt(statement) = stmt else {
                return None;
            };
            let call = &statement.call;
            let frame = facts.native_call_frame(call)?;
            if call.args.fixed.len() != 2
                || call.args.tail.is_some()
                || call.fastcall.is_some()
                || frame.results != Some(ResultPack::Ignore)
                || !frame.arguments_unaliased
            {
                return None;
            }
            let copy = *copies.get(&facts.call_argument_value(call, 1)?)?.as_ref()?;
            let base = HomeSlotKey::new(frame.home.slot() + 2, 0);
            let input_home = HomeSlotKey::new(base.slot() + 1, 0);
            let state_home = HomeSlotKey::new(base.slot() + 2, 0);
            if copy.target_home != base || copy.source_home != state_home {
                return None;
            }
            let before = sink.checked_sub(1)?;
            let (start, callee, input, argument, state, site, active, replayed) =
                if let HirStmt::NumericFor(loop_) = &stmts[before] {
                    let initial_at = before.checked_sub(1)?;
                    let (state, initial) = scalar_local(&stmts[initial_at])?;
                    let input_at = initial_at.checked_sub(1)?;
                    let (input, argument @ HirExpr::TableConstructor(_)) =
                        scalar_local(&stmts[input_at])?
                    else {
                        return None;
                    };
                    let update = lookup_loop(loop_, state, input, facts)?;
                    let mut bounds = [0; 3];
                    for (offset, ((expr, home), original)) in
                        [&loop_.start, &loop_.limit, &loop_.step]
                            .into_iter()
                            .zip(loop_.control_homes)
                            .zip(loop_.control_values)
                            .enumerate()
                    {
                        // prepare_source_frames 已消费 header 的独立准备；使用保留的
                        // control_values/home 核对当前字面量头，不重建另一份控制槽分析。
                        if facts.trusted_temp_home_slot(original?) != Some(home) {
                            return None;
                        }
                        bounds[offset] = small_integer(expr)?;
                    }
                    let key = (
                        small_integer(initial)?,
                        bounds[0],
                        bounds[1],
                        bounds[2],
                        small_integer(&update.rhs)?,
                    );
                    let callee = *loops.get(&key)?.as_ref()?;
                    if !plain_copy(&stmts[initial_at]) {
                        return None;
                    }
                    (
                        input_at.checked_sub(2)?,
                        callee,
                        input,
                        argument,
                        state,
                        update.source_site?,
                        true,
                        vec![before],
                    )
                } else {
                    let (state, value) = scalar_local(&stmts[before])?;
                    let (initial, updates, binary) = chain(value)?;
                    let callee = *unrolled.get(&(initial, updates))?.as_ref()?;
                    let site = binary.source_site?;
                    let input_at = before.checked_sub(1)?;
                    let (input, argument @ HirExpr::TableConstructor(_)) =
                        scalar_local(&stmts[input_at])?
                    else {
                        return None;
                    };
                    if copy.source != facts.operation_result_temp(site)
                        || facts.operation_result_home(site) != Some(state_home)
                        || !facts.operation_result_reference_unaliased(site)
                        || !plain_copy(&stmts[before])
                    {
                        return None;
                    }
                    chain_layout(value, facts, state_home)?;
                    (
                        input_at.checked_sub(2)?,
                        callee,
                        input,
                        argument,
                        state,
                        site,
                        false,
                        Vec::new(),
                    )
                };
            if start <= callee.declaration
                || call.args.fixed[1] != HirExpr::LocalRef(state)
                || facts.trusted_local_home_slot(input) != Some(input_home)
                || facts.trusted_local_home_slot(state) != Some(state_home)
                || [input, state].iter().any(|local| {
                    context.proto.local_debug_hints[local.index()].is_some()
                        || context.proto.local_debug_scopes[local.index()].is_some()
                })
                || (frame.home.slot()..=state_home.slot() + if active { 4 } else { 0 }).any(
                    |slot| {
                        let home = HomeSlotKey::new(slot, 0);
                        // 后继按值捕获可以复用此槽；原引用别名证书及当前捕获身份
                        // 共同排除状态自身被捕获。不能只凭槽号把新值的捕获回溯到旧值。
                        context.closed.contains(&home)
                            || context.barred.contains(&home)
                                && !(home == state_home
                                    && facts.local_definitions_reference_unaliased(state)
                                    && !captured.bindings.locals.contains(&state)
                                    && copy.source.is_some_and(|source| {
                                        !captured.bindings.temps.contains(&source)
                                    }))
                    },
                )
            {
                // 候选拒绝[ProofIncomplete]：debug、闭合或捕获身份仍需要原声明，不能仅按槽号退休。
                return None;
            }
            let HirExpr::TableConstructor(table) = argument else {
                return None;
            };
            if facts.allocation_result_home(table) != Some(input_home)
                || !facts.allocation_result_reference_unaliased(table)
            {
                return None;
            }
            let prefix = [&stmts[start], &stmts[start + 1]];
            let mut builder = frame_builder(
                context,
                &prefix,
                facts,
                DecompileDialect::Luau,
                frame.home.slot(),
            )?;
            let global = builder.expr(
                &call.callee,
                prefix.len(),
                frame.home.slot(),
                None,
                true,
                false,
                Some(frame.callee),
            )?;
            let label = builder.expr(
                &call.args.fixed[0],
                prefix.len(),
                frame.home.slot() + 1,
                None,
                false,
                true,
                facts.call_argument_value(call, 0),
            )?;
            if !matches!(&global,HirExpr::GlobalRef(global) if global.key.as_utf8()==Some("print"))
                || !matches!(label, HirExpr::String(_))
                || builder.first_event != Some(0)
                || builder.next_event != prefix.len()
            {
                return None;
            }
            let mut builder =
                frame_builder(context, &[], facts, DecompileDialect::Luau, base.slot())?;
            let argument = builder.expr(argument, 0, input_home.slot(), None, false, true, None)?;
            let invocation = factories::factory_call(
                callee.local,
                Some(site),
                vec![HirExpr::Boolean(active), HirExpr::Boolean(true), argument].into(),
            );
            let mut restored = call.clone();
            restored.callee = global;
            restored.args = vec![label, invocation].into();
            Some((
                site,
                base.slot(),
                Plan {
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
                },
            ))
        })();
        if let Some((site, slot, plan)) = candidate {
            result.result_slots.insert(site, slot);
            result.plans.push(plan);
        }
    }
    let uses = super::value_uses::ValueUses::new(context.proto);
    let mut iteration_inputs = BTreeSet::new();
    for &(_, stmt) in &uses.points {
        if let HirStmt::GenericFor(loop_) = stmt
            && facts.generic_for_body_frame(loop_).is_some()
        {
            for result in &loop_.dispatch_results {
                // success binding 由原 dispatch Def 建立；通用 local 合并中包含
                // loop phi 时，直接消费原结果身份，并要求当前循环绑定没有后续写入。
                if uses.writes(result.success_binding) == 1
                    && facts.temp_definition_reference_unaliased(result.result_def)
                    && !references.bindings.locals.contains(&result.success_binding)
                    && !references.bindings.temps.contains(&result.result_def)
                {
                    iteration_inputs.insert(result.success_binding);
                }
            }
        }
    }
    let mut blocks = vec![uses.tree.root_block()];
    while let Some(block) = blocks.pop() {
        let ids = uses.tree.block(block);
        for &id in ids {
            blocks.extend(uses.tree.stmt(id).children.iter().copied());
        }
        let stmts: Vec<_> = ids.iter().map(|id| uses.points[id.index()].1).collect();
        for sink in 3..stmts.len() {
            let candidate = (|| {
                let HirStmt::CallStmt(statement) = stmts[sink] else {
                    return None;
                };
                let frame = counter_while::assertion_frame(
                    &statement.call,
                    stmts[sink - 1],
                    stmts[sink - 2],
                    facts,
                )?;
                let state_home = HomeSlotKey::new(frame.base.slot() + 3, 0);
                let result_home = HomeSlotKey::new(frame.base.slot() + 2, 0);
                let mut before = sink - 3;
                let mut value = &frame.compare.lhs;
                if let Some((target, copied @ HirExpr::LocalRef(_))) = scalar_local(stmts[before])
                    && *value == HirExpr::LocalRef(target)
                {
                    if facts.promoted_local_for_temp(frame.result) != Some(target)
                        || !plain_copy(stmts[before])
                    {
                        return None;
                    }
                    value = copied;
                    before = before.checked_sub(1)?;
                }
                let (start, callee, site, arguments, loop_at) =
                    if let HirStmt::NumericFor(loop_) = stmts[before] {
                        let first = before.checked_sub(1)?;
                        let (state, initial) = scalar_local(stmts[first])?;
                        if *value != HirExpr::LocalRef(state)
                            || facts.trusted_local_home_slot(state) != Some(state_home)
                            || !plain_copy(stmts[first])
                        {
                            return None;
                        }
                        let (update, condition, input) = dynamic_loop(loop_, state, facts)?;
                        let key = (
                            small_integer(initial)?,
                            small_integer(&loop_.start)?,
                            small_integer(&loop_.limit)?,
                            small_integer(&loop_.step)?,
                            small_integer(&update.rhs)?,
                        );
                        let callee = *loops.get(&key)?.as_ref()?;
                        for local in [condition, input] {
                            if facts.trusted_local_home_slot(local)?.slot() >= frame.base.slot()
                                || !(facts.local_definitions_reference_unaliased(local)
                                    || iteration_inputs.contains(&local))
                            {
                                return None;
                            }
                        }
                        (
                            first,
                            callee,
                            update.source_site?,
                            vec![
                                HirExpr::Boolean(true),
                                HirExpr::LocalRef(condition),
                                HirExpr::LocalRef(input),
                            ],
                            Some(before),
                        )
                    } else {
                        let (target, expression) = scalar_local(stmts[before])?;
                        let (initial, updates, last) = chain(expression)?;
                        let callee = *unrolled.get(&(initial, updates))?.as_ref()?;
                        let site = last.source_site?;
                        if *value != HirExpr::LocalRef(target)
                            || facts.promoted_local_for_temp(frame.result) != Some(target)
                            || facts.trusted_local_home_slot(target) != Some(result_home)
                            || facts.operation_result_temp(site) != Some(frame.source)
                            || !plain_copy(stmts[before])
                        {
                            return None;
                        }
                        chain_layout(expression, facts, state_home)?;
                        // 首参数为 false 时，模板中第三参数的全部读取都被原编译器擦除。
                        // nil 只代表这一无操作实参；原有的其它声明仍由后缀事务保留。
                        (
                            before,
                            callee,
                            site,
                            vec![
                                HirExpr::Boolean(false),
                                HirExpr::Boolean(true),
                                HirExpr::Nil,
                            ],
                            None,
                        )
                    };
                if callee.creation.instr >= site.instr {
                    return None;
                }
                let end = state_home.slot() + if loop_at.is_some() { 4 } else { 0 };
                if (frame.base.slot()..=end).any(|slot| {
                    let home = HomeSlotKey::new(slot, 0);
                    context.closed.contains(&home)
                        || context.barred.contains(&home)
                            && !(home == state_home
                                && loop_at.is_none()
                                && facts.temp_definition_is_uncaptured(frame.source))
                }) {
                    // 候选拒绝[ProofIncomplete]：比较调用的 scratch 区仍与未退休身份共享。
                    return None;
                }
                let mut builder = frame_builder(
                    context,
                    &[],
                    facts,
                    DecompileDialect::Luau,
                    frame.base.slot(),
                )?;
                let global = builder.expr(
                    frame.global,
                    0,
                    frame.base.slot(),
                    None,
                    true,
                    false,
                    Some(facts.native_fastcall_frame(frame.call)?.callee),
                )?;
                let mut compare = frame.compare.clone();
                compare.lhs = factories::factory_call(callee.local, Some(site), arguments.into());
                let mut call = frame.call.clone();
                call.callee = global;
                call.args = vec![HirExpr::Binary(Box::new(compare))].into();
                let coordinate = |ordinal: usize| uses.points[ids[ordinal].index()].0;
                let mut replayed = Vec::new();
                if let Some(loop_at) = loop_at {
                    replayed.extend(coordinate(loop_at)..coordinate(loop_at + 1));
                }
                Some((
                    site,
                    result_home.slot(),
                    Plan {
                        prefix_at_sink: false,
                        luau_function_declaration: false,
                        start: coordinate(start),
                        sink: coordinate(sink),
                        base: frame.base,
                        values: vec![HirExpr::Call(Box::new(call))].into(),
                        result_locals: Vec::new(),
                        assignment_targets: Vec::new(),
                        luau_compound_global: false,
                        indexed_target: None,
                        continuing_root: None,
                        retained_copies: Vec::new(),
                        replayed_effects: replayed,
                        removed: (coordinate(start)..coordinate(sink)).collect(),
                    },
                ))
            })();
            if let Some((site, slot, plan)) = candidate {
                result.result_slots.insert(site, slot);
                result.nested_plans.push(plan);
            }
        }
    }
    result
}

fn dynamic_loop<'a>(
    loop_: &'a crate::hir::HirNumericFor,
    state: LocalId,
    facts: &ProtoPromotionFacts,
) -> Option<(&'a HirBinaryExpr, LocalId, LocalId)> {
    let [update, HirStmt::While(repeat)] = loop_.body.stmts.as_slice() else {
        return None;
    };
    let (target, HirExpr::Binary(binary)) = scalar_local(update)? else {
        return None;
    };
    let HirExpr::LogicalAnd(condition) = &repeat.cond else {
        return None;
    };
    let (HirExpr::Unary(left), HirExpr::Unary(right)) = (&condition.lhs, &condition.rhs) else {
        return None;
    };
    let (HirExpr::TableAccess(access), HirExpr::LocalRef(condition)) = (&left.expr, &right.expr)
    else {
        return None;
    };
    let HirExpr::LocalRef(input) = access.base else {
        return None;
    };
    let home = facts.trusted_local_home_slot(state)?;
    let layout = facts.native_table_read_layout(access)?;
    let frame = facts.numeric_for_body_frame(loop_)?;
    if target != state
        || binary.op != HirBinaryOpKind::Add
        || binary.lhs != HirExpr::LocalRef(state)
        || !repeat_prefix::update_layout(binary, facts, home)
        || !repeat.body.stmts.is_empty()
        || left.op != crate::hir::HirUnaryOpKind::Not
        || right.op != crate::hir::HirUnaryOpKind::Not
        || left.source_site.is_some()
        || right.source_site.is_some()
        || access.key != HirExpr::LocalRef(state)
        || layout.key != Some(home)
        || layout.base != facts.trusted_local_home_slot(input)?
        || facts.table_read_result_home(access) != Some(HomeSlotKey::new(home.slot() + 4, 0))
        || frame.controls_len != 2
        || frame.binding_slot != home.slot() + 3
        || frame.controls != [1, 2, 3].map(|offset| HomeSlotKey::new(home.slot() + offset, 0))
    {
        return None;
    }
    for (home, original) in loop_.control_homes.into_iter().zip(loop_.control_values) {
        if facts.trusted_temp_home_slot(original?) != Some(home) {
            return None;
        }
    }
    Some((binary, *condition, input))
}
