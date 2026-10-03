//! 恢复 generic-for 的完整初始化值包，并联合消费 dispatch 根释放。
//! 消费原 producer occurrence 与控制槽事实；调用和固定值包共用 native 原子预览。

use super::*;
use crate::hir::simplify::generic_for_iterators;

/// initializer CALL 与 dispatch root endpoints 属于同一循环头事务。
/// marker 只提供原配对；完整 CALL、控制槽、成功结果槽及最终声明前缀仍分别核对。
pub(super) fn plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    for_: &crate::hir::common::HirGenericFor,
) -> Option<Plan> {
    let frame = facts.generic_for_body_frame(for_)?;
    let dispatch = for_.body_frame_source?;
    let base = *frame.initializers.first()?;
    let results = for_
        .dispatch_results
        .iter()
        .zip(&frame.bindings)
        .map(|(result, home)| (result.result_def, *home))
        .collect::<BTreeMap<_, _>>();
    let mut seen_results = BTreeSet::new();
    let mut release_start = run.len();
    while let Some(HirStmt::Assign(assign)) = release_start.checked_sub(1).map(|index| run[index]) {
        let Some(crate::hir::common::HirRootRelease::GenericForDispatch(release)) =
            &assign.root_release
        else {
            break;
        };
        let home = *results.get(&release.result_def)?;
        let target_matches = match assign.targets.as_slice() {
            [HirLValue::Temp(temp)] => *temp == release.released,
            [HirLValue::Local(local)] => {
                facts.promoted_local_for_temp(release.released) == Some(*local)
                    && facts.trusted_local_home_slot(*local) == Some(home)
            }
            _ => false,
        };
        if release.dispatch != dispatch
            || !target_matches
            || facts.trusted_temp_home_slot(release.released) != Some(home)
            || assign.values.fixed.as_slice() != [HirExpr::Nil]
            || assign.values.tail.is_some()
            || (context.barred.contains(&home)
                && !facts.temp_definition_reference_unaliased(release.released))
            || context.closed.contains(&home)
            || !seen_results.insert(release.result_def)
        {
            return None;
        }
        release_start -= 1;
    }
    // dispatch release 是可选的尾部协议；没有 release 时仍需把 initializer
    // CALL 与其构造准备作为完整帧证明，不能要求 iterator 先独立折叠。
    if let Some(plan) = fixed_values_plan(context, run, facts, dialect, for_, release_start) {
        return Some(plan);
    }
    let initializer = release_start.checked_sub(1)?;
    let HirStmt::Assign(assign) = run[initializer] else {
        return None;
    };
    let Some(call) = generic_for_iterators::single_call_initializer(assign, for_) else {
        return generic_for_open_prefix_plan(context, run, facts, dialect, for_, release_start)
            .or_else(|| {
                generic_for_fixed_call_plan(context, run, facts, dialect, for_, release_start)
            });
    };
    let results_unaliased = facts.native_call_layout(call)?.fixed_results_unaliased;
    if assign
        .targets
        .iter()
        .zip(&frame.initializers)
        .any(|(target, home)| {
            let (home_slot, has_debug) = match target {
                HirLValue::Temp(temp) => (
                    facts.trusted_temp_home_slot(*temp),
                    context
                        .proto
                        .temp_debug_locals
                        .get(temp.index())
                        .is_some_and(Option::is_some),
                ),
                HirLValue::Local(local) => (
                    facts.trusted_local_home_slot(*local),
                    context.proto.local_debug_hints[local.index()].is_some()
                        || context.proto.local_debug_scopes[local.index()].is_some(),
                ),
                _ => return true,
            };
            home_slot != Some(*home)
                || has_debug
                || (context.barred.contains(home) && !results_unaliased)
                || context.closed.contains(home)
        })
    {
        return None;
    }
    // 紧邻的整组空声明与初始化一起消费；连续循环也可复用前一组声明。
    // 后一种情况由整批 preview 核对旧声明是否已退休及后继读写，不能把它
    // 预先合成普通 initializer 而丢掉 GenericFor 的 occurrence 身份。
    let prefix_end = match initializer.checked_sub(1).and_then(|declaration| {
        batched_initializer(run[declaration], run[initializer], facts)
            .map(|(_, width)| (declaration, width))
    }) {
        Some((declaration, width)) if width == frame.initializers.len() => declaration,
        Some(_) => return None,
        None => {
            // 只有部分控制值因后续同槽捕获被提升为 Local 时，其余结果仍是 Temp。
            // 三个原结果已在上方核对；这里仅消费这次初始化紧邻的合成空声明。
            initializer
                .checked_sub(1)
                .filter(|&index| {
                    matches!(run[index], HirStmt::LocalDecl(decl)
                    if decl.values.is_empty()
                        && decl.initializer_merge_transaction.is_none()
                        && !decl.bindings.is_empty()
                        && decl.bindings.iter().all(|local|
                            assign.targets.contains(&HirLValue::Local(*local))))
                })
                .unwrap_or(initializer)
        }
    };
    let prefix_run = &run[..prefix_end];
    let mut builder = frame_builder(context, prefix_run, facts, dialect, base.slot())?;
    if dialect == DecompileDialect::Luau {
        // Luau 在初始化表达式前预留 iterator/state/control；表的数组缓冲从
        // 整个协议槽组之后开始，不一定紧邻 table 参数槽。
        builder.declaration_reserved_top = Some(base.slot() + frame.initializers.len());
    }
    let call = builder.call(
        call,
        prefix_run.len(),
        base.slot(),
        true,
        CallWidth::Fixed(frame.initializers.len()),
    )?;
    if builder.first_event.is_some() && builder.next_event != prefix_run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: builder.first_event.unwrap_or(prefix_end),
        sink: run.len(),
        base,
        values: HirValuePack {
            fixed: Vec::new(),
            tail: Some(HirPackTail::open(HirExpr::Call(Box::new(call)))),
        },
        result_locals: Vec::new(),
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// 固定全局前缀与开放 CALL 共同填充控制包；前缀声明由当前绑定及原读取来源匹配。
fn generic_for_open_prefix_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    for_: &crate::hir::common::HirGenericFor,
    release_start: usize,
) -> Option<Plan> {
    if dialect != DecompileDialect::Luau {
        return None;
    }
    let frame = facts.generic_for_body_frame(for_)?;
    let base = *frame.initializers.first()?;
    let transaction = for_.initializer_transaction.as_ref()?;
    let [prefix, tail] = transaction.producers.as_slice() else {
        return None;
    };
    let initializer = release_start.checked_sub(1)?;
    let HirStmt::Assign(assign) = run[initializer] else {
        return None;
    };
    let HirExpr::LocalRef(local) = for_.iterator.fixed.first()? else {
        return None;
    };
    if prefix.value_start != 0
        || prefix.value_count != 1
        || tail.value_start != 1
        || tail.value_count + 1 != frame.initializers.len()
        || transaction.iterator_width != frame.initializers.len()
        || for_.iterator.fixed.len() != frame.initializers.len()
        || for_.iterator.tail.is_some()
        || prefix.producer.transaction() != transaction.id
        || tail.producer.transaction() != transaction.id
        || assign.generic_for_initializer_producer != Some(tail.producer)
        || !generic_for_iterators::producer_matches_iterator_span(assign, for_, tail)
        || !assign.values.fixed.is_empty()
        || assign.values.tail.as_ref()?.exact_width() != Some(tail.value_count)
        || facts.trusted_local_home_slot(*local) != Some(base)
        || context.proto.local_debug_hints[local.index()].is_some()
        || context.proto.local_debug_scopes[local.index()].is_some()
        || context.barred.contains(&base)
        || context.closed.contains(&base)
    {
        return None;
    }
    let HirExpr::Call(call) = assign.values.tail.as_ref()?.as_expr() else {
        return None;
    };
    let call_home = frame.initializers[1];
    if facts.native_call_layout(call)?.home != call_home {
        return None;
    }
    for (target, home) in assign.targets.iter().zip(&frame.initializers[1..]) {
        let HirLValue::Local(local) = target else {
            return None;
        };
        if facts.trusted_local_home_slot(*local) != Some(*home)
            || context.proto.local_debug_hints[local.index()].is_some()
            || context.proto.local_debug_scopes[local.index()].is_some()
            || context.closed.contains(home)
            || (context.barred.contains(home)
                && !facts.native_call_layout(call)?.fixed_results_unaliased)
        {
            return None;
        }
    }
    let prefix_end = initializer
        .checked_sub(1)
        .filter(|&index| {
            batched_initializer(run[index], run[initializer], facts)
                .is_some_and(|(_, width)| width == tail.value_count)
                || matches!(run[index], HirStmt::LocalDecl(decl)
                if decl.values.is_empty() && decl.initializer_merge_transaction.is_none()
                    && !decl.bindings.is_empty() && decl.bindings.iter().all(|local|
                        assign.targets.contains(&HirLValue::Local(*local))))
        })
        .unwrap_or(initializer);
    let prefix_index = run[..prefix_end]
        .iter()
        .rposition(|stmt| scalar_local(stmt).is_some_and(|(target, _)| target == *local))?;
    let (_, HirExpr::GlobalRef(global)) = scalar_local(run[prefix_index])? else {
        return None;
    };
    let crate::hir::common::HirOperationSources::Single(source) = global.sources else {
        return None;
    };
    let producer = facts.operation_result_temp(source)?;
    if facts.promoted_local_for_temp(producer) != Some(*local)
        || facts.global_read_frame(global, dialect) != Some(base)
    {
        return None;
    }
    let mut builder = frame_builder(context, &run[..prefix_end], facts, dialect, base.slot())?;
    builder.declaration_reserved_top = Some(base.slot() + frame.initializers.len());
    let prefix = builder.expr(
        &HirExpr::LocalRef(*local),
        prefix_end,
        base.slot(),
        None,
        false,
        true,
        Some(producer),
    )?;
    let call = builder.call(
        call,
        prefix_end,
        call_home.slot(),
        true,
        CallWidth::Fixed(tail.value_count),
    )?;
    let start = builder.first_event?;
    if builder.next_event != prefix_end {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink: run.len(),
        base,
        values: HirValuePack::expanding(
            vec![prefix],
            HirPackTail::open(HirExpr::Call(Box::new(call))),
        ),
        result_locals: Vec::new(),
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// 固定单结果 CALL 在控制组之后求值，再 COPY 至对应控制槽，并显式补齐 nil。
/// 三段 occurrence 和 dispatch release 共同提交，避免先退休 scratch 声明而遗留根释放。
fn generic_for_fixed_call_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    for_: &crate::hir::common::HirGenericFor,
    release_start: usize,
) -> Option<Plan> {
    if dialect != DecompileDialect::Luau {
        return None;
    }
    let frame = facts.generic_for_body_frame(for_)?;
    let transaction = for_.initializer_transaction.as_ref()?;
    let width = frame.initializers.len();
    if transaction.iterator_width != width
        || transaction.producers.len() != width
        || for_.iterator.fixed.len() != width
        || for_.iterator.tail.is_some()
    {
        return None;
    }
    let base = *frame.initializers.first()?;
    let mut positions = Vec::with_capacity(width);
    for index in (0..release_start).rev() {
        let HirStmt::Assign(assign) = run[index] else {
            continue;
        };
        if assign
            .generic_for_initializer_producer
            .is_some_and(|producer| producer.transaction() == transaction.id)
        {
            if assign.generic_for_initializer_producer
                != Some(transaction.producers[width - positions.len() - 1].producer)
            {
                return None;
            }
            positions.push(index);
            if positions.len() == width {
                break;
            }
        }
    }
    if positions.len() != width {
        return None;
    }
    positions.reverse();
    let mut builder = frame_builder(context, &run[..release_start], facts, dialect, base.slot())?;
    builder.declaration_reserved_top = Some(base.slot() + width);
    let mut values = Vec::with_capacity(width);
    let mut has_call = false;
    for (offset, (&index, span)) in positions.iter().zip(&transaction.producers).enumerate() {
        let HirStmt::Assign(assign) = run[index] else {
            unreachable!()
        };
        let [HirLValue::Local(local)] = assign.targets.as_slice() else {
            return None;
        };
        let home = frame.initializers[offset];
        if span.value_start != offset
            || span.value_count != 1
            || span.producer.transaction() != transaction.id
            || assign.generic_for_initializer_producer != Some(span.producer)
            || !generic_for_iterators::producer_matches_iterator_span(assign, for_, span)
            || assign.initializer_merge_transaction.is_some()
            || facts.trusted_local_home_slot(*local) != Some(home)
            || home != HomeSlotKey::new(base.slot() + offset, 0)
            || context.proto.local_debug_hints[local.index()].is_some()
            || context.proto.local_debug_scopes[local.index()].is_some()
            || context.closed.contains(&home)
        {
            return None;
        }
        let (_, value) = scalar_local(run[index])?;
        if let HirExpr::GlobalRef(global) = value
            && !has_call
        {
            // 固定前缀仍在原控制槽读取；不把后继 CALL 的结果槽当成整个循环头入口。
            if context.barred.contains(&home)
                || facts.global_read_frame(global, dialect) != Some(home)
            {
                return None;
            }
            values.push(builder.expr(value, index, home.slot(), None, false, true, None)?);
            builder.finish_event(index)?;
            continue;
        }
        if *value == HirExpr::Nil && has_call && !context.barred.contains(&home) {
            values.push(HirExpr::Nil);
            builder.finish_event(index)?;
            continue;
        }
        if has_call {
            return None;
        }
        let (call_index, call) = match value {
            HirExpr::Call(call) => (index, call.as_ref()),
            HirExpr::LocalRef(owner) => {
                let previous = index.checked_sub(1)?;
                let (local, HirExpr::Call(call)) = scalar_local(run[previous])? else {
                    return None;
                };
                if local != *owner
                    || context.proto.local_debug_hints[local.index()].is_some()
                    || context.proto.local_debug_scopes[local.index()].is_some()
                {
                    return None;
                }
                (previous, call.as_ref())
            }
            _ => return None,
        };
        let (producer, call_home) =
            declarations::call_result(call, *local, base.slot() + width, facts)?;
        if context.closed.contains(&call_home)
            || (context.barred.contains(&home)
                && !facts.native_call_layout(call)?.fixed_results_unaliased)
            || (call_index != index
                && scalar_local(run[call_index]).map(|(local, _)| local)
                    != facts.promoted_local_for_temp(producer))
        {
            return None;
        }
        let call = builder.call(call, call_index, call_home.slot(), false, CallWidth::Single)?;
        builder.finish_event(call_index)?;
        if call_index != index {
            builder.finish_event(index)?;
        }
        values.push(HirExpr::Call(Box::new(call)));
        has_call = true;
    }
    if !has_call || !matches!(values.last(), Some(HirExpr::Nil)) {
        return None;
    }
    let start = builder.first_event?;
    if builder.next_event != release_start {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink: run.len(),
        base,
        values: values.into(),
        result_locals: Vec::new(),
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

fn fixed_values_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    for_: &crate::hir::common::HirGenericFor,
    release_start: usize,
) -> Option<Plan> {
    let frame = facts.generic_for_body_frame(for_)?;
    let transaction = for_.initializer_transaction.as_ref()?;
    let width = frame.initializers.len();
    if for_.iterator.tail.is_some()
        || for_.iterator.fixed.len() > width
        || transaction.iterator_width != width
        || transaction.producers.is_empty()
        || transaction.producers.len() > for_.iterator.fixed.len()
    {
        return None;
    }
    let base = *frame.initializers.first()?;
    let remaining = transaction.producers.len();
    let mut positions = Vec::with_capacity(remaining);
    for index in (0..release_start).rev() {
        let producer = match run[index] {
            HirStmt::LocalDecl(decl) => decl.generic_for_initializer_producer,
            HirStmt::Assign(assign) => assign.generic_for_initializer_producer,
            _ => None,
        };
        let Some(producer) = producer.filter(|id| id.transaction() == transaction.id) else {
            continue;
        };
        if producer != transaction.producers[remaining - positions.len() - 1].producer {
            // MissingFact：相邻外形不能代替完整且有序的原 producer 身份。
            return None;
        }
        positions.push(index);
        if positions.len() == remaining {
            break;
        }
    }
    if positions.len() != remaining {
        return None;
    }
    positions.reverse();
    let mut builder = frame_builder(context, &run[..release_start], facts, dialect, base.slot())?;
    if dialect == DecompileDialect::Luau {
        builder.declaration_reserved_top = Some(base.slot() + width);
    }
    let mut values = Vec::with_capacity(width);
    for (offset, (&index, span)) in positions.iter().zip(&transaction.producers).enumerate() {
        let (local, value) = scalar_local(run[index])?;
        let home = frame.initializers[offset];
        let (has_tail, fixed_width, merge) = match run[index] {
            HirStmt::LocalDecl(decl) => (
                decl.values.tail.is_some(),
                decl.values.fixed.len(),
                decl.initializer_merge_transaction.is_some(),
            ),
            HirStmt::Assign(assign) => (
                assign.values.tail.is_some(),
                assign.values.fixed.len(),
                assign.initializer_merge_transaction.is_some(),
            ),
            _ => return None,
        };
        // 同槽后续捕获不回溯到当前 producer；原定义的未别名事实仍须有效。
        if span.value_start != offset
            || span.value_count != 1
            || has_tail
            || fixed_width != 1
            || merge
            || for_.iterator.fixed[offset] != HirExpr::LocalRef(local)
            || facts.trusted_local_home_slot(local) != Some(home)
            || context.proto.local_debug_hints[local.index()].is_some()
            || context.proto.local_debug_scopes[local.index()].is_some()
            || (context.barred.contains(&home)
                && !facts.local_definitions_reference_unaliased(local))
            || context.closed.contains(&home)
            || matches!(
                value,
                HirExpr::Call(_) | HirExpr::VarArg | HirExpr::Closure(_)
            )
        {
            // SemanticBarrier：独立身份及关闭/capture 义务保留；多值 CALL 由原调用协议恢复。
            return None;
        }
        if let HirExpr::TableConstructor(table) = value
            && builder.constructors.contains_key(&index)
        {
            // producer 标识原分配；尚未树化的 SETLIST/字段准备属于同一构造器。
            // 共享 builder 按已预留的控制槽重放整个构造，再接后续 state/control。
            values.push(builder.constructor(index, table, home.slot())?);
        } else {
            values.push(builder.expr(value, index, home.slot(), None, false, true, None)?);
            builder.finish_event(index)?;
        }
    }
    // 原 iterator owner 已消费的固定后缀保持在循环头；不把未证明的交错 span 猜成准备区。
    // iterator owner 会在保留 transaction 时省略尾部 nil；固定值包在原协议宽度内
    // 的这些位置仍确定为 nil，不能把展示长度当作初始化帧的物理宽度。
    for offset in remaining..width {
        let value = for_.iterator.fixed.get(offset).unwrap_or(&HirExpr::Nil);
        if !matches!(
            value,
            HirExpr::Nil
                | HirExpr::Boolean(_)
                | HirExpr::Integer(_)
                | HirExpr::Number(_)
                | HirExpr::String(_)
                | HirExpr::LocalRef(_)
                | HirExpr::TableConstructor(_)
        ) {
            return None;
        }
        values.push(builder.expr(
            value,
            release_start,
            frame.initializers[offset].slot(),
            None,
            false,
            true,
            None,
        )?);
    }
    let start = builder.first_event?;
    if builder.next_event != release_start {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink: run.len(),
        base,
        values: values.into(),
        result_locals: Vec::new(),
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}
