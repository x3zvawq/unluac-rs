//! 恢复整组 RHS 准备与声明、上值写回，保留原暂存区和提交顺序。
//!
//! Promotion 提供原 home 和写回事实，FrameBuilder 核对 Def 版本及求值事件；
//! 整组声明再交给 native preview 验证源码前缀和被消费身份的后继使用。

use super::*;
use crate::hir::simplify::table_constructors::{ConstructorWrite, constructor_write};

/// 共同的 debug 生效边界证明这些声明属于同一 initializer，而非相邻的独立语句。
pub(super) fn collect_debug_groups(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    flat: &[Option<FlatStmt<'_>>],
) -> Vec<Plan> {
    let declaration = |entry: Option<FlatStmt<'_>>| {
        let entry = entry?;
        let HirStmt::LocalDecl(decl) = entry.stmt else {
            return None;
        };
        let ([local], [_], None) = (
            decl.bindings.as_slice(),
            decl.values.fixed.as_slice(),
            &decl.values.tail,
        ) else {
            return None;
        };
        if decl.initializer_merge_transaction.is_some() {
            return None;
        }
        let scope = context.proto.local_debug_scopes[local.index()]?;
        let scope = context.proto.debug_scopes[scope]?;
        let temp = scope.initializer_temp?;
        let home = facts.trusted_local_home_slot(*local)?;
        (facts.promoted_local_for_temp(temp) == Some(*local)
            && facts.trusted_temp_home_slot(temp) == Some(home)
            && !context.closed.contains(&home))
        .then_some((*local, home, scope.start_pc, scope.end_pc))
    };
    let mut plans = Vec::new();
    let mut cursor = 0;
    while cursor < flat.len() {
        let start = cursor;
        cursor += 1;
        let Some((first, base, start_pc, end_pc)) = declaration(flat[start]) else {
            continue;
        };
        let mut locals = vec![first];
        while let Some(Some(entry)) = flat.get(cursor) {
            let Some((local, home, next_start, next_end)) = declaration(Some(*entry)) else {
                break;
            };
            if next_start != start_pc
                || next_end != end_pc
                || home.slot() != base.slot() + locals.len()
            {
                break;
            }
            locals.push(local);
            cursor += 1;
        }
        if locals.len() < 2 {
            continue;
        }
        // 整组只建立一次索引；失败后不从内部重试逐渐缩短的候选。
        let entries = flat[start..cursor]
            .iter()
            .map(|entry| entry.unwrap())
            .collect::<Vec<_>>();
        let run = entries.iter().map(|entry| entry.stmt).collect::<Vec<_>>();
        let plan = (|| {
            let mut builder = frame_builder(context, &run, facts, dialect, base.slot())?;
            if dialect == DecompileDialect::Luau {
                builder.declaration_reserved_top = Some(base.slot() + locals.len());
            }
            let mut values = Vec::with_capacity(locals.len());
            for (index, stmt) in run.iter().enumerate() {
                let (_, value) = scalar_local(stmt)?;
                let value = if dialect == DecompileDialect::Luau
                    && let HirExpr::Call(call) = value
                {
                    let (_, home) =
                        call_result(call, locals[index], base.slot() + locals.len(), facts)?;
                    HirExpr::Call(Box::new(builder.call(
                        call,
                        index,
                        home.slot(),
                        false,
                        CallWidth::Single,
                    )?))
                } else {
                    builder.expr(value, index, base.slot() + index, None, false, true, None)?
                };
                values.push(value);
                builder.finish_event(index)?;
            }
            (builder.first_event == Some(0) && builder.next_event == run.len()).then_some(Plan {
                start: entries[0].id,
                sink: entries.last()?.id,
                base,
                values: values.into(),
                result_locals: locals,
                discarded_result: None,
                assignment_targets: Vec::new(),
                luau_compound_global: false,
                indexed_target: None,
                continuing_root: None,
                retained_copies: Vec::new(),
                replayed_effects: Vec::new(),
                removed: entries[..entries.len() - 1]
                    .iter()
                    .map(|entry| entry.id)
                    .collect(),
            })
        })();
        if let Some(plan) = plan {
            plans.push(plan);
        }
    }
    plans
}

/// 连续常量准备或原 LOADNIL 组与逆序 SETUPVAL 组成 PUC 并列赋值，保持原 scratch 槽。
pub(super) fn collect_upvalue_literals(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    flat: &[Option<FlatStmt<'_>>],
) -> Vec<Plan> {
    if matches!(dialect, DecompileDialect::Luajit | DecompileDialect::Luau) {
        return Vec::new();
    }
    let literal = |entry: Option<FlatStmt<'_>>| {
        let entry = entry?;
        let HirStmt::LocalDecl(decl) = entry.stmt else {
            return None;
        };
        let ([local], [value], None) = (
            decl.bindings.as_slice(),
            decl.values.fixed.as_slice(),
            &decl.values.tail,
        ) else {
            return None;
        };
        (decl.initializer_merge_transaction.is_none()
            && matches!(
                value,
                HirExpr::Boolean(_) | HirExpr::Integer(_) | HirExpr::Number(_) | HirExpr::String(_)
            ))
        .then_some((HirBinding::Local(*local), value.clone()))
    };
    let input_home = |binding| {
        let (home, writes, protected) = match binding {
            HirBinding::Local(local) => (
                facts.trusted_local_home_slot(local)?,
                facts.complete_local_definition_write_homes(local),
                context.proto.local_debug_hints[local.index()].is_some()
                    || context.proto.local_debug_scopes[local.index()].is_some()
                    || context
                        .proto
                        .inline_dispositions
                        .local(local)
                        .must_preserve(),
            ),
            HirBinding::Temp(temp) => (
                facts.trusted_temp_home_slot(temp)?,
                facts.complete_temp_definition_write_homes(temp),
                context.proto.temp_debug_locals[temp.index()].is_some()
                    || context.proto.temp_debug_scopes[temp.index()].is_some()
                    || context.proto.inline_dispositions.temp(temp).must_preserve(),
            ),
            _ => return None,
        };
        (!protected
            && !context.barred.contains(&home)
            && !context.closed.contains(&home)
            && writes.iter().copied().eq(std::iter::once(home)))
        .then_some(home)
    };
    let mut plans = Vec::new();
    let mut cursor = 0;
    if dialect == DecompileDialect::Lua51
        && let Some((plan, end)) = entry_nil_upvalues(context, facts, flat)
    {
        plans.push(plan);
        cursor = end;
    }
    while cursor < flat.len() {
        let start = cursor;
        let mut inputs = Vec::new();
        if let Some(group) = flat[cursor].and_then(|entry| nil_argument_group(entry.stmt, facts)) {
            // LOADNIL 是一条完整的批量写；不能先把其中一个 Temp 当作普通 local 提升。
            inputs.extend(
                group
                    .iter()
                    .map(|&temp| (HirBinding::Temp(temp), HirExpr::Nil)),
            );
            cursor += 1;
        }
        while cursor < flat.len() {
            let Some(input) = literal(flat[cursor]) else {
                break;
            };
            inputs.push(input);
            cursor += 1;
        }
        if inputs.len() < 2 {
            cursor = cursor.max(start + 1);
            continue;
        }
        // 失败组不从内部重新扫描，长常量前缀的收集仍为线性。
        let Some(base) = input_home(inputs[0].0) else {
            continue;
        };
        let width = inputs.len();
        let Some(writes) = flat.get(cursor..cursor + width) else {
            continue;
        };
        let mut targets = Vec::with_capacity(width);
        let mut valid = true;
        for (offset, ((binding, _), write)) in inputs.iter().zip(writes.iter().rev()).enumerate() {
            let Some(write) = write else {
                valid = false;
                break;
            };
            let Some(expected) = input_home(*binding) else {
                valid = false;
                break;
            };
            if expected.slot() != base.slot() + offset {
                valid = false;
                break;
            }
            let HirStmt::Assign(assign) = write.stmt else {
                valid = false;
                break;
            };
            let ([HirLValue::Upvalue(target)], [source], None) = (
                assign.targets.as_slice(),
                assign.values.fixed.as_slice(),
                &assign.values.tail,
            ) else {
                valid = false;
                break;
            };
            if HirBinding::from_expr(source) != Some(*binding)
                || assign.is_phi_transfer
                || assign.initializer_merge_transaction.is_some()
                || assign.generic_for_initializer_producer.is_some()
                || assign.generic_for_dispatch_release.is_some()
                || assign.method_rewrite_transaction.is_some()
            {
                valid = false;
                break;
            }
            targets.push(HirLValue::Upvalue(*target));
        }
        let end = cursor + width;
        let first_id = flat[start].unwrap().id;
        if !valid
            || flat[start..end]
                .iter()
                .enumerate()
                .any(|(offset, entry)| entry.is_none_or(|entry| entry.id != first_id + offset))
        {
            continue;
        }
        plans.push(Plan {
            start: first_id,
            sink: flat[end - 1].unwrap().id,
            base,
            values: inputs
                .into_iter()
                .map(|(_, value)| value)
                .collect::<Vec<_>>()
                .into(),
            result_locals: Vec::new(),
            discarded_result: None,
            assignment_targets: targets,
            luau_compound_global: false,
            indexed_target: None,
            continuing_root: None,
            retained_copies: Vec::new(),
            replayed_effects: flat[cursor..end - 1]
                .iter()
                .map(|entry| entry.unwrap().id)
                .collect(),
            removed: flat[start..end - 1]
                .iter()
                .map(|entry| entry.unwrap().id)
                .collect(),
        });
        cursor = end;
    }
    plans
}

/// Lua 5.1 省略函数入口的 LOADNIL；仍按原逆序 SETUPVAL 的连续输入槽重建并行 RHS。
fn entry_nil_upvalues(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    flat: &[Option<FlatStmt<'_>>],
) -> Option<(Plan, usize)> {
    let mut writes = Vec::new();
    for entry in flat {
        let Some(entry) = entry else { break };
        let HirStmt::Assign(assign) = entry.stmt else {
            break;
        };
        let Some((site, target, home)) = facts.entry_nil_upvalue_write(assign) else {
            break;
        };
        if site.index() != writes.len()
            || assign.initializer_merge_transaction.is_some()
            || assign.generic_for_initializer_producer.is_some()
            || assign.generic_for_dispatch_release.is_some()
            || assign.method_rewrite_transaction.is_some()
            || context.barred.contains(&home)
            || context.closed.contains(&home)
        {
            break;
        }
        writes.push((entry.id, target, home));
    }
    if writes.len() < 2 {
        return None;
    }
    let &(sink, _, base) = writes.last()?;
    if writes
        .iter()
        .rev()
        .enumerate()
        .any(|(offset, (_, _, home))| home.slot() != base.slot() + offset)
    {
        return None;
    }
    let removed = writes[..writes.len() - 1]
        .iter()
        .map(|(id, _, _)| *id)
        .collect::<Vec<_>>();
    Some((
        Plan {
            start: writes[0].0,
            sink,
            base,
            values: vec![HirExpr::Nil; writes.len()].into(),
            result_locals: Vec::new(),
            discarded_result: None,
            assignment_targets: writes
                .iter()
                .rev()
                .map(|(_, target, _)| HirLValue::Upvalue(*target))
                .collect(),
            luau_compound_global: false,
            indexed_target: None,
            continuing_root: None,
            retained_copies: Vec::new(),
            replayed_effects: removed.clone(),
            removed,
        },
        writes.len(),
    ))
}

pub(super) fn collect_comparisons(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    flat: &[Option<FlatStmt<'_>>],
) -> Vec<Plan> {
    if dialect != DecompileDialect::Luau {
        return Vec::new();
    }
    let mut plans = Vec::new();
    let mut cursor = 0;
    while cursor < flat.len() {
        let first = cursor;
        cursor += 1;
        let Some((_, binary, base, start)) = comparison_declaration(flat, first, facts) else {
            continue;
        };
        let arithmetic = [&binary.lhs, &binary.rhs]
            .into_iter()
            .find_map(|value| match value {
                HirExpr::Binary(arithmetic) if numeric_rk_arithmetic(arithmetic) => {
                    Some(arithmetic)
                }
                _ => None,
            });
        let Some(top) =
            arithmetic.and_then(|arithmetic| facts.operation_result_home(arithmetic.source_site?))
        else {
            continue;
        };
        if top.slot() <= base.slot() + 1 {
            continue;
        }
        let width = top.slot() - base.slot();
        let mut seeds = Vec::new();
        let mut empty = BTreeSet::new();
        let mut next = first;
        while next < flat.len() && seeds.len() < width {
            let Some(entry) = flat[next] else { break };
            if let Some((local, _, home, declaration)) = comparison_declaration(flat, next, facts) {
                if home.slot() != base.slot() + seeds.len() {
                    break;
                }
                if declaration < next {
                    empty.insert(declaration);
                }
                seeds.push((next, local));
            } else if scalar_binding(entry.stmt).is_none()
                && !matches!(entry.stmt, HirStmt::LocalDecl(decl)
                    if decl.values.is_empty() && decl.bindings.len() == 1)
            {
                break;
            }
            next += 1;
        }
        // 同一组只扫描一次；不能从失败组内部重复构建增长的定义索引。
        cursor = cursor.max(next);
        if seeds.len() != width {
            continue;
        }
        let end = next - 1;
        let mut run = Vec::new();
        let mut positions = Vec::with_capacity(width);
        let mut seed = 0;
        for (index, entry) in flat.iter().enumerate().take(end + 1).skip(start) {
            if empty.contains(&index) {
                continue;
            }
            if seed < seeds.len() && seeds[seed].0 == index {
                positions.push(run.len());
                seed += 1;
            }
            run.push(entry.unwrap().stmt);
        }
        let Some(mut builder) = frame_builder(context, &run, facts, dialect, base.slot()) else {
            continue;
        };
        builder.declaration_reserved_top = Some(top.slot());
        let values = positions
            .iter()
            .enumerate()
            .map(|(offset, &position)| {
                let (_, value) = scalar_local(run[position])?;
                let slot = base.slot() + offset;
                builder.boolean_frame = Some(slot);
                let value = builder.expr(value, position, slot, None, false, true, None)?;
                builder.finish_event(position)?;
                Some(value)
            })
            .collect::<Option<Vec<_>>>();
        let Some(values) = values else { continue };
        if builder.first_event != Some(0) || builder.next_event != run.len() {
            continue;
        }
        // 每个比较仍向自己的低槽写 Boolean，全部 operand 借用同一个组末 scratch。
        // 结果声明不退休；后续根、debug 身份与前缀由整批 native preview 核对。
        plans.push(Plan {
            start: flat[start].unwrap().id,
            sink: flat[end].unwrap().id,
            base,
            values: values.into(),
            result_locals: seeds.into_iter().map(|(_, local)| local).collect(),
            discarded_result: None,
            assignment_targets: Vec::new(),
            luau_compound_global: false,
            indexed_target: None,
            continuing_root: None,
            retained_copies: Vec::new(),
            replayed_effects: Vec::new(),
            removed: flat[start..end]
                .iter()
                .map(|entry| entry.unwrap().id)
                .collect(),
        });
    }
    plans
}

fn comparison_declaration<'a>(
    flat: &[Option<FlatStmt<'a>>],
    index: usize,
    facts: &ProtoPromotionFacts,
) -> Option<(
    LocalId,
    &'a crate::hir::common::HirBinaryExpr,
    HomeSlotKey,
    usize,
)> {
    let entry = flat[index]?;
    let (local, HirExpr::Binary(binary)) = scalar_local(entry.stmt)? else {
        return None;
    };
    let result = facts.comparison_result_temp(binary)?;
    let home = facts.trusted_temp_home_slot(result)?;
    if facts.promoted_local_for_temp(result) != Some(local)
        || facts.trusted_local_home_slot(local) != Some(home)
    {
        return None;
    }
    let declaration = match entry.stmt {
        HirStmt::LocalDecl(decl) if decl.initializer_merge_transaction.is_none() => index,
        HirStmt::Assign(assign)
            if assign.initializer_merge_transaction.is_none()
                && assign.generic_for_initializer_producer.is_none()
                && assign.generic_for_dispatch_release.is_none()
                && assign.method_rewrite_transaction.is_none() =>
        {
            let previous = index.checked_sub(1)?;
            let HirStmt::LocalDecl(decl) = flat[previous]?.stmt else {
                return None;
            };
            if decl.bindings.as_slice() != [local]
                || !decl.values.is_empty()
                || decl.initializer_merge_transaction.is_some()
            {
                return None;
            }
            previous
        }
        _ => return None,
    };
    Some((local, binary, home, declaration))
}

pub(super) fn collect(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    flat: &[Option<FlatStmt<'_>>],
    empty: &BTreeSet<usize>,
    ends: &BTreeMap<usize, usize>,
    arguments: &BTreeSet<LocalId>,
) -> Vec<Plan> {
    if dialect != DecompileDialect::Luau {
        return Vec::new();
    }
    let mut plans = Vec::new();
    let mut cursor = 0;
    while cursor < flat.len() {
        let start = cursor;
        cursor += 1;
        let Some(entry) = flat[start] else { continue };
        let Some((_, table)) = declaration(entry.stmt) else {
            continue;
        };
        let Some(base) = facts.allocation_result_home(table) else {
            continue;
        };
        let Some(&first_end) = ends.get(&start) else {
            continue;
        };
        let Some(write) = flat[first_end].and_then(|entry| constructor_write(entry.stmt)) else {
            continue;
        };
        let top = match write {
            ConstructorWrite::Record { access, .. } => {
                let Some(layout) = facts.native_table_write_layout(access) else {
                    continue;
                };
                if layout.base != base || layout.key.is_some() {
                    continue;
                }
                let Some(top) = layout.value else { continue };
                top
            }
            ConstructorWrite::Batch { batch, .. } => {
                let Some(layout) = facts.native_table_batch_layout(batch) else {
                    continue;
                };
                if layout.base != base {
                    continue;
                }
                layout.buffer
            }
        };
        if top.slot() <= base.slot() + 1 {
            continue;
        }
        // r8/r9 的两个构造器都借用 r10 时，拆成独立声明会错移第一份 scratch。
        // `{nested={}}` 与 `{f()}` 都需覆盖整组目标，单个偏高 buffer 不证明分组。
        let width = top.slot() - base.slot();
        let mut seeds = Vec::new();
        let mut next = start;
        for offset in 0..width {
            while flat
                .get(next)
                .and_then(|entry| *entry)
                .is_some_and(|entry| empty.contains(&entry.id))
            {
                next += 1;
            }
            let Some(entry) = flat.get(next).and_then(|entry| *entry) else {
                break;
            };
            let Some((local, table)) = declaration(entry.stmt) else {
                break;
            };
            let home = HomeSlotKey::new(base.slot() + offset, 0);
            if facts.trusted_local_home_slot(local) != Some(home)
                || facts.allocation_result_home(table) != Some(home)
                || arguments.contains(&local)
            {
                break;
            }
            let Some(&end) = ends.get(&next) else { break };
            seeds.push((next, local));
            next = end + 1;
        }
        // 即使整组拒绝，也不从其内部的每个 seed 重试同一增长窗口。
        cursor = cursor.max(next);
        if seeds.len() != width {
            continue;
        }
        let end = next - 1;
        let mut run = Vec::new();
        let mut positions = Vec::with_capacity(width);
        let mut seed_iter = seeds.iter().peekable();
        let mut boundary = false;
        for (offset, entry) in flat[start..=end].iter().enumerate() {
            let Some(entry) = entry else {
                boundary = true;
                break;
            };
            if seed_iter
                .peek()
                .is_some_and(|(seed, _)| *seed == start + offset)
            {
                positions.push(run.len());
                seed_iter.next();
            }
            if !empty.contains(&entry.id) {
                run.push(entry.stmt);
            }
        }
        if boundary {
            continue;
        }
        let Some(mut builder) = frame_builder(context, &run, facts, dialect, base.slot()) else {
            continue;
        };
        builder.declaration_reserved_top = Some(top.slot());
        let values = positions
            .iter()
            .enumerate()
            .map(|(offset, &seed)| {
                let (_, table) = declaration(run[seed])?;
                builder.constructor(seed, table, base.slot() + offset)
            })
            .collect::<Option<Vec<_>>>();
        let Some(values) = values else { continue };
        if builder.first_event != Some(0) || builder.next_event != run.len() {
            continue;
        }
        plans.push(Plan {
            start: flat[start].unwrap().id,
            sink: flat[end].unwrap().id,
            base,
            values: values.into(),
            result_locals: seeds.into_iter().map(|(_, local)| local).collect(),
            discarded_result: None,
            assignment_targets: Vec::new(),
            luau_compound_global: false,
            indexed_target: None,
            continuing_root: None,
            retained_copies: Vec::new(),
            replayed_effects: Vec::new(),
            removed: flat[start..end]
                .iter()
                .map(|entry| entry.unwrap().id)
                .collect(),
        });
    }
    plans
}

fn declaration(stmt: &HirStmt) -> Option<(LocalId, &crate::hir::common::HirTableConstructor)> {
    let HirStmt::LocalDecl(decl) = stmt else {
        return None;
    };
    let ([local], [HirExpr::TableConstructor(table)], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    matches!(
        table.allocation,
        HirTableAllocation::LuauTemplate { .. } | HirTableAllocation::Luau(_)
    )
    .then_some((*local, table))
}

/// 每个非末尾 CALL 在组末 scratch 求值，再紧邻写回对应声明槽；末尾 CALL 原位返回。
/// 此查询只证明原 Def 的槽与写域，当前 COPY 和事件顺序仍由整组候选核对。
pub(super) fn call_result(
    call: &HirCallExpr,
    local: LocalId,
    top: usize,
    facts: &ProtoPromotionFacts,
) -> Option<(TempId, HomeSlotKey)> {
    let target = facts.trusted_local_home_slot(local)?;
    let frame = facts
        .native_call_frame(call)
        .or_else(|| facts.native_fastcall_frame(call))?;
    let producer = facts.operation_result_temp(call.source_site?)?;
    let slot = if target.slot() + 1 == top {
        target.slot()
    } else {
        top
    };
    if target.slot() >= top
        || frame.home.slot() != slot
        || facts.trusted_temp_home_slot(producer) != Some(frame.home)
        || !matches!(frame.results, Some(crate::transformer::ResultPack::Fixed(pack))
            if pack.len == 1 && pack.start.index() == slot)
        || facts
            .complete_temp_non_move_write_homes(producer)
            .iter()
            .any(|home| *home != frame.home)
        || facts
            .complete_temp_definition_write_homes(producer)
            .iter()
            .any(|home| *home != frame.home && *home != target)
    {
        return None;
    }
    let moves = facts.trusted_immediate_moves(producer)?;
    let result = if target == frame.home {
        if !moves.is_empty() {
            return None;
        }
        producer
    } else {
        let [copy] = moves else {
            return None;
        };
        if copy.source != Some(producer)
            || copy.source_home != frame.home
            || copy.target_home != target
        {
            return None;
        }
        copy.target
    };
    (facts.promoted_local_for_temp(result) == Some(local)).then_some((producer, frame.home))
}

pub(super) fn collect_calls(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    flat: &[Option<FlatStmt<'_>>],
    empty: &BTreeSet<usize>,
) -> Vec<Plan> {
    if dialect != DecompileDialect::Luau {
        return Vec::new();
    }
    let mut plans = Vec::new();
    let mut floor = 0;
    let mut cursor = 0;
    while cursor < flat.len() {
        let index = cursor;
        cursor += 1;
        let Some(entry) = flat[index] else {
            floor = cursor;
            continue;
        };
        let Some((_, HirExpr::Call(call))) = scalar_local(entry.stmt) else {
            if scalar_binding(entry.stmt).is_none()
                && !empty.contains(&entry.id)
                && constructor_write(entry.stmt).is_none()
                && !matches!(entry.stmt, HirStmt::LocalRootRelease(_))
            {
                floor = cursor;
            }
            continue;
        };
        let Some(producer) = call
            .source_site
            .and_then(|site| facts.operation_result_temp(site))
        else {
            continue;
        };
        let Some([copy]) = facts.trusted_immediate_moves(producer) else {
            continue;
        };
        let base = copy.target_home;
        let top = copy.source_home.slot();
        if top <= base.slot() + 1 {
            continue;
        }
        let width = top - base.slot();
        let mut calls = Vec::new();
        let mut next = index;
        for offset in 0..width {
            while let Some(Some(entry)) = flat.get(next) {
                if matches!(scalar_local(entry.stmt), Some((_, HirExpr::Call(_)))) {
                    break;
                }
                if scalar_binding(entry.stmt).is_none()
                    && !empty.contains(&entry.id)
                    && constructor_write(entry.stmt).is_none()
                    // 根释放仍留在完整 run 中验证，不能让候选扫描先截断整组 CALL/COPY。
                    && !matches!(entry.stmt, HirStmt::LocalRootRelease(_))
                {
                    break;
                }
                next += 1;
            }
            let Some(entry) = flat.get(next).and_then(|entry| *entry) else {
                break;
            };
            let Some((owner, HirExpr::Call(call))) = scalar_local(entry.stmt) else {
                break;
            };
            let Some(producer) = call
                .source_site
                .and_then(|site| facts.operation_result_temp(site))
            else {
                break;
            };
            let result = if offset + 1 == width {
                Some(producer)
            } else {
                facts
                    .trusted_immediate_moves(producer)
                    .and_then(|moves| match moves {
                        [copy] => Some(copy.target),
                        _ => None,
                    })
            };
            let Some(local) = result.and_then(|temp| facts.promoted_local_for_temp(temp)) else {
                break;
            };
            // Promotion 可能已把 CALL+MOVE 合入结果 local；仍消费原 COPY 事实，
            // 只有保留独立 producer 时才要求当前树上紧邻的 COPY 语句。
            let copied = owner != local;
            let end = next + usize::from(copied);
            let Some(sink) = flat.get(end).and_then(|entry| *entry) else {
                break;
            };
            let Some((target, value)) = scalar_local(sink.stmt) else {
                break;
            };
            let Some((producer, home)) = call_result(call, local, top, facts) else {
                break;
            };
            if target != local
                || facts.trusted_local_home_slot(local)
                    != Some(HomeSlotKey::new(base.slot() + offset, 0))
                || (copied && *value != HirExpr::LocalRef(owner))
                || matches!(sink.stmt, HirStmt::LocalDecl(decl) if decl.initializer_merge_transaction.is_some())
                || matches!(sink.stmt, HirStmt::Assign(assign) if assign.initializer_merge_transaction.is_some())
                || (copied && facts.promoted_local_for_temp(producer) != Some(owner))
                || (copied
                    && (context.proto.local_debug_hints[owner.index()].is_some()
                        || context.proto.local_debug_scopes[owner.index()].is_some()
                        || context
                            .proto
                            .inline_dispositions
                            .local(owner)
                            .must_preserve()))
                || context
                    .closed
                    .contains(&HomeSlotKey::new(base.slot() + offset, 0))
                || context.closed.contains(&home)
            {
                break;
            }
            calls.push((next, end, local));
            next = end + 1;
        }
        // 每个候选窗口只建一次 Def 索引；拒绝后也不从其内部反复扫描增长前缀。
        cursor = cursor.max(next);
        let start = floor;
        floor = cursor;
        if calls.len() != width {
            continue;
        }
        if let Some(plan) = call_plan(
            context, facts, dialect, flat, empty, start, next, base, &calls,
        ) {
            plans.push(plan);
        }
    }
    plans
}

#[expect(
    clippy::too_many_arguments,
    reason = "候选窗口与原 CALL/COPY 终点共同交给同一个事务 builder"
)]
fn call_plan(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    flat: &[Option<FlatStmt<'_>>],
    empty: &BTreeSet<usize>,
    start: usize,
    end: usize,
    base: HomeSlotKey,
    calls: &[(usize, usize, LocalId)],
) -> Option<Plan> {
    let entries = flat[start..end]
        .iter()
        .copied()
        .collect::<Option<Vec<_>>>()?;
    let mut run = Vec::new();
    let mut indices = BTreeMap::new();
    let mut ids = Vec::new();
    for (offset, entry) in entries.iter().enumerate() {
        if !empty.contains(&entry.id) {
            indices.insert(start + offset, run.len());
            ids.push(entry.id);
            run.push(entry.stmt);
        }
    }
    let mut builder = frame_builder(context, &run, facts, dialect, base.slot())?;
    builder.declaration_reserved_top = Some(base.slot() + calls.len());
    let mut values = Vec::new();
    for &(call_index, copy_index, local) in calls {
        let index = indices[&call_index];
        let (_, HirExpr::Call(call)) = scalar_local(run[index])? else {
            return None;
        };
        let (_, home) = call_result(call, local, base.slot() + calls.len(), facts)?;
        values.push(HirExpr::Call(Box::new(builder.call(
            call,
            index,
            home.slot(),
            false,
            CallWidth::Single,
        )?)));
        builder.finish_event(index)?;
        if copy_index != call_index {
            builder.finish_event(indices[&copy_index])?;
        }
    }
    let first = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    let sink = *ids.last()?;
    Some(Plan {
        start: ids[first],
        sink,
        base,
        values: values.into(),
        result_locals: calls.iter().map(|(_, _, local)| *local).collect(),
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: entries
            .iter()
            .filter(|entry| entry.id >= ids[first] && entry.id < sink)
            .map(|entry| entry.id)
            .collect(),
    })
}
