//! 恢复调用、算术及寄存器快照的赋值帧，保留 RHS 求值顺序和原目标写回。
//! 原操作与 COPY 来源由 Promotion 提供；声明前缀和后续 scratch 复用交给 native preview。

use super::*;

pub(super) mod globals;
pub(super) mod nil;
pub(super) mod prepared_writes;

/// 按完整原准备组消费常量或分配 RHS，避免先恢复尾部两项并截断更宽的并列写回。
pub(super) fn prepared_local_plans(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    flat: &[Option<FlatStmt<'_>>],
) -> BTreeMap<usize, (Plan, usize)> {
    let mut plans = BTreeMap::new();
    let mut literals = BTreeMap::new();
    for frame in facts.literal_assignment_frames() {
        let Some(local) = frame
            .inputs
            .first()
            .and_then(|input| facts.promoted_local_for_temp(input.value))
        else {
            continue;
        };
        literals
            .entry(local)
            .and_modify(|known| *known = None)
            .or_insert(Some(frame));
    }
    for (index, entry) in flat.iter().enumerate() {
        let Some(entry) = entry else { continue };
        if let Some((local, _)) = scalar_local(entry.stmt)
            && let Some(Some(frame)) = literals.get(&local)
            && let Some((plan, end)) = prepared_local_plan(context, facts, flat, index, frame)
        {
            plans.insert(index, (plan, end));
        }
        let Some((_, HirExpr::TableConstructor(table))) = scalar_local(entry.stmt) else {
            continue;
        };
        let Some(frame) = facts.allocation_frame(table) else {
            continue;
        };
        let Some(start) = index.checked_sub(frame.inputs.len() - 1) else {
            continue;
        };
        if let Some((plan, end)) = prepared_local_plan(context, facts, flat, start, frame) {
            plans.insert(start, (plan, end));
        }
    }
    plans
}

fn prepared_local_plan(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    flat: &[Option<FlatStmt<'_>>],
    start: usize,
    frame: &crate::hir::promotion::NativePreparedFrame,
) -> Option<(Plan, usize)> {
    let count = frame.inputs.len();
    let preparations = flat
        .get(start..start + count)?
        .iter()
        .copied()
        .collect::<Option<Vec<_>>>()?;
    let targets = frame
        .writes
        .iter()
        .map(|write| {
            let local = facts.promoted_local_for_temp(write.target)?;
            (facts.trusted_local_home_slot(local) == Some(write.home)).then_some(local)
        })
        .collect::<Option<Vec<_>>>()?;
    let direct = scalar_local(preparations.last()?.stmt)?.0 == *targets.last()?;
    let end = start + count * 2 - usize::from(direct);
    let writes = flat
        .get(start + count..end)?
        .iter()
        .copied()
        .collect::<Option<Vec<_>>>()?;
    let mut values = Vec::with_capacity(count);
    for (offset, (entry, input)) in preparations.iter().zip(&frame.inputs).enumerate() {
        let (local, value) = scalar_local(entry.stmt)?;
        if !plain_copy(entry.stmt) {
            return None;
        }
        let matches = match (&input.literal, input.copied, value) {
            (Some(original), None, value) => original == value,
            (None, Some((temp, home)), HirExpr::LocalRef(source)) => {
                facts.promoted_local_for_temp(temp) == Some(*source)
                    && facts.trusted_local_home_slot(*source) == Some(home)
            }
            (None, None, HirExpr::TableConstructor(table)) => {
                matches!(table.sources, crate::hir::common::HirOperationSources::Single(source)
                    if source.instr == input.site && facts.operation_result_temp(source) == Some(input.value))
                    && table.fields.is_empty()
                    && table.trailing_multivalue.is_none()
                    && table.matches_allocation_capacity(0)
            }
            _ => false,
        };
        if !matches {
            return None;
        }
        if direct && offset + 1 == count {
            if !matches!(entry.stmt, HirStmt::Assign(_)) {
                return None;
            }
        } else {
            let write = writes.get(count - offset - 1 - usize::from(direct))?;
            if facts.promoted_local_for_temp(input.value) != Some(local)
                || facts.trusted_local_home_slot(local) != Some(input.home)
                || context.closed.contains(&input.home)
                || context.proto.local_debug_hints[local.index()].is_some()
                || context.proto.local_debug_scopes[local.index()].is_some()
                || matches!(context.proto.inline_dispositions.local(local),
                    crate::hir::common::HirInlineDisposition::Preserve(reasons)
                        if reasons.iter().any(|reason| *reason != HirInlineRetentionReason::PhysicalFramePrefix))
                || !plain_copy(write.stmt)
                || !matches!(write.stmt, HirStmt::Assign(_))
                || scalar_local(write.stmt) != Some((targets[offset], &HirExpr::LocalRef(local)))
            {
                // 候选拒绝[ProofIncomplete:BindingIdentity]：整组原准备、目标与写回必须仍相邻，
                // 不能跨过观察点或借用同槽的其它版本补全赋值。
                return None;
            }
        }
        values.push(value.clone());
    }
    let sink = writes.last()?.id;
    let mut removed = preparations
        .iter()
        .map(|entry| entry.id)
        .collect::<Vec<_>>();
    removed.extend(writes[..writes.len() - 1].iter().map(|entry| entry.id));
    let mut replayed_effects = Vec::new();
    if direct {
        replayed_effects.push(preparations.last()?.id);
    }
    replayed_effects.extend(writes[..writes.len() - 1].iter().map(|entry| entry.id));
    Some((
        Plan {
            prefix_at_sink: false,
            luau_function_declaration: false,
            start: preparations[0].id,
            sink,
            base: frame.inputs[0].home,
            values: values.into(),
            result_locals: Vec::new(),
            assignment_targets: targets.into_iter().map(HirLValue::Local).collect(),
            luau_compound_global: false,
            indexed_target: None,
            continuing_root: None,
            retained_copies: Vec::new(),
            replayed_effects,
            removed,
        },
        end - 1,
    ))
}

/// PUC/LuaJIT 的末项查表、标量或 CONCAT 写入最后一个 local；其余 RHS 先占连续 scratch，
/// 随后逆序提交。全部原写同批重发，不能把某个捕获 cell 的更新提前到后续读取前。
pub(super) fn lookup_pack(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    flat: &[Option<FlatStmt<'_>>],
    index: usize,
    first: &crate::hir::common::HirTableAccess,
) -> Option<(Plan, usize)> {
    let frame = facts.lookup_assignment_frame(first)?;
    let count = frame.writes.len();
    let tail = frame.reads.last()?;
    let producer = if let Some(inputs) = frame.concat_inputs {
        // 原输入准备与 CONCAT 属于一个不重叠的 LIR 帧；只查看其有界 HIR 准备区，
        // 不从每个查表候选向函数末尾搜索，也不跨过已物化的控制流。
        let mut producer = index + count;
        loop {
            let (_, value) = scalar_local(flat.get(producer)?.as_ref()?.stmt)?;
            if matches!(value, HirExpr::Binary(binary)
                if binary.op == crate::hir::common::HirBinaryOpKind::Concat
                    && binary.source_site.is_some_and(|source| source.instr == tail.site))
            {
                break producer;
            }
            if producer == index + count + inputs {
                return None;
            }
            producer += 1;
        }
    } else {
        index + count
    };
    let separate_result = frame.concat_inputs.is_some()
        && !matches!(flat.get(producer)?.as_ref()?.stmt, HirStmt::Assign(_));
    let tail_assignment = producer + usize::from(separate_result);
    let end = tail_assignment + count;
    let entries = flat
        .get(index..=end)?
        .iter()
        .copied()
        .collect::<Option<Vec<_>>>()?;
    let base = frame.reads[0].home;
    if !context.constants_fit_rk
        || entries.iter().enumerate().any(|(offset, entry)| {
            if offset > tail_assignment - index
                && let HirStmt::Assign(assign) = entry.stmt
            {
                // 分支 COPY 可同时承担 phi 交接；后面逐项核对原 Def、当前目标及
                // 逆序写回后才消费，不能把 is_phi_transfer 本身当作不同操作。
                !unclaimed_assignment(assign)
            } else {
                !plain_copy(entry.stmt)
            }
        })
    {
        return None;
    }
    let mut values = Vec::with_capacity(count + 1);
    let mut targets = Vec::with_capacity(count + 1);
    for (offset, read) in frame.reads.iter().enumerate() {
        if offset == count && frame.concat_inputs.is_some() {
            let assignment = concat_assignment_source(
                entries[tail_assignment - index].stmt,
                separate_result.then_some(entries[producer - index].stmt),
                facts,
            )?;
            let (target_temp, target_home) = frame
                .tail_write
                .as_ref()
                .and_then(|write| write.target)
                .unwrap_or((read.value, read.home));
            let HirLValue::Local(target) = assignment.target else {
                return None;
            };
            if facts.promoted_local_for_temp(target_temp) != Some(*target)
                || assignment.target_home != target_home
                || assignment.base.slot() != base.slot() + count
                || facts.operation_result_temp(assignment.binary.source_site?) != Some(read.value)
                || facts
                    .complete_temp_definition_write_homes(read.value)
                    .iter()
                    .any(|home| *home != read.home && *home != target_home)
            {
                // 候选拒绝[ProofIncomplete:BindingIdentity]：CONCAT 结果与可选 COPY
                // 必须仍指向原末项目标，不能借同槽的其它写回版本。
                return None;
            }
            targets.push(assignment.target.clone());
            values.push(HirExpr::Binary(Box::new(assignment.binary.clone())));
            continue;
        }
        let (local, value) = scalar_local(entries[offset].stmt)?;
        if facts.promoted_local_for_temp(read.value) != Some(local) {
            return None;
        }
        let access = match (&read.literal, value) {
            (None, HirExpr::TableAccess(access))
                if matches!(access.sources,
                crate::hir::common::HirOperationSources::Single(source)
                    if source.instr == read.site && facts.operation_result_temp(source) == Some(read.value)) =>
            {
                Some(access)
            }
            (Some(literal), value) if literal == value => None,
            _ => return None,
        };
        if offset == count {
            // 末项直接写既有目标 cell；原字面量与查表沿用同一低槽写回身份。
            if !matches!(entries[offset].stmt, HirStmt::Assign(_))
                || facts.trusted_local_home_slot(local) != Some(read.home)
                || access.is_some_and(|access| {
                    facts.native_table_read_layout(access).is_none_or(|layout| {
                        layout.key.is_some()
                            || layout.base.slot() >= base.slot()
                            || facts.table_read_base_home(access) != Some(layout.base)
                    })
                })
            {
                return None;
            }
            targets.push(HirLValue::Local(local));
            values.push(value.clone());
            continue;
        }
        let write = &frame.writes[offset];
        let HirStmt::Assign(assign) = entries[end - index - offset].stmt else {
            return None;
        };
        let ([target], [HirExpr::LocalRef(source)], None) = (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail,
        ) else {
            return None;
        };
        if *source != local {
            return None;
        }
        match (target, write.target) {
            (HirLValue::Local(target), Some((temp, home)))
                if (facts.promoted_local_for_temp(temp) == Some(*target)
                    || facts.promoted_binding_for_temp(temp).is_none()
                        && assign.is_phi_transfer)
                    && facts.trusted_local_home_slot(*target) == Some(home) => {}
            (HirLValue::TableAccess(target), None)
                if matches!(target.sources, crate::hir::common::HirOperationSources::Single(source) if source.instr == write.site)
                    && facts.table_write_value_preparation(target, value)
                        == Some((read.value, read.home))
                    && facts
                        .native_table_write_layout(target)
                        .is_some_and(|layout| {
                            layout.key.is_none()
                                && layout.base.slot() < base.slot()
                                && facts.direct_table_write_input_home(target, 0)
                                    == Some(layout.base)
                        }) => {}
            _ => return None,
        }
        // 未物化的原 MOVE 可由紧邻 phi 交接承担：上面已将 RHS 绑定到这次查表 Def，
        // 当前 Assign 自身提供目标身份，原写回只核对其精确 home，不能改选同槽其它绑定。
        targets.push(target.clone());
        values.push(HirExpr::LocalRef(local));
    }
    let run = entries[..producer - index]
        .iter()
        .map(|entry| entry.stmt)
        .collect::<Vec<_>>();
    let mut builder = frame_builder(context, &run, facts, dialect, base.slot())?;
    for (offset, value) in values.iter_mut().take(count).enumerate() {
        let HirExpr::LocalRef(local) = *value else {
            return None;
        };
        builder.result_move = Some((
            local,
            offset,
            frame.writes[offset]
                .target
                .map(|(_, home)| home)
                .into_iter()
                .collect(),
        ));
        *value = builder.expr(
            value,
            run.len(),
            base.slot() + offset,
            None,
            false,
            true,
            Some(frame.reads[offset].value),
        )?;
    }
    if frame.concat_inputs.is_some() {
        let HirExpr::Binary(binary) = values.last()? else {
            return None;
        };
        let value = builder.concat_in_frame(binary, run.len(), base.slot() + count, tail.home)?;
        *values.last_mut()? = value;
    }
    if builder.first_event != Some(0) || builder.next_event != run.len() {
        return None;
    }
    Some((
        Plan {
            prefix_at_sink: false,
            luau_function_declaration: false,
            start: entries[0].id,
            sink: entries.last()?.id,
            base,
            values: values.into(),
            result_locals: Vec::new(),
            assignment_targets: targets,
            luau_compound_global: false,
            indexed_target: None,
            continuing_root: None,
            retained_copies: Vec::new(),
            replayed_effects: entries[tail_assignment - index..entries.len() - 1]
                .iter()
                .map(|entry| entry.id)
                .collect(),
            removed: entries[..entries.len() - 1]
                .iter()
                .map(|entry| entry.id)
                .collect(),
        },
        end,
    ))
}

/// 复合全局更新先在结果槽读取旧值；普通赋值会把旧值留在额外 operand scratch。
/// 数值常量须来自原 RK 或相邻加载，不据同名全局推断独立读取或带左值准备的表写。
pub(super) fn compound_global(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    target: &HirLValue,
    binary: &crate::hir::common::HirBinaryExpr,
    home: HomeSlotKey,
) -> bool {
    let (HirLValue::Global(target), HirExpr::GlobalRef(input)) = (target, &binary.lhs) else {
        return false;
    };
    numeric_rk_arithmetic(binary)
        && target.key == input.key
        && context.constants_fit_rk
        && !context.barred.contains(&home)
        && !context.closed.contains(&home)
        && facts.global_read_frame(input, DecompileDialect::Luau) == Some(home)
        && facts.global_write_value_home(target, DecompileDialect::Luau) == Some(home)
        && facts.native_binary_layout(binary).is_some_and(|layout| {
            layout.lhs == Some(home)
                && (layout.rhs.is_none()
                    || binary.source_site.is_some_and(|source| {
                        facts
                            .operation_input_preparation(source, &binary.rhs)
                            .is_some_and(|(_, rhs)| {
                                Some(rhs) == layout.rhs
                                    && rhs == HomeSlotKey::new(home.slot() + 1, 0)
                            })
                    }))
        })
}

/// 算术结果可能已经树化进全局写，只有原读取仍被物化；两种输入共享同一帧证明。
pub(super) fn global_arithmetic(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    sink: FlatStmt<'_>,
    previous: Option<FlatStmt<'_>>,
) -> Option<Plan> {
    let HirStmt::Assign(assign) = sink.stmt else {
        return None;
    };
    let ([target @ HirLValue::Global(global)], [HirExpr::Binary(binary)], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    if assign.luau_compound_global || !plain_copy(sink.stmt) || !numeric_rk_arithmetic(binary) {
        return None;
    }
    let home = facts.operation_result_home(binary.source_site?)?;
    if facts.global_write_value_home(global, DecompileDialect::Luau) != Some(home) {
        return None;
    }
    let mut rebuilt = binary.as_ref().clone();
    let preparation = if let HirExpr::LocalRef(local) = binary.lhs {
        let previous = previous?;
        let (owner, value @ HirExpr::GlobalRef(_)) = scalar_local(previous.stmt)? else {
            return None;
        };
        if owner != local || previous.id + 1 != sink.id {
            return None;
        }
        rebuilt.lhs = value.clone();
        Some(previous)
    } else {
        None
    };
    let compound = compound_global(context, facts, target, &rebuilt, home);
    if !compound && preparation.is_none() {
        return None;
    }
    let run = preparation
        .iter()
        .map(|entry| entry.stmt)
        .collect::<Vec<_>>();
    let mut builder = frame_builder(context, &run, facts, DecompileDialect::Luau, home.slot())?;
    let value = if compound {
        if preparation.is_some() {
            let producer = facts
                .operation_input_preparation(binary.source_site?, &rebuilt.lhs)?
                .0;
            rebuilt.lhs = builder.expr(
                &binary.lhs,
                run.len(),
                home.slot(),
                None,
                false,
                true,
                Some(producer),
            )?;
        }
        HirExpr::Binary(Box::new(rebuilt))
    } else {
        builder.expr(
            &HirExpr::Binary(binary.clone()),
            run.len(),
            home.slot(),
            None,
            false,
            true,
            None,
        )?
    };
    if builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: preparation.map_or(sink.id, |entry| entry.id),
        sink: sink.id,
        base: home,
        values: vec![value].into(),
        result_locals: Vec::new(),
        assignment_targets: vec![target.clone()],
        luau_compound_global: compound,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: preparation.iter().map(|entry| entry.id).collect(),
    })
}

pub(super) fn plain_copy(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::Assign(assign) => !assign.is_phi_transfer && unclaimed_assignment(assign),
        HirStmt::LocalDecl(decl) => decl.initializer_merge_transaction.is_none(),
        _ => false,
    }
}

fn unclaimed_assignment(assign: &crate::hir::common::HirAssign) -> bool {
    assign.initializer_merge_transaction.is_none()
        && assign.generic_for_initializer_producer.is_none()
        && assign.root_release.is_none()
        && assign.method_rewrite_transaction.is_none()
}

/// 从当前准备操作读取原定义身份，不按被复用的 Local 或物理槽选择结果帧。
pub(super) fn selection_input(
    assign: &crate::hir::common::HirAssign,
    previous: Option<&HirStmt>,
    facts: &ProtoPromotionFacts,
) -> Option<TempId> {
    let [HirExpr::LogicalOr(alternative)] = assign.values.fixed.as_slice() else {
        return None;
    };
    let HirExpr::LogicalAnd(selected) = &alternative.lhs else {
        return None;
    };
    let value = if let HirExpr::LocalRef(input) = selected.lhs {
        let (owner, value) = scalar_local(previous?)?;
        (owner == input).then_some(value)?
    } else {
        &selected.lhs
    };
    let source = match value {
        HirExpr::Unary(unary) => unary.source_site?,
        HirExpr::Binary(binary) => binary.source_site?,
        HirExpr::Call(call) => call.source_site?,
        HirExpr::TableAccess(access) => {
            let crate::hir::common::HirOperationSources::Single(source) = access.sources else {
                return None;
            };
            source
        }
        _ => return None,
    };
    facts.operation_result_temp(source)
}

/// 原高槽谓词选择两个字面量后写回已有低槽；只退休准备，保留目标声明和原短路求值。
pub(super) fn selection_writeback(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    run: &[&HirStmt],
    assign: &crate::hir::common::HirAssign,
    result: TempId,
) -> Option<Plan> {
    let ([HirLValue::Local(target)], [HirExpr::LogicalOr(alternative)], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    let HirExpr::LogicalAnd(selected) = &alternative.lhs else {
        return None;
    };
    let home = if dialect == DecompileDialect::Luau {
        facts.trusted_temp_home_slot(result)?
    } else {
        let HirExpr::LocalRef(input) = selected.lhs else {
            return None;
        };
        facts.trusted_local_home_slot(input)?
    };
    let mut builder = frame_builder(context, run, facts, dialect, home.slot())?;
    let prepared = if let HirExpr::LocalRef(input) = selected.lhs {
        scalar_local(run[builder.definition(input, run.len())?])?.1
    } else {
        &selected.lhs
    };
    let layout =
        facts.selection_writeback(result, dialect, prepared, &selected.rhs, &alternative.rhs)?;
    if assign.is_phi_transfer
        || assign.initializer_merge_transaction.is_some()
        || assign.root_release.is_some()
        || assign.method_rewrite_transaction.is_some()
        || assign.generic_for_initializer_producer.is_some()
        || matches!(selected.lhs, HirExpr::LocalRef(input)
            if facts.promoted_local_for_temp(layout.input) != Some(input)
                || facts.trusted_local_home_slot(input) != Some(layout.input_home))
        || home != layout.base
        || facts.promoted_local_for_temp(layout.target) != Some(*target)
        || facts.trusted_local_home_slot(*target) != Some(layout.target_home)
        || context.closed.contains(&home)
        || context.barred.contains(&home)
        || context.closed.contains(&layout.input_home)
        || context.barred.contains(&layout.input_home)
    {
        return None;
    }
    let value = if dialect == DecompileDialect::Luau {
        builder.luau_logical_value(&assign.values.fixed[0], run.len(), home, None)?
    } else {
        let input = builder.expr(
            &selected.lhs,
            run.len(),
            home.slot(),
            None,
            false,
            true,
            Some(layout.input),
        )?;
        HirExpr::LogicalOr(Box::new(crate::hir::common::HirLogicalExpr {
            lhs: HirExpr::LogicalAnd(Box::new(crate::hir::common::HirLogicalExpr {
                lhs: input,
                ..selected.as_ref().clone()
            })),
            ..alternative.as_ref().clone()
        }))
    };
    let first = builder.first_event?;
    if first == run.len() || builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: first,
        sink: run.len(),
        base: home,
        values: vec![value].into(),
        result_locals: Vec::new(),
        assignment_targets: assign.targets.clone(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// MOVE 预写和结果可已提升成同一 local；整个 initializer 在原结果槽重发 COPY。
pub(super) fn copy_value_initializer(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    first: FlatStmt<'_>,
    last: FlatStmt<'_>,
    (initial, result, home): (TempId, TempId, HomeSlotKey),
) -> Option<Plan> {
    let HirStmt::LocalDecl(decl) = first.stmt else {
        return None;
    };
    let ([owner], [input], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    let (target, value) = scalar_local(last.stmt)?;
    let completed_result = matches!(input, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))
        && *value == HirExpr::LocalRef(*owner);
    if !completed_result && !matches!(input, HirExpr::LocalRef(_) | HirExpr::ParamRef(_)) {
        return None;
    }
    let value = if completed_result { input } else { value };
    // 原 COPY 可在完整值树之后写回已有低槽；结果身份仍由同一
    // ValueDecision 的最终 COPY 给出，不能把赋值伪装成高槽的新声明。
    let writeback = facts.value_result_copy(result).is_some_and(|copy| {
        matches!(last.stmt, HirStmt::Assign(_))
            && copy.source_home == home
            && copy.target_home.slot() < home.slot()
            && facts.promoted_local_for_temp(copy.target) == Some(target)
            && facts.trusted_local_home_slot(target) == Some(copy.target_home)
    });
    if !plain_copy(first.stmt)
        || !plain_copy(last.stmt)
        || !matches!(value, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))
        || completed_result && !writeback
        || facts.promoted_local_for_temp(if completed_result { result } else { initial })
            != Some(*owner)
        || !writeback && facts.promoted_local_for_temp(result) != Some(target)
        || facts.trusted_local_home_slot(*owner) != Some(home)
        || !writeback && facts.trusted_local_home_slot(target) != Some(home)
        || context.barred.contains(&home)
        || context.closed.contains(&home)
        || context.proto.local_debug_hints[owner.index()].is_some()
        || context.proto.local_debug_scopes[owner.index()].is_some()
    {
        return None;
    }
    let run = [first.stmt];
    let mut builder = frame_builder(context, &run, facts, DecompileDialect::Luau, home.slot())?;
    let value = if completed_result {
        // 前一轮已把预写收进结果 RHS 时，原低槽 COPY 仍属于同一事务；
        // 不保留高槽临时声明，也不把 RHS 改到低槽提前求值。
        let copy = facts.value_result_copy(result)?;
        builder.result_move = Some((*owner, 0, BTreeSet::from([copy.target_home])));
        if !builder.homes_match(*owner, 0, home.slot(), None, Some(result))
            || matches!(context.proto.inline_dispositions.local(*owner),
                crate::hir::common::HirInlineDisposition::Preserve(reasons)
                    if reasons.iter().any(|reason| *reason != HirInlineRetentionReason::PhysicalFramePrefix
                        && *reason != HirInlineRetentionReason::BooleanValueContext))
        {
            return None;
        }
        let value = builder.luau_logical_value(value, 0, home, None)?;
        builder.finish_event(0)?;
        value
    } else {
        builder.luau_copy_value(value, 1, initial, home)?
    };
    if builder.first_event != Some(0) || builder.next_event != 1 {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: first.id,
        sink: last.id,
        base: home,
        values: vec![value].into(),
        result_locals: if writeback { Vec::new() } else { vec![target] },
        assignment_targets: if writeback {
            vec![HirLValue::Local(target)]
        } else {
            Vec::new()
        },
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: vec![first.id],
    })
}

pub(super) struct ScalarPair<'a> {
    pub(super) left: HirLValue,
    pub(super) right: HirLValue,
    pub(super) copied_input: Option<HirBinding>,
    pub(super) base: HomeSlotKey,
    pub(super) literal_input: Option<&'a HirExpr>,
    pub(super) tail: crate::hir::promotion::ScalarPairTail,
    /// 只有运算尾项需要逐 Def 核对来源；直接值的合同由值与绑定本身给出。
    pub(super) tail_result: Option<TempId>,
}

impl ScalarPair<'_> {
    pub(super) fn same_contract(&self, other: &Self) -> bool {
        self.left == other.left
            && self.right == other.right
            && self.copied_input == other.copied_input
            && self.base == other.base
            && self.tail_result == other.tail_result
            && match (self.literal_input, other.literal_input) {
                (None, None) => true,
                (Some(left), Some(right)) => scalar_value_matches(left, right),
                _ => false,
            }
            && match (&self.tail, &other.tail) {
                (
                    crate::hir::promotion::ScalarPairTail::Value(left),
                    crate::hir::promotion::ScalarPairTail::Value(right),
                ) => scalar_value_matches(left, right),
                (
                    crate::hir::promotion::ScalarPairTail::Binary {
                        instruction: left,
                        input: left_home,
                    },
                    crate::hir::promotion::ScalarPairTail::Binary {
                        instruction: right,
                        input: right_home,
                    },
                ) => left == right && left_home == right_home,
                _ => false,
            }
    }
}

// 写回证书比较原标量表示；数值相等不能把 -0.0 的写入替换为 +0.0。
fn scalar_value_matches(left: &HirExpr, right: &HirExpr) -> bool {
    match (left, right) {
        (HirExpr::Number(left), HirExpr::Number(right)) => left.to_bits() == right.to_bits(),
        _ => left == right,
    }
}

/// 标量尾项的并列赋值仍在原高槽准备首项，再写第二项和首项；完整前缀不得移动。
pub(super) fn scalar_pair(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    frames: &BTreeMap<LocalId, Option<ScalarPair<'_>>>,
    first: FlatStmt<'_>,
    second: FlatStmt<'_>,
    last: FlatStmt<'_>,
) -> Option<Plan> {
    // 前一调用的结果槽可在同批帧恢复中退休，当前高槽快照因而也可能
    // 仍呈 Assign。原三个 Def 和完整 preview 共同核对其写域及后缀身份。
    let (snapshot, value) = scalar_local(first.stmt)?;
    let frame = frames.get(&snapshot)?.as_ref()?;

    let (left, right) = (&frame.left, &frame.right);
    let copied_input = frame.copied_input;
    let base = frame.base;
    let literal_input = frame.literal_input;
    let tail = &frame.tail;
    // 候选拒绝[TargetConstraint]：PUC 的双 nil 会改用批量 LOADNIL，不能假定
    // 仍覆盖原高槽；旧值快照则与 JIT 一样先 MOVE 到原准备槽。Luau 另有写回协议。
    if dialect == DecompileDialect::Luau
        || (literal_input == Some(&HirExpr::Nil)
            && matches!(
                tail,
                crate::hir::promotion::ScalarPairTail::Value(HirExpr::Nil)
            )
            && dialect != DecompileDialect::Luajit)
        || match (copied_input, value) {
            (None, value) => {
                literal_input.is_none_or(|literal| !scalar_value_matches(literal, value))
            }
            (Some(input), value) => HirBinding::from_expr(value) != Some(input),
        }
    {
        return None;
    }
    if !plain_copy(first.stmt)
        || !plain_copy(second.stmt)
        || !plain_copy(last.stmt)
        || second.id != first.id + 1
        || last.id != second.id + 1
        || *left == HirLValue::Local(snapshot)
        || *right == HirLValue::Local(snapshot)
        || context.closed.contains(&base)
        || context.proto.local_debug_hints[snapshot.index()].is_some()
        || context.proto.local_debug_scopes[snapshot.index()].is_some()
        || matches!(context.proto.inline_dispositions.local(snapshot),
            crate::hir::common::HirInlineDisposition::Preserve(reasons)
                if reasons.iter().any(|reason| *reason != HirInlineRetentionReason::PhysicalFramePrefix))
    {
        return None;
    }
    let (HirStmt::Assign(second_write), HirStmt::Assign(first_write)) = (second.stmt, last.stmt)
    else {
        return None;
    };
    if second_write.targets.as_slice() != std::slice::from_ref(right)
        || second_write.values.tail.is_some()
        || first_write.targets.as_slice() != std::slice::from_ref(left)
        || first_write.values.fixed.as_slice() != [HirExpr::LocalRef(snapshot)]
        || first_write.values.tail.is_some()
    {
        return None;
    }
    let [current_tail] = second_write.values.fixed.as_slice() else {
        return None;
    };
    let tail = match tail {
        crate::hir::promotion::ScalarPairTail::Value(tail)
            if scalar_value_matches(current_tail, tail) =>
        {
            tail.clone()
        }
        crate::hir::promotion::ScalarPairTail::Binary { instruction, input } => {
            let HirExpr::Binary(binary) = current_tail else {
                return None;
            };
            let source = binary.source_site?;
            if source.instr != *instruction
                || facts.operation_result_temp(source) != frame.tail_result
                || ![&binary.lhs, &binary.rhs]
                    .into_iter()
                    .all(|value| matches!(value, HirExpr::Integer(_) | HirExpr::Number(_)))
            {
                return None;
            }
            // 输入准备已树化，但原 use→Def、RK 编码及低槽结果仍逐项核对。
            let mut builder = frame_builder(context, &[], facts, dialect, input.slot())?;
            builder.register_arithmetic_writeback(binary, 0, *input)?
        }
        _ => return None,
    };
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: first.id,
        sink: last.id,
        base,
        values: vec![value.clone(), tail].into(),
        result_locals: Vec::new(),
        assignment_targets: vec![left.clone(), right.clone()],
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: vec![second.id],
        removed: vec![first.id, second.id],
    })
}

fn luau_plan(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    entries: &[FlatStmt<'_>],
    call_index: usize,
    call: &HirCallExpr,
    frame: &crate::hir::promotion::NativeParallelFrame,
    targets: Vec<HirLValue>,
) -> Option<Plan> {
    let layout = frame.luau.as_ref()?;
    for (entry, write) in entries.iter().zip(&layout.leading) {
        let (target, value) = scalar_local(entry.stmt)?;
        if !plain_copy(entry.stmt)
            || facts.promoted_local_for_temp(write.target) != Some(target)
            || facts.trusted_local_home_slot(target) != Some(write.home)
            || !matches!(value, HirExpr::LocalRef(source) if facts.promoted_local_for_temp(write.source) == Some(*source))
            || (write.home.slot() < frame.base.slot() && !matches!(entry.stmt, HirStmt::Assign(_)))
        {
            return None;
        }
    }
    for write in frame
        .moves()
        .filter(|write| write.home.slot() >= frame.base.slot())
    {
        let local = facts.promoted_local_for_temp(write.target)?;
        if context.proto.local_debug_hints[local.index()].is_some()
            || context.proto.local_debug_scopes[local.index()].is_some()
            || context
                .proto
                .inline_dispositions
                .local(local)
                .must_preserve()
            || context.barred.contains(&write.home)
            || context.closed.contains(&write.home)
        {
            // SemanticBarrier:Binding：协议相同也不能吞掉有源码身份的独立快照声明。
            return None;
        }
    }
    let result = facts.operation_result_temp(call.source_site?)?;
    let source = facts.promoted_local_for_temp(result)?;
    let home = facts.trusted_temp_home_slot(result)?;
    let run = entries.iter().map(|entry| entry.stmt).collect::<Vec<_>>();
    let mut builder = frame_builder(
        context,
        &run,
        facts,
        DecompileDialect::Luau,
        frame.base.slot(),
    )?;
    // 低槽普通 COPY 与冲突暂存 COPY 都按原顺序重发；callee MOVE 单独交 CALL builder。
    for index in 0..call_index.checked_sub(1)? {
        builder.finish_event(index)?;
    }
    let mut result_copies = BTreeSet::from([result]);
    let mut result_homes = BTreeSet::new();
    for write in &frame.tail {
        if result_copies.contains(&write.source) {
            result_copies.insert(write.target);
            result_homes.insert(write.home);
        }
    }
    builder.result_move = Some((source, call_index, result_homes));
    let value = builder.expr(
        &HirExpr::LocalRef(source),
        call_index + 1,
        home.slot(),
        None,
        false,
        true,
        Some(result),
    )?;
    for index in call_index + 1..run.len() {
        builder.finish_event(index)?;
    }
    if builder.next_event != run.len() {
        return None;
    }
    let values = layout
        .inputs
        .iter()
        .map(|input| {
            if let Some(input) = input {
                let local = facts.promoted_local_for_temp(*input)?;
                (facts.trusted_local_home_slot(local)?.slot() < frame.base.slot())
                    .then_some(HirExpr::LocalRef(local))
            } else {
                Some(value.clone())
            }
        })
        .collect::<Option<Vec<_>>>()?;
    let writes = frame
        .writes
        .iter()
        .map(|write| facts.promoted_local_for_temp(write.target))
        .collect::<Option<BTreeSet<_>>>()?;
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: entries[0].id,
        sink: entries.last()?.id,
        base: frame.base,
        values: values.into(),
        result_locals: Vec::new(),
        assignment_targets: targets,
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: entries[..entries.len() - 1]
            .iter()
            .filter_map(|entry| {
                scalar_local(entry.stmt)
                    .filter(|(local, _)| writes.contains(local))
                    .map(|_| entry.id)
            })
            .collect(),
        removed: entries[..entries.len() - 1]
            .iter()
            .map(|entry| entry.id)
            .collect(),
    })
}

pub(super) fn parallel(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    flat: &[Option<FlatStmt<'_>>],
    start: usize,
    index: usize,
    call: &HirCallExpr,
) -> Option<(Plan, usize)> {
    let frame = facts.native_parallel_assignment(call)?;
    let preparation_start = index.checked_sub(frame.preparation_count)?;
    if preparation_start < start {
        return None;
    }
    let start = preparation_start;
    let end = index + frame.tail.len();
    let entries = flat
        .get(start..=end)?
        .iter()
        .copied()
        .collect::<Option<Vec<_>>>()?;
    let first_write = end + 1 - frame.writes.len();
    for (offset, write) in frame.tail.iter().enumerate() {
        let entry = flat[index + offset + 1]?;
        let (target, value) = scalar_local(entry.stmt)?;
        if !plain_copy(entry.stmt)
            || facts.promoted_local_for_temp(write.target) != Some(target)
            || facts.trusted_local_home_slot(target) != Some(write.home)
            || !matches!(value, HirExpr::LocalRef(source) if facts.promoted_local_for_temp(write.source) == Some(*source))
            || (index + offset + 1 >= first_write && !matches!(entry.stmt, HirStmt::Assign(_)))
        {
            return None;
        }
    }
    let mut targets = Vec::new();
    for write in frame.writes.iter().rev() {
        let target = facts.promoted_local_for_temp(write.target)?;
        if (frame.luau.is_some() && context.barred.contains(&write.home))
            || context.closed.contains(&write.home)
        {
            // 候选拒绝[SemanticBarrier:Capture]：Luau 仍可能在准备期更新 cell；PUC/JIT
            // 原事实已证明全部目标写处于 RHS 之后，按原逆序写回不改变捕获 cell 的更新点。
            return None;
        }
        targets.push(HirLValue::Local(target));
    }
    if frame.luau.is_some() {
        let plan = luau_plan(
            context,
            facts,
            &entries,
            index - start,
            call,
            frame,
            targets,
        )?;
        return Some((plan, end));
    }
    let run = entries[..first_write - start]
        .iter()
        .map(|entry| entry.stmt)
        .collect::<Vec<_>>();
    let mut builder = frame_builder(context, &run, facts, dialect, frame.base.slot())?;
    let mut values = Vec::new();
    for (offset, write) in frame.writes.iter().rev().enumerate() {
        let source = facts.promoted_local_for_temp(write.source)?;
        builder.result_move = builder
            .definition(source, run.len())
            .map(|definition| (source, definition, BTreeSet::from([write.home])));
        values.push(builder.expr(
            &HirExpr::LocalRef(source),
            run.len(),
            frame.base.slot() + offset,
            None,
            false,
            true,
            Some(write.source),
        )?);
    }
    if builder.next_event != run.len() {
        return None;
    }
    let first = builder.first_event?;
    let removed = entries[first..entries.len() - 1]
        .iter()
        .map(|entry| entry.id)
        .collect();
    Some((
        Plan {
            prefix_at_sink: false,
            luau_function_declaration: false,
            start: entries[first].id,
            sink: entries.last()?.id,
            base: frame.base,
            values: values.into(),
            result_locals: Vec::new(),
            assignment_targets: targets,
            luau_compound_global: false,
            indexed_target: None,
            continuing_root: None,
            retained_copies: Vec::new(),
            replayed_effects: entries[first_write - start..entries.len() - 1]
                .iter()
                .map(|entry| entry.id)
                .collect(),
            removed,
        },
        end,
    ))
}

/// PUC 的末级 GETTABLE 写低槽目标；高槽 base 准备仍按原 Def 在赋值 RHS 内求值。
pub(super) fn lookup_result(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    run: &[&HirStmt],
    target: &HirLValue,
    access: &crate::hir::common::HirTableAccess,
) -> Option<Plan> {
    let result = facts.table_read_result_home(access)?;
    let target_home = match target {
        HirLValue::Local(local) => facts.trusted_local_home_slot(*local),
        HirLValue::Param(param) => facts.trusted_param_home_slot(*param),
        _ => return None,
    };
    if target_home != Some(result) || context.closed.contains(&result) {
        return None;
    }
    let layout = facts.native_table_read_layout(access);
    let upvalue_key = facts.upvalue_table_read_key(access);
    let frame = layout
        .map(|layout| {
            layout
                .key
                .filter(|key| {
                    key.slot() > result.slot()
                        && key.slot() + 1 == layout.base.slot()
                        && facts.table_key_preparation(access) == Some(*key)
                })
                .unwrap_or(layout.base)
        })
        .or_else(|| upvalue_key.map(|(_, home)| home))?;
    if frame.slot() <= result.slot() {
        return None;
    }
    let mut builder = frame_builder(context, run, facts, dialect, frame.slot())?;
    let (base, key) = if let Some((producer, home)) = upvalue_key {
        let key = builder.expr(
            &access.key,
            run.len(),
            home.slot(),
            None,
            false,
            true,
            Some(producer),
        )?;
        (access.base.clone(), key)
    } else {
        let layout = layout?;
        let producer = facts.table_read_base_value(access)?;
        // Lua 5.4 的动态上值索引先准备 key，再在其上方读取 base。
        // 5.1 的寄存器 base 则先于 key；按原准备布局重放，而非固定先读 base。
        let early_key = if layout.key == Some(frame) && frame != layout.base {
            if layout.base.slot() != frame.slot() + 1 {
                return None;
            }
            Some(builder.register_operand(&access.key, run.len(), frame.slot())?)
        } else {
            None
        };
        let base = builder.expr(
            &access.base,
            run.len(),
            layout.base.slot(),
            None,
            false,
            true,
            Some(producer),
        )?;
        let key = if let Some(key) = early_key {
            key
        } else if let Some(home) = layout.key {
            if builder.direct_home(&access.key) == Some(home) && home.slot() < layout.base.slot() {
                access.key.clone()
            } else {
                if home.slot() != layout.base.slot() + 1 {
                    return None;
                }
                builder.register_operand(&access.key, run.len(), home.slot())?
            }
        } else {
            if !context.constants_fit_rk || !tables::literal_rk(&access.key) {
                return None;
            }
            access.key.clone()
        };
        (base, key)
    };
    let start = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink: run.len(),
        base: frame,
        values: vec![HirExpr::TableAccess(Box::new(
            crate::hir::common::HirTableAccess {
                base,
                key,
                ..access.clone()
            },
        ))]
        .into(),
        result_locals: Vec::new(),
        assignment_targets: vec![target.clone()],
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}
