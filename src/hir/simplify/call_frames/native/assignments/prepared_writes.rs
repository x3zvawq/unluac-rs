//! 恢复准备值到上值与表字段的完整赋值帧，支持单目标及同批写回。
//! 原操作提供输入版本和槽位；共享 builder 验证左值、RHS 准备及目标方言的写回顺序。

use super::*;

fn write(stmt: &HirStmt) -> Option<&crate::hir::common::HirAssign> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    (plain_copy(stmt)
        && matches!(
            assign.targets.as_slice(),
            [HirLValue::Upvalue(_) | HirLValue::TableAccess(_)]
        )
        && assign.values.fixed.len() == 1
        && assign.values.tail.is_none())
    .then_some(assign)
}

fn input_home(
    assign: &crate::hir::common::HirAssign,
    facts: &ProtoPromotionFacts,
) -> Option<HomeSlotKey> {
    match &assign.targets[0] {
        HirLValue::Upvalue(_) => Some(facts.upvalue_write_value(assign)?.1),
        HirLValue::TableAccess(access) => facts.native_table_write_layout(access)?.value,
        _ => None,
    }
}

fn prepared_value<'a>(builder: &FrameBuilder<'a>, value: &'a HirExpr) -> &'a HirExpr {
    if let HirExpr::LocalRef(local) = value
        && let Some(index) = builder.definition(*local, builder.run.len())
        && let Some((_, prepared)) = scalar_local(builder.run[index])
    {
        prepared
    } else {
        value
    }
}

pub(in crate::hir::simplify::call_frames::native) fn plans(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    flat: &[Option<FlatStmt<'_>>],
) -> BTreeMap<usize, (Plan, usize)> {
    let mut result = BTreeMap::new();
    let mut index = 0;
    while index < flat.len() {
        let start = index;
        while flat
            .get(index)
            .and_then(Option::as_ref)
            .is_some_and(|entry| plain_copy(entry.stmt) && scalar_local(entry.stmt).is_some())
        {
            index += 1;
        }
        if index == start {
            index += 1;
            continue;
        }
        let first_write = index;
        // 同一准备区后也可能紧跟独立的低槽上值写；按原输入槽的写回方向
        // 划定窗口，不能把这些语句拼成需要额外 scratch 的并列 RHS。
        let mut previous_home = None::<HomeSlotKey>;
        while let Some(assign) = flat
            .get(index)
            .and_then(Option::as_ref)
            .and_then(|entry| write(entry.stmt))
        {
            // JIT 的末项常量由 USETN/USETS/USETP 直接写 cell；逆序发布时
            // 它先于寄存器 RHS，不占也不推进准备槽序列。
            if dialect == DecompileDialect::Luajit
                && index == first_write
                && facts.literal_upvalue_write(assign)
            {
                index += 1;
                continue;
            }
            let Some(home) = input_home(assign, facts) else {
                break;
            };
            if let Some(previous) = previous_home {
                let ordered = if dialect == DecompileDialect::Luau {
                    home.slot() == previous.slot() + 1
                } else {
                    home.slot() + 1 == previous.slot()
                        || index == first_write + 1 && home.slot() > previous.slot()
                };
                if !ordered {
                    break;
                }
            }
            previous_home = Some(home);
            index += 1;
        }
        // 单目标 SETUPVAL 同样有原输入版本和完整准备区；无需第二个写回
        // 才能消费准备声明，后续仍由 candidate 核对原槽及完整求值顺序。
        if index == first_write {
            continue;
        }
        let definitions = flat[start..first_write]
            .iter()
            .map(|entry| entry.unwrap())
            .collect::<Vec<_>>();
        let writes = flat[first_write..index]
            .iter()
            .map(|entry| entry.unwrap())
            .collect::<Vec<_>>();
        if let Some((plan, first)) = candidate(context, facts, dialect, &definitions, &writes) {
            result.insert(start + first, (plan, index - 1));
        }
    }
    result
}

fn candidate(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    definitions: &[FlatStmt<'_>],
    writes: &[FlatStmt<'_>],
) -> Option<(Plan, usize)> {
    let mut ordered = writes.to_vec();
    if dialect != DecompileDialect::Luau {
        ordered.reverse();
    }
    let first = write(ordered.first()?.stmt)?;
    let rhs_base = input_home(first, facts)?;
    let run = definitions
        .iter()
        .map(|entry| entry.stmt)
        .collect::<Vec<_>>();
    let mut builder = frame_builder(context, &run, facts, dialect, rhs_base.slot())?;
    let mut targets = ordered
        .iter()
        .map(|entry| write(entry.stmt).map(|assign| assign.targets[0].clone()))
        .collect::<Option<Vec<_>>>()?;
    if targets.len() == 1 && matches!(targets[0], HirLValue::TableAccess(_)) {
        // 候选拒绝[ProofIncomplete]：单字段写可能仍属于尚未完成的构造器。
        // 其构造器根与后继字段由 indexed/tables owner 一起消费；这里只扩展并列写回。
        return None;
    }
    let mut base = rhs_base;
    for target in &targets {
        let HirLValue::TableAccess(access) = target else {
            continue;
        };
        let layout = facts.native_table_write_layout(access)?;
        if layout.key.is_some()
            || builder.literal_uses_rk(&access.key, Some((&access.sources, false))) != Some(true)
        {
            // 候选拒绝[ProofIncomplete]：动态 key 的原准备事务尚未在此消费。
            return None;
        }
        if let HirExpr::LocalRef(local) = access.base
            && builder.definition(local, run.len()).is_some()
        {
            let (_, home) = facts
                .table_write_base_preparation(access, prepared_value(&builder, &access.base))?;
            if home.slot() < base.slot() {
                base = home;
            }
        }
    }
    builder.base = base.slot();
    let mut next = base.slot();
    for target in &mut targets {
        let HirLValue::TableAccess(access) = target else {
            continue;
        };
        let layout = facts.native_table_write_layout(access)?;
        if layout.base.slot() < base.slot()
            && facts.direct_table_write_input_home(access, 0) == Some(layout.base)
        {
            continue;
        }
        let value = prepared_value(&builder, &access.base);
        let (producer, home) = facts.table_write_base_preparation(access, value)?;
        if home != layout.base
            || home.slot() != next
            || !super::super::indexed::snapshot_matches_target(value, home, access, facts, dialect)
        {
            // 候选拒绝[TargetConstraint]：所有计算左值必须按源码次序先于 RHS 准备，
            // SETTABUP 等不同读取时点不能伪造成提前的表快照。
            return None;
        }
        access.base = builder.expr(
            &access.base,
            run.len(),
            next,
            None,
            false,
            true,
            Some(producer),
        )?;
        next += 1;
    }
    if next != rhs_base.slot() {
        return None;
    }
    let mut values = Vec::with_capacity(writes.len());
    for (offset, entry) in ordered.iter().enumerate() {
        let assign = write(entry.stmt)?;
        let value = &assign.values.fixed[0];
        if dialect == DecompileDialect::Luajit
            && offset + 1 == ordered.len()
            && facts.literal_upvalue_write(assign)
        {
            values.push(value.clone());
            continue;
        }
        let (producer, home) = match &assign.targets[0] {
            HirLValue::Upvalue(_) => facts.upvalue_write_value(assign)?,
            HirLValue::TableAccess(access) => {
                let (producer, home) =
                    facts.table_write_value_preparation(access, prepared_value(&builder, value))?;
                (Some(producer), home)
            }
            _ => return None,
        };
        // PUC/JIT 可直接读取末项既有低槽；其它 RHS 必须依次占用连续 scratch。
        // 不以同名 Local/上值推断原输入，尚存的准备声明仍按确切 Def 消费。
        if home.slot() < rhs_base.slot() {
            if dialect == DecompileDialect::Luau
                || offset + 1 != ordered.len()
                || builder.direct_home(value) != Some(home)
            {
                // 候选拒绝[ProofIncomplete]：既有低槽只可对应方言允许直读的末项。
                return None;
            }
            values.push(value.clone());
        } else {
            if home.slot() != rhs_base.slot() + offset {
                // 候选拒绝[TargetConstraint]：源码并列 RHS 必须重发原连续准备槽。
                return None;
            }
            values.push(builder.expr(
                value,
                run.len(),
                home.slot(),
                None,
                false,
                true,
                producer,
            )?);
        }
    }
    let first = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    Some((
        Plan {
            prefix_at_sink: false,
            luau_function_declaration: false,
            start: definitions[first].id,
            sink: writes.last()?.id,
            base,
            values: values.into(),
            result_locals: Vec::new(),
            discarded_result: None,
            assignment_targets: targets,
            luau_compound_global: false,
            indexed_target: None,
            continuing_root: None,
            retained_copies: Vec::new(),
            replayed_effects: writes[..writes.len() - 1]
                .iter()
                .map(|entry| entry.id)
                .collect(),
            removed: definitions[first..]
                .iter()
                .chain(&writes[..writes.len() - 1])
                .map(|entry| entry.id)
                .collect(),
        },
        first,
    ))
}
