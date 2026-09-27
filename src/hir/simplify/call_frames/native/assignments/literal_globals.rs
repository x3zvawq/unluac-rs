//! 恢复连续字面量准备及全局写回的并列赋值帧。
//!
//! 全局环境可能带写入元方法，写回次序不能交换；每项准备依赖原 use→Def，
//! 方言的正序/逆序写回和末项 RK 规则在完整源码前缀事务内一起核对。

use super::*;

fn literal(value: &HirExpr) -> bool {
    matches!(
        value,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
    )
}

fn global_write(
    stmt: &HirStmt,
) -> Option<(&HirLValue, &crate::hir::common::HirGlobalRef, &HirExpr)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let ([target @ HirLValue::Global(global)], [value], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    plain_copy(stmt).then_some((target, global, value))
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
            .is_some_and(|entry| {
                plain_copy(entry.stmt)
                    && (scalar_local(entry.stmt).is_some_and(|(_, value)| literal(value))
                        || nil_argument_group(entry.stmt, facts).is_some())
            })
        {
            index += 1;
        }
        if index == start {
            index += 1;
            continue;
        }
        let first_write = index;
        while flat
            .get(index)
            .and_then(Option::as_ref)
            .is_some_and(|entry| {
                global_write(entry.stmt).is_some_and(|(_, global, value)| {
                    matches!(value, HirExpr::LocalRef(_) | HirExpr::TempRef(_))
                        || literal(value)
                            && (facts.global_write_has_no_preparation(global, dialect)
                                || facts
                                    .global_write_value_preparation(global, value)
                                    .is_some())
                })
            })
        {
            index += 1;
        }
        if index - first_write < 2 {
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
        if let Some(plan) = candidate(context, facts, dialect, &definitions, &writes) {
            result.insert(start, (plan, index - 1));
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
) -> Option<Plan> {
    let mut inputs = BTreeMap::new();
    let mut base = None;
    for entry in definitions {
        if let Some((local, value)) = scalar_local(entry.stmt) {
            base.get_or_insert(facts.trusted_local_home_slot(local)?);
            if inputs
                .insert(HirBinding::Local(local), value.clone())
                .is_some()
            {
                return None;
            }
        } else {
            // LOADNIL 的整组 Temp 由同一个原写产生；不能拆成单项初始化，
            // 否则会改变全局写元方法调用时可见的 scratch 根。
            for &temp in nil_argument_group(entry.stmt, facts)? {
                base.get_or_insert(facts.trusted_temp_home_slot(temp)?);
                if inputs
                    .insert(HirBinding::Temp(temp), HirExpr::Nil)
                    .is_some()
                {
                    return None;
                }
            }
        }
    }
    let base = base?;
    let run = definitions
        .iter()
        .map(|entry| entry.stmt)
        .collect::<Vec<_>>();
    let mut builder = frame_builder(context, &run, facts, dialect, base.slot())?;
    let mut targets = Vec::with_capacity(writes.len());
    let mut values = Vec::with_capacity(writes.len());
    for offset in 0..writes.len() {
        let write = &writes[if dialect == DecompileDialect::Luau {
            offset
        } else {
            writes.len() - offset - 1
        }];
        let (target, global, value) = global_write(write.stmt)?;
        let original = if let Some(binding) = HirBinding::from_expr(value) {
            inputs.get(&binding)?
        } else {
            value
        };
        if !literal(original) {
            return None;
        }
        let input = if let Some((temp, home)) = facts
            .global_write_value_preparation(global, original)
            .or_else(|| {
                matches!(original, HirExpr::Nil)
                    .then(|| facts.global_nil_batch_preparation(global))
                    .flatten()
            }) {
            if home.slot() != base.slot() + offset
                || facts.global_write_value_home(global, dialect) != Some(home)
                || matches!(value, HirExpr::LocalRef(local) if facts.promoted_local_for_temp(temp) != Some(*local))
                || matches!(value, HirExpr::TempRef(input) if *input != temp)
            {
                return None;
            }
            Some(temp)
        } else {
            // PUC/LuaJIT 末项可保留为 RK；其它项必须先装入对应 scratch。
            if dialect == DecompileDialect::Luau
                || offset + 1 != writes.len()
                || !literal(value)
                || !facts.global_write_has_no_preparation(global, dialect)
                || builder.literal_uses_rk(value, Some((&global.sources, true))) != Some(true)
            {
                return None;
            }
            None
        };
        values.push(builder.expr(
            value,
            run.len(),
            base.slot() + offset,
            None,
            false,
            true,
            input,
        )?);
        targets.push(target.clone());
    }
    if builder.first_event != Some(0) || builder.next_event != run.len() {
        return None;
    }
    let sink = writes.last()?.id;
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: definitions[0].id,
        sink,
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
        removed: definitions
            .iter()
            .chain(&writes[..writes.len() - 1])
            .map(|entry| entry.id)
            .collect(),
    })
}
