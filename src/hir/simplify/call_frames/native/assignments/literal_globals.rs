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
                    && scalar_local(entry.stmt).is_some_and(|(_, value)| literal(value))
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
                global_write(entry.stmt).is_some_and(|(_, _, value)| {
                    literal(value) || matches!(value, HirExpr::LocalRef(_))
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
    if !context.constants_fit_rk {
        return None;
    }
    let base = facts.trusted_local_home_slot(scalar_local(definitions.first()?.stmt)?.0)?;
    let mut locals = BTreeMap::new();
    for entry in definitions {
        let (local, value) = scalar_local(entry.stmt)?;
        if locals.insert(local, value).is_some() {
            return None;
        }
    }
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
        let original = if let HirExpr::LocalRef(local) = value {
            *locals.get(local)?
        } else {
            value
        };
        if !literal(original) {
            return None;
        }
        let input = if let Some((temp, home)) =
            facts.global_write_value_preparation(global, original)
        {
            if home != HomeSlotKey::new(base.slot() + offset, 0)
                || facts.global_write_value_home(global, dialect) != Some(home)
                || matches!(value, HirExpr::LocalRef(local) if facts.promoted_local_for_temp(temp) != Some(*local))
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
