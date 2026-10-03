//! 恢复计算左值与标量 RHS 的同一原生赋值帧。
//!
//! 消费 Promotion 的 SETTABLE/SETTABUP 布局与输入 Def，由共享 builder 核对
//! 目标表读取、key 和 RHS 的准备顺序，再由父事务验证完整声明前后缀。

use super::*;
use crate::hir::common::{HirAssign, HirBinaryOpKind, HirExpr, HirTableAccess};

/// 并列 nil 字段写保留原左值布局，再一次准备 LOADNIL，最后逆序写回。
/// 每个目标快照及 RHS 成员都消费原 use→Def，不能拆开后改变元方法前的根覆盖。
pub(super) fn parallel_preparations(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    entries: &[Option<FlatStmt<'_>>],
    preparation_end: usize,
) -> Option<(Plan, usize)> {
    if !matches!(dialect, DecompileDialect::Lua51 | DecompileDialect::Luajit) {
        return None;
    }
    let group = nil_argument_group(entries.get(preparation_end)?.as_ref()?.stmt, facts);
    let direct_targets = dialect == DecompileDialect::Luajit;
    if direct_targets && group.is_none() {
        return None;
    }
    let first_write = preparation_end + usize::from(group.is_some());
    let width = group.as_ref().map_or(2, |group| group.len());
    let end = first_write + width - 1;
    let writes = entries
        .get(first_write..=end)?
        .iter()
        .copied()
        .collect::<Option<Vec<_>>>()?;
    fn parse(stmt: &HirStmt) -> Option<(&HirTableAccess, &HirExpr)> {
        let HirStmt::Assign(assign) = stmt else {
            return None;
        };
        let ([HirLValue::TableAccess(access)], [value], None) = (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail,
        ) else {
            return None;
        };
        assignments::plain_copy(stmt).then_some((access.as_ref(), value))
    }
    let (first, first_value) = parse(writes.last()?.stmt)?;
    let (last, last_value) = parse(writes.first()?.stmt)?;
    if HirBinding::from_expr(first_value).is_none()
        || HirBinding::from_expr(last_value).is_none()
        || facts.native_table_write_layout(first)?.value?.slot() + width - 1
            != facts.native_table_write_layout(last)?.value?.slot()
    {
        return None;
    }
    let first_layout = facts.native_table_write_layout(first)?;
    let base = if direct_targets {
        first_layout.value?
    } else {
        first_layout.base
    };
    // 先排除普通字段写；只有相邻写回确实属于同一并列帧时才索引准备区。
    // JIT 直接左值没有前置准备；只索引这一条 nil 批次，拒绝时也不重扫增长前缀。
    let run_start = if direct_targets { preparation_end } else { 0 };
    let run = entries[run_start..first_write]
        .iter()
        .map(|entry| entry.map(|entry| entry.stmt))
        .collect::<Option<Vec<_>>>()?;
    let mut builder = frame_builder(context, &run, facts, dialect, base.slot())?;
    let mut targets = Vec::with_capacity(writes.len());
    let mut next = base.slot();
    let mut rhs = Vec::with_capacity(width);
    for (offset, write) in writes.iter().rev().enumerate() {
        let (access, value) = parse(write.stmt)?;
        let layout = facts.native_table_write_layout(access)?;
        let (producer, home) = if let Some(group) = &group {
            let temp = group[offset];
            if *value != HirExpr::TempRef(temp) {
                return None;
            }
            facts.table_nil_batch_preparation(access)?
        } else {
            let prepared = match HirBinding::from_expr(value) {
                Some(binding) => run
                    .iter()
                    .rev()
                    .find_map(|stmt| {
                        scalar_binding(stmt).filter(|(written, _)| *written == binding)
                    })
                    .map(|(_, value)| value)?,
                None => value,
            };
            facts.table_write_value_preparation(access, prepared)?
        };
        if layout.value != Some(home) || !direct_targets && layout.base.slot() != next {
            return None;
        }
        rhs.push((value, producer, home));
        if direct_targets {
            // JIT 固定字段直接读取原低槽表，不额外制造左值快照。各次 SETTABLE
            // 仍按原逆序发布；整组 nil 由后面的 builder 一次消费并核对后缀。
            if layout.base.slot() >= base.slot()
                || facts.direct_table_write_input_home(access, 0) != Some(layout.base)
                || layout.key.is_some()
                || !tables::literal_rk(&access.key)
                || builder.literal_uses_rk(&access.key, Some((&access.sources, false)))
                    != Some(true)
            {
                return None;
            }
            targets.push(HirLValue::TableAccess(Box::new(access.clone())));
            continue;
        }
        let (binding, prepared) = HirBinding::from_expr(&access.base).and_then(|binding| {
            run[..preparation_end]
                .iter()
                .rev()
                .find_map(|stmt| scalar_binding(stmt).filter(|(written, _)| *written == binding))
        })?;
        let (producer, home) = facts.table_write_base_preparation(access, prepared)?;
        if home != layout.base
            || !match binding {
                HirBinding::Temp(temp) => temp == producer,
                HirBinding::Local(local) => facts.promoted_local_for_temp(producer) == Some(local),
                _ => false,
            }
        {
            return None;
        }
        let target = builder.expr(
            &access.base,
            preparation_end,
            next,
            None,
            false,
            true,
            Some(producer),
        )?;
        next += 1;
        let key = if let Some(home) = layout.key {
            if home.slot() != next {
                return None;
            }
            let previous = builder.register_operand;
            builder.register_operand = true;
            let key = builder.expr(&access.key, preparation_end, next, None, false, true, None)?;
            builder.register_operand = previous;
            if builder.literal_uses_rk(&key, Some((&access.sources, false))) != Some(false) {
                return None;
            }
            next += 1;
            key
        } else {
            if builder.literal_uses_rk(&access.key, Some((&access.sources, false))) != Some(true) {
                return None;
            }
            access.key.clone()
        };
        targets.push(HirLValue::TableAccess(Box::new(HirTableAccess {
            base: target,
            key,
            ..access.clone()
        })));
    }
    let mut values = Vec::with_capacity(width);
    for (offset, (value, producer, home)) in rhs.into_iter().enumerate() {
        if home.slot() != next + offset {
            return None;
        }
        values.push(builder.expr(
            value,
            run.len(),
            next + offset,
            None,
            false,
            true,
            Some(producer),
        )?);
    }
    let start = run_start + builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    Some((
        Plan {
            prefix_at_sink: false,
            luau_function_declaration: false,
            start: entries[start]?.id,
            sink: writes.last()?.id,
            base,
            values: values.into(),
            result_locals: Vec::new(),
            assignment_targets: targets,
            luau_compound_global: false,
            indexed_target: None,
            continuing_root: None,
            retained_copies: Vec::new(),
            replayed_effects: writes[..writes.len() - 1]
                .iter()
                .map(|entry| entry.id)
                .collect(),
            removed: entries[start..end]
                .iter()
                .map(|entry| entry.unwrap().id)
                .collect(),
        },
        end,
    ))
}

/// Luau 并列固定字段写先连续准备 RHS，再按源码顺序写回；两个准备槽须一起退休。
pub(super) fn parallel_literals(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    entries: [FlatStmt<'_>; 4],
) -> Option<Plan> {
    if dialect != DecompileDialect::Luau {
        return None;
    }
    let [first, second, write_first, write_second] = entries;
    let run = [first.stmt, second.stmt];
    let (first_local, _) = scalar_local(first.stmt)?;
    let base = facts.trusted_local_home_slot(first_local)?;
    let mut builder = frame_builder(context, &run, facts, dialect, base.slot())?;
    let mut targets = Vec::with_capacity(2);
    let mut values = Vec::with_capacity(2);
    for (offset, (preparation, write)) in
        run.into_iter().zip([write_first, write_second]).enumerate()
    {
        let (local, literal) = scalar_local(preparation)?;
        let HirStmt::Assign(assign) = write.stmt else {
            return None;
        };
        let ([HirLValue::TableAccess(access)], [value], None) = (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail,
        ) else {
            return None;
        };
        let home = facts.luau_literal_table_write_frame(access, literal)?;
        if home.slot() != base.slot() + offset
            || facts.trusted_local_home_slot(local) != Some(home)
            || value != &HirExpr::LocalRef(local)
            || facts.native_table_write_layout(access)?.base.slot() >= base.slot()
            || assign.initializer_merge_transaction.is_some()
            || assign.generic_for_initializer_producer.is_some()
            || assign.root_release.is_some()
            || assign.method_rewrite_transaction.is_some()
        {
            return None;
        }
        let (producer, original_home) = facts.table_write_value_preparation(access, literal)?;
        if original_home != home || facts.promoted_local_for_temp(producer) != Some(local) {
            return None;
        }
        // SETTABLE 的 use-to-Def 许可让同槽重发消费 PhysicalFramePrefix；
        // 不能仅因当前字面量相等就把旧槽版本当作本次准备。
        values.push(builder.expr(
            value,
            run.len(),
            home.slot(),
            None,
            false,
            true,
            Some(producer),
        )?);
        targets.push(assign.targets[0].clone());
    }
    if builder.first_event != Some(0) || builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: first.id,
        sink: write_second.id,
        base,
        values: values.into(),
        result_locals: Vec::new(),
        assignment_targets: targets,
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: vec![write_first.id],
        removed: vec![first.id, second.id, write_first.id],
    })
}

/// 两项字段赋值的首个 RHS 在高槽准备，末项直接读低槽或 RK；PUC/JIT 逆序写回两个字段。
/// 把快照连同两次写一起重发，避免独立 local 延长到后继复用该槽的调用。
pub(super) fn parallel_values(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    preparations: &[Option<FlatStmt<'_>>],
    first: FlatStmt<'_>,
    second: FlatStmt<'_>,
    last: FlatStmt<'_>,
) -> Option<Plan> {
    if dialect == DecompileDialect::Luau || !context.constants_fit_rk {
        return None;
    }
    if !assignments::plain_copy(first.stmt) {
        return None;
    }
    let (snapshot, source) = scalar_local(first.stmt)?;
    let direct_home = |value: &HirExpr| match value {
        HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local),
        HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param),
        _ => None,
    };
    let home = facts.trusted_local_home_slot(snapshot)?;
    if !(tables::literal_rk(source)
        || direct_home(source).is_some_and(|source| source.slot() < home.slot()))
        || context.barred.contains(&home)
        || context.closed.contains(&home)
        || context.proto.local_debug_hints[snapshot.index()].is_some()
        || context.proto.local_debug_scopes[snapshot.index()].is_some()
        || context
            .proto
            .inline_dispositions
            .local(snapshot)
            .must_preserve()
    {
        return None;
    }
    let (HirStmt::Assign(write_second), HirStmt::Assign(write_first)) = (second.stmt, last.stmt)
    else {
        return None;
    };
    if [write_first, write_second].iter().any(|assign| {
        assign.initializer_merge_transaction.is_some()
            || assign.generic_for_initializer_producer.is_some()
            || assign.root_release.is_some()
            || assign.method_rewrite_transaction.is_some()
    }) {
        return None;
    }
    let ([HirLValue::TableAccess(second_target)], [second_value], None) = (
        write_second.targets.as_slice(),
        write_second.values.fixed.as_slice(),
        &write_second.values.tail,
    ) else {
        return None;
    };
    let ([HirLValue::TableAccess(first_target)], [HirExpr::LocalRef(read)], None) = (
        write_first.targets.as_slice(),
        write_first.values.fixed.as_slice(),
        &write_first.values.tail,
    ) else {
        return None;
    };
    let second_home = if tables::literal_rk(second_value) {
        None
    } else {
        Some(direct_home(second_value)?)
    };
    if *read != snapshot || second_home.is_some_and(|second| second.slot() >= home.slot()) {
        return None;
    }
    if tables::literal_rk(source) || !matches!(first.stmt, HirStmt::LocalDecl(_)) {
        // 新的常量准备或复用写必须消费本次 SETTABLE 的原 use→Def，不能把
        // 同槽较早的字面量或后继 callee 版本当作并列 RHS。旧根退休仍由整批验证。
        let (producer, original_home) =
            facts.table_write_value_preparation(first_target, source)?;
        if original_home != home || facts.promoted_local_for_temp(producer) != Some(snapshot) {
            return None;
        }
    }
    for (target, value) in [(first_target, Some(home)), (second_target, second_home)] {
        let (key, original_value) = if let Some(layout) = facts.native_table_write_layout(target) {
            if layout.base != direct_home(&target.base)? || layout.base.slot() >= home.slot() {
                return None;
            }
            (layout.key, layout.value)
        } else {
            // 5.2/5.3 的 SETTABUP 在各次写入时读取 cell，源码并行赋值也保留这个时点。
            // 不为它伪造 GETUPVAL 快照；其它方言的目标准备继续走寄存器布局。
            if !matches!(dialect, DecompileDialect::Lua52 | DecompileDialect::Lua53) {
                return None;
            }
            let layout = facts.native_upvalue_table_write_layout(target)?;
            if target.base != HirExpr::UpvalueRef(layout.base) {
                return None;
            }
            (layout.key, layout.value)
        };
        if key.is_some()
            || !matches!(
                target.key,
                HirExpr::String(_) | HirExpr::Integer(_) | HirExpr::Number(_)
            )
            || original_value != value
        {
            return None;
        }
    }
    let mut plan = Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: first.id,
        sink: last.id,
        base: home,
        values: vec![source.clone(), second_value.clone()].into(),
        result_locals: Vec::new(),
        assignment_targets: vec![
            write_first.targets[0].clone(),
            write_second.targets[0].clone(),
        ],
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: vec![second.id],
        removed: vec![first.id, second.id],
    };
    if let Some((base, targets, removed)) = prepared_parallel_targets(
        context,
        facts,
        dialect,
        preparations,
        [first_target, second_target],
        home,
    ) {
        plan.start = removed[0];
        plan.base = base;
        plan.assignment_targets = targets;
        plan.removed.splice(0..0, removed);
    }
    Some(plan)
}

/// 两个 GETUPVAL 先固定左值，再准备 RHS；末项 SETTABLE 的元方法可以改写
/// 目标 cell，因此两次读取必须一起留在写入之前，不能逐条赋值各自内联。
fn prepared_parallel_targets(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    preparations: &[Option<FlatStmt<'_>>],
    targets: [&HirTableAccess; 2],
    rhs: HomeSlotKey,
) -> Option<(HomeSlotKey, Vec<HirLValue>, Vec<usize>)> {
    let [Some(first), Some(second)] = preparations.get(preparations.len().checked_sub(2)?..)?
    else {
        return None;
    };
    let run = [first.stmt, second.stmt];
    let base = facts.native_table_write_layout(targets[0])?.base;
    if rhs.slot() != base.slot() + 2 {
        return None;
    }
    let mut builder = frame_builder(context, &run, facts, dialect, base.slot())?;
    let mut rebuilt = Vec::with_capacity(2);
    for (index, target) in targets.into_iter().enumerate() {
        let (local, value @ HirExpr::UpvalueRef(_)) = scalar_local(run[index])? else {
            return None;
        };
        let (producer, home) = facts.table_write_base_preparation(target, value)?;
        if target.base != HirExpr::LocalRef(local)
            || facts.promoted_local_for_temp(producer) != Some(local)
            || home.slot() != base.slot() + index
            || facts.native_table_write_layout(target)?.base != home
        {
            return None;
        }
        let mut target = target.clone();
        target.base = builder.expr(
            &target.base,
            run.len(),
            home.slot(),
            None,
            false,
            true,
            Some(producer),
        )?;
        rebuilt.push(HirLValue::TableAccess(Box::new(target)));
    }
    (builder.first_event == Some(0) && builder.next_event == run.len()).then_some((
        base,
        rebuilt,
        vec![first.id, second.id],
    ))
}

// SETTABLE 的输入 Def 只证明原快照身份，并不证明源码仍会在同一时点读取 cell。
// 5.2/5.3 直接写上值表使用 SETTABUP；5.4+ 动态 key 在 key 之后快照目标，
// 整数 SETI 则在 RHS 之前快照，字符串 SETTABUP 仍在 RHS 之后读取 cell。
// 显式提前保存的上值表必须继续作为独立 local，不能套用其它方言的左值准备顺序。
pub(super) fn snapshot_matches_target(
    source: &HirExpr,
    home: HomeSlotKey,
    access: &HirTableAccess,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> bool {
    if !matches!(source, HirExpr::UpvalueRef(_)) {
        return true;
    }
    match dialect {
        DecompileDialect::Lua52 | DecompileDialect::Lua53 => false,
        DecompileDialect::Lua54 | DecompileDialect::Lua55 => {
            let key = facts
                .native_table_write_layout(access)
                .and_then(|layout| layout.key);
            key.is_some_and(|key| {
                home.slot().abs_diff(key.slot()) == 1
                    // 已有低槽 key 不产生准备事件；GETUPVAL 使用当前空闲槽，
                    // 两者之间可有其它声明或隐式 vararg 表。直接输入身份由原
                    // SETTABLE 核对，快照与 RHS 的完整顺序仍由 builder 验证。
                    || (key.slot() < home.slot()
                        && facts.direct_table_write_input_home(access, 1) == Some(key))
            }) || (key.is_none() && matches!(access.key, HirExpr::Integer(_)))
        }
        _ => true,
    }
}

/// 仅用于识别完整赋值候选；原结果槽、RK 与左值准备仍由 plan 验证。
pub(super) fn is_rhs_candidate(value: &HirExpr) -> bool {
    matches!(
        value,
        HirExpr::Binary(_)
            | HirExpr::Closure(_)
            | HirExpr::Unary(_)
            | HirExpr::Call(_)
            | HirExpr::TableAccess(_)
            | HirExpr::TableConstructor(_)
            | HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::LocalRef(_)
            | HirExpr::TempRef(_)
            | HirExpr::ParamRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::GlobalRef(_)
    )
}

pub(super) fn is_candidate(assign: &HirAssign) -> bool {
    !assign.luau_function_declaration
        && matches!(
            (
                assign.targets.as_slice(),
                assign.values.fixed.as_slice(),
                &assign.values.tail
            ),
            ([HirLValue::TableAccess(_)], [_], None)
        )
}

/// 合成反相仍消费同一个比较的 Boolean 写回；原 NOT 不属于该结果身份。
fn comparison_result(value: &HirExpr, facts: &ProtoPromotionFacts) -> Option<TempId> {
    match value {
        HirExpr::Binary(binary) => facts.comparison_result_temp(binary),
        HirExpr::Unary(unary)
            if unary.source_site.is_none()
                && unary.op == crate::hir::common::HirUnaryOpKind::Not =>
        {
            match &unary.expr {
                HirExpr::Binary(binary) => facts.comparison_result_temp(binary),
                _ => None,
            }
        }
        _ => None,
    }
}

/// 单字段和并列左值共用原 key Def 与 scratch 证明；调用方验证整个赋值的事件顺序。
pub(super) fn prepared_key(
    builder: &mut FrameBuilder<'_>,
    access: &HirTableAccess,
    home: HomeSlotKey,
    base: usize,
) -> Option<HirExpr> {
    // Luau 的复合 key 从 key 上一槽开始；PUC/JIT 可复用该目标尚未写入的 base 槽。
    let previous_key_base =
        builder
            .indexed_key_base
            .replace(if builder.dialect == DecompileDialect::Luau {
                home.slot()
            } else {
                base
            });
    let prepared = if let HirExpr::LocalRef(local) = access.key {
        builder
            .definition(local, builder.run.len())
            .and_then(|index| scalar_local(builder.run[index]).map(|(_, value)| value))
            .unwrap_or(&access.key)
    } else {
        &access.key
    };
    let prepared_register = matches!(prepared, HirExpr::UpvalueRef(_))
        || (tables::literal_rk(prepared)
            && builder.table_key_uses_rk(access, prepared) == Some(false));
    let producer = if prepared_register || matches!(access.key, HirExpr::TempRef(_)) {
        let (producer, original) = builder.facts.table_key_value_preparation(access)?;
        if original != home {
            return None;
        }
        Some(producer)
    } else {
        None
    };
    let previous_register_operand =
        std::mem::replace(&mut builder.register_operand, producer.is_none());
    let key = builder.expr(
        &access.key,
        builder.run.len(),
        home.slot(),
        None,
        false,
        true,
        producer,
    );
    builder.register_operand = previous_register_operand;
    builder.indexed_key_base = previous_key_base;
    key
}

pub(super) fn plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    assign: &HirAssign,
    rhs_live_after: bool,
    retain_key_prefix: bool,
) -> Option<Plan> {
    let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    if !rhs_live_after
        && let Some(plan) = function_declaration(context, run, facts, dialect, access, value)
    {
        return Some(plan);
    }
    if let Some(plan) = prepared_field_target(context, run, facts, dialect, access, value) {
        return Some(plan);
    }
    let register_layout = facts.native_table_write_layout(access);
    let upvalue_layout = facts.native_upvalue_table_write_layout(access);
    let direct_rhs_home = match value {
        HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local),
        HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param),
        _ => None,
    }
    .filter(|home| {
        let (key, original) = register_layout
            .map(|layout| (layout.key, layout.value))
            .or_else(|| upvalue_layout.map(|layout| (layout.key, layout.value)))
            .unwrap_or((None, None));
        original == Some(*home) && key.is_some_and(|key| home.slot() < key.slot())
    });
    let (rhs, result_binding) = match value {
        value if direct_rhs_home.is_some() => (value, None),
        value @ (HirExpr::LocalRef(_) | HirExpr::TempRef(_)) => {
            let binding = HirBinding::from_expr(value)?;
            // SETLIST/字段写属于同一个构造器 RHS，seed 不一定紧邻最终 SETTABLE。
            // builder 仍核对所选版本及全部中间事件，不能跳过独立语句。
            let (_, rhs) = run
                .iter()
                .rev()
                .find_map(|stmt| scalar_binding(stmt).filter(|(target, _)| *target == binding))?;
            (rhs, Some(binding))
        }
        value => (value, None),
    };
    if !context.constants_fit_rk && dialect != DecompileDialect::Luau {
        let key = HirBinding::from_expr(&access.key)
            .and_then(|binding| {
                run.iter().rev().find_map(|stmt| {
                    scalar_binding(stmt)
                        .filter(|(written, _)| *written == binding)
                        .map(|(_, value)| value)
                })
            })
            .unwrap_or(&access.key);
        let layout = register_layout?;
        // 字面 key 核对 RK/LOADK；动态 key 必须保留原寄存器输入，内部常量
        // 再由共享表达式 builder 逐层核对，不能因整个池较大而拒绝无 RK 的目标。
        if dialect == DecompileDialect::Luajit
            || if tables::literal_rk(key) {
                context.literal_uses_rk(key, Some((&access.sources, false)), dialect)
                    != Some(layout.key.is_none())
            } else {
                layout.key.is_none()
            }
            || (tables::literal_rk(rhs)
                && context.literal_uses_rk(rhs, Some((&access.sources, true)), dialect)
                    != Some(layout.value.is_none()))
        {
            return None;
        }
    }
    // 候选拒绝[SemanticBarrier:BindingIdentity]：RHS 仍被后缀读取，或其声明仍承接后继覆盖。
    // 现成低槽 RHS 不在本事务删除范围内；不能因此阻止其独立 key/base 准备。
    if result_binding.is_some() && rhs_live_after {
        return None;
    }
    // 动态 key 后的字面量也有原 LOAD Def；Luau 与 JIT 都须保留其 RHS 槽，
    // 不能只接受固定字段，或误套用 PUC 的 RK 常量布局。
    let prepared_literal = ((matches!(dialect, DecompileDialect::Luajit | DecompileDialect::Luau)
        || !context.constants_fit_rk)
        && tables::literal_rk(rhs))
    .then(|| facts.table_write_value_preparation(access, rhs))
    .flatten();
    let comparison = comparison_result(rhs, facts);
    // 原 SETTABLE 的 phi 输入与当前 binding 一起确认短路值身份；完整 builder
    // 仍逐叶证明读取及结果槽，不能仅凭同槽或相似表达式认领另一版值。
    let selection = matches!(rhs, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))
        .then(|| facts.table_write_value_phi(access))
        .flatten()
        .filter(|result| match result_binding {
            Some(HirBinding::Temp(temp)) => temp == *result,
            Some(HirBinding::Local(local)) => facts.promoted_local_for_temp(*result) == Some(local),
            _ => false,
        });
    if matches!(rhs, HirExpr::UpvalueRef(_)) {
        // GETUPVAL 的原准备 Def 与字段写布局由同一 owner 核对；所有方言都
        // 需要重发原读取槽，不能把它误送到仅接受字面量的 Luau 分支。
        return scalar_rhs(
            context,
            run,
            facts,
            dialect,
            access,
            value,
            rhs,
            result_binding,
        );
    }
    if dialect == DecompileDialect::Luau
        && comparison.is_none()
        && selection.is_none()
        && prepared_literal.is_none()
        && direct_rhs_home.is_none()
        && !matches!(rhs, HirExpr::Call(_))
        && !matches!(rhs, HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Concat)
        && !matches!(rhs, HirExpr::Binary(binary) if is_scalar_binary_operation(binary.op))
    {
        // Luau 的字面量或分配 RHS 仍在原 scratch 准备，再写入目标的固定字段；
        // 不套用 PUC 的 RK 消除规则。CALL/CONCAT 则交下方连续 key/result 帧证明。
        if matches!(rhs, HirExpr::Closure(_) | HirExpr::TableConstructor(_)) {
            facts.luau_allocation_table_write_frame(access, rhs)?;
        } else {
            result_binding?;
            facts.luau_literal_table_write_frame(access, rhs)?;
        }
        return scalar_rhs(
            context,
            run,
            facts,
            dialect,
            access,
            value,
            rhs,
            result_binding,
        );
    }
    // JIT 的直接低槽 RHS 不需重新准备；算术由 register_arithmetic 逐槽验证，
    // 查表由 register_lookup 验证；闭包在 scalar_rhs 核对原创建 Def 与 capture，
    // CALL gap 与连续拼接区仍各自使用原协议。
    if dialect == DecompileDialect::Luajit
        && selection.is_none()
        && prepared_literal.is_none()
        && direct_rhs_home.is_none()
        && !(matches!(
            rhs,
            HirExpr::Call(_)
                | HirExpr::TableAccess(_)
                | HirExpr::Closure(_)
                | HirExpr::TableConstructor(_)
        ) || matches!(rhs, HirExpr::Binary(binary) if (is_scalar_binary_operation(binary.op) || binary.op == crate::hir::common::HirBinaryOpKind::Concat)))
    {
        return None;
    }
    let (key_home, value_home) = if let Some(layout) = register_layout {
        (layout.key, layout.value)
    } else {
        let layout = upvalue_layout?;
        if access.base != HirExpr::UpvalueRef(layout.base) {
            return None;
        }
        (layout.key, layout.value)
    };
    let literal_rhs = value_home.is_none()
        && result_binding.is_none()
        && matches!(
            rhs,
            HirExpr::Nil
                | HirExpr::Boolean(_)
                | HirExpr::Integer(_)
                | HirExpr::Number(_)
                | HirExpr::String(_)
        );
    if !(matches!(rhs, HirExpr::Binary(binary) if (is_scalar_binary_operation(binary.op) || binary.op == crate::hir::common::HirBinaryOpKind::Concat))
        || matches!(rhs, HirExpr::Call(_))
        || matches!(
            rhs,
            HirExpr::TableConstructor(_)
                | HirExpr::TableAccess(_)
                | HirExpr::GlobalRef(_)
                | HirExpr::Closure(_)
        )
        || comparison.is_some()
        || selection.is_some()
        || direct_rhs_home.is_some()
        || literal_rhs
        || prepared_literal.is_some())
        || key_home.is_none()
    {
        return scalar_rhs(
            context,
            run,
            facts,
            dialect,
            access,
            value,
            rhs,
            result_binding,
        );
    }
    let existing_key_frame = key_home.is_some_and(|key| {
        facts.direct_table_write_input_home(access, 1) == Some(key)
            && value_home.is_some_and(|value| key.slot() < value.slot())
    });
    let existing_key = || {
        // key 也可以是循环变量等已有低槽输入，此时只准备 RHS。
        // 仍由原 SETTABLE 输入身份及 scalar_rhs 的完整事件/前缀证明约束。
        existing_key_frame
            .then(|| {
                scalar_rhs(
                    context,
                    run,
                    facts,
                    dialect,
                    access,
                    value,
                    rhs,
                    result_binding,
                )
            })
            .flatten()
    };
    if retain_key_prefix && existing_key_frame {
        // 已消费的高槽 RHS 仍可能依赖 key 的声明位置；没有新事件时不能删除它。
        // 字面量准备不产生独立结果根，仍可由完整 key/RHS 事务共同恢复。
        let plan = existing_key();
        if plan.is_some() || prepared_literal.is_none() {
            return plan;
        }
    }
    // 没有后继声明依赖时，优先证明包含 key 准备的完整帧；
    // 否则会把 #out + 1 等原准备永久冻结为声明。
    let prepared_key = (|| {
        let result = if literal_rhs || direct_rhs_home.is_some() {
            None
        } else if let Some((temp, _)) = prepared_literal {
            Some(temp)
        } else if let Some(result) = comparison.or(selection) {
            // 比较及短路值使用原合流写回，不能借谓词操作数猜 RHS 槽。
            Some(result)
        } else {
            let source = match rhs {
                HirExpr::Binary(binary) => binary.source_site?,
                HirExpr::Call(call) => call.source_site?,
                HirExpr::Closure(closure) => closure.source_site?,
                HirExpr::TableAccess(access) => {
                    let crate::hir::common::HirOperationSources::Single(source) = access.sources
                    else {
                        return None;
                    };
                    source
                }
                HirExpr::GlobalRef(global) => {
                    let crate::hir::common::HirOperationSources::Single(source) = global.sources
                    else {
                        return None;
                    };
                    source
                }
                HirExpr::TableConstructor(table) => {
                    let crate::hir::common::HirOperationSources::Single(source) = table.sources
                    else {
                        return None;
                    };
                    source
                }
                _ => return None,
            };
            Some(facts.operation_result_temp(source)?)
        };
        let key_home = key_home?;
        let direct_base = match &access.base {
            HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local),
            HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param),
            _ => None,
        }
        .filter(|home| {
            register_layout.is_some_and(|layout| *home == layout.base)
                && home.slot() < key_home.slot()
        });
        // 动态 key 前的全局/上值目标快照同样由原 SETTABLE use-to-Def 识别。
        // Temp 与 Local 只是当前物化状态，不能因此漏掉同一段左值准备。
        let snapshot = match &access.base {
            HirExpr::TempRef(_) | HirExpr::LocalRef(_) => run
                .iter()
                .rev()
                .find_map(|stmt| {
                    let (binding, source) = scalar_binding(stmt)?;
                    let matches = match (&access.base, binding) {
                        (HirExpr::TempRef(read), HirBinding::Temp(write)) => *read == write,
                        (HirExpr::LocalRef(read), HirBinding::Local(write)) => *read == write,
                        _ => false,
                    };
                    matches.then_some((binding, source))
                })
                .and_then(|(binding, source)| {
                    if !matches!(
                        source,
                        HirExpr::UpvalueRef(_) | HirExpr::GlobalRef(_) | HirExpr::TableAccess(_)
                    ) {
                        return None;
                    }
                    let (producer, home) = facts.table_write_base_preparation(access, source)?;
                    let same_definition = match binding {
                        HirBinding::Temp(temp) => temp == producer,
                        HirBinding::Local(local) => {
                            facts.promoted_local_for_temp(producer) == Some(local)
                        }
                        _ => false,
                    };
                    (same_definition
                        && register_layout.is_some_and(|layout| home == layout.base)
                        && snapshot_matches_target(source, home, access, facts, dialect))
                    .then_some((producer, home, matches!(source, HirExpr::UpvalueRef(_))))
                }),
            HirExpr::UpvalueRef(_) | HirExpr::GlobalRef(_) | HirExpr::TableAccess(_)
                if register_layout.is_some() =>
            {
                facts
                    .table_write_base_preparation(access, &access.base)
                    .filter(|(_, home)| {
                        snapshot_matches_target(&access.base, *home, access, facts, dialect)
                    })
                    .map(|(producer, home)| {
                        (
                            producer,
                            home,
                            matches!(access.base, HirExpr::UpvalueRef(_)),
                        )
                    })
            }
            _ => None,
        };

        let rhs_slot = snapshot.map_or(key_home.slot(), |(_, home, _)| {
            home.slot().max(key_home.slot())
        }) + 1;
        if let Some(result) = result
            && (facts.trusted_temp_home_slot(result) != value_home
                || value_home != Some(HomeSlotKey::new(rhs_slot, 0)))
        {
            return None;
        }
        let base = if let Some((_, home, _)) = snapshot {
            if key_home == HomeSlotKey::new(home.slot() + 1, 0) {
                home
            } else if matches!(dialect, DecompileDialect::Lua54 | DecompileDialect::Lua55)
                && home == HomeSlotKey::new(key_home.slot() + 1, 0)
            {
                // key 的 CALL 先占 free slot，随后 GETUPVAL 在其上一槽准备目标；
                // RHS 从目标上一槽开始，整个事务仍从 key 槽按原顺序验证。
                key_home
            } else {
                return None;
            }
        } else {
            if upvalue_layout.is_none() {
                direct_base?;
            }
            key_home
        };
        if direct_rhs_home.is_some_and(|home| home.slot() >= base.slot()) {
            // 只保留左值准备区之下的原寄存器读取，不把准备区中的 RHS 快照当成已有值。
            return None;
        }
        let mut builder = frame_builder(context, run, facts, dialect, base.slot())?;
        // Lua 5.1/JIT/Luau 在 key 之前保存上值目标；5.4+ 的动态索引先计算 key，随后
        // GETUPVAL 保存目标。SETTABUP 则始终在 RHS 后读取 cell，不生成快照。
        // 因而 log[#log+1]=f() 中 __len 与 f 改写同名 log cell 时，不能只凭名字合并读取。
        let early_base = if snapshot.is_some_and(|(_, home, upvalue)| {
            home.slot() < key_home.slot()
                && !(upvalue
                    && matches!(dialect, DecompileDialect::Lua54 | DecompileDialect::Lua55))
        }) {
            if let Some((producer, home, _)) = snapshot {
                Some(builder.expr(
                    &access.base,
                    run.len(),
                    home.slot(),
                    None,
                    false,
                    true,
                    Some(producer),
                )?)
            } else {
                None
            }
        } else {
            None
        };
        let key = prepared_key(&mut builder, access, key_home, base.slot())?;
        let target_base = if let Some(base) = early_base {
            base
        } else if let Some((producer, home, _)) = snapshot {
            builder.expr(
                &access.base,
                run.len(),
                home.slot(),
                None,
                false,
                true,
                Some(producer),
            )?
        } else {
            access.base.clone()
        };
        // 字段 RHS 的低槽 base 与计算 key 必须按原 GETTABLE 布局核对，
        // 不能只凭字面字段名走一般 CALL 参数的语法重建入口。
        builder.register_operand = matches!(rhs, HirExpr::TableAccess(_));
        let value = if literal_rhs || direct_rhs_home.is_some() {
            // RK 常量和既有低槽都不需新 RHS 准备；低槽读取仍留在 key 求值后的写入点。
            rhs.clone()
        } else if prepared_literal.is_some() || result_binding.is_some() {
            // JIT/Luau 字面量仍在 key 后的原槽加载；连同现存准备声明一起消费，
            // 不能把这个写入当成 PUC 的 RK 直接省掉。
            builder.expr(
                value,
                run.len(),
                value_home?.slot(),
                None,
                false,
                true,
                result,
            )?
        } else {
            match rhs {
                value if comparison.is_some() => builder.expr(
                    value,
                    run.len(),
                    value_home?.slot(),
                    None,
                    false,
                    true,
                    result,
                )?,
                HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Concat => {
                    builder.concat(binary, run.len(), value_home?.slot())?
                }
                HirExpr::Binary(_) => builder.expr(
                    rhs,
                    run.len(),
                    value_home?.slot(),
                    None,
                    false,
                    true,
                    result,
                )?,
                HirExpr::Call(call) => HirExpr::Call(Box::new(builder.call(
                    call,
                    run.len(),
                    value_home?.slot(),
                    true,
                    CallWidth::Single,
                )?)),
                // 字段 RHS 同样在 key 后的相邻槽读取；完整 lookup 由共享 builder 验证，
                // 不先冻结 key 声明再把其后续同槽值连成一个 Local 身份。
                HirExpr::TableConstructor(_)
                | HirExpr::TableAccess(_)
                | HirExpr::GlobalRef(_)
                | HirExpr::Closure(_) => builder.expr(
                    rhs,
                    run.len(),
                    value_home?.slot(),
                    None,
                    false,
                    true,
                    result,
                )?,
                _ => return None,
            }
        };
        let start = builder.first_event?;
        // 候选拒绝[ProofIncomplete]：只能收回一次完整连续准备区，遗漏的事件或独立快照不能跨越。
        if builder.next_event != run.len() {
            return None;
        }
        Some(Plan {
            prefix_at_sink: false,
            luau_function_declaration: false,
            start,
            sink: run.len(),
            base,
            values: vec![value].into(),
            result_locals: Vec::new(),
            assignment_targets: Vec::new(),
            luau_compound_global: false,
            indexed_target: Some(HirTableAccess {
                base: target_base,
                key,
                ..access.as_ref().clone()
            }),
            continuing_root: None,
            retained_copies: Vec::new(),
            replayed_effects: Vec::new(),
            removed: Vec::new(),
        })
    })();
    prepared_key.or_else(existing_key)
}

/// Luau 的具名字段函数先创建闭包，再读取全局目标；这是声明帧，不能重发为普通赋值。
fn function_declaration(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    access: &HirTableAccess,
    value: &HirExpr,
) -> Option<Plan> {
    if dialect != DecompileDialect::Luau || !context.constants_fit_rk {
        return None;
    }
    let HirExpr::LocalRef(local) = value else {
        return None;
    };
    let layout = facts.native_table_write_layout(access)?;
    let base = layout.value?;
    if layout.key.is_some()
        || layout.base != HomeSlotKey::new(base.slot() + 1, 0)
        || !matches!(&access.key, HirExpr::String(key)
            if key.as_utf8().is_some_and(|name| dialect.is_identifier_name(name)))
    {
        return None;
    }
    let mut builder = frame_builder(context, run, facts, dialect, base.slot())?;
    let definition = builder.definition(*local, run.len())?;
    let (_, HirExpr::Closure(closure)) = scalar_local(run[definition])? else {
        return None;
    };
    let source = closure.source_site?;
    let producer = facts.operation_result_temp(source)?;
    if facts.operation_result_home(source) != Some(base) {
        return None;
    }
    let prepared = match &access.base {
        HirExpr::LocalRef(target) => scalar_local(run[builder.definition(*target, run.len())?])?.1,
        target => target,
    };
    let HirExpr::GlobalRef(global) = prepared else {
        return None;
    };
    if !global
        .key
        .as_utf8()
        .is_some_and(|name| dialect.is_identifier_name(name))
    {
        return None;
    }
    let (target_producer, target_home) = facts.table_write_base_preparation(access, prepared)?;
    if target_home != layout.base {
        return None;
    }
    let closure = builder.expr(
        value,
        run.len(),
        base.slot(),
        None,
        false,
        true,
        Some(producer),
    )?;
    let target = builder.expr(
        &access.base,
        run.len(),
        target_home.slot(),
        None,
        false,
        true,
        Some(target_producer),
    )?;
    let start = builder.first_event?;
    if builder.next_event != run.len() || !matches!(target, HirExpr::GlobalRef(_)) {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: true,
        start,
        sink: run.len(),
        base,
        values: vec![closure].into(),
        result_locals: Vec::new(),
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: Some(HirTableAccess {
            base: target,
            ..access.clone()
        }),
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// key 与 RHS 已在低槽时，只收回目标表的原 CALL/读取准备，读取仍在原写入点。
fn prepared_field_target(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    access: &HirTableAccess,
    value: &HirExpr,
) -> Option<Plan> {
    let layout = facts.native_table_write_layout(access)?;
    let value_home = match value {
        HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local)?,
        HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param)?,
        _ => return None,
    };
    let key_preserved = match &access.key {
        HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local),
        HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param),
        HirExpr::String(_) | HirExpr::Integer(_) | HirExpr::Number(_) => {
            // 大函数的常量池上界不能代替该字段的原 RK 输入证明。
            if context.literal_uses_rk(&access.key, Some((&access.sources, false)), dialect)
                != Some(true)
            {
                return None;
            }
            None
        }
        _ => return None,
    };
    if layout.key != key_preserved
        || key_preserved.is_some_and(|key| key.slot() >= layout.base.slot())
        || layout.value != Some(value_home)
        || value_home.slot() >= layout.base.slot()
    {
        return None;
    }
    let HirExpr::LocalRef(local) = access.base else {
        return None;
    };
    let mut builder = frame_builder(context, run, facts, dialect, layout.base.slot())?;
    let index = builder.definition(local, run.len())?;
    let (_, prepared) = scalar_local(run[index])?;
    let (producer, home) = facts.table_write_base_preparation(access, prepared)?;
    if home != layout.base || facts.promoted_local_for_temp(producer) != Some(local) {
        return None;
    }
    let target = builder.expr(
        &access.base,
        run.len(),
        home.slot(),
        None,
        false,
        true,
        Some(producer),
    )?;
    let start = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink: run.len(),
        base: home,
        values: vec![value.clone()].into(),
        result_locals: Vec::new(),
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: Some(HirTableAccess {
            base: target,
            ..access.clone()
        }),
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

#[expect(
    clippy::too_many_arguments,
    reason = "沿用已解析的赋值终点与原 RHS，避免重新扫描候选区"
)]
fn scalar_rhs(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    access: &HirTableAccess,
    value: &HirExpr,
    rhs: &HirExpr,
    result_binding: Option<HirBinding>,
) -> Option<Plan> {
    let layout = facts.native_table_write_layout(access);
    let (key_home, value_home) = if let Some(layout) = layout {
        (layout.key, layout.value)
    } else {
        let layout = facts.native_upvalue_table_write_layout(access)?;
        if access.base != HirExpr::UpvalueRef(layout.base) {
            return None;
        }
        (layout.key, layout.value)
    };
    let comparison = comparison_result(rhs, facts);
    let prepared_value = if let Some(result) = comparison {
        // 比较指令不直接定义结果；沿冻结的 Boolean 写回核对 SETTABLE 的原 RHS 槽。
        // 候选拒绝[ProofIncomplete]：比较的结果身份不属于本次字段写的准备槽。
        if facts.trusted_temp_home_slot(result) != value_home {
            return None;
        }
        Some(result)
    } else if matches!(rhs, HirExpr::UpvalueRef(_))
        || ((matches!(dialect, DecompileDialect::Luau | DecompileDialect::Luajit)
            || !context.constants_fit_rk)
            && tables::literal_rk(rhs)
            && value_home.is_some())
    {
        let (producer, home) = facts.table_write_value_preparation(access, rhs)?;
        if Some(home) != value_home {
            return None;
        }
        Some(producer)
    } else {
        None
    };
    let source = match rhs {
        _ if comparison.is_some() => None,
        HirExpr::UpvalueRef(_) if prepared_value.is_some() => None,
        HirExpr::Closure(closure) => Some(closure.source_site?),
        HirExpr::TableConstructor(table) => match table.sources {
            crate::hir::common::HirOperationSources::Single(source) => Some(source),
            _ => return None,
        },
        HirExpr::Call(call) => Some(call.source_site?),
        HirExpr::Binary(binary)
            if (is_scalar_binary_operation(binary.op)
                || binary.op == crate::hir::common::HirBinaryOpKind::Concat) =>
        {
            Some(binary.source_site?)
        }
        HirExpr::GlobalRef(global) => match global.sources {
            crate::hir::common::HirOperationSources::Single(source) => Some(source),
            _ => return None,
        },
        HirExpr::TableAccess(read) => match read.sources {
            crate::hir::common::HirOperationSources::Single(source) => Some(source),
            _ => return None,
        },
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
            if (value_home.is_none() && result_binding.is_none()) || prepared_value.is_some() =>
        {
            None
        }
        _ => return None,
    };
    if let Some(source) = source
        && facts.operation_result_home(source) != Some(value_home?)
    {
        return None;
    }
    if matches!(rhs, HirExpr::Closure(_))
        && source
            .and_then(|source| facts.operation_result_temp(source))
            .is_some_and(|temp| facts.temp_is_published_closure_declaration(temp))
    {
        // SemanticBarrier:PhysicalFramePrefix：原闭包槽在字段发布后仍被后续
        // 观察保活；字段写不承担它的退休责任，须保留原声明作为低槽前缀。
        return None;
    }
    let mut builder = frame_builder(
        context,
        run,
        facts,
        dialect,
        value_home
            .or_else(|| layout.map(|layout| layout.base))?
            .slot(),
    )?;
    // 只有 SETTABLE 的唯一原读取 Def 才是可消费的左值快照；多次读取的现成表仍是低槽变量。
    // t.a[1]=t.b[2]+5 必须先保存 t.a；weak[1]=holder.inner.child 同样不能把
    // GETUPVAL 拖到 RHS 之后。内嵌常量 RHS 则不新增结果准备槽。
    // 全局表的 GETGLOBAL/GETTABUP 快照遵守同一合同，仍先读取目标再创建字段闭包。
    let snapshot = match &access.base {
        _ if layout.is_none() => None,
        HirExpr::TempRef(temp) => builder.temp_definitions.get(temp).and_then(|&index| {
            let (
                HirBinding::Temp(definition),
                source @ (HirExpr::TableAccess(_) | HirExpr::UpvalueRef(_) | HirExpr::GlobalRef(_)),
            ) = scalar_binding(run[index])?
            else {
                return None;
            };
            let (producer, home) = facts.table_write_base_preparation(access, source)?;
            // 尚未提升的左值快照与 Local 使用同一 use→Def 证明；不另建
            // 源码声明，否则该 scratch 会阻断后继复用同槽的构造器。
            (definition == *temp
                && producer == *temp
                && snapshot_matches_target(source, home, access, facts, dialect))
            .then_some((producer, home))
        }),
        HirExpr::LocalRef(local) => builder.definition(*local, run.len()).and_then(|index| {
            let (
                _,
                source @ (HirExpr::TableAccess(_) | HirExpr::UpvalueRef(_) | HirExpr::GlobalRef(_)),
            ) = scalar_local(run[index])?
            else {
                return None;
            };
            let (producer, home) = facts.table_write_base_preparation(access, source)?;
            (facts.promoted_local_for_temp(producer) == Some(*local)
                && snapshot_matches_target(source, home, access, facts, dialect))
            .then_some((producer, home))
        }),
        HirExpr::TableAccess(_) | HirExpr::UpvalueRef(_) | HirExpr::GlobalRef(_) => facts
            .table_write_base_preparation(access, &access.base)
            .filter(|(_, home)| {
                snapshot_matches_target(&access.base, *home, access, facts, dialect)
            }),
        _ => None,
    };
    let base = if let Some((_, home)) = snapshot {
        let layout = layout?;
        if home != layout.base
            || value_home.is_some_and(|value_home| value_home.slot() != home.slot() + 1)
        {
            return None;
        }
        home
    } else if let Some(layout) = layout {
        let value_home = value_home?;
        if facts.direct_table_write_input_home(access, 0) != Some(layout.base)
            || layout.base.slot() >= value_home.slot()
        {
            return None;
        }
        value_home
    } else {
        // SETTABUP 在 RHS 完成后直接读取目标 cell，不生成 GETUPVAL 快照。
        // RHS 仍占原 freereg，闭包捕获和后继覆盖由 builder/preview 一起核对。
        value_home?
    };
    builder.base = base.slot();
    let key = if let Some(home) = key_home {
        if facts.direct_table_write_input_home(access, 1) != Some(home)
            || home.slot() >= base.slot()
        {
            return None;
        }
        access.key.clone()
    } else {
        if !matches!(
            access.key,
            HirExpr::String(_) | HirExpr::Integer(_) | HirExpr::Number(_)
        ) {
            return None;
        }
        access.key.clone()
    };
    let target_base = if let Some((producer, home)) = snapshot {
        match &access.base {
            HirExpr::TableAccess(access) => {
                builder.register_lookup(access, run.len(), home.slot())?
            }
            _ => builder.expr(
                &access.base,
                run.len(),
                home.slot(),
                None,
                false,
                true,
                Some(producer),
            )?,
        }
    } else {
        access.base.clone()
    };
    let value = if result_binding.is_some() {
        let previous = builder.register_operand;
        if matches!(rhs, HirExpr::TableAccess(_)) {
            builder.register_operand = true;
        }
        let rebuilt = builder.expr(
            value,
            run.len(),
            value_home?.slot(),
            None,
            false,
            true,
            prepared_value
                .or_else(|| source.and_then(|source| facts.operation_result_temp(source))),
        );
        builder.register_operand = previous;
        rebuilt?
    } else {
        match rhs {
            _ if comparison.is_some() => builder.expr(
                rhs,
                run.len(),
                value_home?.slot(),
                None,
                false,
                true,
                prepared_value,
            )?,
            HirExpr::UpvalueRef(_) => {
                // 同一 SETTABLE 的 use→Def 保证 RHS 是原 GETUPVAL，目标表的
                // GETUPVAL 已在前面按原槽消费；不借上值名把读取移过 RHS 或元方法。
                builder.expr(
                    rhs,
                    run.len(),
                    value_home?.slot(),
                    None,
                    false,
                    true,
                    prepared_value,
                )?
            }
            HirExpr::Closure(_) | HirExpr::TableConstructor(_) => builder.expr(
                rhs,
                run.len(),
                value_home?.slot(),
                None,
                false,
                true,
                source.and_then(|source| facts.operation_result_temp(source)),
            )?,
            HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Concat => {
                builder.concat(binary, run.len(), value_home?.slot())?
            }
            HirExpr::Binary(binary) => {
                if dialect == DecompileDialect::Luau {
                    builder.expr(rhs, run.len(), value_home?.slot(), None, false, true, None)?
                } else {
                    builder.register_arithmetic(binary, run.len(), value_home?.slot())?
                }
            }
            HirExpr::TableAccess(read) => {
                builder.register_lookup(read, run.len(), value_home?.slot())?
            }
            HirExpr::Call(call) => HirExpr::Call(Box::new(builder.call(
                call,
                run.len(),
                value_home?.slot(),
                true,
                CallWidth::Single,
            )?)),
            value => value.clone(),
        }
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
        base,
        values: vec![value].into(),
        result_locals: Vec::new(),
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: Some(HirTableAccess {
            base: target_base,
            key,
            ..access.clone()
        }),
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}
