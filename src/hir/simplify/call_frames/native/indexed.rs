//! 恢复计算左值与标量 RHS 的同一原生赋值帧。
//!
//! 消费 Promotion 的 SETTABLE/SETTABUP 布局与输入 Def，由共享 builder 核对
//! 目标表读取、key 和 RHS 的准备顺序，再由父事务验证完整声明前后缀。

use super::*;
use crate::hir::common::{HirAssign, HirBinaryOpKind, HirExpr, HirTableAccess};

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
            || assign.generic_for_dispatch_release.is_some()
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
        start: first.id,
        sink: write_second.id,
        base,
        values: values.into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: targets,
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: vec![write_first.id],
        removed: vec![first.id, second.id, write_first.id],
    })
}

/// 两项字段赋值的首个 RHS 在高槽快照，末项直接读低槽；PUC/JIT 逆序写回两个字段。
/// 把快照连同两次写一起重发，避免独立 local 延长到后继复用该槽的调用。
pub(super) fn parallel_copies(
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
    let HirStmt::LocalDecl(decl) = first.stmt else {
        return None;
    };
    let ([snapshot], [source], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    let direct_home = |value: &HirExpr| match value {
        HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local),
        HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param),
        _ => None,
    };
    let home = facts.trusted_local_home_slot(*snapshot)?;
    if direct_home(source)?.slot() >= home.slot()
        || decl.initializer_merge_transaction.is_some()
        || context.barred.contains(&home)
        || context.closed.contains(&home)
        || context.proto.local_debug_hints[snapshot.index()].is_some()
        || context.proto.local_debug_scopes[snapshot.index()].is_some()
        || context
            .proto
            .inline_dispositions
            .local(*snapshot)
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
            || assign.generic_for_dispatch_release.is_some()
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
    let second_home = direct_home(second_value)?;
    if *read != *snapshot || second_home.slot() >= home.slot() {
        return None;
    }
    for (target, value) in [(first_target, home), (second_target, second_home)] {
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
            || original_value != Some(value)
        {
            return None;
        }
    }
    let mut plan = Plan {
        start: first.id,
        sink: last.id,
        base: home,
        values: vec![source.clone(), second_value.clone()].into(),
        result_locals: Vec::new(),
        discarded_result: None,
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
            | HirExpr::ParamRef(_)
            | HirExpr::UpvalueRef(_)
    )
}

pub(super) fn is_candidate(assign: &HirAssign) -> bool {
    matches!(
        (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail
        ),
        ([HirLValue::TableAccess(_)], [_], None)
    )
}

pub(super) fn plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    assign: &HirAssign,
    rhs_live_after: bool,
) -> Option<Plan> {
    if !context.constants_fit_rk {
        return None;
    }
    let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
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
    let (rhs, result_local) = match value {
        value if direct_rhs_home.is_some() => (value, None),
        HirExpr::LocalRef(local) => {
            // SETLIST/字段写属于同一个构造器 RHS，seed 不一定紧邻最终 SETTABLE。
            // builder 仍核对所选版本及全部中间事件，不能跳过独立语句。
            let (_, rhs) = run
                .iter()
                .rev()
                .find_map(|stmt| scalar_local(stmt).filter(|(target, _)| target == local))?;
            (rhs, Some(*local))
        }
        value => (value, None),
    };
    // 候选拒绝[SemanticBarrier:BindingIdentity]：待退休的 RHS 值版本仍被后缀读取。
    // 现成低槽 RHS 不在本事务删除范围内；不能因此阻止其独立 key/base 准备。
    if result_local.is_some() && rhs_live_after {
        return None;
    }
    // 动态 key 后的字面量也有原 LOAD Def；Luau 与 JIT 都须保留其 RHS 槽，
    // 不能只接受固定字段，或误套用 PUC 的 RK 常量布局。
    let prepared_literal = (matches!(dialect, DecompileDialect::Luajit | DecompileDialect::Luau)
        && tables::literal_rk(rhs))
    .then(|| facts.table_write_value_preparation(access, rhs))
    .flatten();
    if dialect == DecompileDialect::Luau
        && prepared_literal.is_none()
        && direct_rhs_home.is_none()
        && !matches!(rhs, HirExpr::Call(_))
        && !matches!(rhs, HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Concat)
        && !matches!(rhs, HirExpr::Binary(binary) if matches!(binary.op, HirBinaryOpKind::Add | HirBinaryOpKind::Sub | HirBinaryOpKind::Mul | HirBinaryOpKind::Div | HirBinaryOpKind::Mod | HirBinaryOpKind::Pow))
    {
        // Luau 的字面量或分配 RHS 仍在原 scratch 准备，再写入目标的固定字段；
        // 不套用 PUC 的 RK 消除规则。CALL/CONCAT 则交下方连续 key/result 帧证明。
        if matches!(rhs, HirExpr::Closure(_) | HirExpr::TableConstructor(_)) {
            facts.luau_allocation_table_write_frame(access, rhs)?;
        } else {
            result_local?;
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
            result_local,
        );
    }
    // JIT 的直接低槽 RHS 不需重新准备；算术由 register_arithmetic 逐槽验证，
    // 查表由 register_lookup 验证；闭包在 scalar_rhs 核对原创建 Def 与 capture，
    // CALL gap 与连续拼接区仍各自使用原协议。
    if dialect == DecompileDialect::Luajit
        && prepared_literal.is_none()
        && direct_rhs_home.is_none()
        && !(matches!(
            rhs,
            HirExpr::Call(_) | HirExpr::TableAccess(_) | HirExpr::Closure(_)
        ) || matches!(rhs, HirExpr::Binary(binary) if matches!(binary.op, HirBinaryOpKind::Concat | HirBinaryOpKind::Add | HirBinaryOpKind::Sub | HirBinaryOpKind::Mul | HirBinaryOpKind::Div | HirBinaryOpKind::Mod | HirBinaryOpKind::Pow)))
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
    let comparison = match rhs {
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
    };
    let literal_rhs = value_home.is_none()
        && result_local.is_none()
        && matches!(
            rhs,
            HirExpr::Nil
                | HirExpr::Boolean(_)
                | HirExpr::Integer(_)
                | HirExpr::Number(_)
                | HirExpr::String(_)
        );
    if !(matches!(rhs, HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Concat)
        || matches!(rhs, HirExpr::Call(_))
        || matches!(rhs, HirExpr::TableConstructor(_) | HirExpr::TableAccess(_))
        || comparison.is_some()
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
            result_local,
        );
    }
    let result = if literal_rhs || direct_rhs_home.is_some() {
        None
    } else if let Some((temp, _)) = prepared_literal {
        Some(temp)
    } else if let Some(result) = comparison {
        // 比较指令本身不写结果；使用原双分支 Boolean 写回，不能借谓词操作数猜 RHS 槽。
        Some(result)
    } else {
        let source = match rhs {
            HirExpr::Binary(binary) => binary.source_site?,
            HirExpr::Call(call) => call.source_site?,
            HirExpr::TableAccess(access) => {
                let crate::hir::common::HirOperationSources::Single(source) = access.sources else {
                    return None;
                };
                source
            }
            HirExpr::TableConstructor(table) => {
                let crate::hir::common::HirOperationSources::Single(source) = table.sources else {
                    return None;
                };
                source
            }
            _ => return None,
        };
        Some(facts.operation_result_temp(source)?)
    };
    let key_home = key_home?;
    if let Some(result) = result
        && (facts.trusted_temp_home_slot(result) != value_home
            || value_home != Some(HomeSlotKey::new(key_home.slot() + 1, 0)))
    {
        return None;
    }
    let direct_base = match &access.base {
        HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local),
        HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param),
        _ => None,
    }
    .filter(|home| {
        register_layout.is_some_and(|layout| *home == layout.base) && home.slot() < key_home.slot()
    });
    // 低槽 local/param 是 SETTABLE 的直接操作数；高槽上值快照必须消费其唯一原 GETUPVAL。
    let snapshot = if let HirExpr::LocalRef(local) = access.base {
        run.iter()
            .rposition(|stmt| scalar_local(stmt).is_some_and(|(target, _)| target == local))
            .and_then(|index| {
                let (_, value @ HirExpr::UpvalueRef(_)) = scalar_local(run[index])? else {
                    return None;
                };
                let (producer, home) = facts.table_write_base_preparation(access, value)?;
                (register_layout.is_some_and(|layout| home == layout.base)
                    && facts.promoted_local_for_temp(producer) == Some(local))
                .then_some((producer, home))
            })
    } else if matches!(access.base, HirExpr::UpvalueRef(_)) && register_layout.is_some() {
        facts.table_write_base_preparation(access, &access.base)
    } else {
        None
    };
    let base = if let Some((_, home)) = snapshot {
        if key_home == HomeSlotKey::new(home.slot() + 1, 0) {
            home
        } else if matches!(dialect, DecompileDialect::Lua54 | DecompileDialect::Lua55)
            && (literal_rhs || direct_rhs_home.is_some())
            && home == HomeSlotKey::new(key_home.slot() + 1, 0)
        {
            // key 的 CALL 先占 free slot，随后 GETUPVAL 在其上一槽准备目标；
            // RHS 没有新增 scratch，整个事务从 key 槽开始，仍在 key 后读取目标。
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
    let early_base = if matches!(
        dialect,
        DecompileDialect::Lua51 | DecompileDialect::Luajit | DecompileDialect::Luau
    ) {
        if let Some((producer, home)) = snapshot {
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
    // Luau 的 key 结果槽独立于更低的表快照槽；复合 key 的 scratch 从 key 上一槽开始。
    builder.indexed_key_base = Some(if dialect == DecompileDialect::Luau {
        key_home.slot()
    } else {
        base.slot()
    });
    let previous_register_operand = builder.register_operand;
    builder.register_operand = true;
    let key = builder.expr(
        &access.key,
        run.len(),
        key_home.slot(),
        None,
        false,
        true,
        None,
    )?;
    builder.register_operand = previous_register_operand;
    builder.indexed_key_base = None;
    let target_base = if let Some(base) = early_base {
        base
    } else if let Some((producer, home)) = snapshot {
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
    } else if prepared_literal.is_some() || result_local.is_some() {
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
            HirExpr::Binary(binary) => builder.concat(binary, run.len(), value_home?.slot())?,
            HirExpr::Call(call) => HirExpr::Call(Box::new(builder.call(
                call,
                run.len(),
                value_home?.slot(),
                true,
                CallWidth::Single,
            )?)),
            // 字段 RHS 同样在 key 后的相邻槽读取；完整 lookup 由共享 builder 验证，
            // 不先冻结 key 声明再把其后续同槽值连成一个 Local 身份。
            HirExpr::TableConstructor(_) | HirExpr::TableAccess(_) => builder.expr(
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
        start,
        sink: run.len(),
        base,
        values: vec![value].into(),
        result_locals: Vec::new(),
        discarded_result: None,
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
}

/// 固定字段的 RHS 已在低槽，只收回目标表的原 CALL/读取准备，不重发或提前读取 RHS。
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
    if layout.key.is_some()
        || layout.value != Some(value_home)
        || value_home.slot() >= layout.base.slot()
        || !matches!(
            access.key,
            HirExpr::String(_) | HirExpr::Integer(_) | HirExpr::Number(_)
        )
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
        start,
        sink: run.len(),
        base: home,
        values: vec![value.clone()].into(),
        result_locals: Vec::new(),
        discarded_result: None,
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
    result_local: Option<LocalId>,
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
    let prepared_upvalue = if matches!(rhs, HirExpr::UpvalueRef(_))
        && !matches!(dialect, DecompileDialect::Luau | DecompileDialect::Luajit)
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
        HirExpr::UpvalueRef(_) if prepared_upvalue.is_some() => None,
        HirExpr::Closure(closure) => Some(closure.source_site?),
        HirExpr::TableConstructor(table) if dialect == DecompileDialect::Luau => {
            match table.sources {
                crate::hir::common::HirOperationSources::Single(source) => Some(source),
                _ => return None,
            }
        }
        HirExpr::Call(call) => Some(call.source_site?),
        HirExpr::Binary(binary)
            if matches!(
                binary.op,
                HirBinaryOpKind::Add
                    | HirBinaryOpKind::Sub
                    | HirBinaryOpKind::Mul
                    | HirBinaryOpKind::Div
                    | HirBinaryOpKind::Mod
                    | HirBinaryOpKind::Pow
                    | HirBinaryOpKind::Concat
            ) =>
        {
            Some(binary.source_site?)
        }
        HirExpr::TableAccess(read) => match read.sources {
            crate::hir::common::HirOperationSources::Single(source) => Some(source),
            _ => return None,
        },
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
            if (value_home.is_none() && result_local.is_none())
                || (dialect == DecompileDialect::Luau && value_home.is_some()) =>
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
        HirExpr::LocalRef(local) => builder.definition(*local, run.len()).and_then(|index| {
            let (
                _,
                source @ (HirExpr::TableAccess(_) | HirExpr::UpvalueRef(_) | HirExpr::GlobalRef(_)),
            ) = scalar_local(run[index])?
            else {
                return None;
            };
            let (producer, home) = facts.table_write_base_preparation(access, source)?;
            (facts.promoted_local_for_temp(producer) == Some(*local)).then_some((producer, home))
        }),
        HirExpr::TableAccess(_) | HirExpr::UpvalueRef(_) | HirExpr::GlobalRef(_) => {
            facts.table_write_base_preparation(access, &access.base)
        }
        _ => None,
    };
    let base = if let Some((_, home)) = snapshot {
        let layout = layout?;
        if home != layout.base
            || value_home
                .is_some_and(|value_home| value_home != HomeSlotKey::new(home.slot() + 1, 0))
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
    let value = if result_local.is_some() {
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
            prepared_upvalue
                .or_else(|| source.and_then(|source| facts.operation_result_temp(source))),
        );
        builder.register_operand = previous;
        rebuilt?
    } else {
        match rhs {
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
                    prepared_upvalue,
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
        start,
        sink: run.len(),
        base,
        values: vec![value].into(),
        result_locals: Vec::new(),
        discarded_result: None,
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
