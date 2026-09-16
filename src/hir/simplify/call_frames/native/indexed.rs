//! 恢复计算左值与算术/CONCAT 的同一 PUC 赋值帧。
//!
//! Promotion 提供 SETTABLE 布局、单次 base 读取和 CONCAT 输入 Def；共享 builder
//! 核对每个准备写与事件，父事务同时替换左值/RHS 并验证声明前后缀。
//! 例如 `log[#log+1]=value.name..":"..tostring(message)`，上值 log 的 key 先
//! 执行 LEN，随后才保存目标表，最后准备 CONCAT；__len 改写 log 后必须读取新表，
//! RHS 回调再次改写 log 则不能影响已保存目标。这里不以表达式同名代替读取身份。
//! 普通算术同样消费 SETTABLE 的唯一 GETTABLE base Def：`t.a[1]=t.b[2]+5`
//! 必须先保存 t.a 再执行 RHS；低槽动态 key 则保持原 SETTABLE 的直接读取时点。
//! 固定字段 key 的 CONCAT 共用标量 RHS 事务；`self.value=a..":"..b` 的整个原
//! 连续输入区由 CONCAT 重发，不能把每轮编译产生的 COPY 当作额外源码声明保留。
//! 字段读取 RHS 与内嵌常量写也消费同一左值快照协议；如 `weak[1]=holder.inner.child`
//! 保持先 GETUPVAL、后 RHS，再 SETTABLE，`holder.inner.child=nil` 则不新增 RHS 准备槽。

use super::*;
use crate::hir::common::{HirAssign, HirBinaryOpKind, HirExpr, HirTableAccess};

/// 仅用于识别完整赋值候选；原结果槽、RK 与左值准备仍由 plan 验证。
pub(super) fn is_rhs_candidate(value: &HirExpr) -> bool {
    matches!(
        value,
        HirExpr::Binary(_)
            | HirExpr::TableAccess(_)
            | HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
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
) -> Option<Plan> {
    // 候选拒绝[TargetConstraint]：这里证明 PUC 的 RK 索引与可重定位结果，不套用 Luau/JIT 布局。
    if matches!(dialect, DecompileDialect::Luajit | DecompileDialect::Luau)
        || !context.constants_fit_rk
    {
        return None;
    }
    let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    let layout = facts.native_table_write_layout(access)?;
    let (rhs, result_local) = match value {
        HirExpr::LocalRef(local) => {
            let (target, rhs) = scalar_local(run.last()?)?;
            if target != *local {
                return None;
            }
            (rhs, Some(*local))
        }
        value => (value, None),
    };
    if !matches!(rhs, HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Concat)
        || layout.key.is_none()
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
    let HirExpr::Binary(binary) = rhs else {
        return None;
    };
    let value_home = layout.value?;
    let key_home = layout.key?;
    if facts.operation_result_home(binary.source_site?) != Some(value_home)
        || value_home != HomeSlotKey::new(key_home.slot() + 1, 0)
    {
        return None;
    }
    let direct_base = match &access.base {
        HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local),
        HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param),
        _ => None,
    }
    .filter(|home| *home == layout.base && home.slot() < key_home.slot());
    // 低槽 local/param 是 SETTABLE 的直接操作数；高槽上值快照必须消费其唯一原 GETUPVAL。
    let snapshot = if let HirExpr::LocalRef(local) = access.base {
        run.iter()
            .rposition(|stmt| scalar_local(stmt).is_some_and(|(target, _)| target == local))
            .and_then(|index| {
                let (_, value @ HirExpr::UpvalueRef(_)) = scalar_local(run[index])? else {
                    return None;
                };
                let (producer, home) = facts.table_write_base_preparation(access, value)?;
                (home == layout.base && facts.promoted_local_for_temp(producer) == Some(local))
                    .then_some((producer, home))
            })
    } else {
        None
    };
    let base = if let Some((_, home)) = snapshot {
        if key_home != HomeSlotKey::new(home.slot() + 1, 0) {
            return None;
        }
        home
    } else {
        direct_base?;
        key_home
    };
    let mut builder = frame_builder(context, run, facts, dialect, base.slot())?;
    builder.indexed_key_base = Some(base.slot());
    let key = builder.expr(
        &access.key,
        run.len(),
        key_home.slot(),
        None,
        false,
        true,
        None,
    )?;
    builder.indexed_key_base = None;
    let target_base = if let Some((producer, home)) = snapshot {
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
    let value = if result_local.is_some() {
        builder.expr(
            value,
            run.len(),
            value_home.slot(),
            None,
            false,
            true,
            facts.operation_result_temp(binary.source_site?),
        )?
    } else {
        builder.concat(binary, run.len(), value_home.slot())?
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
        indexed_target: Some(HirTableAccess {
            base: target_base,
            key,
            ..access.as_ref().clone()
        }),
        continuing_root: None,
        retained_copies: Vec::new(),
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
    let layout = facts.native_table_write_layout(access)?;
    let source = match rhs {
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
            if layout.value.is_none() && result_local.is_none() =>
        {
            None
        }
        _ => return None,
    };
    if let Some(source) = source
        && facts.operation_result_home(source) != Some(layout.value?)
    {
        return None;
    }
    let mut builder = frame_builder(
        context,
        run,
        facts,
        dialect,
        layout.value.unwrap_or(layout.base).slot(),
    )?;
    // 只有 SETTABLE 的唯一原读取 Def 才是可消费的左值快照；多次读取的现成表仍是低槽变量。
    let snapshot = match &access.base {
        HirExpr::LocalRef(local) => builder.definition(*local, run.len()).and_then(|index| {
            let (_, source @ (HirExpr::TableAccess(_) | HirExpr::UpvalueRef(_))) =
                scalar_local(run[index])?
            else {
                return None;
            };
            let (producer, home) = facts.table_write_base_preparation(access, source)?;
            (facts.promoted_local_for_temp(producer) == Some(*local)).then_some((producer, home))
        }),
        HirExpr::TableAccess(_) | HirExpr::UpvalueRef(_) => {
            facts.table_write_base_preparation(access, &access.base)
        }
        _ => None,
    };
    let base = if let Some((_, home)) = snapshot {
        if home != layout.base
            || layout
                .value
                .is_some_and(|value_home| value_home != HomeSlotKey::new(home.slot() + 1, 0))
        {
            return None;
        }
        home
    } else {
        let value_home = layout.value?;
        if builder.direct_home(&access.base) != Some(layout.base)
            || layout.base.slot() >= value_home.slot()
        {
            return None;
        }
        value_home
    };
    builder.base = base.slot();
    let key = if let Some(home) = layout.key {
        if builder.direct_home(&access.key) != Some(home) || home.slot() >= base.slot() {
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
            layout.value?.slot(),
            None,
            false,
            true,
            facts.operation_result_temp(source?),
        );
        builder.register_operand = previous;
        rebuilt?
    } else {
        match rhs {
            HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Concat => {
                builder.concat(binary, run.len(), layout.value?.slot())?
            }
            HirExpr::Binary(binary) => {
                builder.puc_arithmetic(binary, run.len(), layout.value?.slot())?
            }
            HirExpr::TableAccess(read) => {
                builder.register_lookup(read, run.len(), layout.value?.slot())?
            }
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
        indexed_target: Some(HirTableAccess {
            base: target_base,
            key,
            ..access.clone()
        }),
        continuing_root: None,
        retained_copies: Vec::new(),
        removed: Vec::new(),
    })
}
