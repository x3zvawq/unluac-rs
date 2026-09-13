//! 恢复计算左值与 CONCAT 的同一 PUC 赋值帧。
//!
//! Promotion 提供 SETTABLE 布局、单次 base 读取和 CONCAT 输入 Def；共享 builder
//! 核对每个准备写与事件，父事务同时替换左值/RHS 并验证声明前后缀。
//! 例如 `log[#log+1]=value.name..":"..tostring(message)`，上值 log 的 key 先
//! 执行 LEN，随后才保存目标表，最后准备 CONCAT；__len 改写 log 后必须读取新表，
//! RHS 回调再次改写 log 则不能影响已保存目标。这里不以表达式同名代替读取身份。

use super::*;
use crate::hir::common::{HirAssign, HirBinaryOpKind, HirExpr, HirTableAccess};

pub(super) fn is_candidate(assign: &HirAssign) -> bool {
    matches!((assign.targets.as_slice(), assign.values.fixed.as_slice(), &assign.values.tail),
        ([HirLValue::TableAccess(access)], [_], None)
            if matches!(access.key, HirExpr::LocalRef(_)))
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
    let key_home = layout.key?;
    let value_home = layout.value?;
    let (binary, result_local) = match value {
        HirExpr::Binary(binary) => (binary.as_ref(), None),
        HirExpr::LocalRef(local) => {
            let (target, HirExpr::Binary(binary)) = scalar_local(run.last()?)? else {
                return None;
            };
            if target != *local {
                return None;
            }
            (binary.as_ref(), Some(*local))
        }
        _ => return None,
    };
    if binary.op != HirBinaryOpKind::Concat
        || facts.operation_result_home(binary.source_site?) != Some(value_home)
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
        result_local: None,
        discarded_result: None,
        assignment_targets: Vec::new(),
        indexed_target: Some(HirTableAccess {
            base: target_base,
            key,
            ..access.as_ref().clone()
        }),
        retained_copies: Vec::new(),
        removed: Vec::new(),
    })
}
