//! 解析 carried-local handoff seed，并提供局部 seed 重写。
//!
//! 消费当前语句，发布交接身份与剩余赋值；完整后缀和生命周期证明归 handoffs。

use std::collections::BTreeSet;

use crate::hir::common::{HirExpr, HirLValue, HirStmt, TempId};

use super::binding::{
    CarryBinding, TempBindingRewrite, carry_binding_from_expr, carry_binding_from_lvalue,
};
use super::reads::BindingReadCollector;

pub(super) struct BindingHandoffSeed {
    pub(super) rewrites: Vec<TempBindingRewrite>,
    pub(super) retained_pairs: Vec<(HirLValue, HirExpr)>,
}

pub(super) fn binding_handoff_seed(stmt: &HirStmt) -> Option<BindingHandoffSeed> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    if assign.values.tail.is_some()
        || assign.targets.len() < 2
        || assign.targets.len() != assign.values.fixed.len()
    {
        return None;
    }

    let mut seen_targets = BTreeSet::new();
    let mut repeated_targets = BTreeSet::new();
    let mut rewrites = Vec::with_capacity(assign.targets.len());
    let mut retained_pairs = Vec::new();
    for (target, value) in assign.targets.iter().zip(&assign.values) {
        if let HirLValue::Temp(target_temp) = target
            && !seen_targets.insert(*target_temp)
        {
            repeated_targets.insert(*target_temp);
        }
        let rewrite = match target {
            HirLValue::Temp(target_temp) => {
                carry_binding_from_expr(value).map(|binding| TempBindingRewrite {
                    from: *target_temp,
                    to: binding,
                })
            }
            _ => None,
        };
        let Some(rewrite) = rewrite else {
            retained_pairs.push((target.clone(), value.clone()));
            continue;
        };
        rewrites.push(rewrite);
    }
    if rewrites.is_empty() {
        return None;
    }
    if rewrites
        .iter()
        .any(|rewrite| repeated_targets.contains(&rewrite.from))
    {
        // 候选拒绝[SemanticBarrier:EvalOrder]：同一 temp 的并行 targets 中只要有一项
        // 会被删除，保留的最后写覆盖关系就会改变；全部 retained 的重复 target 不受影响。
        return None;
    }
    if rewrites.iter().any(|rewrite| {
        retained_pairs.iter().any(|(target, _)| {
            carry_binding_from_lvalue(target).is_some_and(|target| target == rewrite.to)
        })
    }) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：`s, t = value, s` 中删除 `t -> s` 会改变同一并行赋值对 `s` 的覆盖顺序。
        return None;
    }
    Some(BindingHandoffSeed {
        rewrites,
        retained_pairs,
    })
}

pub(super) fn rewrite_binding_handoff_seed(
    stmt: &mut HirStmt,
    retained_pairs: &[(HirLValue, HirExpr)],
) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        panic!("parsed binding handoff seed must remain an assignment during apply")
    };
    assign.targets = retained_pairs
        .iter()
        .map(|(target, _)| target.clone())
        .collect();
    assign.values.fixed = retained_pairs
        .iter()
        .map(|(_, value)| value.clone())
        .collect();
    assign.generic_for_initializer_producer = None;
    true
}

pub(super) fn direct_temp_writeback_stmt(stmt: &HirStmt) -> Option<(CarryBinding, TempId)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [HirExpr::TempRef(update_temp)] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
    let carried = carry_binding_from_lvalue(target)?;
    if matches!(carried, CarryBinding::Temp(temp) if temp == *update_temp) {
        return None;
    }
    Some((carried, *update_temp))
}

pub(super) fn update_handoff_seed(stmt: &HirStmt) -> Option<(TempId, CarryBinding)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Temp(target_temp)] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
    // `assign tX = lY` 这种纯别名交棒应继续走旧分支；这里只有“先算一个 next 状态，
    // 再把后半段身份完全交给它”的形状才应该继续往下看。
    if matches!(value, HirExpr::LocalRef(_) | HirExpr::TempRef(_)) {
        return None;
    }
    let mut collector = BindingReadCollector::default();
    collector.collect_expr(value);
    let carried = collector.single_read()?;
    match carried {
        CarryBinding::Temp(temp) if temp == *target_temp => None,
        _ => Some((*target_temp, carried)),
    }
}

pub(super) fn rewrite_update_handoff_seed(stmt: &mut HirStmt, carried: CarryBinding) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        panic!("parsed update handoff seed must remain an assignment during apply")
    };
    let [target] = assign.targets.as_mut_slice() else {
        panic!("parsed update handoff seed must retain its unique target during apply")
    };
    *target = match carried {
        CarryBinding::Param(param) => HirLValue::Param(param),
        CarryBinding::Local(local) => HirLValue::Local(local),
        CarryBinding::Temp(temp) => HirLValue::Temp(temp),
    };
    assign.generic_for_initializer_producer = None;
    true
}

pub(super) fn single_binding_handoff_seed(stmt: &HirStmt) -> Option<(TempId, CarryBinding)> {
    let (temp, value) = stmt.scalar_temp_assignment()?;
    Some((temp, carry_binding_from_expr(value)?))
}
