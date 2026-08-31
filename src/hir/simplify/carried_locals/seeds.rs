//! carried-local handoff seed 的形状解析与 seed 语句重写。
//!
//! 这个模块只把当前语句识别成可折叠的 seed：纯别名、单目标 local/temp handoff、
//! 更新后 handoff，以及边界入口处的直接写回。它不检查 suffix 是否安全、不触碰外层
//! temp 活跃性，也不执行整段 rewrite；这些策略条件由 `handoffs.rs` 统一判断。
//!
//! 例子：
//! - 输入 seed：`assign tA, tB, keep = sA, sB, 0`
//! - 输出事实：`tA -> sA`、`tB -> sB`，并保留 `keep = 0`

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
    let mut seen_bindings = BTreeSet::new();
    let mut rewrites = Vec::with_capacity(assign.targets.len());
    let mut retained_pairs = Vec::new();
    for (target, value) in assign.targets.iter().zip(&assign.values) {
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
        // 候选拒绝[SemanticBarrier:EvalOrder]：同一 temp 在并行 targets 重复出现时最后写胜出，单一 rewrite 会丢失位置语义。
        // 候选拒绝[ProofIncomplete]：多个 temp 复制同一 source 可能可合并，但需证明后续 writeback 不把这些快照作为独立 epoch 使用。
        if !seen_targets.insert(rewrite.from) || !seen_bindings.insert(rewrite.to) {
            return None;
        }
        rewrites.push(rewrite);
    }
    if rewrites.is_empty() {
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
    // 候选拒绝[ConvergenceGuard]：seed parser 已证明当前语句为 Assign；apply 形状不符表示 plan/apply 契约漂移。
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    assign.targets = retained_pairs
        .iter()
        .map(|(target, _)| target.clone())
        .collect();
    assign.values.fixed = retained_pairs
        .iter()
        .map(|(_, value)| value.clone())
        .collect();
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
    // 候选拒绝[ConvergenceGuard]：update seed parser 已证明单 target Assign；apply 失败表示 shape 契约漂移。
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    let [target] = assign.targets.as_mut_slice() else {
        // 候选拒绝[ConvergenceGuard]：已解析的 update seed 不应失去唯一 target。
        return false;
    };
    *target = match carried {
        CarryBinding::Param(param) => HirLValue::Param(param),
        CarryBinding::Local(local) => HirLValue::Local(local),
        CarryBinding::Temp(temp) => HirLValue::Temp(temp),
    };
    true
}

pub(super) fn single_binding_handoff_seed(stmt: &HirStmt) -> Option<(TempId, CarryBinding)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Temp(temp)] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
    let binding = carry_binding_from_expr(value)?;
    Some((*temp, binding))
}
