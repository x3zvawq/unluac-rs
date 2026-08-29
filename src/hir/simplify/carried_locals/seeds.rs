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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::common::{HirAssign, HirValuePack, LocalId};

    fn parallel_copy(left: TempId, right: TempId) -> HirStmt {
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(left), HirLValue::Temp(right)],
            values: HirValuePack::fixed(vec![
                HirExpr::LocalRef(LocalId(0)),
                HirExpr::LocalRef(LocalId(0)),
            ]),
        }))
    }

    #[test]
    fn binding_handoff_seed_accepts_repeated_source() {
        let seed = binding_handoff_seed(&parallel_copy(TempId(0), TempId(1)))
            .expect("independent targets may defer repeated-source safety to handoff proofs");

        assert_eq!(seed.rewrites.len(), 2);
        assert!(
            seed.rewrites
                .iter()
                .all(|rewrite| { matches!(rewrite.to, CarryBinding::Local(LocalId(0))) })
        );
    }

    #[test]
    fn binding_handoff_seed_rejects_repeated_target() {
        assert!(binding_handoff_seed(&parallel_copy(TempId(0), TempId(0))).is_none());
    }

    #[test]
    fn binding_handoff_seed_rejects_rewrite_destination_retained_as_target() {
        let stmt = HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Local(LocalId(0)), HirLValue::Temp(TempId(0))],
            values: HirValuePack::fixed(vec![HirExpr::Integer(1), HirExpr::LocalRef(LocalId(0))]),
        }));

        assert!(binding_handoff_seed(&stmt).is_none());
    }

    #[test]
    fn binding_handoff_seed_rejects_repeated_target_split_between_retained_and_rewrite() {
        let stmt = HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(TempId(0)), HirLValue::Temp(TempId(0))],
            values: HirValuePack::fixed(vec![HirExpr::Integer(1), HirExpr::LocalRef(LocalId(0))]),
        }));

        assert!(binding_handoff_seed(&stmt).is_none());
    }

    #[test]
    fn binding_handoff_seed_keeps_repeated_retained_targets() {
        let stmt = HirStmt::Assign(Box::new(HirAssign {
            targets: vec![
                HirLValue::Temp(TempId(0)),
                HirLValue::Temp(TempId(0)),
                HirLValue::Temp(TempId(1)),
            ],
            values: HirValuePack::fixed(vec![
                HirExpr::Integer(1),
                HirExpr::Integer(2),
                HirExpr::LocalRef(LocalId(0)),
            ]),
        }));

        let seed = binding_handoff_seed(&stmt)
            .expect("unrelated retained target ordering must not block the handoff");
        assert_eq!(seed.rewrites.len(), 1);
        assert_eq!(seed.retained_pairs.len(), 2);
    }
}
