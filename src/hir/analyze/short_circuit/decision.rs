//! 这个子模块把 Structure 冻结的 condition DAG 逐节点降低成 HIR decision。
//!
//! 节点 identity、真假连边和终端出口都由 `ConditionPlan` 给出；这里不再读取 raw
//! candidate、重选候选或截断控制图。入口 block 的 prefix 由结构 lowering 显式发射，
//! 其余被折叠节点使用单次求值表达式，避免引用不会单独发射的中间 temp。

use super::*;
use crate::hir::rewrite::replace_temp_in_expr;

pub(crate) fn build_condition_decision_expr(
    lowering: &ProtoLowering<'_>,
    condition: &ConditionPlan,
) -> Option<HirDecisionExpr> {
    let mut remap = vec![None; condition.nodes.len()];
    let mut values_by_consumer = vec![Vec::new(); condition.nodes.len()];
    let mut next_node = 0usize;
    for node in &condition.nodes {
        if let Some(value) = node.materialized_value {
            values_by_consumer
                .get_mut(value.consumer.index())?
                .push(node.id);
        } else {
            remap[node.id.index()] = Some(HirDecisionNodeRef(next_node));
            next_node += 1;
        }
    }
    let resolved = resolve_condition_nodes(condition, &remap)?;
    let entry = resolved.get(condition.entry.index()).copied().flatten()?;
    let mut subjects = lower_condition_subjects(lowering, condition, &values_by_consumer)?;
    let nodes = condition
        .nodes
        .iter()
        .filter(|node| node.materialized_value.is_none())
        .map(|node| {
            let test = subjects.get_mut(node.id.index())?.take()?;
            Some(HirDecisionNode {
                id: remap[node.id.index()]?,
                test,
                truthy: lower_target(node.semantic_target(true), &resolved)?,
                falsy: lower_target(node.semantic_target(false), &resolved)?,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    (!nodes.is_empty()).then_some(HirDecisionExpr { entry, nodes })
}

pub(crate) fn build_value_decision_expr(
    lowering: &ProtoLowering<'_>,
    decision: &ValueDecisionPlan,
) -> Option<HirDecisionExpr> {
    let entry = HirDecisionNodeRef(decision.entry.index());
    let nodes = decision
        .nodes
        .iter()
        .map(|node| {
            let test = if node.id == decision.entry {
                lower_short_circuit_subject(lowering, node.block, node.predicate)
            } else {
                lower_short_circuit_subject_single_eval(lowering, node.block, node.predicate)
            }?;
            Some(HirDecisionNode {
                id: HirDecisionNodeRef(node.id.index()),
                test,
                truthy: lower_value_target(lowering, decision, node.truthy.target)?,
                falsy: lower_value_target(lowering, decision, node.falsy.target)?,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    (!nodes.is_empty() && entry.index() < nodes.len()).then_some(HirDecisionExpr { entry, nodes })
}

fn lower_value_target(
    lowering: &ProtoLowering<'_>,
    decision: &ValueDecisionPlan,
    target: ValueDecisionTarget,
) -> Option<HirDecisionTarget> {
    match target {
        ValueDecisionTarget::Node(node) => (node.index() < decision.nodes.len())
            .then_some(HirDecisionTarget::Node(HirDecisionNodeRef(node.index()))),
        ValueDecisionTarget::Leaf(leaf) => {
            let leaf = decision.leaves.get(leaf.index())?;
            let expr = match leaf.latest_local_def {
                // entry prefix 会正常发射其中的定义。此时 leaf 必须继续引用这次已经
                // 求值的 SSA identity；重新展开定义会把全局读取等动态操作执行两次。
                Some(def)
                    if lowering.dataflow.def_block(def) == decision.header()?
                        && leaf.value == crate::structure::SsaValue::Def(def) =>
                {
                    expr_for_ssa_value(lowering, leaf.value)
                }
                // ValueDecision 吞掉了 leaf block 的普通指令，必须优先沿完整单次求值
                // 依赖链展开；普通 def lowering 可能返回引用那些不会再被发射的中间 temp。
                Some(def) => expr_for_fixed_def_single_eval(lowering, def)
                    .or_else(|| expr_for_fixed_def(lowering, def))?,
                None => expr_for_ssa_value(lowering, leaf.value),
            };
            Some(HirDecisionTarget::Expr(expr))
        }
        ValueDecisionTarget::CurrentValue(leaf) => decision
            .leaves
            .get(leaf.index())
            .map(|_| HirDecisionTarget::CurrentValue),
    }
}

fn lower_condition_subjects(
    lowering: &ProtoLowering<'_>,
    condition: &ConditionPlan,
    values_by_consumer: &[Vec<crate::structure::ConditionNodeId>],
) -> Option<Vec<Option<HirExpr>>> {
    let mut subjects = vec![None; condition.nodes.len()];
    let mut state = vec![0u8; condition.nodes.len()];

    for start in 0..condition.nodes.len() {
        if state[start] == 2 {
            continue;
        }
        let mut pending = vec![(crate::structure::ConditionNodeId(start), false)];
        while let Some((node_id, exiting)) = pending.pop() {
            let index = node_id.index();
            if exiting {
                if *state.get(index)? != 1 {
                    return None;
                }
                let node = condition.nodes.get(index)?;
                if !matches!(
                    lowering.proto.instrs.get(node.predicate.index()),
                    Some(LowInstr::Branch(_))
                ) {
                    return None;
                }
                let mut expr = if node.id == condition.entry {
                    lower_short_circuit_subject(lowering, node.block, node.predicate)
                } else {
                    lower_short_circuit_subject_single_eval(lowering, node.block, node.predicate)
                }?;
                for producer_id in values_by_consumer.get(index)? {
                    let producer = condition.nodes.get(producer_id.index())?;
                    let value = producer.materialized_value?;
                    let mut replacement = subjects.get_mut(producer_id.index())?.take()?;
                    if value.negated {
                        replacement = HirExpr::Unary(Box::new(crate::hir::HirUnaryExpr {
                            op: crate::hir::HirUnaryOpKind::Not,
                            expr: replacement,
                        }));
                    }
                    let temp = *lowering.bindings.phi_temps.get(value.phi.index())?;
                    if replace_temp_in_expr(&mut expr, temp, &replacement) != 1 {
                        return None;
                    }
                    if let Some(def) = value.forwarded_callee {
                        let temp = *lowering.bindings.fixed_temps.get(def.index())?;
                        let replacement = expr_for_fixed_def_single_eval(lowering, def)?;
                        // absorbed-condition 的稠密 owner 会让 single-eval lowering 提前展开
                        // 同一 condition 内的 callee；0 次替换表示它已经被展开。
                        if replace_temp_in_expr(&mut expr, temp, &replacement) > 1 {
                            return None;
                        }
                    }
                }
                state[index] = 2;
                subjects[index] = Some(expr);
                continue;
            }

            match *state.get(index)? {
                0 => {
                    state[index] = 1;
                    pending.push((node_id, true));
                    for producer in values_by_consumer.get(index)?.iter().rev() {
                        match *state.get(producer.index())? {
                            0 => pending.push((*producer, false)),
                            1 => return None,
                            2 => {}
                            _ => return None,
                        }
                    }
                }
                1 => return None,
                2 => {}
                _ => return None,
            }
        }
    }
    Some(subjects)
}

fn resolve_condition_nodes(
    condition: &ConditionPlan,
    remap: &[Option<HirDecisionNodeRef>],
) -> Option<Vec<Option<HirDecisionNodeRef>>> {
    let mut resolved = vec![None; condition.nodes.len()];
    let mut state = vec![0u8; condition.nodes.len()];
    let mut pending = Vec::new();
    for start in 0..condition.nodes.len() {
        if state[start] == 2 {
            continue;
        }
        pending.clear();
        let mut node = crate::structure::ConditionNodeId(start);
        let target = loop {
            let index = node.index();
            match *state.get(index)? {
                0 => {}
                1 => return None,
                2 => break resolved.get(index).copied().flatten()?,
                _ => return None,
            }
            state[index] = 1;
            pending.push(node);

            let plan = condition.nodes.get(index)?;
            if plan.materialized_value.is_none() {
                break remap.get(index).copied().flatten()?;
            }
            let (ConditionTarget::Node(truthy), ConditionTarget::Node(falsy)) =
                (plan.semantic_target(true), plan.semantic_target(false))
            else {
                return None;
            };
            if truthy != falsy {
                return None;
            }
            node = truthy;
        };
        for node in pending.drain(..).rev() {
            state[node.index()] = 2;
            resolved[node.index()] = Some(target);
        }
    }
    Some(resolved)
}

fn lower_target(
    target: ConditionTarget,
    resolved: &[Option<HirDecisionNodeRef>],
) -> Option<HirDecisionTarget> {
    match target {
        ConditionTarget::Node(node) => Some(HirDecisionTarget::Node(
            resolved.get(node.index()).copied().flatten()?,
        )),
        ConditionTarget::Truthy => Some(HirDecisionTarget::Expr(HirExpr::Boolean(true))),
        ConditionTarget::Falsy => Some(HirDecisionTarget::Expr(HirExpr::Boolean(false))),
    }
}
