//! 消费 Structure 冻结的内嵌取值操作数；每个物理谓词只降低一次。
//! 操作数的单次消费、控制域和 phi 身份由前层证明，这里只组合表达式森林。

use super::*;
use crate::hir::rewrite::replace_temp_in_expr;
use crate::structure::{SsaValue, ValueDecisionNodePlan};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn build_value_operands(
    lowering: &ProtoLowering<'_>,
    plan: &ValueDecisionPlan,
) -> Option<HirDecisionExpr> {
    let root = plan.operands.len();
    let mut owner = vec![root; plan.nodes.len()];
    let mut groups = vec![Vec::new(); root + 1];
    let mut consumers = vec![Vec::new(); plan.nodes.len()];
    for (index, operand) in plan.operands.iter().enumerate() {
        consumers.get_mut(operand.consumer.index())?.push(index);
        for node in &operand.nodes {
            let current = owner.get_mut(node.index())?;
            if *current != root {
                return None;
            }
            *current = index;
        }
    }
    let mut dense = vec![0; plan.nodes.len()];
    for (node, &group) in owner.iter().enumerate() {
        dense[node] = groups[group].len();
        groups[group].push(node);
    }
    let mut children = vec![Vec::new(); root + 1];
    let mut entries = vec![BTreeMap::new(); root + 1];
    for (index, operand) in plan.operands.iter().enumerate() {
        let parent = *owner.get(operand.consumer.index())?;
        children[parent].push(index);
        if entries[parent]
            .insert(operand.entry.index(), operand.continuation.index())
            .is_some()
        {
            return None;
        }
    }
    let mut projection = ControlProjection {
        entries,
        resolved: vec![BTreeMap::new(); root + 1],
    };
    let mut state = vec![0u8; root + 1];
    let mut values = vec![None; root + 1];
    let mut pending = vec![(root, false)];
    while let Some((group, exiting)) = pending.pop() {
        if !exiting {
            if state[group] != 0 {
                return None;
            }
            state[group] = 1;
            pending.push((group, true));
            pending.extend(children[group].iter().rev().map(|child| (*child, false)));
            continue;
        }
        let operand = plan.operands.get(group);
        let entry = operand.map_or(plan.entry, |operand| operand.entry);
        let mut nodes = Vec::with_capacity(groups[group].len());
        for &index in &groups[group] {
            let node = &plan.nodes[index];
            let (mut test, test_source) = if node.id == plan.entry {
                lower_short_circuit_subject(lowering, node.block, node.predicate)
            } else {
                lower_short_circuit_subject_single_eval(lowering, node.block, node.predicate)
            }?;
            for &child in &consumers[index] {
                let value = values[child].take()?;
                let replacement = HirExpr::Decision(Box::new(value));
                let temp = *lowering
                    .bindings
                    .phi_temps
                    .get(plan.operands[child].phi.index())?;
                if replace_temp_in_expr(&mut test, temp, &replacement) != 1 {
                    return None;
                }
            }
            let mut target = |truthy: bool| {
                let arc = if truthy { &node.truthy } else { &node.falsy };
                if let Some(operand) = operand
                    && let Some(value) = operand.leaves.get(arc.route.last()?)
                {
                    // 真值测试同时产生叶值时复用本次求值，不能再次展开 CALL 等 producer。
                    if operand
                        .current_values
                        .contains(&(node.id, *arc.route.last()?))
                    {
                        return Some(HirDecisionTarget::CurrentValue);
                    }
                    return Some(HirDecisionTarget::Expr(lower_operand_leaf(
                        lowering, plan, node, *value,
                    )?));
                }
                match arc.target {
                    ValueDecisionTarget::Node(target) => {
                        let target = projection.resolve(group, target.index())?;
                        (owner[target] == group)
                            .then_some(HirDecisionTarget::Node(HirDecisionNodeRef(dense[target])))
                    }
                    _ if group == root => {
                        super::decision::lower_value_target(lowering, plan, arc.target)
                    }
                    _ => None,
                }
            };
            let mut lowered = HirDecisionNode {
                id: HirDecisionNodeRef(dense[index]),
                test,
                test_source,
                truthy: target(true)?,
                falsy: target(false)?,
            };
            if group == root
                && super::decision::materialized_boolean_comparison(lowering, plan, node, &lowered)
            {
                lowered.truthy = HirDecisionTarget::CurrentValue;
                lowered.falsy = HirDecisionTarget::CurrentValue;
            }
            nodes.push(lowered);
        }
        let entry = projection.resolve(group, entry.index())?;
        if owner[entry] != group || nodes.is_empty() {
            return None;
        }
        values[group] = Some(HirDecisionExpr {
            emit_as_luau_if: false,
            entry: HirDecisionNodeRef(dense[entry]),
            nodes,
        });
        state[group] = 2;
    }
    if state.iter().any(|state| *state != 2) {
        return None;
    }
    values[root].take()
}

fn lower_operand_leaf(
    lowering: &ProtoLowering<'_>,
    plan: &ValueDecisionPlan,
    node: &ValueDecisionNodePlan,
    value: SsaValue,
) -> Option<HirExpr> {
    match value {
        SsaValue::Def(def) if lowering.dataflow.def_block(def) == plan.header()? => Some(
            super::decision::expr_for_emitted_header_leaf(lowering, plan.header()?, def),
        ),
        SsaValue::Def(def)
            if lowering
                .structure
                .plan()
                .region_for_block(lowering.dataflow.def_block(def))
                == lowering.structure.plan().region_for_block(plan.header()?) =>
        {
            expr_for_fixed_def_single_eval(lowering, def)
        }
        value => super::super::exprs::expr_for_ssa_value_in_block(lowering, node.block, value),
    }
}

/// 同一表达式内跳过直接子操作数的物理控制域；值仍在消费谓词的对应位置求值。
/// 按 group 缓存实际访问的入口，连续操作数链不会让每条弧重复遍历整段后缀。
struct ControlProjection {
    entries: Vec<BTreeMap<usize, usize>>,
    resolved: Vec<BTreeMap<usize, usize>>,
}

impl ControlProjection {
    fn resolve(&mut self, group: usize, mut node: usize) -> Option<usize> {
        let mut path = BTreeSet::new();
        let target = loop {
            if let Some(target) = self.resolved[group].get(&node) {
                break *target;
            }
            if !path.insert(node) {
                return None;
            }
            let Some(next) = self.entries[group].get(&node) else {
                break node;
            };
            node = *next;
        };
        for node in path {
            self.resolved[group].insert(node, target);
        }
        Some(target)
    }
}
