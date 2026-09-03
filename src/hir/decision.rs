//! HIR Decision 的结构合同、共享节点查询与表达式化入口。
//!
//! `Decision` 是 HIR 内部为了保住共享短路子图而引入的中间形态，但它到底什么时候
//! 能安全折回普通表达式，不能让 analyze 和 simplify 各自维护一套规则。这里把
//! 那条共享入口固定下来，避免两边因为局部实现分叉而把同一棵决策图恢复成两种风格。
//! DAG identity、可达性和无环性属于 HIR 节点合同；值域与改写者共用此校验，不能让
//! 共享语义查询依赖某个 simplify pass 才能解释 Node/CurrentValue 的输入合法性。

use crate::hir::common::{HirDecisionExpr, HirDecisionNodeRef, HirDecisionTarget, HirExpr};
use crate::hir::expr_safety::HirExprSafety;

pub(in crate::hir) fn decision_has_shared_nodes(decision: &HirDecisionExpr) -> bool {
    assert_valid_decision(decision);

    let mut incoming = vec![0usize; decision.nodes.len()];
    incoming[decision.entry.index()] += 1;

    for node in &decision.nodes {
        for target in [&node.truthy, &node.falsy] {
            if let HirDecisionTarget::Node(node_ref) = target
                && let Some(count) = incoming.get_mut(node_ref.index())
            {
                *count += 1;
            }
        }
    }

    incoming.into_iter().any(|count| count > 1)
}

pub(in crate::hir) fn assert_valid_decision(decision: &HirDecisionExpr) {
    assert!(!decision.nodes.is_empty(), "HIR Decision must not be empty");
    assert!(
        decision.entry.index() < decision.nodes.len(),
        "HIR Decision entry must reference an existing node"
    );

    let mut incoming = vec![0usize; decision.nodes.len()];
    for (index, node) in decision.nodes.iter().enumerate() {
        assert_eq!(
            node.id,
            HirDecisionNodeRef(index),
            "HIR Decision node id must match its arena index"
        );
        for target in [&node.truthy, &node.falsy] {
            if let HirDecisionTarget::Node(node_ref) = target {
                let Some(count) = incoming.get_mut(node_ref.index()) else {
                    panic!("HIR Decision edge must reference an existing node");
                };
                *count += 1;
            }
        }
    }

    let mut reachable = vec![false; decision.nodes.len()];
    let mut pending = vec![decision.entry];
    while let Some(node_ref) = pending.pop() {
        if std::mem::replace(&mut reachable[node_ref.index()], true) {
            continue;
        }
        let node = &decision.nodes[node_ref.index()];
        for target in [&node.truthy, &node.falsy] {
            if let HirDecisionTarget::Node(next_ref) = target {
                pending.push(*next_ref);
            }
        }
    }
    assert!(
        reachable.into_iter().all(|reachable| reachable),
        "HIR Decision must not contain unreachable nodes"
    );

    let mut ready = incoming
        .iter()
        .enumerate()
        .filter_map(|(index, count)| (*count == 0).then_some(index))
        .collect::<Vec<_>>();
    let mut visited = 0usize;
    while let Some(index) = ready.pop() {
        visited += 1;
        let node = &decision.nodes[index];
        for target in [&node.truthy, &node.falsy] {
            let HirDecisionTarget::Node(next_ref) = target else {
                continue;
            };
            incoming[next_ref.index()] -= 1;
            if incoming[next_ref.index()] == 0 {
                ready.push(next_ref.index());
            }
        }
    }
    assert_eq!(
        visited,
        decision.nodes.len(),
        "HIR Decision must be acyclic"
    );
}

pub(in crate::hir) fn finalize_condition_decision_expr(
    decision: HirDecisionExpr,
    safety: HirExprSafety,
) -> HirExpr {
    if decision_has_shared_nodes(&decision) {
        HirExpr::Decision(Box::new(decision))
    } else {
        super::simplify::decision::collapse_condition_decision_expr(&decision, safety)
            .unwrap_or_else(|| HirExpr::Decision(Box::new(decision)))
    }
}

pub(in crate::hir) fn finalize_value_decision_expr(
    decision: HirDecisionExpr,
    safety: HirExprSafety,
) -> HirExpr {
    super::simplify::decision::collapse_value_decision_expr(&decision, safety)
        .unwrap_or_else(|| HirExpr::Decision(Box::new(decision)))
}
