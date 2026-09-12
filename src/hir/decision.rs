//! HIR Decision 的结构合同、共享节点查询与表达式化入口。
//!
//! `Decision` 是 HIR 内部为了保住共享短路子图而引入的中间形态，但它到底什么时候
//! 能安全折回普通表达式，不能让 analyze 和 simplify 各自维护一套规则。这里把
//! 那条共享入口固定下来，避免两边因为局部实现分叉而把同一棵决策图恢复成两种风格。
//! DAG identity、可达性和无环性属于 HIR 节点合同；值域与改写者共用此校验，不能让
//! 共享语义查询依赖某个 simplify pass 才能解释 Node/CurrentValue 的输入合法性。
//! 校验同时发布借用当前节点的拓扑顺序和共享性；例如两臂汇入同一个 tail，值分析按
//! 逆拓扑先算 tail 再合流两臂，payload 按正序传播可达边，不重新排序或按 id 搜索节点。
//! 首次 lowering 可为当前节点快照提供原根终点 query；归约当场消费，失败不发布许可，
//! 组合后的 test 也不能继承单个 producer 的证明。后续快照只能使用自身仍有效的事实。

use crate::hir::common::{HirDecisionExpr, HirDecisionNodeRef, HirDecisionTarget, HirExpr};
use crate::hir::expr_safety::HirExprSafety;

/// 当前不可变 Decision 快照的拓扑事实；借用期间不能改写节点或沿用旧身份。
pub(in crate::hir) struct DecisionFacts<'a> {
    decision: &'a HirDecisionExpr,
    order: Vec<usize>,
    incoming: Vec<usize>,
    has_shared_nodes: bool,
}

impl DecisionFacts<'_> {
    pub(in crate::hir) fn decision(&self) -> &HirDecisionExpr {
        self.decision
    }

    pub(in crate::hir) fn has_shared_nodes(&self) -> bool {
        self.has_shared_nodes
    }

    pub(in crate::hir) fn incoming_counts(&self) -> &[usize] {
        &self.incoming
    }

    pub(in crate::hir) fn topological_nodes(
        &self,
    ) -> impl DoubleEndedIterator<Item = &super::common::HirDecisionNode> {
        self.order.iter().map(|&index| &self.decision.nodes[index])
    }
}

pub(in crate::hir) fn analyze_decision(decision: &HirDecisionExpr) -> DecisionFacts<'_> {
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
    let has_shared_nodes = incoming.iter().any(|&count| count > 1);
    let mut remaining_incoming = incoming.clone();
    let mut ready = incoming
        .iter()
        .enumerate()
        .filter_map(|(index, &count)| (count == 0).then_some(index))
        .collect::<Vec<_>>();
    // 非空 DAG 的每个节点都可从某个零入度源到达；唯一源是 entry 时，全图入口可达。
    // 与下面的无环证明组合即可，无需另起一次可达性遍历。
    let unique_entry_source = ready.as_slice() == [decision.entry.index()];
    let mut order = Vec::with_capacity(decision.nodes.len());
    while let Some(index) = ready.pop() {
        order.push(index);
        let node = &decision.nodes[index];
        for target in [&node.truthy, &node.falsy] {
            if let HirDecisionTarget::Node(next_ref) = target {
                remaining_incoming[next_ref.index()] -= 1;
                if remaining_incoming[next_ref.index()] == 0 {
                    ready.push(next_ref.index());
                }
            }
        }
    }
    assert_eq!(
        order.len(),
        decision.nodes.len(),
        "HIR Decision must be acyclic"
    );
    assert!(
        unique_entry_source,
        "HIR Decision must not contain unreachable nodes"
    );
    DecisionFacts {
        decision,
        order,
        incoming,
        has_shared_nodes,
    }
}

pub(in crate::hir) fn finalize_condition_decision_expr(
    decision: HirDecisionExpr,
    safety: HirExprSafety,
) -> HirExpr {
    let topology = analyze_decision(&decision);
    if topology.has_shared_nodes() {
        HirExpr::Decision(Box::new(decision))
    } else {
        super::simplify::decision::collapse_condition_decision_expr(&topology, safety)
            .unwrap_or_else(|| HirExpr::Decision(Box::new(decision)))
    }
}

pub(in crate::hir) fn finalize_value_decision_expr(
    decision: HirDecisionExpr,
    safety: HirExprSafety,
    root_ends: impl Fn(&super::common::HirDecisionNode) -> bool,
) -> HirExpr {
    super::simplify::decision::collapse_value_decision_expr(
        &analyze_decision(&decision),
        safety,
        root_ends,
    )
    .unwrap_or_else(|| HirExpr::Decision(Box::new(decision)))
}
