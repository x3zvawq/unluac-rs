//! 沿 Decision 共享连边归约短路子图，保持每个 test 的单次求值。
//!
//! 消费 HIR Decision 的节点与 continuation 身份，仅将唯一入边的 child 移入 parent；
//! 不先复制成树，也不靠纯表达式代数猜调用顺序或物理根终点。
//! 例如 a ? (b ? d : (c ? d : e)) : e 可先合并 b or c，再归约外层值链，
//! 共同出口保留原身份与极性。

use crate::hir::common::{
    HirDecisionNode, HirDecisionTarget, HirDecisionTestSource, HirExpr, HirUnaryExpr,
    HirUnaryOpKind,
};
use crate::hir::decision::DecisionFacts;
use crate::hir::expr_safety::HirExprSafety;

use super::{
    CollapsedValueTarget, combine_value_expr, expr_is_boolean_valued, logical_and, logical_or,
};

pub(super) fn collapse_short_circuit_graph(
    topology: &DecisionFacts<'_>,
    safety: HirExprSafety,
    root_ends: impl Fn(&HirDecisionNode) -> bool,
) -> Option<HirExpr> {
    collapse_graph(topology, safety, root_ends, false)
}

pub(super) fn collapse_condition_graph(
    topology: &DecisionFacts<'_>,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    // 这里只收回纯控制出口；CurrentValue 和一般值叶继续由值选择合同处理。
    if topology.decision().nodes.iter().any(|node| {
        [&node.truthy, &node.falsy].iter().any(|target| {
            !matches!(
                target,
                HirDecisionTarget::Node(_) | HirDecisionTarget::Expr(HirExpr::Boolean(_))
            )
        })
    }) {
        return None;
    }
    collapse_graph(topology, safety, |_| false, true)
}

fn collapse_graph(
    topology: &DecisionFacts<'_>,
    safety: HirExprSafety,
    root_ends: impl Fn(&HirDecisionNode) -> bool,
    condition: bool,
) -> Option<HirExpr> {
    let decision = topology.decision();
    let mut nodes = reduce_graph(topology, safety, root_ends, condition)?;

    let (root, _) = nodes[decision.entry.index()].as_ref()?;
    if matches!(root.truthy, HirDecisionTarget::Node(_))
        || matches!(root.falsy, HirDecisionTarget::Node(_))
    {
        if condition {
            return None;
        }
        // 图归约后的共享 fallback 已变为唯一值链；直接消费该链，不能丢弃归约结果
        // 再从原 DAG 复制 memo 表达式。非线性残余仍由原 Decision owner 处理。
        return super::collapse_linear_value_chain_with(decision.entry, |node| {
            nodes[node.index()].take().map(|(node, _)| node)
        });
    }
    let (root, _) = nodes[decision.entry.index()].take()?;
    if condition {
        let (HirDecisionTarget::Expr(truthy), HirDecisionTarget::Expr(falsy)) =
            (root.truthy, root.falsy)
        else {
            return None;
        };
        return super::combine_condition_expr(root.test, truthy, falsy, safety);
    }
    let collapse_target = |target| match target {
        HirDecisionTarget::CurrentValue => Some(CollapsedValueTarget::CurrentValue),
        HirDecisionTarget::Expr(expr) => Some(CollapsedValueTarget::Expr(expr)),
        // 候选拒绝[ProofIncomplete]：非串联短路图尚有独立共享入口，不能复制 test 来强行合并。
        HirDecisionTarget::Node(_) => None,
    };
    combine_value_expr(
        root.test,
        collapse_target(root.truthy)?,
        collapse_target(root.falsy)?,
        safety,
    )
}

type ReducedNodes = Vec<Option<(HirDecisionNode, bool)>>;

fn reduce_graph(
    topology: &DecisionFacts<'_>,
    safety: HirExprSafety,
    root_ends: impl Fn(&HirDecisionNode) -> bool,
    condition: bool,
) -> Option<ReducedNodes> {
    let decision = topology.decision();
    let mut incoming = topology.incoming_counts().to_vec();
    let mut nodes = decision
        .nodes
        .iter()
        .cloned()
        .map(|mut node| {
            let root_ends = root_ends(&node);
            if !condition {
                normalize_boolean_terminals(&mut node, safety, root_ends);
            }
            Some((node, root_ends))
        })
        .collect::<Vec<_>>();

    // 子图先归约；每次成功都消费一个节点，不枚举路径或复制共享 continuation。
    for original in topology.topological_nodes().rev() {
        let index = original.id.index();
        loop {
            let (node, _) = nodes[index].as_ref()?;
            let merge = [
                (&node.truthy, &node.falsy, true),
                (&node.falsy, &node.truthy, false),
            ]
            .into_iter()
            .find_map(|(edge, common, is_and)| {
                let HirDecisionTarget::Node(child) = edge else {
                    return None;
                };
                if incoming[child.index()] != 1 {
                    // 候选拒绝[ProofIncomplete]：须先归约 child 的其它入口，不能复制共享 test 的求值。
                    return None;
                }
                let (child_node, root_ends) = nodes[child.index()].as_ref()?;
                let child_common = if is_and {
                    &child_node.falsy
                } else {
                    &child_node.truthy
                };
                if child_common == common {
                    return Some((child.index(), is_and, false));
                }
                let inverse_common = if is_and {
                    &child_node.truthy
                } else {
                    &child_node.falsy
                };
                (inverse_common == common
                    && (condition || can_invert_test(child_node, safety, *root_ends)))
                .then_some((child.index(), is_and, true))
            });
            let Some((child_index, is_and, invert)) = merge else {
                break;
            };
            let (mut child, _) = nodes[child_index]
                .take()
                .expect("unique child remains in decision arena");
            if invert {
                invert_test(&mut child);
            }
            let (parent, root_ends) = nodes[index].as_mut().expect("decision parent remains live");
            // 证书只属于输入快照的单个 test epoch；组合后不能沿用 parent 的许可。
            *root_ends = false;
            let common = if is_and {
                &parent.falsy
            } else {
                &parent.truthy
            };
            if let HirDecisionTarget::Node(next) = common {
                incoming[next.index()] -= 1;
            }
            incoming[child_index] = 0;
            let test = std::mem::replace(&mut parent.test, HirExpr::Nil);
            parent.test = if is_and {
                logical_and(test, child.test)
            } else {
                logical_or(test, child.test)
            };
            if child.test_source == HirDecisionTestSource::Predicate {
                parent.test_source = HirDecisionTestSource::Predicate;
            }
            parent.truthy = child.truthy;
            parent.falsy = child.falsy;
        }
    }

    Some(nodes)
}

/// 终端赋值的控制测试也能消费局部短路归约；不要求整图可折成一个 Lua 值。
pub(super) fn prepare_control_materialization(
    decision: crate::hir::common::HirDecisionExpr,
    safety: HirExprSafety,
) -> crate::hir::common::HirDecisionExpr {
    if decision.nodes.iter().any(|node| {
        matches!(node.truthy, HirDecisionTarget::CurrentValue)
            || matches!(node.falsy, HirDecisionTarget::CurrentValue)
    }) {
        // 候选拒绝[SemanticBarrier:ValueArity]：CurrentValue 仍消费原测试值，不能按纯控制边翻转。
        return decision;
    }
    let topology = super::analyze_decision(&decision);
    let reduced = reduce_graph(&topology, safety, |_| false, true)
        .expect("validated decision reduction retains its live parents");
    // 只移动唯一入边 child，保持检查次数和惰性次序；终端仍在选中后提交，不提前写目标。
    // 未归约部分连同已归约节点一起物化，不能因整图值表达式失败而丢弃局部证明。
    let nodes = reduced
        .into_iter()
        .zip(&decision.nodes)
        .map(|(node, original)| node.map_or_else(|| original.clone(), |(node, _)| node))
        .collect::<Vec<_>>();
    super::rebuild_decision(decision.entry, &nodes).0
}

fn normalize_boolean_terminals(node: &mut HirDecisionNode, safety: HirExprSafety, root_ends: bool) {
    let inverse_terminal =
        matches!(
            &node.truthy,
            HirDecisionTarget::Expr(HirExpr::Boolean(false))
        ) || matches!(&node.falsy, HirDecisionTarget::Expr(HirExpr::Boolean(true)));
    if inverse_terminal
        && !matches!(node.truthy, HirDecisionTarget::CurrentValue)
        && !matches!(node.falsy, HirDecisionTarget::CurrentValue)
    {
        if !can_invert_test(node, safety, root_ends) {
            return;
        }
        invert_test(node);
    }
    // CurrentValue 要求真实返回值为 Boolean；truthy 对象不能替代 true。
    if !expr_is_boolean_valued(&node.test)
        || (node.test_source == HirDecisionTestSource::Predicate
            && !safety.is_repeatable_in_single_value_context(&node.test))
    {
        return;
    }
    if matches!(
        &node.truthy,
        HirDecisionTarget::Expr(HirExpr::Boolean(true))
    ) {
        node.truthy = HirDecisionTarget::CurrentValue;
    }
    if matches!(
        &node.falsy,
        HirDecisionTarget::Expr(HirExpr::Boolean(false))
    ) {
        node.falsy = HirDecisionTarget::CurrentValue;
    }
}

fn can_invert_test(node: &HirDecisionNode, safety: HirExprSafety, root_ends: bool) -> bool {
    // CurrentValue 返回原 test 的值，翻边后不能把它静默换成相反的 Boolean。
    // 候选拒绝[SemanticBarrier:Lifetime]：未知调用或合成谓词没有原 Boolean 值操作；
    // 不能靠外层 not 插入原图未证明的根覆盖。Value 路径严格保留已有内部操作；
    // callback 由 lowering 的精确覆盖证书，或完整返回帧事务签发；后者必须在提交前
    // 核对整个候选的原位调用布局，不表示旧根已经结束。组合后单节点许可失效。
    !matches!(node.truthy, HirDecisionTarget::CurrentValue)
        && !matches!(node.falsy, HirDecisionTarget::CurrentValue)
        && (root_ends
            || safety.is_repeatable_in_single_value_context(&node.test)
            || (node.test_source == HirDecisionTestSource::Value
                && expr_is_boolean_valued(&node.test)))
}

fn invert_test(node: &mut HirDecisionNode) {
    // 严格保留内部 Boolean 值操作；翻边只增加外层极性，不消解原有 NOT。
    let test = std::mem::replace(&mut node.test, HirExpr::Nil);
    node.test = HirExpr::Unary(Box::new(HirUnaryExpr {
        source_site: None,
        op: HirUnaryOpKind::Not,
        expr: test,
    }));
    std::mem::swap(&mut node.truthy, &mut node.falsy);
}
