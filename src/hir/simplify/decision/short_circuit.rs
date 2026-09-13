//! 消费 Decision 已有的共享连边，把串联短路子图归约为单次求值表达式。
//!
//! 节点与 continuation 身份来自 HIR Decision，不能先复制成树再靠 AST 寻找共同尾。
//! 只有唯一入边的 child 才能移入 parent；两节点共享的另一条出口保持原身份与极性。
//! 例如 `a ? (b ? d : (c ? d : e)) : e` 中先合并 `b or c`，再恢复
//! `a and (b or c) and d or e`（d 的真出口返回 CurrentValue）。每个 test 只移动一次，
//! 对应路径上的调用顺序、条件执行及返回原值均不依赖纯表达式代数猜测。
//! 纯 test 的布尔终端先按共享值域对齐极性：`d ? fallback : true` 可成为
//! `not d ? CurrentValue : fallback`，从而保留共同失败尾。归约后的线性值链直接
//! 消费当前节点，不丢弃已建立的共享事实后重新构造表达式树；物理根仍由其原 owner 证明。
//! 已来自原 operand 的 Boolean test 可严格加外层 NOT 翻转连边，保留内部值运算：
//! `a ? (not f() ? tail : (b ? CurrentValue : tail)) : tail`
//! 恢复 `a and not not f() and b or tail`。
//! If 极性和比较谓词不提供这种值来源证明，不能据此给未知调用插入 Boolean 覆写。
//! 未知 CALL 只有在首次 lowering 对当前 test epoch 提供精确根终点证明时才能翻边；
//! 例如 `a and not f() or fallback()` 的两个后继先覆盖原调用槽，而 `methods.next()`
//! 的 __index 可在覆盖之前观察该槽，后者没有这种许可。

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
    let decision = topology.decision();
    let mut incoming = topology.incoming_counts().to_vec();
    let mut nodes = decision
        .nodes
        .iter()
        .cloned()
        .map(|mut node| {
            let root_ends = root_ends(&node);
            normalize_boolean_terminals(&mut node, safety, root_ends);
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
                (inverse_common == common && can_invert_test(child_node, safety, *root_ends))
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

    let (root, _) = nodes[decision.entry.index()].as_ref()?;
    if matches!(root.truthy, HirDecisionTarget::Node(_))
        || matches!(root.falsy, HirDecisionTarget::Node(_))
    {
        // 图归约后的共享 fallback 已变为唯一值链；直接消费该链，不能丢弃归约结果
        // 再从原 DAG 复制 memo 表达式。非线性残余仍由原 Decision owner 处理。
        return super::collapse_linear_value_chain_with(decision.entry, |node| {
            nodes[node.index()].take().map(|(node, _)| node)
        });
    }
    let (root, _) = nodes[decision.entry.index()].take()?;
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
    // root_ends 仅由当前 lowering 快照对精确 CALL test 签发，并在组合时失效。
    !matches!(node.truthy, HirDecisionTarget::CurrentValue)
        && !matches!(node.falsy, HirDecisionTarget::CurrentValue)
        && (root_ends
            || safety.is_repeatable_in_single_value_context(&node.test)
            || (node.test_source == HirDecisionTestSource::Value
                && expr_is_boolean_valued(&node.test)))
}

fn invert_test(node: &mut HirDecisionNode) {
    // 严格保留内部 Boolean 值操作；negate() 的双 not 消解会重新退化成裸调用谓词。
    let test = std::mem::replace(&mut node.test, HirExpr::Nil);
    node.test = HirExpr::Unary(Box::new(HirUnaryExpr {
        source_site: None,
        op: HirUnaryOpKind::Not,
        expr: test,
    }));
    std::mem::swap(&mut node.truthy, &mut node.falsy);
}
