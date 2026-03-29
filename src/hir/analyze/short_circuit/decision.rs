//! 这个子模块负责把 `ShortCircuitCandidate` 解释成 decision-expression 形式。
//!
//! 它依赖 StructureFacts 已经确认好的短路 DAG 和真假出口，不会在这里重新抽取候选或决定
//! 是否改写成 `if then else` 赋值壳。
//! 例如：`a and b or c` 这类值级短路，会先在这里整理成 decision node/leaf 图。

use super::*;

pub(crate) fn branch_exit_blocks_from_value_merge_candidate(
    short: &ShortCircuitCandidate,
) -> Option<(BlockRef, BlockRef, BTreeSet<BlockRef>, BTreeSet<BlockRef>)> {
    let ShortCircuitExit::ValueMerge(_) = short.exit else {
        return None;
    };

    let (truthy_leaves, falsy_leaves) = short.value_truthiness_leaves()?;

    if truthy_leaves.len() != 1 || falsy_leaves.len() != 1 {
        return None;
    }

    let truthy = *truthy_leaves
        .iter()
        .next()
        .expect("len checked above, exactly one truthy leaf exists");
    let falsy = *falsy_leaves
        .iter()
        .next()
        .expect("len checked above, exactly one falsy leaf exists");
    (truthy != falsy).then_some((truthy, falsy, truthy_leaves, falsy_leaves))
}

pub(crate) fn build_branch_decision_expr(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    entry: ShortCircuitNodeRef,
) -> Option<HirDecisionExpr> {
    build_decision_expr(
        lowering,
        short,
        entry,
        lower_short_circuit_subject,
        |node, target| match target {
            ShortCircuitTarget::Node(next_ref) => Some(DecisionEdge::Node(*next_ref)),
            ShortCircuitTarget::TruthyExit => Some(DecisionEdge::Leaf(HirDecisionTarget::Expr(
                HirExpr::Boolean(true),
            ))),
            ShortCircuitTarget::FalsyExit => Some(DecisionEdge::Leaf(HirDecisionTarget::Expr(
                HirExpr::Boolean(false),
            ))),
            ShortCircuitTarget::Value(block) if *block == node.header => Some(DecisionEdge::Leaf(
                HirDecisionTarget::Expr(HirExpr::Boolean(true)),
            )),
            ShortCircuitTarget::Value(_) => None,
        },
    )
}

pub(crate) fn build_branch_decision_expr_for_value_merge_candidate(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    truthy_leaves: &BTreeSet<BlockRef>,
    falsy_leaves: &BTreeSet<BlockRef>,
) -> Option<HirDecisionExpr> {
    let _ = branch_exit_blocks_from_value_merge_candidate(short)?;
    build_decision_expr(
        lowering,
        short,
        short.entry,
        lower_short_circuit_subject_inline,
        |_, target| match target {
            ShortCircuitTarget::Node(next_ref) => Some(DecisionEdge::Node(*next_ref)),
            ShortCircuitTarget::Value(block) if truthy_leaves.contains(block) => Some(
                DecisionEdge::Leaf(HirDecisionTarget::Expr(HirExpr::Boolean(true))),
            ),
            ShortCircuitTarget::Value(block) if falsy_leaves.contains(block) => Some(
                DecisionEdge::Leaf(HirDecisionTarget::Expr(HirExpr::Boolean(false))),
            ),
            ShortCircuitTarget::Value(_)
            | ShortCircuitTarget::TruthyExit
            | ShortCircuitTarget::FalsyExit => None,
        },
    )
}

pub(crate) fn build_value_decision_expr(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    entry: ShortCircuitNodeRef,
) -> Option<HirDecisionExpr> {
    build_decision_expr(
        lowering,
        short,
        entry,
        lower_short_circuit_subject_inline,
        |node, target| match target {
            ShortCircuitTarget::Node(next_ref) => Some(DecisionEdge::Node(*next_ref)),
            ShortCircuitTarget::Value(block) if *block == node.header => {
                Some(DecisionEdge::Leaf(HirDecisionTarget::CurrentValue))
            }
            ShortCircuitTarget::Value(block) => Some(DecisionEdge::Leaf(HirDecisionTarget::Expr(
                lower_value_leaf_expr(lowering, short, *block)?,
            ))),
            ShortCircuitTarget::TruthyExit | ShortCircuitTarget::FalsyExit => None,
        },
    )
}

/// 纯 `Decision` 综合器会拒绝带副作用的 subject，但值短路里的 `call(...) and ...`
/// 在 Lua 里本来就是合法且单次求值的。
///
/// 这里补的是一条更早层的、结构受限的恢复路径：只吃“共享 fallback 的 guarded
/// disjunction”这一类值短路 DAG。它不会尝试做表达式空间搜索，也不会放宽成
/// 可重复求值的 inline；目标只是把最常见的带副作用短路值恢复成源码级 `and/or`
/// 形状，而不是让它们先掉成 `if` 壳。
pub(crate) fn build_impure_value_merge_expr(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    entry: ShortCircuitNodeRef,
) -> Option<HirExpr> {
    Some(build_impure_value_merge_plan(lowering, short, entry)?.into_expr())
}

#[derive(Debug, Clone, PartialEq)]
enum ImpureValueMergePlan {
    Expr(HirExpr),
    OrFallback { head: HirExpr, fallback: HirExpr },
}

impl ImpureValueMergePlan {
    fn into_expr(self) -> HirExpr {
        match self {
            Self::Expr(expr) => expr,
            Self::OrFallback { head, fallback } => {
                HirExpr::LogicalOr(Box::new(crate::hir::common::HirLogicalExpr {
                    lhs: head,
                    rhs: fallback,
                }))
            }
        }
    }

    fn as_expr(&self) -> HirExpr {
        self.clone().into_expr()
    }
}

#[derive(Debug, Clone, PartialEq)]
enum ImpureValueMergeTarget {
    Current,
    Plan(ImpureValueMergePlan),
}

fn build_impure_value_merge_plan(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    node_ref: ShortCircuitNodeRef,
) -> Option<ImpureValueMergePlan> {
    let node = short.nodes.get(node_ref.index())?;
    let subject = lower_short_circuit_subject_single_eval(lowering, node.header)?;
    let truthy = build_impure_value_merge_target(lowering, short, node.header, &node.truthy)?;
    let falsy = build_impure_value_merge_target(lowering, short, node.header, &node.falsy)?;
    combine_impure_value_merge_targets(subject, truthy, falsy)
}

fn build_impure_value_merge_target(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    current_header: BlockRef,
    target: &ShortCircuitTarget,
) -> Option<ImpureValueMergeTarget> {
    match target {
        ShortCircuitTarget::Node(next_ref) => Some(ImpureValueMergeTarget::Plan(
            build_impure_value_merge_plan(lowering, short, *next_ref)?,
        )),
        ShortCircuitTarget::Value(block) if *block == current_header => {
            Some(ImpureValueMergeTarget::Current)
        }
        ShortCircuitTarget::Value(block) => Some(ImpureValueMergeTarget::Plan(
            ImpureValueMergePlan::Expr(lower_value_leaf_expr(lowering, short, *block)?),
        )),
        ShortCircuitTarget::TruthyExit | ShortCircuitTarget::FalsyExit => None,
    }
}

fn combine_impure_value_merge_targets(
    subject: HirExpr,
    truthy: ImpureValueMergeTarget,
    falsy: ImpureValueMergeTarget,
) -> Option<ImpureValueMergePlan> {
    match (truthy, falsy) {
        (ImpureValueMergeTarget::Current, ImpureValueMergeTarget::Current) => {
            Some(ImpureValueMergePlan::Expr(subject))
        }
        (ImpureValueMergeTarget::Current, ImpureValueMergeTarget::Plan(fallback)) => {
            Some(ImpureValueMergePlan::OrFallback {
                head: subject,
                fallback: fallback.into_expr(),
            })
        }
        (ImpureValueMergeTarget::Plan(truthy), ImpureValueMergeTarget::Current) => {
            Some(ImpureValueMergePlan::Expr(HirExpr::LogicalAnd(Box::new(
                crate::hir::common::HirLogicalExpr {
                    lhs: subject,
                    rhs: truthy.into_expr(),
                },
            ))))
        }
        (
            ImpureValueMergeTarget::Plan(ImpureValueMergePlan::OrFallback { head, fallback }),
            ImpureValueMergeTarget::Plan(falsy),
        ) if falsy.as_expr() == fallback => Some(ImpureValueMergePlan::OrFallback {
            head: HirExpr::LogicalAnd(Box::new(crate::hir::common::HirLogicalExpr {
                lhs: subject,
                rhs: head,
            })),
            fallback,
        }),
        _ => None,
    }
}

#[derive(Debug, Clone)]
pub(crate) enum DecisionEdge {
    Node(ShortCircuitNodeRef),
    Leaf(HirDecisionTarget),
}

/// 共享 DAG 恢复本身就是一次图重建过程，这里把中间状态收进一个结构体里，
/// 避免在递归构图时把 `remap/nodes` 之类的细节参数层层外泄。
struct DecisionBuildState {
    remap: BTreeMap<ShortCircuitNodeRef, HirDecisionNodeRef>,
    nodes: Vec<HirDecisionNode>,
}

pub(crate) fn build_decision_expr<FTest, FTarget>(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    entry: ShortCircuitNodeRef,
    test_for_block: FTest,
    target_for_edge: FTarget,
) -> Option<HirDecisionExpr>
where
    FTest: Fn(&ProtoLowering<'_>, BlockRef) -> Option<HirExpr>,
    FTarget: Fn(&ShortCircuitNode, &ShortCircuitTarget) -> Option<DecisionEdge>,
{
    let mut state = DecisionBuildState {
        remap: BTreeMap::new(),
        nodes: Vec::new(),
    };
    let entry = build_decision_node(
        lowering,
        short,
        entry,
        &test_for_block,
        &target_for_edge,
        &mut state,
    )?;
    Some(HirDecisionExpr {
        entry,
        nodes: state.nodes,
    })
}

fn build_decision_node<FTest, FTarget>(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    node_ref: ShortCircuitNodeRef,
    test_for_block: &FTest,
    target_for_edge: &FTarget,
    state: &mut DecisionBuildState,
) -> Option<HirDecisionNodeRef>
where
    FTest: Fn(&ProtoLowering<'_>, BlockRef) -> Option<HirExpr>,
    FTarget: Fn(&ShortCircuitNode, &ShortCircuitTarget) -> Option<DecisionEdge>,
{
    if let Some(mapped) = state.remap.get(&node_ref) {
        return Some(*mapped);
    }

    let node = short.nodes.get(node_ref.index())?;
    let mapped = HirDecisionNodeRef(state.nodes.len());
    state.remap.insert(node_ref, mapped);
    state.nodes.push(HirDecisionNode {
        id: mapped,
        test: HirExpr::Boolean(false),
        truthy: HirDecisionTarget::Expr(HirExpr::Boolean(false)),
        falsy: HirDecisionTarget::Expr(HirExpr::Boolean(false)),
    });

    let test = test_for_block(lowering, node.header)?;
    let truthy = build_decision_target(
        lowering,
        short,
        node,
        &node.truthy,
        test_for_block,
        target_for_edge,
        state,
    )?;
    let falsy = build_decision_target(
        lowering,
        short,
        node,
        &node.falsy,
        test_for_block,
        target_for_edge,
        state,
    )?;

    state.nodes[mapped.index()] = HirDecisionNode {
        id: mapped,
        test,
        truthy,
        falsy,
    };
    Some(mapped)
}

fn build_decision_target<FTest, FTarget>(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    node: &ShortCircuitNode,
    target: &ShortCircuitTarget,
    test_for_block: &FTest,
    target_for_edge: &FTarget,
    state: &mut DecisionBuildState,
) -> Option<HirDecisionTarget>
where
    FTest: Fn(&ProtoLowering<'_>, BlockRef) -> Option<HirExpr>,
    FTarget: Fn(&ShortCircuitNode, &ShortCircuitTarget) -> Option<DecisionEdge>,
{
    match target_for_edge(node, target)? {
        DecisionEdge::Node(next_ref) => Some(HirDecisionTarget::Node(build_decision_node(
            lowering,
            short,
            next_ref,
            test_for_block,
            target_for_edge,
            state,
        )?)),
        DecisionEdge::Leaf(target) => Some(target),
    }
}
