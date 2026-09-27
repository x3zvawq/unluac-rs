//! 将纯条件 Decision 的树形路径直接接到原控制出口。
//!
//! break、continue 和 goto 没有结果值或声明身份，不需要先构造 Boolean holder；
//! 每个原测试仍各自发射。共享子图继续交给现有物化通道，不复制共享求值。

use crate::hir::common::{HirBlock, HirDecisionTarget, HirExpr, HirIf, HirStmt, HirUnaryOpKind};
use crate::hir::decision::analyze_decision;

use super::eliminate_materialize::expr_contains_eliminable_decision;

pub(super) fn materialize_control(if_stmt: &HirIf) -> Option<Vec<HirStmt>> {
    let mut condition = &if_stmt.cond;
    let mut inverted = false;
    while let HirExpr::Unary(unary) = condition {
        if unary.op != HirUnaryOpKind::Not || unary.source_site.is_some() {
            // 候选拒绝[PolicyBoundary]：只能用合成极性交换出口，原 NOT 仍须作为值操作重发。
            return None;
        }
        condition = &unary.expr;
        inverted = !inverted;
    }
    let HirExpr::Decision(decision) = condition else {
        return None;
    };
    if decision.emit_as_luau_if {
        return None;
    }
    let empty = HirBlock::default();
    let then_block = &if_stmt.then_block;
    let else_block = if_stmt.else_block.as_ref().unwrap_or(&empty);
    let transfer = |block: &HirBlock| {
        matches!(
            block.stmts.as_slice(),
            [] | [HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_)]
        )
    };
    if !transfer(then_block) || !transfer(else_block) {
        // 候选拒绝[ProofIncomplete]：一般出口含值求值、声明或 cleanup，尚无可复制的控制叶合同。
        return None;
    }
    let topology = analyze_decision(decision);
    if topology.has_shared_nodes() {
        // 候选拒绝[ProofIncomplete]：共享 test 需要显式合流，不能展开成树后重复原节点。
        return None;
    }
    if topology.topological_nodes().any(|node| {
        expr_contains_eliminable_decision(&node.test)
            || [&node.truthy, &node.falsy].iter().any(|target| {
                !matches!(
                    target,
                    HirDecisionTarget::Node(_) | HirDecisionTarget::Expr(HirExpr::Boolean(_))
                )
            })
    }) {
        // 候选拒绝[ProofIncomplete]：嵌套值决策或 CurrentValue 仍需要独立的值和根生命周期证明。
        return None;
    }
    let mut blocks: Vec<Option<HirBlock>> = vec![None; decision.nodes.len()];
    for node in topology.topological_nodes().rev() {
        let mut arm = |target: &HirDecisionTarget| match target {
            HirDecisionTarget::Node(next) => blocks[next.index()]
                .take()
                .expect("tree child is emitted once before its parent"),
            HirDecisionTarget::Expr(HirExpr::Boolean(value)) => {
                if *value != inverted {
                    then_block.clone()
                } else {
                    else_block.clone()
                }
            }
            _ => unreachable!("control leaves were validated"),
        };
        let mut truthy = arm(&node.truthy);
        let mut falsy = arm(&node.falsy);
        let mut cond = node.test.clone();
        if truthy.stmts.is_empty() && !falsy.stmts.is_empty() {
            std::mem::swap(&mut truthy, &mut falsy);
            cond = cond.negate();
        }
        blocks[node.id.index()] = Some(HirBlock {
            stmts: vec![HirStmt::If(Box::new(HirIf {
                cond,
                // 原测试可以改变极性和嵌套形状，但不能因两条控制叶相同而消失。
                preserves_empty_test: true,
                preserves_arm_order: false,
                then_block: truthy,
                else_block: (!falsy.stmts.is_empty()).then_some(falsy),
            }))],
        });
    }
    Some(
        blocks[decision.entry.index()]
            .take()
            .expect("entry exists")
            .stmts,
    )
}
