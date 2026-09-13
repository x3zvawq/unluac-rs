//! 这个文件承载 `Decision -> Expr` 综合时的形状成本评估。
//!
//! 这里的职责不是判断语义是否正确，语义等价已经由外层的抽象值校验负责。这个模块只
//! 回答一个更工程化的问题：当几种候选都等价时，哪一种更接近源码短路直觉、也更不容易
//! 把共享子图机械展开成难读的乘积式。
//! 字面量及引用身份直接消费综合域的 AtomKey，包括 cdata、vector 和单值 vararg；
//! 不维护另一份“哪些是原子值”的分类，以免合法方言常量在成本遍历中变成不可达分支。

use crate::hir::common::{HirBinaryOpKind, HirExpr, HirUnaryOpKind};

use super::domain::{AbstractValue, AtomKey};

const AND_WITH_OR_CHILD_PENALTY: usize = 8;
const COMPLEX_AND_WITH_OR_EXTRA_PENALTY: usize = 4;
const OR_WITH_AND_CHILD_PENALTY: usize = 0;

pub(crate) fn expr_cost(expr: &HirExpr) -> usize {
    structural_expr_cost(expr) + duplicate_atom_penalty(expr) + logical_shape_penalty(expr)
}

pub(super) fn is_truthy(value: &AbstractValue) -> bool {
    !matches!(value, AbstractValue::Nil | AbstractValue::False)
}

fn structural_expr_cost(expr: &HirExpr) -> usize {
    match expr {
        HirExpr::Unary(unary) => 1 + structural_expr_cost(&unary.expr),
        HirExpr::Binary(binary) => {
            1 + structural_expr_cost(&binary.lhs) + structural_expr_cost(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            1 + structural_expr_cost(&logical.lhs) + structural_expr_cost(&logical.rhs)
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::VarArg => 1,
        HirExpr::CaptureInitializer(_) => 7,
        HirExpr::Decision(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Call(_)
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => usize::MAX / 4,
    }
}

fn duplicate_atom_penalty(expr: &HirExpr) -> usize {
    let mut atoms = Vec::new();
    collect_atomic_occurrences(expr, &mut atoms);
    if atoms.len() < 2 {
        return 0;
    }

    atoms.sort_unstable();

    let mut duplicates = 0;
    let mut run_len = 1usize;
    for window in atoms.windows(2) {
        if window[0] == window[1] {
            run_len += 1;
        } else {
            duplicates += run_len.saturating_sub(1);
            run_len = 1;
        }
    }
    duplicates + run_len.saturating_sub(1)
}

fn logical_shape_penalty(expr: &HirExpr) -> usize {
    match expr {
        HirExpr::Unary(unary) => logical_shape_penalty(&unary.expr),
        HirExpr::Binary(binary) => {
            logical_shape_penalty(&binary.lhs) + logical_shape_penalty(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) => {
            let lhs_penalty = logical_shape_penalty(&logical.lhs);
            let rhs_penalty = logical_shape_penalty(&logical.rhs);
            lhs_penalty
                + rhs_penalty
                + direct_child_penalty(LogicalShapeKind::And, &logical.lhs, &logical.rhs)
        }
        HirExpr::LogicalOr(logical) => {
            let lhs_penalty = logical_shape_penalty(&logical.lhs);
            let rhs_penalty = logical_shape_penalty(&logical.rhs);
            lhs_penalty
                + rhs_penalty
                + direct_child_penalty(LogicalShapeKind::Or, &logical.lhs, &logical.rhs)
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::Decision(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Call(_)
        | HirExpr::CaptureInitializer(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => 0,
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum LogicalShapeKind {
    And,
    Or,
}

fn direct_child_penalty(kind: LogicalShapeKind, lhs: &HirExpr, rhs: &HirExpr) -> usize {
    match kind {
        // `Decision` 本质上表达的是“若干守卫分支二选一”。
        // 当一组等价候选里同时出现 `A or B` 和 `(X or Y) and (Z or W)` 这两种形态时，
        // 后者往往只是共享 continuation 被机械因式分解后的结果；它虽然等价，
        // 但会把原本更接近源码的“分支择一”结构压成更难读的乘积式。
        //
        // 这里真正该打压的是“两边都像和式”的乘积形状，而不是一切 `a and (b or c)`。
        // 后者本来就是 Lua 源码里非常自然的短路表达式，如果统一惩罚，
        // `boolean_hell` 这类 case 会被硬推回更机械的展开树。
        LogicalShapeKind::And => {
            let or_children = usize::from(matches!(lhs, HirExpr::LogicalOr(_)))
                + usize::from(matches!(rhs, HirExpr::LogicalOr(_)));
            if or_children == 0 {
                return 0;
            }
            if or_children == 1 {
                let other = if matches!(lhs, HirExpr::LogicalOr(_)) {
                    rhs
                } else {
                    lhs
                };
                return if expr_is_compact_logical_branch(other) {
                    0
                } else {
                    COMPLEX_AND_WITH_OR_EXTRA_PENALTY
                };
            }

            let mut penalty = or_children * AND_WITH_OR_CHILD_PENALTY;
            if !expr_is_compact_logical_branch(lhs) || !expr_is_compact_logical_branch(rhs) {
                penalty += COMPLEX_AND_WITH_OR_EXTRA_PENALTY;
            }
            penalty
        }
        LogicalShapeKind::Or => {
            let and_children = usize::from(matches!(lhs, HirExpr::LogicalAnd(_)))
                + usize::from(matches!(rhs, HirExpr::LogicalAnd(_)));
            and_children * OR_WITH_AND_CHILD_PENALTY
        }
    }
}

fn expr_is_compact_logical_branch(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Vector(_)
            | HirExpr::Complex { .. }
            | HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::TempRef(_)
    ) || matches!(
        expr,
        HirExpr::Unary(unary)
            if unary.op == HirUnaryOpKind::Not && matches!(
                &unary.expr,
                HirExpr::ParamRef(_)
                    | HirExpr::LocalRef(_)
                    | HirExpr::UpvalueRef(_)
                    | HirExpr::TempRef(_)
            )
    ) || matches!(expr, HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Eq)
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd)]
enum AtomicOccurrenceKey {
    Value(AtomKey),
    Not(AtomKey),
}

fn collect_atomic_occurrences(expr: &HirExpr, atoms: &mut Vec<AtomicOccurrenceKey>) {
    if let Some(key) = AtomKey::from_expr(expr) {
        atoms.push(AtomicOccurrenceKey::Value(key));
        return;
    }

    match expr {
        HirExpr::Unary(unary) => {
            if unary.op == HirUnaryOpKind::Not
                && let Some(key) = AtomKey::from_expr(&unary.expr)
            {
                atoms.push(AtomicOccurrenceKey::Not(key));
            } else {
                collect_atomic_occurrences(&unary.expr, atoms);
            }
        }
        HirExpr::Binary(binary) => {
            collect_atomic_occurrences(&binary.lhs, atoms);
            collect_atomic_occurrences(&binary.rhs, atoms);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_atomic_occurrences(&logical.lhs, atoms);
            collect_atomic_occurrences(&logical.rhs, atoms);
        }
        _ => {}
    }
}
