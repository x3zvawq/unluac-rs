//! 这个文件承载 `Decision -> Expr` 综合时的形状成本评估。
//!
//! 这里的职责不是判断语义是否正确，语义等价已经由外层的抽象值校验负责。这个模块只
//! 回答一个更工程化的问题：当几种候选都等价时，哪一种更接近源码短路直觉、也更不容易
//! 把共享子图机械展开成难读的乘积式。

use std::collections::BTreeMap;

use super::*;

const AND_WITH_OR_CHILD_PENALTY: usize = 8;
const COMPLEX_AND_WITH_OR_EXTRA_PENALTY: usize = 4;
const OR_WITH_AND_CHILD_PENALTY: usize = 0;

pub(super) fn expr_cost(expr: &HirExpr) -> usize {
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
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_) => 1,
        HirExpr::Decision(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => usize::MAX / 4,
    }
}

fn duplicate_atom_penalty(expr: &HirExpr) -> usize {
    let mut counts = BTreeMap::new();
    collect_atomic_occurrences(expr, &mut counts);
    counts
        .into_values()
        .map(|count| count.saturating_sub(1))
        .sum::<usize>()
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
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::Decision(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Call(_)
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

fn collect_atomic_occurrences(expr: &HirExpr, counts: &mut BTreeMap<String, usize>) {
    match expr {
        HirExpr::Nil => bump_atom("nil".to_owned(), counts),
        HirExpr::Boolean(value) => bump_atom(format!("bool:{value}"), counts),
        HirExpr::Integer(value) => bump_atom(format!("int:{value}"), counts),
        HirExpr::Number(value) => bump_atom(format!("num:{:?}", value.to_bits()), counts),
        HirExpr::String(value) => bump_atom(format!("str:{value}"), counts),
        HirExpr::ParamRef(param) => bump_atom(format!("p{}", param.index()), counts),
        HirExpr::LocalRef(local) => bump_atom(format!("l{}", local.index()), counts),
        HirExpr::UpvalueRef(upvalue) => bump_atom(format!("u{}", upvalue.index()), counts),
        HirExpr::TempRef(temp) => bump_atom(format!("t{}", temp.index()), counts),
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not && is_atomic_expr(&unary.expr) => {
            bump_atom(format!("not({})", atomic_expr_key(&unary.expr)), counts);
        }
        HirExpr::Unary(unary) => collect_atomic_occurrences(&unary.expr, counts),
        HirExpr::Binary(binary) => {
            collect_atomic_occurrences(&binary.lhs, counts);
            collect_atomic_occurrences(&binary.rhs, counts);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_atomic_occurrences(&logical.lhs, counts);
            collect_atomic_occurrences(&logical.rhs, counts);
        }
        HirExpr::Decision(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => {}
    }
}

fn bump_atom(key: String, counts: &mut BTreeMap<String, usize>) {
    *counts.entry(key).or_default() += 1;
}

fn is_atomic_expr(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::TempRef(_)
    )
}

fn atomic_expr_key(expr: &HirExpr) -> String {
    match expr {
        HirExpr::Nil => "nil".to_owned(),
        HirExpr::Boolean(value) => format!("bool:{value}"),
        HirExpr::Integer(value) => format!("int:{value}"),
        HirExpr::Number(value) => format!("num:{:?}", value.to_bits()),
        HirExpr::String(value) => format!("str:{value}"),
        HirExpr::ParamRef(param) => format!("p{}", param.index()),
        HirExpr::LocalRef(local) => format!("l{}", local.index()),
        HirExpr::UpvalueRef(upvalue) => format!("u{}", upvalue.index()),
        HirExpr::TempRef(temp) => format!("t{}", temp.index()),
        _ => "complex".to_owned(),
    }
}
