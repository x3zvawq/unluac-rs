//! 这个文件承载 `Decision -> Expr` 综合时的形状成本评估。
//!
//! 这里的职责不是判断语义是否正确，语义等价已经由外层的抽象值校验负责。这个模块只
//! 回答一个更工程化的问题：当几种候选都等价时，哪一种更接近源码短路直觉、也更不容易
//! 把共享子图机械展开成难读的乘积式。

use crate::hir::common::{HirBinaryOpKind, HirExpr, HirUnaryOpKind};

use super::domain::AbstractValue;
use super::readable::flatten_or_chain;

const AND_WITH_OR_CHILD_PENALTY: usize = 8;
const COMPLEX_AND_WITH_OR_EXTRA_PENALTY: usize = 4;
const OR_WITH_AND_CHILD_PENALTY: usize = 0;

pub(crate) fn expr_cost(expr: &HirExpr) -> usize {
    structural_expr_cost(expr) + duplicate_atom_penalty(expr) + logical_shape_penalty(expr)
}

pub(super) fn readable_expr_cost(expr: &HirExpr) -> ReadableExprCost {
    ReadableExprCost {
        duplicate_branch_penalty: duplicate_branch_penalty(expr),
        duplicate_atom_penalty: duplicate_atom_penalty(expr),
        or_chain_penalty: or_chain_penalty(expr),
        structural_cost: structural_expr_cost(expr),
    }
}

pub(super) fn is_truthy(value: &AbstractValue) -> bool {
    !matches!(value, AbstractValue::Nil | AbstractValue::False)
}

#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct ReadableExprCost {
    duplicate_branch_penalty: usize,
    duplicate_atom_penalty: usize,
    or_chain_penalty: usize,
    structural_cost: usize,
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
        | HirExpr::Complex { .. }
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

fn duplicate_branch_penalty(expr: &HirExpr) -> usize {
    let mut branches = Vec::new();
    collect_branch_subexprs(expr, &mut branches);
    let mut counts = std::collections::BTreeMap::<ExprShapeKey<'_>, (usize, usize)>::new();
    for branch in branches {
        let key = expr_shape_key(branch);
        let cost = structural_expr_cost(branch);
        let entry = counts.entry(key).or_insert((0, cost));
        entry.0 += 1;
    }
    counts
        .into_values()
        .map(|(count, cost)| count.saturating_sub(1) * count / 2 * cost)
        .sum()
}

fn collect_branch_subexprs<'a>(expr: &'a HirExpr, out: &mut Vec<&'a HirExpr>) {
    match expr {
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            out.push(expr);
            collect_branch_subexprs(&logical.lhs, out);
            collect_branch_subexprs(&logical.rhs, out);
        }
        HirExpr::Unary(unary) => collect_branch_subexprs(&unary.expr, out),
        HirExpr::Binary(binary) => {
            collect_branch_subexprs(&binary.lhs, out);
            collect_branch_subexprs(&binary.rhs, out);
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
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
        | HirExpr::Unresolved(_) => {}
    }
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd)]
enum ExprShapeKey<'a> {
    Nil,
    Boolean(bool),
    Integer(i64),
    Number(u64),
    String(&'a str),
    Int64(i64),
    UInt64(u64),
    Complex { real_bits: u64, imag_bits: u64 },
    Param(usize),
    Local(usize),
    Upvalue(usize),
    Temp(usize),
    Not(Box<ExprShapeKey<'a>>),
    Eq(Box<ExprShapeKey<'a>>, Box<ExprShapeKey<'a>>),
    LogicalAnd(Box<ExprShapeKey<'a>>, Box<ExprShapeKey<'a>>),
    LogicalOr(Box<ExprShapeKey<'a>>, Box<ExprShapeKey<'a>>),
    Global(&'a str),
    TableAccess(Box<ExprShapeKey<'a>>, Box<ExprShapeKey<'a>>),
    Call,
    VarArg,
    TableConstructor,
    Closure,
    Decision,
    Unresolved,
}

fn expr_shape_key<'a>(expr: &'a HirExpr) -> ExprShapeKey<'a> {
    match expr {
        HirExpr::Nil => ExprShapeKey::Nil,
        HirExpr::Boolean(value) => ExprShapeKey::Boolean(*value),
        HirExpr::Integer(value) => ExprShapeKey::Integer(*value),
        HirExpr::Number(value) => ExprShapeKey::Number(value.to_bits()),
        HirExpr::String(value) => ExprShapeKey::String(value.as_str()),
        HirExpr::Int64(value) => ExprShapeKey::Int64(*value),
        HirExpr::UInt64(value) => ExprShapeKey::UInt64(*value),
        HirExpr::Complex { real, imag } => ExprShapeKey::Complex {
            real_bits: real.to_bits(),
            imag_bits: imag.to_bits(),
        },
        HirExpr::ParamRef(param) => ExprShapeKey::Param(param.index()),
        HirExpr::LocalRef(local) => ExprShapeKey::Local(local.index()),
        HirExpr::UpvalueRef(upvalue) => ExprShapeKey::Upvalue(upvalue.index()),
        HirExpr::TempRef(temp) => ExprShapeKey::Temp(temp.index()),
        HirExpr::GlobalRef(global) => ExprShapeKey::Global(global.name.as_str()),
        HirExpr::TableAccess(access) => ExprShapeKey::TableAccess(
            Box::new(expr_shape_key(&access.base)),
            Box::new(expr_shape_key(&access.key)),
        ),
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            ExprShapeKey::Not(Box::new(expr_shape_key(&unary.expr)))
        }
        HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Eq => ExprShapeKey::Eq(
            Box::new(expr_shape_key(&binary.lhs)),
            Box::new(expr_shape_key(&binary.rhs)),
        ),
        HirExpr::LogicalAnd(logical) => ExprShapeKey::LogicalAnd(
            Box::new(expr_shape_key(&logical.lhs)),
            Box::new(expr_shape_key(&logical.rhs)),
        ),
        HirExpr::LogicalOr(logical) => ExprShapeKey::LogicalOr(
            Box::new(expr_shape_key(&logical.lhs)),
            Box::new(expr_shape_key(&logical.rhs)),
        ),
        HirExpr::Unary(_other) => ExprShapeKey::Unresolved,
        HirExpr::Binary(_other) => ExprShapeKey::Unresolved,
        HirExpr::Decision(_) => ExprShapeKey::Decision,
        HirExpr::Call(_) => ExprShapeKey::Call,
        HirExpr::VarArg => ExprShapeKey::VarArg,
        HirExpr::TableConstructor(_) => ExprShapeKey::TableConstructor,
        HirExpr::Closure(_) => ExprShapeKey::Closure,
        HirExpr::Unresolved(_) => ExprShapeKey::Unresolved,
    }
}

fn or_chain_penalty(expr: &HirExpr) -> usize {
    match expr {
        HirExpr::LogicalOr(logical) => {
            let chain_penalty = flatten_or_chain(expr).len().saturating_sub(2) * 4;
            chain_penalty + or_chain_penalty(&logical.lhs) + or_chain_penalty(&logical.rhs)
        }
        HirExpr::LogicalAnd(logical) => {
            or_chain_penalty(&logical.lhs) + or_chain_penalty(&logical.rhs)
        }
        HirExpr::Unary(unary) => or_chain_penalty(&unary.expr),
        HirExpr::Binary(binary) => or_chain_penalty(&binary.lhs) + or_chain_penalty(&binary.rhs),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
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
        | HirExpr::Complex { .. }
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
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
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

#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
enum AtomicValueKey<'a> {
    Nil,
    Boolean(bool),
    Integer(i64),
    Number(u64),
    String(&'a str),
    Param(usize),
    Local(usize),
    Upvalue(usize),
    Temp(usize),
}

#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
enum AtomicOccurrenceKey<'a> {
    Value(AtomicValueKey<'a>),
    Not(AtomicValueKey<'a>),
}

fn collect_atomic_occurrences<'a>(expr: &'a HirExpr, atoms: &mut Vec<AtomicOccurrenceKey<'a>>) {
    if let Some(key) = atomic_value_key(expr) {
        atoms.push(AtomicOccurrenceKey::Value(key));
        return;
    }

    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_) => {
            unreachable!("atomic exprs should have been handled before recursing")
        }
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not && is_atomic_expr(&unary.expr) => {
            atoms.push(AtomicOccurrenceKey::Not(
                atomic_value_key(&unary.expr).expect("atomic expr must map to an atomic key"),
            ));
        }
        HirExpr::Unary(unary) => collect_atomic_occurrences(&unary.expr, atoms),
        HirExpr::Binary(binary) => {
            collect_atomic_occurrences(&binary.lhs, atoms);
            collect_atomic_occurrences(&binary.rhs, atoms);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_atomic_occurrences(&logical.lhs, atoms);
            collect_atomic_occurrences(&logical.rhs, atoms);
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

fn is_atomic_expr(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Complex { .. }
            | HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::TempRef(_)
    )
}

fn atomic_value_key(expr: &HirExpr) -> Option<AtomicValueKey<'_>> {
    match expr {
        HirExpr::Nil => Some(AtomicValueKey::Nil),
        HirExpr::Boolean(value) => Some(AtomicValueKey::Boolean(*value)),
        HirExpr::Integer(value) => Some(AtomicValueKey::Integer(*value)),
        HirExpr::Number(value) => Some(AtomicValueKey::Number(value.to_bits())),
        HirExpr::String(value) => Some(AtomicValueKey::String(value.as_str())),
        HirExpr::ParamRef(param) => Some(AtomicValueKey::Param(param.index())),
        HirExpr::LocalRef(local) => Some(AtomicValueKey::Local(local.index())),
        HirExpr::UpvalueRef(upvalue) => Some(AtomicValueKey::Upvalue(upvalue.index())),
        HirExpr::TempRef(temp) => Some(AtomicValueKey::Temp(temp.index())),
        _ => None,
    }
}
