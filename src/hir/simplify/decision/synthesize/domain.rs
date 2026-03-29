//! 这个子模块负责 decision synthesis 的抽象值域和等价性验证上下文。
//!
//! 它依赖前面已经规范化的 HIR decision 表达式，只表达“候选式子在抽象环境里代表什么”，
//! 不会在这里决定哪一种源码形状更可读。
//! 例如：`temp == nil` 会在这里被解释成可枚举的抽象真假环境。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirBinaryOpKind, HirDecisionExpr, HirDecisionNodeRef, HirDecisionTarget, HirExpr, LocalId,
    ParamId, TempId, UpvalueId,
};

use super::EXTRA_TRUTHY_SYMBOLS;
use super::cost::is_truthy;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(super) enum RefKey {
    Param(ParamId),
    Local(LocalId),
    Upvalue(UpvalueId),
    Temp(TempId),
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(super) enum AbstractValue {
    Nil,
    False,
    True,
    Integer(i64),
    Number(u64),
    String(String),
    Int64(i64),
    UInt64(u64),
    Complex { real_bits: u64, imag_bits: u64 },
    TruthySymbol(u8),
}

#[derive(Clone)]
pub(super) struct SynthesisContext<'a> {
    pub(super) decision: &'a HirDecisionExpr,
    pub(super) ref_positions: BTreeMap<RefKey, usize>,
    pub(super) environments: Vec<Vec<AbstractValue>>,
}

impl<'a> SynthesisContext<'a> {
    pub(super) fn new(decision: &'a HirDecisionExpr, refs: Vec<RefKey>) -> Option<Self> {
        let ref_positions = refs
            .iter()
            .enumerate()
            .map(|(index, key)| (*key, index))
            .collect::<BTreeMap<_, _>>();
        let domain = build_domain(decision);
        let environments = enumerate_environments(refs.len(), &domain)?;
        Some(Self {
            decision,
            ref_positions,
            environments,
        })
    }

    pub(super) fn eval_node(
        &self,
        node_ref: HirDecisionNodeRef,
        env: &[AbstractValue],
    ) -> Option<AbstractValue> {
        let node = self.decision.nodes.get(node_ref.index())?;
        let test = self.eval_expr(&node.test, env)?;
        let branch = if is_truthy(&test) {
            &node.truthy
        } else {
            &node.falsy
        };
        self.eval_target(branch, &test, env)
    }

    fn eval_target(
        &self,
        target: &HirDecisionTarget,
        current: &AbstractValue,
        env: &[AbstractValue],
    ) -> Option<AbstractValue> {
        match target {
            HirDecisionTarget::Node(next_ref) => self.eval_node(*next_ref, env),
            HirDecisionTarget::CurrentValue => Some(current.clone()),
            HirDecisionTarget::Expr(expr) => self.eval_expr(expr, env),
        }
    }

    pub(super) fn eval_expr(&self, expr: &HirExpr, env: &[AbstractValue]) -> Option<AbstractValue> {
        eval_pure_expr(expr, env, &self.ref_positions)
    }
}

pub(super) fn eval_pure_expr(
    expr: &HirExpr,
    env: &[AbstractValue],
    ref_positions: &BTreeMap<RefKey, usize>,
) -> Option<AbstractValue> {
    match expr {
        HirExpr::Nil => Some(AbstractValue::Nil),
        HirExpr::Boolean(false) => Some(AbstractValue::False),
        HirExpr::Boolean(true) => Some(AbstractValue::True),
        HirExpr::Integer(value) => Some(AbstractValue::Integer(*value)),
        HirExpr::Number(value) => Some(AbstractValue::Number(value.to_bits())),
        HirExpr::String(value) => Some(AbstractValue::String(value.clone())),
        HirExpr::Int64(value) => Some(AbstractValue::Int64(*value)),
        HirExpr::UInt64(value) => Some(AbstractValue::UInt64(*value)),
        HirExpr::Complex { real, imag } => Some(AbstractValue::Complex {
            real_bits: real.to_bits(),
            imag_bits: imag.to_bits(),
        }),
        HirExpr::ParamRef(param) => env
            .get(*ref_positions.get(&RefKey::Param(*param))?)
            .cloned(),
        HirExpr::LocalRef(local) => env
            .get(*ref_positions.get(&RefKey::Local(*local))?)
            .cloned(),
        HirExpr::UpvalueRef(upvalue) => env
            .get(*ref_positions.get(&RefKey::Upvalue(*upvalue))?)
            .cloned(),
        HirExpr::TempRef(temp) => env.get(*ref_positions.get(&RefKey::Temp(*temp))?).cloned(),
        HirExpr::Unary(unary) if unary.op == crate::hir::common::HirUnaryOpKind::Not => {
            let value = eval_pure_expr(&unary.expr, env, ref_positions)?;
            Some(if is_truthy(&value) {
                AbstractValue::False
            } else {
                AbstractValue::True
            })
        }
        HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Eq => {
            let lhs = eval_pure_expr(&binary.lhs, env, ref_positions)?;
            let rhs = eval_pure_expr(&binary.rhs, env, ref_positions)?;
            Some(if lhs == rhs {
                AbstractValue::True
            } else {
                AbstractValue::False
            })
        }
        HirExpr::LogicalAnd(logical) => {
            let lhs = eval_pure_expr(&logical.lhs, env, ref_positions)?;
            if is_truthy(&lhs) {
                eval_pure_expr(&logical.rhs, env, ref_positions)
            } else {
                Some(lhs)
            }
        }
        HirExpr::LogicalOr(logical) => {
            let lhs = eval_pure_expr(&logical.lhs, env, ref_positions)?;
            if is_truthy(&lhs) {
                Some(lhs)
            } else {
                eval_pure_expr(&logical.rhs, env, ref_positions)
            }
        }
        HirExpr::Decision(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => None,
    }
}

pub(super) fn validate_pure_expr_equivalence(
    lhs: &HirExpr,
    rhs: &HirExpr,
    environments: &[Vec<AbstractValue>],
    ref_positions: &BTreeMap<RefKey, usize>,
) -> bool {
    environments.iter().all(|env| {
        eval_pure_expr(lhs, env, ref_positions) == eval_pure_expr(rhs, env, ref_positions)
    })
}

pub(super) fn collect_refs_from_decision(decision: &HirDecisionExpr) -> Vec<RefKey> {
    let mut refs = BTreeSet::new();
    for node in &decision.nodes {
        collect_refs_from_expr(&node.test, &mut refs);
        collect_refs_from_target(&node.truthy, &mut refs);
        collect_refs_from_target(&node.falsy, &mut refs);
    }
    refs.into_iter().collect()
}

pub(super) fn collect_refs_from_expr(expr: &HirExpr, refs: &mut BTreeSet<RefKey>) {
    match expr {
        HirExpr::ParamRef(param) => {
            refs.insert(RefKey::Param(*param));
        }
        HirExpr::LocalRef(local) => {
            refs.insert(RefKey::Local(*local));
        }
        HirExpr::UpvalueRef(upvalue) => {
            refs.insert(RefKey::Upvalue(*upvalue));
        }
        HirExpr::TempRef(temp) => {
            refs.insert(RefKey::Temp(*temp));
        }
        HirExpr::Unary(unary) => collect_refs_from_expr(&unary.expr, refs),
        HirExpr::Binary(binary) => {
            collect_refs_from_expr(&binary.lhs, refs);
            collect_refs_from_expr(&binary.rhs, refs);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_refs_from_expr(&logical.lhs, refs);
            collect_refs_from_expr(&logical.rhs, refs);
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
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

pub(super) fn collect_literals_from_expr(expr: &HirExpr, literals: &mut BTreeSet<AbstractValue>) {
    match expr {
        HirExpr::Integer(value) => {
            literals.insert(AbstractValue::Integer(*value));
        }
        HirExpr::Number(value) => {
            literals.insert(AbstractValue::Number(value.to_bits()));
        }
        HirExpr::String(value) => {
            literals.insert(AbstractValue::String(value.clone()));
        }
        HirExpr::Int64(value) => {
            literals.insert(AbstractValue::Int64(*value));
        }
        HirExpr::UInt64(value) => {
            literals.insert(AbstractValue::UInt64(*value));
        }
        HirExpr::Complex { real, imag } => {
            literals.insert(AbstractValue::Complex {
                real_bits: real.to_bits(),
                imag_bits: imag.to_bits(),
            });
        }
        HirExpr::Unary(unary) => collect_literals_from_expr(&unary.expr, literals),
        HirExpr::Binary(binary) => {
            collect_literals_from_expr(&binary.lhs, literals);
            collect_literals_from_expr(&binary.rhs, literals);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_literals_from_expr(&logical.lhs, literals);
            collect_literals_from_expr(&logical.rhs, literals);
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
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

pub(super) fn enumerate_environments(
    ref_count: usize,
    domain: &[AbstractValue],
) -> Option<Vec<Vec<AbstractValue>>> {
    let total = domain.len().checked_pow(ref_count as u32)?;
    if total > 4096 {
        return None;
    }

    let mut envs = Vec::with_capacity(total);
    let mut current = Vec::with_capacity(ref_count);
    enumerate_envs_recursive(ref_count, domain, &mut current, &mut envs);
    Some(envs)
}

fn collect_refs_from_target(target: &HirDecisionTarget, refs: &mut BTreeSet<RefKey>) {
    if let HirDecisionTarget::Expr(expr) = target {
        collect_refs_from_expr(expr, refs);
    }
}

fn build_domain(decision: &HirDecisionExpr) -> Vec<AbstractValue> {
    let mut domain = vec![
        AbstractValue::Nil,
        AbstractValue::False,
        AbstractValue::True,
    ];
    let mut literals = BTreeSet::new();
    for node in &decision.nodes {
        collect_literals_from_expr(&node.test, &mut literals);
        collect_literals_from_target(&node.truthy, &mut literals);
        collect_literals_from_target(&node.falsy, &mut literals);
    }
    domain.extend(literals);
    domain.extend((0..EXTRA_TRUTHY_SYMBOLS).map(|index| AbstractValue::TruthySymbol(index as u8)));
    domain
}

fn collect_literals_from_target(
    target: &HirDecisionTarget,
    literals: &mut BTreeSet<AbstractValue>,
) {
    if let HirDecisionTarget::Expr(expr) = target {
        collect_literals_from_expr(expr, literals);
    }
}

fn enumerate_envs_recursive(
    remaining: usize,
    domain: &[AbstractValue],
    current: &mut Vec<AbstractValue>,
    out: &mut Vec<Vec<AbstractValue>>,
) {
    if remaining == 0 {
        out.push(current.clone());
        return;
    }

    for value in domain {
        current.push(value.clone());
        enumerate_envs_recursive(remaining - 1, domain, current, out);
        current.pop();
    }
}
