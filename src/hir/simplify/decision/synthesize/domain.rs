//! 这个子模块负责 decision synthesis 的抽象值域和等价性验证上下文。
//!
//! 它依赖前面已经规范化的 HIR decision 表达式，只表达“候选式子在抽象环境里代表什么”，
//! 不会在这里决定哪一种源码形状更可读。
//! 例如：`temp == nil` 会在这里被解释成可枚举的抽象真假环境；整数与浮点数的判等
//! 则按 Lua 数值语义计算，而不是按抽象值枚举项的 Rust 身份计算。

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};

use crate::LuaString;
use crate::hir::common::{
    HirBinaryOpKind, HirDecisionExpr, HirDecisionNodeRef, HirDecisionTarget, HirExpr, LocalId,
    ParamId, TempId, UpvalueId,
};
use crate::hir::expr_safety::HirExprSafety;

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
    String(LuaString),
    Int64(i64),
    UInt64(u64),
    Vector([u32; 4]),
    Complex { real_bits: u64, imag_bits: u64 },
    TruthySymbol(u8),
}

/// 模拟 Lua 对两个抽象值的 `<` / `<=` 比较语义。
///
/// Lua 只允许两个数字或两个字符串之间的比较（不考虑元方法）。
/// `TruthySymbol` 是综合域里的标记值，按索引给出确定序以保证验证可判定。
/// 其余类型组合（如 Nil 与数字）在运行时会抛出错误，此处返回 `None`。
fn abstract_value_partial_cmp(
    lhs: &AbstractValue,
    rhs: &AbstractValue,
    safety: HirExprSafety,
) -> Option<std::cmp::Ordering> {
    match (lhs, rhs) {
        (AbstractValue::Integer(a), AbstractValue::Integer(b)) => Some(a.cmp(b)),
        (AbstractValue::Number(a), AbstractValue::Number(b)) => {
            f64::from_bits(*a).partial_cmp(&f64::from_bits(*b))
        }
        (AbstractValue::Integer(a), AbstractValue::Number(b)) => {
            safety.mixed_integer_number_ordering(*a, f64::from_bits(*b))
        }
        (AbstractValue::Number(a), AbstractValue::Integer(b)) => safety
            .mixed_integer_number_ordering(*b, f64::from_bits(*a))
            .map(|o| o.reverse()),
        (AbstractValue::String(a), AbstractValue::String(b)) => {
            // 候选拒绝[SemanticBarrier:Locale]：PUC Lua 的字符串顺序依赖运行时 `LC_COLLATE`，抽象域不能用固定字节序验证候选。
            safety.literal_string_order_is_binary().then(|| a.cmp(b))
        }
        (AbstractValue::Int64(a), AbstractValue::Int64(b)) => Some(a.cmp(b)),
        (AbstractValue::UInt64(a), AbstractValue::UInt64(b)) => Some(a.cmp(b)),
        // 模型边界：TruthySymbol 的全序不是 Lua 语义；当前 repeatable 安全门会拒绝两个非字面量的顺序比较。
        (AbstractValue::TruthySymbol(a), AbstractValue::TruthySymbol(b)) => Some(a.cmp(b)),
        _ => None,
    }
}

/// 模拟 Lua `==` 对抽象值的原始判等语义。
///
/// 结果值等价性仍需区分 Integer/Number，因为 Lua 5.3+ 的 `math.type` 能观察表示；只有
/// `==` 运算本身会在整数与浮点数之间做精确数值比较。浮点同类比较直接使用 IEEE 754
/// `==`，从而让正负零相等、NaN 与任何值（包括自身）都不相等。
fn abstract_value_eq(
    lhs: &AbstractValue,
    rhs: &AbstractValue,
    safety: HirExprSafety,
) -> Option<bool> {
    match (lhs, rhs) {
        (AbstractValue::Number(lhs), AbstractValue::Number(rhs)) => {
            Some(f64::from_bits(*lhs) == f64::from_bits(*rhs))
        }
        (AbstractValue::Integer(integer), AbstractValue::Number(number))
        | (AbstractValue::Number(number), AbstractValue::Integer(integer)) => {
            safety.mixed_integer_number_equal(*integer, f64::from_bits(*number))
        }
        _ => Some(lhs == rhs),
    }
}

#[derive(Clone)]
pub(super) struct SynthesisContext<'a> {
    pub(super) decision: &'a HirDecisionExpr,
    pub(super) ref_positions: Cow<'a, BTreeMap<RefKey, usize>>,
    pub(super) environments: Cow<'a, [Vec<AbstractValue>]>,
    safety: HirExprSafety,
}

impl<'a> SynthesisContext<'a> {
    pub(super) fn new(
        decision: &'a HirDecisionExpr,
        refs: Vec<RefKey>,
        safety: HirExprSafety,
    ) -> Option<Self> {
        let ref_positions = refs
            .iter()
            .enumerate()
            .map(|(index, key)| (*key, index))
            .collect::<BTreeMap<_, _>>();
        let domain = build_domain(decision);
        let environments = enumerate_environments(refs.len(), &domain)?;
        Some(Self {
            decision,
            ref_positions: Cow::Owned(ref_positions),
            environments: Cow::Owned(environments),
            safety,
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
        eval_pure_expr(expr, env, &self.ref_positions, self.safety)
    }
}

pub(super) fn eval_pure_expr(
    expr: &HirExpr,
    env: &[AbstractValue],
    ref_positions: &BTreeMap<RefKey, usize>,
    safety: HirExprSafety,
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
        HirExpr::Vector(vector) => Some(AbstractValue::Vector(vector.components)),
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
            let value = eval_pure_expr(&unary.expr, env, ref_positions, safety)?;
            Some(if is_truthy(&value) {
                AbstractValue::False
            } else {
                AbstractValue::True
            })
        }
        HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Eq => {
            let lhs = eval_pure_expr(&binary.lhs, env, ref_positions, safety)?;
            let rhs = eval_pure_expr(&binary.rhs, env, ref_positions, safety)?;
            Some(if abstract_value_eq(&lhs, &rhs, safety)? {
                AbstractValue::True
            } else {
                AbstractValue::False
            })
        }
        HirExpr::Binary(binary)
            if matches!(binary.op, HirBinaryOpKind::Lt | HirBinaryOpKind::Le) =>
        {
            let lhs = eval_pure_expr(&binary.lhs, env, ref_positions, safety)?;
            let rhs = eval_pure_expr(&binary.rhs, env, ref_positions, safety)?;
            let ordering = abstract_value_partial_cmp(&lhs, &rhs, safety)?;
            let result = match binary.op {
                HirBinaryOpKind::Lt => ordering == std::cmp::Ordering::Less,
                HirBinaryOpKind::Le => ordering != std::cmp::Ordering::Greater,
                _ => unreachable!(),
            };
            Some(if result {
                AbstractValue::True
            } else {
                AbstractValue::False
            })
        }
        HirExpr::LogicalAnd(logical) => {
            let lhs = eval_pure_expr(&logical.lhs, env, ref_positions, safety)?;
            if is_truthy(&lhs) {
                eval_pure_expr(&logical.rhs, env, ref_positions, safety)
            } else {
                Some(lhs)
            }
        }
        HirExpr::LogicalOr(logical) => {
            let lhs = eval_pure_expr(&logical.lhs, env, ref_positions, safety)?;
            if is_truthy(&lhs) {
                Some(lhs)
            } else {
                eval_pure_expr(&logical.rhs, env, ref_positions, safety)
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
    safety: HirExprSafety,
) -> bool {
    environments.iter().all(|env| {
        let lhs = eval_pure_expr(lhs, env, ref_positions, safety);
        let rhs = eval_pure_expr(rhs, env, ref_positions, safety);
        // 候选拒绝[ProofIncomplete]：抽象解释任一侧未知时没有等价证明，`None == None` 不能作为接受依据。
        matches!((lhs, rhs), (Some(lhs), Some(rhs)) if lhs == rhs)
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
        | HirExpr::Vector(_)
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
        HirExpr::Vector(vector) => {
            literals.insert(AbstractValue::Vector(vector.components));
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
    // 候选拒绝[ResourceLimit]：环境数溢出 usize 时无法分配穷举表；后续应改用符号验证。
    // u32 是 checked_pow 的指数类型；超出它时直接拒绝，不能截断成较小指数。
    let exponent = u32::try_from(ref_count).ok()?;
    let total = domain.len().checked_pow(exponent)?;
    // 候选拒绝[ResourceLimit]：完整环境枚举上限为 4096；后续应改用符号验证或按依赖分区。
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

#[cfg(test)]
mod tests {
    use super::{AbstractValue, enumerate_environments};

    #[test]
    fn environment_cap_allows_five_base_domain_references() {
        let domain = [
            AbstractValue::Nil,
            AbstractValue::False,
            AbstractValue::True,
            AbstractValue::TruthySymbol(0),
            AbstractValue::TruthySymbol(1),
        ];
        assert_eq!(
            enumerate_environments(5, &domain).map(|envs| envs.len()),
            Some(3125)
        );
        assert!(enumerate_environments(6, &domain).is_none());
    }

    #[test]
    fn environment_exponent_does_not_truncate() {
        let Some(ref_count) = usize::try_from(u64::from(u32::MAX) + 1).ok() else {
            return;
        };
        assert!(enumerate_environments(ref_count, &[AbstractValue::Nil]).is_none());
    }
}
