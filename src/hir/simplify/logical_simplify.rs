//! 这个文件承载 HIR 的保守逻辑表达式整理。
//!
//! Lua 的 `and/or` 返回的是原始操作数，不是布尔值，所以很多看似显然的布尔代数
//! 恒等式其实并不安全。这里故意只实现一小撮在 Lua 值语义下也严格成立的规则，
//! 用来压掉短路 DAG 恢复后最机械的重复，而不越权重写控制流结构。
//!
//! 它依赖前面的 short-circuit / decision 恢复已经把候选逻辑表达式保守落成 HIR，
//! 这里仅做“值语义严格不变”的局部整理，不重新分析 CFG，也不替前层兜底修坏掉的
//! 短路结构。
//!
//! 例子：
//! - `x and x` 只会在 `x` 可稳定重复求值时折成 `x`
//! - `(a and b) or (a and c)` 只会在整段表达式均可稳定重复求值时整理
//! - `not a and x or y` 在 `x/y` 恒真时整理成 `a and y or x`
//! - 条件中的 `not (a or b)` 会在一次遍历中下推成 `not a and not b`
//! - `x or x` 会折成 `x`
//! - 它不会把一般 `if/branch` 结构强行改写成逻辑表达式，那仍然属于更前面的结构恢复职责

use super::expr_facts::{expr_is_boolean_valued, expr_truthiness};
use super::walk::{ExprRewritePass, rewrite_proto_exprs};
use crate::decompile::DecompileDialect;
use crate::hir::common::{HirBinaryOpKind, HirExpr, HirLogicalExpr, HirProto, HirUnaryOpKind};
use crate::hir::expr_safety::{
    expr_is_discard_safe, expr_is_repeatable, luau_literal_addition_value,
    primitive_literal_comparison_value,
};

/// 对单个 proto 递归执行安全的逻辑表达式整理。
pub(super) fn simplify_logical_exprs_in_proto(
    proto: &mut HirProto,
    dialect: DecompileDialect,
) -> bool {
    rewrite_proto_exprs(proto, &mut LogicalExprPass::for_dialect(dialect))
}

struct LogicalExprPass {
    fold_luau_literal_addition: bool,
}

impl LogicalExprPass {
    fn for_dialect(dialect: DecompileDialect) -> Self {
        Self {
            fold_luau_literal_addition: dialect == DecompileDialect::Luau,
        }
    }
}

impl ExprRewritePass for LogicalExprPass {
    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        let mut changed = false;

        if let HirExpr::Binary(binary) = expr
            && let Some(value) =
                primitive_literal_comparison_value(binary.op, &binary.lhs, &binary.rhs)
        {
            *expr = HirExpr::Boolean(value);
            changed = true;
        }

        // 候选拒绝[TargetConstraint]：非 Luau 方言的整数/浮点算术与结果类型合同不同，不能套用 Luau number 快路径。
        // 候选拒绝[SemanticBarrier:Numeric]：把 `-0.0 + -0.0` 经整数域折成 `0.0` 会丢失可观察的负零符号位。
        // 候选拒绝[ProofIncomplete]：其余有限小数及大整数尚未直接按 Luau f64 语义求值，应扩展 helper 而非永久保留。
        if self.fold_luau_literal_addition
            && let HirExpr::Binary(binary) = expr
            && binary.op == HirBinaryOpKind::Add
            && let Some(value) = luau_literal_addition_value(&binary.lhs, &binary.rhs)
        {
            *expr = value;
            changed = true;
        }

        if let Some(replacement) = simplify_logical_shape(expr) {
            *expr = replacement;
            changed = true;
        }
        if let Some(replacement) = super::decision::naturalize_pure_logical_expr(expr) {
            *expr = replacement;
            changed = true;
        }

        changed
    }

    fn rewrite_condition_expr(&mut self, expr: &mut HirExpr) -> bool {
        let mut changed = false;
        if let Some(replacement) = simplify_logical_shape(expr) {
            *expr = replacement;
            changed = true;
        }
        if let Some(replacement) = simplify_condition_truthiness_shape(expr) {
            *expr = replacement;
            changed = true;
        }
        let normalized = normalize_condition_context(expr, false);
        if normalized.changed {
            *expr = normalized.expr;
            changed = true;
        }
        changed
    }
}

pub(super) fn simplify_logical_shape(expr: &HirExpr) -> Option<HirExpr> {
    match expr {
        HirExpr::LogicalAnd(logical) => simplify_logical_and(&logical.lhs, &logical.rhs),
        HirExpr::LogicalOr(logical) => simplify_logical_or(&logical.lhs, &logical.rhs),
        _ => None,
    }
}

fn simplify_logical_and(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    // 候选拒绝[SemanticBarrier:EvalCount]：`f() and f()` 折成 `f()` 会在首个结果 truthy 时少调用一次。
    if lhs == rhs && expr_is_repeatable(lhs) {
        return Some(lhs.clone());
    }

    if let Some(replacement) = fold_associative_duplicate_and(lhs, rhs) {
        return Some(replacement);
    }

    if let Some(replacement) = fold_constant_short_circuit_and(lhs, rhs) {
        return Some(replacement);
    }

    match (rhs, expr_is_boolean_valued(lhs)) {
        (HirExpr::Boolean(true), true) => return Some(lhs.clone()),
        // 候选拒绝[SemanticBarrier:Value]：`1 and true` 返回 true，而直接改成 `1` 返回原始数值。
        (HirExpr::Boolean(true), false) => {}
        _ => {}
    }

    // 候选拒绝[ProofIncomplete]：以下 blanket gate 连未被删除的单次子式也要求 repeatable；需按吸收形状只核验实际重复 occurrence。
    if !expr_is_repeatable(lhs) || !expr_is_repeatable(rhs) {
        return None;
    }

    match (lhs, rhs) {
        (lhs, HirExpr::LogicalOr(inner)) if lhs == &inner.lhs => Some(lhs.clone()),
        (HirExpr::LogicalOr(inner), rhs) if rhs == &inner.rhs => Some(rhs.clone()),
        _ => None,
    }
}

fn simplify_logical_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    // 候选拒绝[SemanticBarrier:EvalCount]：`f() or f()` 折成 `f()` 会在首个结果 falsy 时少调用一次。
    if lhs == rhs && expr_is_repeatable(lhs) {
        return Some(lhs.clone());
    }

    if let Some(replacement) = fold_associative_duplicate_or(lhs, rhs) {
        return Some(replacement);
    }

    if let Some(replacement) = fold_constant_short_circuit_or(lhs, rhs) {
        return Some(replacement);
    }

    match (rhs, expr_is_boolean_valued(lhs)) {
        (HirExpr::Boolean(false), true) => return Some(lhs.clone()),
        // 候选拒绝[SemanticBarrier:Value]：`nil or false` 返回 false，而直接改成 lhs 会返回 nil。
        (HirExpr::Boolean(false), false) => {}
        _ => {}
    }
    if let Some(replacement) = naturalize_truthy_ternary(lhs, rhs) {
        return Some(replacement);
    }
    if let Some(replacement) = factor_shared_and_guards(lhs, rhs) {
        return Some(replacement);
    }
    if let Some(replacement) = pull_shared_or_tail(lhs, rhs) {
        return Some(replacement);
    }
    if let Some(replacement) = fold_shared_fallback_or(lhs, rhs) {
        return Some(replacement);
    }

    // 候选拒绝[ProofIncomplete]：以下 blanket gate 连未被删除的单次子式也要求 repeatable；需按吸收形状只核验实际重复 occurrence。
    if !expr_is_repeatable(lhs) || !expr_is_repeatable(rhs) {
        return None;
    }

    match (lhs, rhs) {
        (lhs, HirExpr::LogicalAnd(inner)) if lhs == &inner.lhs => Some(lhs.clone()),
        (HirExpr::LogicalAnd(inner), rhs) if rhs == &inner.rhs => Some(rhs.clone()),
        _ => None,
    }
}

/// `not a and x or y` 在 `x/y` 恒真时等价于 `a and y or x`。
///
/// 两种形状都会先且仅求值一次 `a`，随后在 `a` 为真时求值 `y`，否则求值 `x`；
/// 恒真约束保证选中分支不会继续落到另一个分支。
fn naturalize_truthy_ternary(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    let HirExpr::LogicalAnd(and_expr) = lhs else {
        return None;
    };
    let HirExpr::Unary(guard) = &and_expr.lhs else {
        return None;
    };
    if guard.op != HirUnaryOpKind::Not {
        return None;
    }
    // 候选拒绝[SemanticBarrier:Value]：分支非恒真时两式会返回不同 falsy 原值；`a=false,x=false,y=1` 时原式为 1、候选为 false。
    if expr_truthiness(&and_expr.rhs) != Some(true) || expr_truthiness(rhs) != Some(true) {
        return None;
    }

    Some(HirExpr::LogicalOr(Box::new(HirLogicalExpr {
        lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            lhs: guard.expr.clone(),
            rhs: rhs.clone(),
        })),
        rhs: and_expr.rhs.clone(),
    })))
}

fn fold_associative_duplicate_and(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    // 候选拒绝[SemanticBarrier:EvalCount]：匹配到重复项但其为 `f()` 时，删除一项会减少一次可能调用。
    match (lhs, rhs) {
        (HirExpr::LogicalAnd(inner), rhs) if rhs == &inner.rhs && expr_is_repeatable(rhs) => {
            Some(lhs.clone())
        }
        (lhs, HirExpr::LogicalAnd(inner)) if lhs == &inner.lhs && expr_is_repeatable(lhs) => {
            Some(rhs.clone())
        }
        _ => None,
    }
}

fn fold_associative_duplicate_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    // 候选拒绝[SemanticBarrier:EvalCount]：匹配到重复项但其为 `f()` 时，删除一项会减少一次可能调用。
    match (lhs, rhs) {
        (HirExpr::LogicalOr(inner), rhs) if rhs == &inner.rhs && expr_is_repeatable(rhs) => {
            Some(lhs.clone())
        }
        (lhs, HirExpr::LogicalOr(inner)) if lhs == &inner.lhs && expr_is_repeatable(lhs) => {
            Some(rhs.clone())
        }
        _ => None,
    }
}

fn factor_shared_and_guards(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    factor_shared_and_guards_one_side(lhs, rhs)
}

fn factor_shared_and_guards_one_side(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    let HirExpr::LogicalAnd(lhs_and) = lhs else {
        return None;
    };
    let HirExpr::LogicalAnd(rhs_and) = rhs else {
        return None;
    };

    if lhs_and.lhs == rhs_and.lhs {
        // 候选拒绝[ProofIncomplete]：只需证明共享 guard 可重复；当前整臂 gate 会连仅求值一次的 b/c call 一并拒绝，应改为 occurrence 级证明。
        if !expr_is_repeatable(lhs) || !expr_is_repeatable(rhs) {
            return None;
        }
        return Some(HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            lhs: lhs_and.lhs.clone(),
            rhs: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                lhs: lhs_and.rhs.clone(),
                rhs: rhs_and.rhs.clone(),
            })),
        })));
    }

    None
}

fn pull_shared_or_tail(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    pull_shared_or_tail_one_side(lhs, rhs)
}

fn pull_shared_or_tail_one_side(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    let HirExpr::LogicalAnd(lhs_and) = lhs else {
        return None;
    };
    let HirExpr::LogicalOr(inner_or) = &lhs_and.rhs else {
        return None;
    };
    if rhs != &inner_or.rhs {
        return None;
    }
    // 候选拒绝[ProofIncomplete]：只需证明被删除的共享 tail 可重复；当前整臂 gate 会拒绝未移动且仅求值一次的 guard/前缀 call。
    if !expr_is_repeatable(lhs) || !expr_is_repeatable(rhs) {
        return None;
    }

    Some(HirExpr::LogicalOr(Box::new(HirLogicalExpr {
        lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            lhs: lhs_and.lhs.clone(),
            rhs: inner_or.lhs.clone(),
        })),
        rhs: rhs.clone(),
    })))
}

/// 这里只折叠“左值 truthiness 已知”的短路表达式。
fn fold_constant_short_circuit_and(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    match expr_truthiness(lhs) {
        Some(true) if expr_is_discard_safe(lhs) => Some(rhs.clone()),
        Some(false) => Some(lhs.clone()),
        // 候选拒绝[SemanticBarrier:EvalCount]：已知 truthy 的 `{ f() }` 仍不可删除，否则字段表达式中的一次 `f()` 消失。
        Some(true) => None,
        None => None,
    }
}

fn fold_constant_short_circuit_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    match expr_truthiness(lhs) {
        Some(true) => Some(lhs.clone()),
        Some(false) if expr_is_discard_safe(lhs) => Some(rhs.clone()),
        // 候选拒绝[SemanticBarrier:EvalCount]：已知 falsy 但不可丢弃的 lhs 仍必须求值一次，不能直接选 rhs。
        Some(false) => None,
        None => None,
    }
}

/// 这里处理一类共享 fallback 的机械展开：
///
/// `((not x) and y) or (x or y)` 在 Lua 里和 `x or y` 等价，只是前者会在恢复
/// 决策 DAG 时留下重复的 fallback 片段。只要 `y` 无副作用，这里就可以安全地
/// 把它重新收回更自然的短路表达式。
fn fold_shared_fallback_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    shared_fallback_or_one_side(lhs, rhs)
        .or_else(|| shared_fallback_or_one_side(rhs, lhs))
        .or_else(|| fold_prefixed_shared_fallback_or(lhs, rhs))
}

fn shared_fallback_or_one_side(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    let HirExpr::LogicalAnd(lhs_and) = lhs else {
        return None;
    };
    let HirExpr::LogicalOr(rhs_or) = rhs else {
        return None;
    };
    let guard = strip_negation(&lhs_and.lhs)?;
    if guard != rhs_or.lhs || lhs_and.rhs != rhs_or.rhs {
        return None;
    }
    // 候选拒绝[SemanticBarrier:EvalCount]：fallback 为 `f()` 且返回 falsy 时，机械展开可能调用两次，合并后只调用一次。
    if !expr_is_repeatable(lhs) || !expr_is_repeatable(rhs) {
        return None;
    }
    Some(rhs.clone())
}

fn fold_prefixed_shared_fallback_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    let HirExpr::LogicalOr(rhs_or) = rhs else {
        return None;
    };
    let prefix = HirExpr::LogicalOr(Box::new(HirLogicalExpr {
        lhs: lhs.clone(),
        rhs: rhs_or.lhs.clone(),
    }));
    shared_fallback_or_one_side(&rhs_or.rhs, &prefix)
}

fn strip_negation(expr: &HirExpr) -> Option<HirExpr> {
    match expr {
        HirExpr::Unary(unary) if matches!(unary.op, crate::hir::common::HirUnaryOpKind::Not) => {
            Some(unary.expr.clone())
        }
        _ => None,
    }
}

pub(super) fn simplify_condition_truthiness_shape(expr: &HirExpr) -> Option<HirExpr> {
    match expr {
        HirExpr::LogicalAnd(logical) => simplify_condition_logical_and(&logical.lhs, &logical.rhs),
        HirExpr::LogicalOr(logical) => simplify_condition_logical_or(&logical.lhs, &logical.rhs),
        _ => None,
    }
}

pub(super) struct ConditionContextForm {
    pub(super) expr: HirExpr,
    pub(super) not_cost: usize,
    pub(super) changed: bool,
}

/// 构造条件及其反形的统一规范形，并计算最终需要打印的显式 `not` 数。
///
/// De Morgan 只沿 `and/or/not` 条件骨架下推，始终先处理 lhs 再处理 rhs，不交换也不复制
/// 操作数。`not Eq` 可由生成器直接打印成 `~=`，因此不计成本；`Lt/Le` 不能在 NaN 或
/// 元方法语义下安全反转，仍保留为显式 `not`。
pub(super) fn normalize_condition_context(expr: &HirExpr, negated: bool) -> ConditionContextForm {
    let changed = requested_polarity_needs_normalization(expr, negated);
    let (expr, not_cost) = normalize_condition_context_inner(expr, negated);
    ConditionContextForm {
        expr,
        not_cost,
        changed,
    }
}

fn normalize_condition_context_inner(expr: &HirExpr, negated: bool) -> (HirExpr, usize) {
    match expr {
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            normalize_condition_context_inner(&unary.expr, !negated)
        }
        HirExpr::LogicalAnd(logical) => {
            let (lhs, lhs_cost) = normalize_condition_context_inner(&logical.lhs, negated);
            let (rhs, rhs_cost) = normalize_condition_context_inner(&logical.rhs, negated);
            let logical = Box::new(HirLogicalExpr { lhs, rhs });
            let expr = if negated {
                HirExpr::LogicalOr(logical)
            } else {
                HirExpr::LogicalAnd(logical)
            };
            (expr, lhs_cost.saturating_add(rhs_cost))
        }
        HirExpr::LogicalOr(logical) => {
            let (lhs, lhs_cost) = normalize_condition_context_inner(&logical.lhs, negated);
            let (rhs, rhs_cost) = normalize_condition_context_inner(&logical.rhs, negated);
            let logical = Box::new(HirLogicalExpr { lhs, rhs });
            let expr = if negated {
                HirExpr::LogicalAnd(logical)
            } else {
                HirExpr::LogicalOr(logical)
            };
            (expr, lhs_cost.saturating_add(rhs_cost))
        }
        _ if negated => {
            let not_cost = usize::from(
                !matches!(expr, HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Eq),
            );
            (expr.clone().negate(), not_cost)
        }
        _ => (expr.clone(), 0),
    }
}

fn requested_polarity_needs_normalization(expr: &HirExpr, negated: bool) -> bool {
    if !negated {
        return condition_needs_normalization(expr);
    }

    match expr {
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            condition_needs_normalization(&unary.expr)
        }
        HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_) => true,
        _ => false,
    }
}

fn condition_needs_normalization(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            matches!(
                &unary.expr,
                HirExpr::Unary(inner) if inner.op == HirUnaryOpKind::Not
            ) || matches!(&unary.expr, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            condition_needs_normalization(&logical.lhs)
                || condition_needs_normalization(&logical.rhs)
        }
        _ => false,
    }
}

fn simplify_condition_logical_and(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    if matches!(rhs, HirExpr::Boolean(true)) {
        return Some(lhs.clone());
    }
    match (rhs, expr_is_discard_safe(lhs)) {
        (HirExpr::Boolean(false), true) => return Some(HirExpr::Boolean(false)),
        // 候选拒绝[SemanticBarrier:EvalCount]：`f() and false` 在条件中仍调用 `f()`，不能直接变成 false。
        (HirExpr::Boolean(false), false) => {}
        _ => {}
    }
    if matches!(lhs, HirExpr::Boolean(true)) {
        return Some(rhs.clone());
    }
    if matches!(lhs, HirExpr::Boolean(false)) {
        return Some(HirExpr::Boolean(false));
    }
    None
}

fn simplify_condition_logical_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    if let Some(replacement) = factor_condition_shared_and_tail(lhs, rhs) {
        return Some(replacement);
    }
    if let Some(replacement) = absorb_stable_or_guard(lhs, rhs) {
        return Some(replacement);
    }
    if matches!(rhs, HirExpr::Boolean(false)) {
        return Some(lhs.clone());
    }
    match (rhs, expr_is_discard_safe(lhs)) {
        (HirExpr::Boolean(true), true) => return Some(HirExpr::Boolean(true)),
        // 候选拒绝[SemanticBarrier:EvalCount]：`f() or true` 在条件中仍调用 `f()`，不能直接变成 true。
        (HirExpr::Boolean(true), false) => {}
        _ => {}
    }
    if matches!(lhs, HirExpr::Boolean(false)) {
        return Some(rhs.clone());
    }
    if matches!(lhs, HirExpr::Boolean(true)) {
        return Some(HirExpr::Boolean(true));
    }
    None
}

/// `(a and c) or (b and c)` 在条件中可收成 `(a or b) and c`。
///
/// 两臂均可重复时，被删除的 `b` 或第二次 `c` 读取没有可观察事件；这里只保持 truthiness，
/// 所以不能进入会返回原始 Lua 操作数的普通值语境。
fn factor_condition_shared_and_tail(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    let (HirExpr::LogicalAnd(lhs_and), HirExpr::LogicalAnd(rhs_and)) = (lhs, rhs) else {
        return None;
    };
    if lhs_and.rhs != rhs_and.rhs {
        return None;
    }
    // 候选拒绝[ProofIncomplete]：当前整臂 repeatable gate 未区分被合并 occurrence 与仍单次原位求值的子式，需候选级 eval-trace 对照。
    if !expr_is_repeatable(lhs) || !expr_is_repeatable(rhs) {
        return None;
    }

    Some(HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
        lhs: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
            lhs: lhs_and.lhs.clone(),
            rhs: rhs_and.lhs.clone(),
        })),
        rhs: lhs_and.rhs.clone(),
    })))
}

/// In a condition, a stable guard repeated on the left side of a nested `or` is
/// only an implementation detail of a shared short-circuit DAG:
/// `x or ((x or y) and z)` and `x or (y and z)` have the same truthiness and
/// preserve the evaluation order of `y` and `z`.  Keep this rule in the
/// condition-only path; the two expressions do not have the same Lua value.
fn absorb_stable_or_guard(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    let HirExpr::LogicalAnd(and_expr) = rhs else {
        return None;
    };
    let HirExpr::LogicalOr(inner_or) = &and_expr.lhs else {
        return None;
    };
    if lhs != &inner_or.lhs {
        return None;
    }
    // 候选拒绝[SemanticBarrier:EvalCount]：重复 guard 为 `f()` 时，吸收会在某些路径把两次调用缩成一次。
    if !expr_is_repeatable(lhs) {
        return None;
    }

    Some(HirExpr::LogicalOr(Box::new(HirLogicalExpr {
        lhs: lhs.clone(),
        rhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            lhs: inner_or.rhs.clone(),
            rhs: and_expr.rhs.clone(),
        })),
    })))
}

#[cfg(test)]
mod tests {
    use super::super::walk::ExprRewritePass;
    use super::{LogicalExprPass, simplify_condition_truthiness_shape, simplify_logical_shape};
    use crate::decompile::DecompileDialect;
    use crate::hir::common::{HirBinaryExpr, HirBinaryOpKind, HirExpr, HirLogicalExpr, ParamId};
    use crate::hir::expr_safety::luau_literal_addition_value;

    fn param(index: usize) -> HirExpr {
        HirExpr::ParamRef(ParamId(index))
    }

    #[test]
    fn absorbs_stable_guard_only_in_condition_context() {
        let a = param(0);
        let b = param(1);
        let c = param(2);
        let expr = HirExpr::LogicalOr(Box::new(HirLogicalExpr {
            lhs: a.clone(),
            rhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                lhs: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                    lhs: a.clone(),
                    rhs: b.clone(),
                })),
                rhs: c.clone(),
            })),
        }));
        let expected = HirExpr::LogicalOr(Box::new(HirLogicalExpr {
            lhs: a,
            rhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr { lhs: b, rhs: c })),
        }));

        assert_eq!(simplify_condition_truthiness_shape(&expr), Some(expected));
        assert_eq!(simplify_logical_shape(&expr), None);
    }

    #[test]
    fn folds_exact_luau_literal_addition() {
        assert_eq!(
            luau_literal_addition_value(&HirExpr::Integer(2), &HirExpr::Integer(3)),
            Some(HirExpr::Number(5.0))
        );
        assert_eq!(
            luau_literal_addition_value(&HirExpr::Number(1.5), &HirExpr::Number(2.0)),
            None
        );
        assert_eq!(
            luau_literal_addition_value(&HirExpr::Integer(0), &HirExpr::Number(1.0)),
            Some(HirExpr::Number(1.0))
        );
    }

    #[test]
    fn rejects_non_literal_or_unrepresentable_addition() {
        assert_eq!(
            luau_literal_addition_value(&param(0), &HirExpr::Number(1.0)),
            None
        );
        assert_eq!(
            luau_literal_addition_value(&HirExpr::Number(-0.0), &HirExpr::Number(0.0)),
            None
        );
        assert_eq!(
            luau_literal_addition_value(
                &HirExpr::Number(9_007_199_254_740_992.0),
                &HirExpr::Number(1.0)
            ),
            None
        );
        assert_eq!(
            luau_literal_addition_value(&HirExpr::Number(f64::NAN), &HirExpr::Number(1.0)),
            None
        );
    }

    #[test]
    fn literal_addition_fold_is_dialect_gated() {
        let add = || {
            HirExpr::Binary(Box::new(HirBinaryExpr {
                op: HirBinaryOpKind::Add,
                lhs: HirExpr::Integer(2),
                rhs: HirExpr::Integer(3),
            }))
        };

        let mut luau_expr = add();
        let mut luau_pass = LogicalExprPass::for_dialect(DecompileDialect::Luau);
        assert!(luau_pass.rewrite_expr(&mut luau_expr));
        assert_eq!(luau_expr, HirExpr::Number(5.0));

        let mut puc_expr = add();
        let mut puc_pass = LogicalExprPass::for_dialect(DecompileDialect::Lua54);
        assert!(!puc_pass.rewrite_expr(&mut puc_expr));
        assert!(matches!(puc_expr, HirExpr::Binary(_)));
    }
}
