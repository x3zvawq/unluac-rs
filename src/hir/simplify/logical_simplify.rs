//! 按 Lua 值语义整理 HIR 逻辑表达式和条件。
//!
//! 消费 short-circuit/decision 已恢复的表达式与共享值域、安全性事实，消除机械
//! 重复及合成 NOT 链；原字节码的显式运算保留，不重新分析 CFG 或改写一般控制结构。
//! Lua 的 and/or 返回原操作数，因此 x and x 只有在 x 可稳定重复求值时才可折为 x，
//! 未知值的偶数 NOT 链仍需保留两层布尔转换。具体恒等式的证明放在对应归约处。

use super::expr_facts::{expr_is_boolean_valued, expr_truthiness};
use super::walk::{HirRewritePass, rewrite_proto};
use crate::decompile::DecompileDialect;
use crate::hir::common::{
    HirBinaryOpKind, HirBinding, HirExpr, HirLogicalExpr, HirProto, HirUnaryExpr, HirUnaryOpKind,
};
use crate::hir::expr_safety::{HirExprSafety, luau_literal_addition_value};

/// 对单个 proto 递归执行安全的逻辑表达式整理。
pub(super) fn simplify_logical_exprs_in_proto(
    proto: &mut HirProto,
    dialect: DecompileDialect,
) -> bool {
    rewrite_proto(proto, &mut LogicalExprPass::for_dialect(dialect))
}

struct LogicalExprPass {
    fold_luau_literal_addition: bool,
    safety: HirExprSafety,
}

impl LogicalExprPass {
    fn for_dialect(dialect: DecompileDialect) -> Self {
        Self {
            fold_luau_literal_addition: dialect == DecompileDialect::Luau,
            safety: HirExprSafety::for_dialect(dialect),
        }
    }
}

impl HirRewritePass for LogicalExprPass {
    fn rewrite_expr_before_children(&mut self, expr: &mut HirExpr) -> bool {
        if simplify_equality_negation(expr) {
            true
        } else if simplify_boolean_coercion(expr) {
            // 先让 walker 消费嵌套转换；下一轮统一压缩 NOT 链，避免每个外层
            // coercion 都重新查询尚未归一的完整 operand 值域。
            true
        } else {
            simplify_value_not_chain(expr)
        }
    }

    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        let mut changed = false;

        if let HirExpr::Binary(binary) = expr
            && binary.source_site.is_none()
            && let Some(value) =
                self.safety
                    .primitive_literal_comparison_value(binary.op, &binary.lhs, &binary.rhs)
        {
            *expr = HirExpr::Boolean(value);
            changed = true;
        }

        if let HirExpr::Binary(binary) = expr
            // 原字节码显式运算即使已知结果也要保留；这里只折叠恢复过程合成的表达式。
            && binary.source_site.is_none()
            && binary.op == HirBinaryOpKind::Add
            && let Some(value) = luau_literal_addition_value(&binary.lhs, &binary.rhs)
        {
            if self.fold_luau_literal_addition {
                *expr = value;
                changed = true;
            } else {
                // 候选拒绝[TargetConstraint]：这个精确的 Luau 字面量加法候选在 PUC Lua 下可能有整数结果，不能套用唯一的 f64 number 路径。
            }
        }

        if let Some(replacement) = simplify_logical_shape_with_safety(expr, self.safety) {
            *expr = replacement;
            changed = true;
        }

        changed
    }

    fn rewrite_condition_expr(&mut self, expr: &mut HirExpr) -> bool {
        let mut changed = false;
        if let Some(replacement) = simplify_logical_shape_with_safety(expr, self.safety) {
            *expr = replacement;
            changed = true;
        }
        if let Some(replacement) =
            simplify_condition_truthiness_shape_with_safety(expr, self.safety)
        {
            *expr = replacement;
            changed = true;
        }
        if condition_needs_normalization(expr) {
            *expr = normalize_condition_context(std::mem::replace(expr, HirExpr::Nil), false);
            changed = true;
        }
        changed
    }
}

/// 相等比较树的合成外层 NOT 可下推为 ~=，保留各叶比较及原短路求值顺序。
/// 原 NOT 指令不领此许可；一般值叶或有序比较也不按 Boolean/Eq 的源码发射规则处理。
fn simplify_equality_negation(expr: &mut HirExpr) -> bool {
    fn equality_tree(expr: &HirExpr) -> bool {
        match expr {
            HirExpr::Binary(binary) => binary.op == HirBinaryOpKind::Eq,
            HirExpr::Unary(unary)
                if unary.op == HirUnaryOpKind::Not && unary.source_site.is_none() =>
            {
                matches!(&unary.expr, HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Eq)
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                equality_tree(&logical.lhs) && equality_tree(&logical.rhs)
            }
            _ => false,
        }
    }

    if !matches!(expr, HirExpr::Unary(unary)
        if unary.op == HirUnaryOpKind::Not
            && unary.source_site.is_none()
            && matches!(unary.expr, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))
            && equality_tree(&unary.expr))
    {
        return false;
    }
    let HirExpr::Unary(unary) = std::mem::replace(expr, HirExpr::Nil) else {
        unreachable!()
    };
    *expr = normalize_condition_context(unary.expr, true);
    true
}

/// 两个分支都返回确切 Boolean 时，统一保留一次求值及布尔转换。
/// 这不适用于 `x and true` 或 `x or false`，它们仍可能返回 nil/原值。
/// 原子移动 operand，嵌套转换不反复复制增长的子树。
fn simplify_boolean_coercion(expr: &mut HirExpr) -> bool {
    if !matches!(expr, HirExpr::LogicalOr(or)
        if !or.preserves_boolean_prewrite
            && matches!(or.rhs, HirExpr::Boolean(false))
            && matches!(&or.lhs, HirExpr::LogicalAnd(and)
                if !and.preserves_boolean_prewrite && matches!(and.rhs, HirExpr::Boolean(true))))
    {
        return false;
    }
    let HirExpr::LogicalOr(or) = &*expr else {
        unreachable!()
    };
    let HirExpr::LogicalAnd(and) = &or.lhs else {
        unreachable!()
    };
    if !matches!(
        and.lhs,
        HirExpr::LocalRef(_) | HirExpr::ParamRef(_) | HirExpr::TempRef(_)
    ) && !crate::hir::value_facts::value_facts(&and.lhs).is_gc_inert()
    {
        // 候选拒绝[ProofIncomplete:RootLifetime]：CALL/读取的结果可能仍占原 scratch；
        // 双 NOT 会提前覆盖它。无新增准备的绑定读取及 GC-inert 结果不承担此旧根。
        return false;
    }
    let HirExpr::LogicalOr(or) = std::mem::replace(expr, HirExpr::Nil) else {
        unreachable!("boolean coercion retains its outer or");
    };
    let HirExpr::LogicalAnd(and) = or.lhs else {
        unreachable!("boolean coercion retains its inner and");
    };
    let mut value = and.lhs;
    for _ in 0..2 {
        value = HirExpr::Unary(Box::new(HirUnaryExpr {
            op: HirUnaryOpKind::Not,
            expr: value,
            source_site: None,
        }));
    }
    *expr = value;
    true
}

// 未知值的偶数 NOT 链仍需两层布尔转换；只查询一次底层操作数并移交原节点，
// 避免逐对归约时反复复制或分析同一深链。
fn simplify_value_not_chain(expr: &mut HirExpr) -> bool {
    let mut operand = &*expr;
    let mut depth = 0;
    while let HirExpr::Unary(unary) = operand
        && unary.op == HirUnaryOpKind::Not
        // SemanticBarrier：原 NOT 即使只改变已知 Boolean 的极性也不能按奇偶性删除。
        // 合成外壳可在原运算边界处停止归约，内层原节点仍由 walker 原样保留。
        && unary.source_site.is_none()
    {
        depth += 1;
        operand = &unary.expr;
    }
    if depth < 2 {
        return false;
    }
    let retained = if depth % 2 == 1 {
        1
    } else if expr_is_boolean_valued(operand) {
        0
    } else {
        // 候选拒绝[SemanticBarrier:Value]：not not 0 返回 true，不能恢复为原数值（regress_547）。
        2
    };
    for _ in retained..depth {
        let HirExpr::Unary(unary) = std::mem::replace(expr, HirExpr::Nil) else {
            unreachable!("the proven NOT chain retains its unary prefix");
        };
        *expr = unary.expr;
    }
    retained != depth
}

pub(super) fn simplify_logical_shape_with_safety(
    expr: &HirExpr,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    match expr {
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical)
            if logical.preserves_boolean_prewrite
                || preserves_boolean_prewrite(&logical.lhs)
                || preserves_boolean_prewrite(&logical.rhs) =>
        {
            None
        }
        HirExpr::LogicalAnd(logical) => simplify_logical_and(&logical.lhs, &logical.rhs, safety),
        HirExpr::LogicalOr(logical) => simplify_logical_or(&logical.lhs, &logical.rhs, safety),
        _ => None,
    }
}

fn preserves_boolean_prewrite(expr: &HirExpr) -> bool {
    matches!(expr, HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical)
        if logical.preserves_boolean_prewrite)
}

fn simplify_logical_and(lhs: &HirExpr, rhs: &HirExpr, safety: HirExprSafety) -> Option<HirExpr> {
    if let HirExpr::Unary(unary) = lhs
        && unary.op == HirUnaryOpKind::Not
        && let Some(binding) = HirBinding::from_expr(rhs)
        && HirBinding::from_expr(&unary.expr) == Some(binding)
        && safety.is_repeatable_in_single_value_context(rhs)
    {
        // binding 身份比较为 O(1)，不为复合子树引入重复相等性扫描。
        // falsy 路径必须返回原 nil/false；不能把整个表达式折为 false。
        return Some(HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            preserves_boolean_prewrite: false,
            lhs: binding.expr(),
            rhs: HirExpr::Boolean(false),
        })));
    }

    // 候选拒绝[SemanticBarrier:EvalCount]：`f() and f()` 折成 `f()` 会在首个结果 truthy 时少调用一次。
    if lhs == rhs && safety.is_repeatable_in_single_value_context(lhs) {
        return Some(lhs.clone());
    }

    if let Some(replacement) = fold_associative_duplicate_and(lhs, rhs, safety) {
        return Some(replacement);
    }

    if let Some(replacement) = fold_constant_short_circuit_and(lhs, rhs, safety) {
        return Some(replacement);
    }

    match (rhs, expr_is_boolean_valued(lhs)) {
        (HirExpr::Boolean(true), true) => return Some(lhs.clone()),
        // 候选拒绝[SemanticBarrier:Value]：`1 and true` 返回 true，而直接改成 `1` 返回原始数值。
        (HirExpr::Boolean(true), false) => {}
        _ => {}
    }

    match (lhs, rhs) {
        (lhs, HirExpr::LogicalOr(inner)) if lhs == &inner.lhs => {
            // 候选拒绝[SemanticBarrier:EvalCount]：`f() and (f() or y)` 的 truthy 路径调用两次 `f()`，吸收后只调用一次。
            safety
                .is_repeatable_in_single_value_context(lhs)
                .then(|| lhs.clone())
        }
        (HirExpr::LogicalOr(inner), rhs) if rhs == &inner.rhs => {
            // 候选拒绝[SemanticBarrier:EvalCount]：`(mark() or y) and y` 吸收成 `y` 会删除必达的 `mark()` 求值。
            if !safety.is_discard_safe(&inner.lhs) {
                return None;
            }
            // 候选拒绝[SemanticBarrier:EvalCount]：`(false or f()) and f()` 在首个 `f()` truthy 时调用两次，吸收后只调用一次。
            safety
                .is_repeatable_in_single_value_context(rhs)
                .then(|| rhs.clone())
        }
        _ => None,
    }
}

fn simplify_logical_or(lhs: &HirExpr, rhs: &HirExpr, safety: HirExprSafety) -> Option<HirExpr> {
    // 候选拒绝[SemanticBarrier:EvalCount]：`f() or f()` 折成 `f()` 会在首个结果 falsy 时少调用一次。
    if lhs == rhs && safety.is_repeatable_in_single_value_context(lhs) {
        return Some(lhs.clone());
    }

    if let Some(replacement) = fold_associative_duplicate_or(lhs, rhs, safety) {
        return Some(replacement);
    }

    if let Some(replacement) = fold_constant_short_circuit_or(lhs, rhs, safety) {
        return Some(replacement);
    }

    match (rhs, expr_is_boolean_valued(lhs)) {
        (HirExpr::Boolean(false), true) => return Some(lhs.clone()),
        // 候选拒绝[SemanticBarrier:Value]：`nil or false` 返回 false，而直接改成 lhs 会返回 nil。
        (HirExpr::Boolean(false), false) => {}
        _ => {}
    }
    if let Some(replacement) = naturalize_truthy_ternary(lhs, rhs, safety) {
        return Some(replacement);
    }
    // SemanticBarrier:ControlFlow：公共 guard 即使是稳定绑定，也仍代表两次原检查；
    // 此处没有共享 CFG 节点的证明，不能把 (a and b) or (a and c) 提取成一次 a。
    if let Some(replacement) = pull_shared_or_tail(lhs, rhs, safety) {
        return Some(replacement);
    }
    if let Some(replacement) = fold_shared_fallback_or(lhs, rhs, safety) {
        return Some(replacement);
    }

    match (lhs, rhs) {
        (lhs, HirExpr::LogicalAnd(inner)) if lhs == &inner.lhs => {
            // 候选拒绝[SemanticBarrier:EvalCount]：`f() or (f() and y)` 的 falsy 路径调用两次 `f()`，吸收后只调用一次。
            safety
                .is_repeatable_in_single_value_context(lhs)
                .then(|| lhs.clone())
        }
        (HirExpr::LogicalAnd(inner), rhs) if rhs == &inner.rhs => {
            // 候选拒绝[SemanticBarrier:EvalCount]：`(mark() and y) or y` 吸收成 `y` 会删除必达的 `mark()` 求值。
            if !safety.is_discard_safe(&inner.lhs) {
                return None;
            }
            // 候选拒绝[SemanticBarrier:EvalCount]：`(true and f()) or f()` 在首个 `f()` falsy 时调用两次，吸收后只调用一次。
            safety
                .is_repeatable_in_single_value_context(rhs)
                .then(|| rhs.clone())
        }
        _ => None,
    }
}

/// `not a and x or y` 在 `x/y` 恒真时等价于 `a and y or x`。
///
/// 两种形状都会先且仅求值一次 `a`，随后在 `a` 为真时求值 `y`，否则求值 `x`；
/// 恒真约束保证选中分支不会继续落到另一个分支。
fn naturalize_truthy_ternary(
    lhs: &HirExpr,
    rhs: &HirExpr,
    safety: HirExprSafety,
) -> Option<HirExpr> {
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
    if expr_truthiness(&and_expr.rhs, safety) != Some(true)
        || expr_truthiness(rhs, safety) != Some(true)
    {
        return None;
    }

    Some(HirExpr::LogicalOr(Box::new(HirLogicalExpr {
        preserves_boolean_prewrite: false,
        lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            preserves_boolean_prewrite: false,
            lhs: guard.expr.clone(),
            rhs: rhs.clone(),
        })),
        rhs: and_expr.rhs.clone(),
    })))
}

fn fold_associative_duplicate_and(
    lhs: &HirExpr,
    rhs: &HirExpr,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    // 候选拒绝[SemanticBarrier:EvalCount]：匹配到重复项但其为 `f()` 时，删除一项会减少一次可能调用。
    match (lhs, rhs) {
        (HirExpr::LogicalAnd(inner), rhs)
            if rhs == &inner.rhs && safety.is_repeatable_in_single_value_context(rhs) =>
        {
            Some(lhs.clone())
        }
        (lhs, HirExpr::LogicalAnd(inner))
            if lhs == &inner.lhs && safety.is_repeatable_in_single_value_context(lhs) =>
        {
            Some(rhs.clone())
        }
        _ => None,
    }
}

fn fold_associative_duplicate_or(
    lhs: &HirExpr,
    rhs: &HirExpr,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    // 候选拒绝[SemanticBarrier:EvalCount]：匹配到重复项但其为 `f()` 时，删除一项会减少一次可能调用。
    match (lhs, rhs) {
        (HirExpr::LogicalOr(inner), rhs)
            if rhs == &inner.rhs && safety.is_repeatable_in_single_value_context(rhs) =>
        {
            Some(lhs.clone())
        }
        (lhs, HirExpr::LogicalOr(inner))
            if lhs == &inner.lhs && safety.is_repeatable_in_single_value_context(lhs) =>
        {
            Some(rhs.clone())
        }
        _ => None,
    }
}

fn pull_shared_or_tail(lhs: &HirExpr, rhs: &HirExpr, safety: HirExprSafety) -> Option<HirExpr> {
    pull_shared_or_tail_one_side(lhs, rhs, safety)
}

/// 已证互斥的共同尾可共享构造形状，但后续物理许可仍须覆盖全部原分配。
/// 不改变一般表达式相等关系，也不忽略构造器内部操作与字段求值的来源。
fn merge_alternative_tail(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    if lhs == rhs {
        return Some(lhs.clone());
    }
    let (HirExpr::TableConstructor(lhs), HirExpr::TableConstructor(rhs)) = (lhs, rhs) else {
        return None;
    };
    lhs.merge_alternative(rhs)
        .map(|table| HirExpr::TableConstructor(Box::new(table)))
}

fn pull_shared_or_tail_one_side(
    lhs: &HirExpr,
    rhs: &HirExpr,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    let HirExpr::LogicalAnd(lhs_and) = lhs else {
        return None;
    };
    let HirExpr::LogicalOr(inner_or) = &lhs_and.rhs else {
        return None;
    };
    // 候选拒绝[SemanticBarrier:EvalCount]：`a and (b or f()) or f()` 在 `a` truthy、`b` falsy且首个 `f()` falsy时调用两次，提取后只调用一次。
    // 接受路径[SemanticProof:ShortCircuitReachability]：若共享 tail 恒真，两处 occurrence
    // 互斥；提取只把所选 occurrence 移到同一求值点，不会合并两次求值。
    if expr_truthiness(rhs, safety) != Some(true)
        && !safety.is_repeatable_in_single_value_context(rhs)
    {
        return None;
    }
    let shared_tail = merge_alternative_tail(rhs, &inner_or.rhs)?;

    Some(HirExpr::LogicalOr(Box::new(HirLogicalExpr {
        preserves_boolean_prewrite: false,
        lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            preserves_boolean_prewrite: false,
            lhs: lhs_and.lhs.clone(),
            rhs: inner_or.lhs.clone(),
        })),
        rhs: shared_tail,
    })))
}

/// 这里只折叠“左值 truthiness 已知”的短路表达式。
fn fold_constant_short_circuit_and(
    lhs: &HirExpr,
    rhs: &HirExpr,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    match expr_truthiness(lhs, safety) {
        Some(true) if safety.is_discard_safe(lhs) => Some(rhs.clone()),
        Some(false) if safety.is_discard_safe(lhs) => Some(lhs.clone()),
        // 候选拒绝[SemanticBarrier:EvalCount]：已知 truthy 的 `{ f() }` 仍不可删除，否则字段表达式中的一次 `f()` 消失。
        Some(true) | Some(false) => None,
        None => None,
    }
}

fn fold_constant_short_circuit_or(
    lhs: &HirExpr,
    rhs: &HirExpr,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    match expr_truthiness(lhs, safety) {
        Some(true) if safety.is_discard_safe(lhs) => Some(lhs.clone()),
        Some(false) if safety.is_discard_safe(lhs) => Some(rhs.clone()),
        // 候选拒绝[SemanticBarrier:EvalCount]：已知 falsy 但不可丢弃的 lhs 仍必须求值一次，不能直接选 rhs。
        Some(false) | Some(true) => None,
        None => None,
    }
}

/// 这里处理一类共享 fallback 的机械展开：
///
/// `((not x) and y) or (x or y)` 在 Lua 里和 `x or y` 等价，只是前者会在恢复
/// 决策 DAG 时留下重复的 fallback 片段。只要 `y` 无副作用，这里就可以安全地
/// 把它重新收回更自然的短路表达式。
fn fold_shared_fallback_or(lhs: &HirExpr, rhs: &HirExpr, safety: HirExprSafety) -> Option<HirExpr> {
    shared_fallback_or_one_side(lhs, rhs, safety)
        .or_else(|| shared_fallback_or_one_side(rhs, lhs, safety))
        .or_else(|| fold_prefixed_shared_fallback_or(lhs, rhs, safety))
}

fn shared_fallback_or_one_side(
    lhs: &HirExpr,
    rhs: &HirExpr,
    safety: HirExprSafety,
) -> Option<HirExpr> {
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
    if !safety.is_repeatable_in_single_value_context(lhs)
        || !safety.is_repeatable_in_single_value_context(rhs)
    {
        return None;
    }
    Some(rhs.clone())
}

fn fold_prefixed_shared_fallback_or(
    lhs: &HirExpr,
    rhs: &HirExpr,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    let HirExpr::LogicalOr(rhs_or) = rhs else {
        return None;
    };
    let prefix = HirExpr::LogicalOr(Box::new(HirLogicalExpr {
        preserves_boolean_prewrite: false,
        lhs: lhs.clone(),
        rhs: rhs_or.lhs.clone(),
    }));
    shared_fallback_or_one_side(&rhs_or.rhs, &prefix, safety)
}

fn strip_negation(expr: &HirExpr) -> Option<HirExpr> {
    match expr {
        HirExpr::Unary(unary) if matches!(unary.op, crate::hir::common::HirUnaryOpKind::Not) => {
            Some(unary.expr.clone())
        }
        _ => None,
    }
}

pub(super) fn simplify_condition_truthiness_shape_with_safety(
    expr: &HirExpr,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    let replacement = match expr {
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical)
            if logical.preserves_boolean_prewrite
                || preserves_boolean_prewrite(&logical.lhs)
                || preserves_boolean_prewrite(&logical.rhs) =>
        {
            return None;
        }
        HirExpr::LogicalAnd(logical) => {
            simplify_condition_logical_and(&logical.lhs, &logical.rhs, safety)
        }
        HirExpr::LogicalOr(logical) => {
            simplify_condition_logical_or(&logical.lhs, &logical.rhs, safety)
        }
        _ => None,
    }?;
    // 候选拒绝[PolicyBoundary]：纯条件与值表达式综合共用成本方向，避免先展开
    // `(a or b) and c`，再提取共同尾部，导致同一 pass 每轮往返而无法收敛。
    // 含可观察求值的条件不参与纯综合，仍由各归约的语义证明决定是否接受。
    if safety.is_repeatable_in_single_value_context(expr)
        && super::decision::expr_cost(&replacement) >= super::decision::expr_cost(expr)
    {
        return None;
    }
    Some(replacement)
}

/// 只读投影正、反条件规范形的显式 `not` 成本，不构造任一表达式。
///
/// `not Eq` 可直接打印为 `~=`，成本为零；Lt/Le 在 NaN 或元方法下不能安全反转。
/// 只沿 and/or/not 条件骨架计算，不把调用参数或索引操作数中的 NOT 当作条件极性成本。
pub(super) fn condition_not_costs(expr: &HirExpr) -> [usize; 2] {
    match expr {
        _ if preserves_boolean_prewrite(expr) => [0, 1],
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            let [positive, negative] = condition_not_costs(&unary.expr);
            [negative, positive]
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            let lhs = condition_not_costs(&logical.lhs);
            let rhs = condition_not_costs(&logical.rhs);
            [lhs[0].saturating_add(rhs[0]), lhs[1].saturating_add(rhs[1])]
        }
        _ => [
            0,
            usize::from(
                !matches!(expr, HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Eq),
            ),
        ],
    }
}

/// 移交已选定方向的条件规范形；复用逻辑节点，不为未选方向或未变化的条件复制操作数。
/// De Morgan 只沿 and/or/not 下推，保持 lhs、rhs 顺序；原子反形仍通过 negate 表达。
pub(super) fn normalize_condition_context(expr: HirExpr, negated: bool) -> HirExpr {
    // 原预写与其 TEST 是完整值帧；极性变换只能包住它，不能拆开内部的 and/or。
    if preserves_boolean_prewrite(&expr) {
        return if negated { expr.negate() } else { expr };
    }
    let is_and = matches!(expr, HirExpr::LogicalAnd(_));
    match expr {
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            normalize_condition_context(unary.expr, !negated)
        }
        HirExpr::LogicalAnd(mut logical) | HirExpr::LogicalOr(mut logical) => {
            logical.lhs = normalize_condition_context(logical.lhs, negated);
            logical.rhs = normalize_condition_context(logical.rhs, negated);
            if is_and != negated {
                HirExpr::LogicalAnd(logical)
            } else {
                HirExpr::LogicalOr(logical)
            }
        }
        _ if negated => expr.negate(),
        _ => expr,
    }
}

pub(super) fn condition_needs_normalization(expr: &HirExpr) -> bool {
    match expr {
        _ if preserves_boolean_prewrite(expr) => false,
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            matches!(
                &unary.expr,
                HirExpr::Unary(inner) if inner.op == HirUnaryOpKind::Not
            ) || (matches!(&unary.expr, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))
                && !preserves_boolean_prewrite(&unary.expr))
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            condition_needs_normalization(&logical.lhs)
                || condition_needs_normalization(&logical.rhs)
        }
        _ => false,
    }
}

fn simplify_condition_logical_and(
    lhs: &HirExpr,
    rhs: &HirExpr,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    if matches!(rhs, HirExpr::Boolean(true)) {
        return Some(lhs.clone());
    }
    match (rhs, safety.is_discard_safe(lhs)) {
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

fn simplify_condition_logical_or(
    lhs: &HirExpr,
    rhs: &HirExpr,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    if let Some(replacement) = factor_condition_shared_and_tail(lhs, rhs, safety) {
        return Some(replacement);
    }
    if let Some(replacement) = absorb_stable_or_guard(lhs, rhs, safety) {
        return Some(replacement);
    }
    if matches!(rhs, HirExpr::Boolean(false)) {
        return Some(lhs.clone());
    }
    match (rhs, safety.is_discard_safe(lhs)) {
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
fn factor_condition_shared_and_tail(
    lhs: &HirExpr,
    rhs: &HirExpr,
    safety: HirExprSafety,
) -> Option<HirExpr> {
    let (HirExpr::LogicalAnd(lhs_and), HirExpr::LogicalAnd(rhs_and)) = (lhs, rhs) else {
        return None;
    };
    if expr_truthiness(&lhs_and.rhs, safety) != Some(true) {
        // 候选拒绝[SemanticBarrier:EvalCount]：条件 `(a and f()) or (b and f())` 在首个 `f()` falsy且 b truthy 时调用两次，提取后只调用一次。
        if !safety.is_repeatable_in_single_value_context(&lhs_and.rhs) {
            return None;
        }
        // 候选拒绝[SemanticBarrier:EvalCount]：条件 `(true and false) or (mark() and false)` 原本仍调用 `mark()`，提取后直接返回 false。
        if !safety.is_discard_safe(&rhs_and.lhs) {
            return None;
        }
    }
    let shared_tail = merge_alternative_tail(&lhs_and.rhs, &rhs_and.rhs)?;

    // 接受路径[SemanticProof:ConditionTruthiness]：恒真 tail 只会在被选中的一臂求值一次；
    // 首臂一旦到达 tail 就令外层 or 短路，因此不会删除 b，也不会重复求值 tail。

    Some(HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
        preserves_boolean_prewrite: false,
        lhs: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
            preserves_boolean_prewrite: false,
            lhs: lhs_and.lhs.clone(),
            rhs: rhs_and.lhs.clone(),
        })),
        rhs: shared_tail,
    })))
}

/// In a condition, a stable guard repeated on the left side of a nested `or` is
/// only an implementation detail of a shared short-circuit DAG:
/// `x or ((x or y) and z)` and `x or (y and z)` have the same truthiness and
/// preserve the evaluation order of `y` and `z`.  Keep this rule in the
/// condition-only path; the two expressions do not have the same Lua value.
fn absorb_stable_or_guard(lhs: &HirExpr, rhs: &HirExpr, safety: HirExprSafety) -> Option<HirExpr> {
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
    if !safety.is_repeatable_in_single_value_context(lhs) {
        return None;
    }

    Some(HirExpr::LogicalOr(Box::new(HirLogicalExpr {
        preserves_boolean_prewrite: false,
        lhs: lhs.clone(),
        rhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            preserves_boolean_prewrite: false,
            lhs: inner_or.rhs.clone(),
            rhs: and_expr.rhs.clone(),
        })),
    })))
}
