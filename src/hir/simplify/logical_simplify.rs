//! 这个文件承载 HIR 的保守逻辑表达式整理。
//!
//! Lua 的 `and/or` 返回的是原始操作数，不是布尔值，所以很多看似显然的布尔代数
//! 恒等式其实并不安全。这里故意只实现一小撮在 Lua 值语义下也严格成立的规则，
//! 用来压掉短路 DAG 恢复后最机械的重复，而不越权重写控制流结构。

use crate::hir::common::{
    HirBlock, HirCallExpr, HirExpr, HirLogicalExpr, HirProto, HirStmt, HirTableConstructor,
    HirTableField, HirTableKey,
};

/// 对单个 proto 递归执行安全的逻辑表达式整理。
pub(super) fn simplify_logical_exprs_in_proto(proto: &mut HirProto) -> bool {
    simplify_block(&mut proto.body)
}

fn simplify_block(block: &mut HirBlock) -> bool {
    block
        .stmts
        .iter_mut()
        .fold(false, |changed, stmt| simplify_stmt(stmt) || changed)
}

fn simplify_stmt(stmt: &mut HirStmt) -> bool {
    match stmt {
        HirStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter_mut()
            .fold(false, |changed, expr| simplify_expr(expr) || changed),
        HirStmt::Assign(assign) => {
            let targets_changed = assign
                .targets
                .iter_mut()
                .fold(false, |changed, target| simplify_lvalue(target) || changed);
            let values_changed = assign
                .values
                .iter_mut()
                .fold(false, |changed, expr| simplify_expr(expr) || changed);
            targets_changed || values_changed
        }
        HirStmt::TableSetList(set_list) => {
            let base_changed = simplify_expr(&mut set_list.base);
            let values_changed = set_list
                .values
                .iter_mut()
                .fold(false, |changed, expr| simplify_expr(expr) || changed);
            let trailing_changed = set_list
                .trailing_multivalue
                .as_mut()
                .is_some_and(simplify_expr);
            base_changed || values_changed || trailing_changed
        }
        HirStmt::ErrNil(err_nil) => simplify_expr(&mut err_nil.value),
        HirStmt::ToBeClosed(to_be_closed) => simplify_expr(&mut to_be_closed.value),
        HirStmt::CallStmt(call_stmt) => simplify_call_expr(&mut call_stmt.call),
        HirStmt::Return(ret) => ret
            .values
            .iter_mut()
            .fold(false, |changed, expr| simplify_expr(expr) || changed),
        HirStmt::If(if_stmt) => {
            simplify_expr(&mut if_stmt.cond)
                || simplify_block(&mut if_stmt.then_block)
                || if_stmt.else_block.as_mut().is_some_and(simplify_block)
        }
        HirStmt::While(while_stmt) => {
            simplify_expr(&mut while_stmt.cond) || simplify_block(&mut while_stmt.body)
        }
        HirStmt::Repeat(repeat_stmt) => {
            simplify_block(&mut repeat_stmt.body) || simplify_expr(&mut repeat_stmt.cond)
        }
        HirStmt::NumericFor(numeric_for) => {
            simplify_expr(&mut numeric_for.start)
                || simplify_expr(&mut numeric_for.limit)
                || simplify_expr(&mut numeric_for.step)
                || simplify_block(&mut numeric_for.body)
        }
        HirStmt::GenericFor(generic_for) => {
            let iterator_changed = generic_for
                .iterator
                .iter_mut()
                .fold(false, |changed, expr| simplify_expr(expr) || changed);
            iterator_changed || simplify_block(&mut generic_for.body)
        }
        HirStmt::Block(block) => simplify_block(block),
        HirStmt::Unstructured(unstructured) => simplify_block(&mut unstructured.body),
        HirStmt::Break
        | HirStmt::Close(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn simplify_lvalue(lvalue: &mut crate::hir::common::HirLValue) -> bool {
    match lvalue {
        crate::hir::common::HirLValue::TableAccess(access) => {
            simplify_expr(&mut access.base) || simplify_expr(&mut access.key)
        }
        crate::hir::common::HirLValue::Temp(_)
        | crate::hir::common::HirLValue::Local(_)
        | crate::hir::common::HirLValue::Upvalue(_)
        | crate::hir::common::HirLValue::Global(_) => false,
    }
}

fn simplify_call_expr(call: &mut HirCallExpr) -> bool {
    let callee_changed = simplify_expr(&mut call.callee);
    let args_changed = call
        .args
        .iter_mut()
        .fold(false, |changed, arg| simplify_expr(arg) || changed);
    callee_changed || args_changed
}

fn simplify_expr(expr: &mut HirExpr) -> bool {
    let mut changed = match expr {
        HirExpr::TableAccess(access) => {
            simplify_expr(&mut access.base) || simplify_expr(&mut access.key)
        }
        HirExpr::Unary(unary) => simplify_expr(&mut unary.expr),
        HirExpr::Binary(binary) => simplify_expr(&mut binary.lhs) || simplify_expr(&mut binary.rhs),
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            simplify_expr(&mut logical.lhs) || simplify_expr(&mut logical.rhs)
        }
        HirExpr::Decision(decision) => simplify_decision_expr(decision),
        HirExpr::Call(call) => simplify_call_expr(call),
        HirExpr::TableConstructor(table) => simplify_table_constructor(table),
        HirExpr::Closure(closure) => closure.captures.iter_mut().fold(false, |acc, capture| {
            simplify_expr(&mut capture.value) || acc
        }),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
    };

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

fn simplify_table_constructor(table: &mut HirTableConstructor) -> bool {
    let fields_changed = table.fields.iter_mut().fold(false, |changed, field| {
        let field_changed = match field {
            HirTableField::Array(expr) => simplify_expr(expr),
            HirTableField::Record(field) => {
                let key_changed = match &mut field.key {
                    HirTableKey::Name(_) => false,
                    HirTableKey::Expr(expr) => simplify_expr(expr),
                };
                let value_changed = simplify_expr(&mut field.value);
                key_changed || value_changed
            }
        };
        changed || field_changed
    });
    let trailing_changed = table
        .trailing_multivalue
        .as_mut()
        .is_some_and(simplify_expr);

    fields_changed || trailing_changed
}

fn simplify_decision_expr(decision: &mut crate::hir::common::HirDecisionExpr) -> bool {
    decision.nodes.iter_mut().fold(false, |changed, node| {
        let test_changed = simplify_expr(&mut node.test);
        let truthy_changed = simplify_decision_target(&mut node.truthy);
        let falsy_changed = simplify_decision_target(&mut node.falsy);
        changed || test_changed || truthy_changed || falsy_changed
    })
}

fn simplify_decision_target(target: &mut crate::hir::common::HirDecisionTarget) -> bool {
    match target {
        crate::hir::common::HirDecisionTarget::Expr(expr) => simplify_expr(expr),
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => false,
    }
}

fn simplify_logical_shape(expr: &HirExpr) -> Option<HirExpr> {
    match expr {
        HirExpr::LogicalAnd(logical) => simplify_logical_and(&logical.lhs, &logical.rhs),
        HirExpr::LogicalOr(logical) => simplify_logical_or(&logical.lhs, &logical.rhs),
        _ => None,
    }
}

fn simplify_logical_and(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    if lhs == rhs {
        return Some(lhs.clone());
    }

    if let Some(replacement) = fold_associative_duplicate_and(lhs, rhs) {
        return Some(replacement);
    }

    if let Some(replacement) = fold_constant_short_circuit_and(lhs, rhs) {
        return Some(replacement);
    }

    match rhs {
        HirExpr::LogicalOr(inner) if lhs == &inner.lhs => Some(lhs.clone()),
        _ => match lhs {
            HirExpr::LogicalOr(inner) if rhs == &inner.lhs || rhs == &inner.rhs => {
                Some(rhs.clone())
            }
            _ => None,
        },
    }
}

fn simplify_logical_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    if lhs == rhs {
        return Some(lhs.clone());
    }

    if let Some(replacement) = fold_associative_duplicate_or(lhs, rhs) {
        return Some(replacement);
    }

    if let Some(replacement) = fold_constant_short_circuit_or(lhs, rhs) {
        return Some(replacement);
    }
    if let Some(replacement) = factor_shared_and_guards(lhs, rhs) {
        return Some(replacement);
    }
    if let Some(replacement) = pull_shared_or_tail(lhs, rhs) {
        return Some(replacement);
    }
    if let Some(replacement) = simplify_or_chain(lhs, rhs) {
        return Some(replacement);
    }
    if let Some(replacement) = fold_shared_fallback_or(lhs, rhs) {
        return Some(replacement);
    }

    match rhs {
        HirExpr::LogicalAnd(inner) if lhs == &inner.lhs => Some(lhs.clone()),
        _ => match lhs {
            // `(x and y) or x == x` 在 Lua 值语义下也严格成立：
            // 当 `x` 为假时，左边退化成 `x`；当 `x` 为真时，右边短路保留 `x`。
            HirExpr::LogicalAnd(inner) if rhs == &inner.lhs || rhs == &inner.rhs => {
                Some(rhs.clone())
            }
            _ => None,
        },
    }
}

fn fold_associative_duplicate_and(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    match lhs {
        HirExpr::LogicalAnd(inner) if rhs == &inner.lhs || rhs == &inner.rhs => Some(lhs.clone()),
        _ => match rhs {
            HirExpr::LogicalAnd(inner) if lhs == &inner.lhs || lhs == &inner.rhs => {
                Some(rhs.clone())
            }
            _ => None,
        },
    }
}

fn fold_associative_duplicate_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    match lhs {
        HirExpr::LogicalOr(inner) if rhs == &inner.lhs || rhs == &inner.rhs => Some(lhs.clone()),
        _ => match rhs {
            HirExpr::LogicalOr(inner) if lhs == &inner.lhs || lhs == &inner.rhs => {
                Some(rhs.clone())
            }
            _ => None,
        },
    }
}

fn factor_shared_and_guards(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    factor_shared_and_guards_one_side(lhs, rhs)
        .or_else(|| factor_shared_and_guards_one_side(rhs, lhs))
}

fn factor_shared_and_guards_one_side(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    let HirExpr::LogicalAnd(lhs_and) = lhs else {
        return None;
    };
    let HirExpr::LogicalAnd(rhs_and) = rhs else {
        return None;
    };

    if lhs_and.lhs == rhs_and.lhs && expr_is_side_effect_free(&lhs_and.lhs) {
        return Some(HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            lhs: lhs_and.lhs.clone(),
            rhs: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                lhs: lhs_and.rhs.clone(),
                rhs: rhs_and.rhs.clone(),
            })),
        })));
    }

    if lhs_and.rhs == rhs_and.rhs && expr_is_side_effect_free(&lhs_and.rhs) {
        return Some(HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            lhs: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                lhs: lhs_and.lhs.clone(),
                rhs: rhs_and.lhs.clone(),
            })),
            rhs: lhs_and.rhs.clone(),
        })));
    }

    None
}

fn pull_shared_or_tail(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    pull_shared_or_tail_one_side(lhs, rhs).or_else(|| pull_shared_or_tail_one_side(rhs, lhs))
}

fn pull_shared_or_tail_one_side(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    let HirExpr::LogicalAnd(lhs_and) = lhs else {
        return None;
    };
    let HirExpr::LogicalOr(inner_or) = &lhs_and.rhs else {
        return None;
    };
    if rhs != &inner_or.rhs || !expr_is_side_effect_free(rhs) {
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

fn simplify_or_chain(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    let terms = flatten_or_chain_exprs(lhs, rhs);
    if terms.len() < 3 {
        return None;
    }

    let mut best = None;
    for left in 0..terms.len() {
        for right in left + 1..terms.len() {
            let rewritten = factor_shared_and_guards_one_side(&terms[left], &terms[right])
                .or_else(|| factor_shared_and_guards_one_side(&terms[right], &terms[left]))
                .or_else(|| pull_shared_or_tail_one_side(&terms[left], &terms[right]))
                .or_else(|| pull_shared_or_tail_one_side(&terms[right], &terms[left]));
            let Some(rewritten) = rewritten else {
                continue;
            };

            let mut rebuilt = Vec::with_capacity(terms.len() - 1);
            for (index, term) in terms.iter().enumerate() {
                if index == left {
                    rebuilt.push(rewritten.clone());
                } else if index != right {
                    rebuilt.push(term.clone());
                }
            }
            let candidate = rebuild_or_chain(rebuilt);
            if expr_cost(&candidate)
                < expr_cost(&HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                })))
            {
                match &best {
                    Some(existing) if expr_cost(existing) <= expr_cost(&candidate) => {}
                    _ => best = Some(candidate),
                }
            }
        }
    }

    best
}

fn flatten_or_chain_exprs(lhs: &HirExpr, rhs: &HirExpr) -> Vec<HirExpr> {
    let mut out = Vec::new();
    collect_or_chain_exprs(lhs, &mut out);
    collect_or_chain_exprs(rhs, &mut out);
    out
}

fn collect_or_chain_exprs(expr: &HirExpr, out: &mut Vec<HirExpr>) {
    match expr {
        HirExpr::LogicalOr(logical) => {
            collect_or_chain_exprs(&logical.lhs, out);
            collect_or_chain_exprs(&logical.rhs, out);
        }
        _ => out.push(expr.clone()),
    }
}

fn rebuild_or_chain(mut terms: Vec<HirExpr>) -> HirExpr {
    let first = terms
        .drain(..1)
        .next()
        .expect("or chain rebuild requires at least one term");
    terms.into_iter().fold(first, |lhs, rhs| {
        HirExpr::LogicalOr(Box::new(HirLogicalExpr { lhs, rhs }))
    })
}

fn expr_cost(expr: &HirExpr) -> usize {
    match expr {
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            1 + expr_cost(&logical.lhs) + expr_cost(&logical.rhs)
        }
        HirExpr::Unary(unary) => 1 + expr_cost(&unary.expr),
        HirExpr::Binary(binary) => 1 + expr_cost(&binary.lhs) + expr_cost(&binary.rhs),
        _ => 1,
    }
}

/// 这里只折叠“左值 truthiness 已知”的短路表达式。
///
/// 这样做的原因是这类重写不需要推导额外控制流，也不会像一般布尔代数那样误伤
/// Lua 的值语义。唯一需要额外守住的是：当运行时原本会短路掉右值时，右值必须
/// 没有副作用，才能把它安全删除。
fn fold_constant_short_circuit_and(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    match expr_truthiness(lhs) {
        Some(true) => Some(rhs.clone()),
        Some(false) if expr_is_side_effect_free(rhs) => Some(lhs.clone()),
        Some(false) => None,
        None => None,
    }
}

/// 这里和 `fold_constant_short_circuit_and` 对偶：只在左值 truthiness 已知时折叠，
/// 并且只在“原本会短路掉右值”的分支上要求右值无副作用。
fn fold_constant_short_circuit_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    match expr_truthiness(lhs) {
        Some(true) if expr_is_side_effect_free(rhs) => Some(lhs.clone()),
        Some(true) => None,
        Some(false) => Some(rhs.clone()),
        None => None,
    }
}

/// 这里处理一类共享 fallback 的机械展开：
///
/// `((not x) and y) or (x or y)` 在 Lua 里和 `x or y` 等价，只是前者会在恢复
/// 决策 DAG 时留下重复的 fallback 片段。只要 `y` 无副作用，这里就可以安全地
/// 把它重新收回更自然的短路表达式。
fn fold_shared_fallback_or(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    shared_fallback_or_one_side(lhs, rhs).or_else(|| shared_fallback_or_one_side(rhs, lhs))
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
    expr_is_side_effect_free(&lhs_and.rhs).then_some(rhs.clone())
}

fn strip_negation(expr: &HirExpr) -> Option<HirExpr> {
    match expr {
        HirExpr::Unary(unary) if matches!(unary.op, crate::hir::common::HirUnaryOpKind::Not) => {
            Some(unary.expr.clone())
        }
        _ => None,
    }
}

fn expr_truthiness(expr: &HirExpr) -> Option<bool> {
    match expr {
        HirExpr::Nil | HirExpr::Boolean(false) => Some(false),
        HirExpr::Boolean(true)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Closure(_)
        | HirExpr::TableConstructor(_) => Some(true),
        HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::LogicalAnd(_)
        | HirExpr::LogicalOr(_)
        | HirExpr::Decision(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => None,
    }
}

fn expr_is_side_effect_free(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_) => true,
        HirExpr::Unary(unary) => expr_is_side_effect_free(&unary.expr),
        HirExpr::Binary(binary) => {
            expr_is_side_effect_free(&binary.lhs) && expr_is_side_effect_free(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_is_side_effect_free(&logical.lhs) && expr_is_side_effect_free(&logical.rhs)
        }
        HirExpr::Decision(decision) => decision.nodes.iter().all(|node| {
            expr_is_side_effect_free(&node.test)
                && decision_target_is_side_effect_free(&node.truthy)
                && decision_target_is_side_effect_free(&node.falsy)
        }),
        HirExpr::TableAccess(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => false,
    }
}

fn decision_target_is_side_effect_free(target: &crate::hir::common::HirDecisionTarget) -> bool {
    match target {
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => true,
        crate::hir::common::HirDecisionTarget::Expr(expr) => expr_is_side_effect_free(expr),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::common::{
        HirAssign, HirLValue, HirLogicalExpr, HirModule, HirProto, HirProtoRef, HirReturn, TempId,
    };

    #[test]
    fn simplifies_safe_lua_logical_absorption() {
        let mut module = HirModule {
            entry: HirProtoRef(0),
            protos: vec![dummy_proto(HirBlock {
                stmts: vec![HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                        lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                            lhs: HirExpr::TempRef(TempId(0)),
                            rhs: HirExpr::TempRef(TempId(1)),
                        })),
                        rhs: HirExpr::TempRef(TempId(1)),
                    }))],
                }))],
            })],
        };

        super::super::simplify_hir(
            &mut module,
            crate::readability::ReadabilityOptions::default(),
        );

        assert!(matches!(
            &module.protos[0].body.stmts.as_slice(),
            [HirStmt::Return(ret)] if matches!(ret.values.as_slice(), [HirExpr::TempRef(TempId(1))])
        ));
    }

    #[test]
    fn keeps_non_safe_lua_logical_shape() {
        let mut proto = dummy_proto(HirBlock {
            stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(2))],
                values: vec![HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                    lhs: HirExpr::TempRef(TempId(0)),
                    rhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                        lhs: HirExpr::TempRef(TempId(1)),
                        rhs: HirExpr::TempRef(TempId(0)),
                    })),
                }))],
            }))],
        });

        assert!(!simplify_logical_exprs_in_proto(&mut proto));
    }

    #[test]
    fn keeps_non_safe_lua_and_or_absorption_shape() {
        let mut proto = dummy_proto(HirBlock {
            stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(2))],
                values: vec![HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                    lhs: HirExpr::TempRef(TempId(0)),
                    rhs: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                        lhs: HirExpr::TempRef(TempId(1)),
                        rhs: HirExpr::TempRef(TempId(0)),
                    })),
                }))],
            }))],
        });

        assert!(!simplify_logical_exprs_in_proto(&mut proto));
    }

    #[test]
    fn folds_constant_short_circuit_when_rhs_is_safe() {
        let mut proto = dummy_proto(HirBlock {
            stmts: vec![HirStmt::Return(Box::new(HirReturn {
                values: vec![HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                    lhs: HirExpr::Boolean(true),
                    rhs: HirExpr::Boolean(false),
                }))],
            }))],
        });

        assert!(simplify_logical_exprs_in_proto(&mut proto));
        assert!(matches!(
            proto.body.stmts.as_slice(),
            [HirStmt::Return(ret)] if matches!(ret.values.as_slice(), [HirExpr::Boolean(true)])
        ));
    }

    #[test]
    fn folds_shared_fallback_tail_back_into_single_or_expr() {
        let mut proto = dummy_proto(HirBlock {
            stmts: vec![HirStmt::Return(Box::new(HirReturn {
                values: vec![HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                    lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                        lhs: HirExpr::Unary(Box::new(crate::hir::common::HirUnaryExpr {
                            op: crate::hir::common::HirUnaryOpKind::Not,
                            expr: HirExpr::TempRef(TempId(0)),
                        })),
                        rhs: HirExpr::String("fallback".into()),
                    })),
                    rhs: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                        lhs: HirExpr::TempRef(TempId(0)),
                        rhs: HirExpr::String("fallback".into()),
                    })),
                }))],
            }))],
        });

        assert!(simplify_logical_exprs_in_proto(&mut proto));
        assert!(matches!(
            proto.body.stmts.as_slice(),
            [HirStmt::Return(ret)]
                if matches!(
                    ret.values.as_slice(),
                    [HirExpr::LogicalOr(logical)]
                        if matches!(&logical.lhs, HirExpr::TempRef(TempId(0)))
                            && matches!(&logical.rhs, HirExpr::String(value) if value == "fallback")
                )
        ));
    }

    #[test]
    fn factors_shared_tail_across_or_chain() {
        let shared_tail = HirExpr::TempRef(TempId(3));
        let mut proto = dummy_proto(HirBlock {
            stmts: vec![HirStmt::Return(Box::new(HirReturn {
                values: vec![HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                    lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                        lhs: HirExpr::TempRef(TempId(0)),
                        rhs: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                            lhs: HirExpr::TempRef(TempId(1)),
                            rhs: shared_tail.clone(),
                        })),
                    })),
                    rhs: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                        lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                            lhs: HirExpr::TempRef(TempId(2)),
                            rhs: HirExpr::TempRef(TempId(1)),
                        })),
                        rhs: shared_tail,
                    })),
                }))],
            }))],
        });

        assert!(simplify_logical_exprs_in_proto(&mut proto));
        assert!(matches!(
            proto.body.stmts.as_slice(),
            [HirStmt::Return(ret)] if matches!(ret.values.as_slice(), [HirExpr::LogicalOr(_)])
        ));
    }

    fn dummy_proto(body: HirBlock) -> HirProto {
        HirProto {
            id: HirProtoRef(0),
            source: None,
            line_range: crate::parser::ProtoLineRange {
                defined_start: 0,
                defined_end: 0,
            },
            signature: crate::parser::ProtoSignature {
                num_params: 0,
                is_vararg: false,
                has_vararg_param_reg: false,
                named_vararg_table: false,
            },
            params: Vec::new(),
            locals: Vec::new(),
            upvalues: Vec::new(),
            temps: vec![TempId(0), TempId(1), TempId(2), TempId(3)],
            temp_debug_locals: vec![None, None, None, None],
            body,
            children: Vec::new(),
        }
    }
}
