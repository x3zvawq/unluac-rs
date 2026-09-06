//! HIR 表达式正常完成后的共享抽象值事实。
//!
//! 当前语法投影到共享 LuaValueFacts；真假选择与结果种类由 value_semantics 统一解释。
//! Decision 沿显式边合流，CurrentValue 使用当前 test 的结果而不重新求值。
//! 例如 unknown and false 只能返回 nil/false，不能因此把 nil 当成 boolean。
//! 常量锚定值不依赖临时栈根；动态对象另占一类。本模块不证明事件可删除、binding
//! 在跨调用后不变或物理 home 可释放；路径假设的有效性由调用者证明。

use super::common::{HirBinaryOpKind, HirDecisionExpr, HirDecisionTarget, HirExpr, HirUnaryOpKind};

use crate::value_semantics::results::LuaValueFacts;

pub(in crate::hir) fn value_facts(expr: &HirExpr) -> LuaValueFacts {
    value_facts_with(expr, &|_| None)
}

/// resolver 只发布已证明的结果事实，例如目标 VM 的字面量比较或当前稳定路径假设。
pub(in crate::hir) fn value_facts_with(
    expr: &HirExpr,
    resolve: &impl Fn(&HirExpr) -> Option<LuaValueFacts>,
) -> LuaValueFacts {
    if let Some(facts) = resolve(expr) {
        return facts;
    }
    match expr {
        HirExpr::Nil => LuaValueFacts::NIL,
        HirExpr::Boolean(value) => LuaValueFacts::boolean(*value),
        HirExpr::Integer(_) | HirExpr::Number(_) => LuaValueFacts::NUMERIC,
        HirExpr::String(_) => LuaValueFacts::STRING,
        HirExpr::Int64(_) | HirExpr::UInt64(_) | HirExpr::Vector(_) | HirExpr::Complex { .. } => {
            LuaValueFacts::ANCHORED
        }
        HirExpr::Closure(_) | HirExpr::TableConstructor(_) => LuaValueFacts::RESOURCE,
        HirExpr::Unary(unary) => {
            let operand = value_facts_with(&unary.expr, resolve);
            match unary.op {
                HirUnaryOpKind::Not => operand.logical_not(),
                HirUnaryOpKind::Neg => operand.negated(),
                HirUnaryOpKind::Length => operand.string_length(),
                _ => LuaValueFacts::UNKNOWN,
            }
        }
        HirExpr::Binary(binary) => {
            if matches!(
                binary.op,
                HirBinaryOpKind::Eq | HirBinaryOpKind::Lt | HirBinaryOpKind::Le
            ) {
                return LuaValueFacts::BOOLEAN;
            }
            // bitwise 转换失败可能调用 primitive metatable；concat 结果没有常量锚点。
            if matches!(
                binary.op,
                HirBinaryOpKind::Add
                    | HirBinaryOpKind::Sub
                    | HirBinaryOpKind::Mul
                    | HirBinaryOpKind::Div
                    | HirBinaryOpKind::FloorDiv
                    | HirBinaryOpKind::Mod
                    | HirBinaryOpKind::Pow
            ) {
                value_facts_with(&binary.lhs, resolve)
                    .arithmetic(|| value_facts_with(&binary.rhs, resolve))
            } else {
                LuaValueFacts::UNKNOWN
            }
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            let lhs = value_facts_with(&logical.lhs, resolve);
            let take_rhs_when = matches!(expr, HirExpr::LogicalAnd(_));
            lhs.logical(take_rhs_when, || value_facts_with(&logical.rhs, resolve))
        }
        HirExpr::Decision(decision) => decision_value_facts(decision, resolve),
        _ => LuaValueFacts::UNKNOWN,
    }
}

fn decision_value_facts(
    decision: &HirDecisionExpr,
    resolve: &impl Fn(&HirExpr) -> Option<LuaValueFacts>,
) -> LuaValueFacts {
    let topology = super::decision::analyze_decision(decision);
    let mut facts = vec![None; decision.nodes.len()];
    for node in topology.topological_nodes().rev() {
        let test = value_facts_with(&node.test, resolve);
        let mut result = LuaValueFacts::EMPTY;
        for (truthy, target) in [(true, &node.truthy), (false, &node.falsy)] {
            let current = test.restrict(truthy);
            if current.is_empty() {
                continue;
            }
            result = result.join(match target {
                HirDecisionTarget::Node(child) => {
                    facts[child.index()].expect("child result precedes parent")
                }
                HirDecisionTarget::CurrentValue => current,
                HirDecisionTarget::Expr(expr) => value_facts_with(expr, resolve),
            });
        }
        facts[node.id.index()] = Some(result);
    }
    facts[decision.entry.index()].expect("Decision entry has a result")
}
