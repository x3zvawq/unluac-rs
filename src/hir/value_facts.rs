//! HIR 表达式正常完成后的共享抽象值事实。
//!
//! 用有限结果集合统一 truthiness、boolean 与 GC 惰性查询；and/or 按短路选择结果，
//! Decision 沿显式边合流，CurrentValue 使用当前 test 的结果而不重新求值。
//! 例如 unknown and false 只能返回 nil/false，不能因此把 nil 当成 boolean。
//! 常量锚定值不依赖临时栈根；动态对象另占一类。本模块不证明事件可删除、binding
//! 在跨调用后不变或物理 home 可释放；路径假设的有效性由调用者证明。

use super::common::{HirBinaryOpKind, HirDecisionExpr, HirDecisionTarget, HirExpr, HirUnaryOpKind};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::hir) struct HirValueFacts(u8);

impl HirValueFacts {
    const NIL: Self = Self(1);
    const FALSE: Self = Self(2);
    const TRUE: Self = Self(4);
    const NUMERIC: Self = Self(8);
    const STRING: Self = Self(16);
    const ANCHORED: Self = Self(32);
    const RESOURCE: Self = Self(64);
    const BOOLEAN: Self = Self(Self::FALSE.0 | Self::TRUE.0);
    const UNKNOWN: Self = Self(127);

    pub(in crate::hir) fn truthiness(self) -> Option<bool> {
        match (self.restrict(false).0 != 0, self.restrict(true).0 != 0) {
            (true, false) => Some(false),
            (false, true) => Some(true),
            _ => None,
        }
    }

    pub(in crate::hir) fn is_boolean(self) -> bool {
        self.0 != 0 && self.0 & !Self::BOOLEAN.0 == 0
    }

    pub(in crate::hir) fn is_gc_inert(self) -> bool {
        self.0 != 0 && self.0 & Self::RESOURCE.0 == 0
    }

    pub(in crate::hir) fn boolean(value: bool) -> Self {
        if value { Self::TRUE } else { Self::FALSE }
    }

    pub(in crate::hir) fn assuming_truthiness(value: bool) -> Self {
        Self::UNKNOWN.restrict(value)
    }

    fn restrict(self, truthy: bool) -> Self {
        let falsy = Self::NIL.0 | Self::FALSE.0;
        Self(self.0 & if truthy { !falsy } else { falsy })
    }

    fn join(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
}

pub(in crate::hir) fn value_facts(expr: &HirExpr) -> HirValueFacts {
    value_facts_with(expr, &|_| None)
}

/// resolver 只发布已证明的结果事实，例如目标 VM 的字面量比较或当前稳定路径假设。
pub(in crate::hir) fn value_facts_with(
    expr: &HirExpr,
    resolve: &impl Fn(&HirExpr) -> Option<HirValueFacts>,
) -> HirValueFacts {
    if let Some(facts) = resolve(expr) {
        return facts;
    }
    match expr {
        HirExpr::Nil => HirValueFacts::NIL,
        HirExpr::Boolean(value) => HirValueFacts::boolean(*value),
        HirExpr::Integer(_) | HirExpr::Number(_) => HirValueFacts::NUMERIC,
        HirExpr::String(_) => HirValueFacts::STRING,
        HirExpr::Int64(_) | HirExpr::UInt64(_) | HirExpr::Vector(_) | HirExpr::Complex { .. } => {
            HirValueFacts::ANCHORED
        }
        HirExpr::Closure(_) | HirExpr::TableConstructor(_) => HirValueFacts::RESOURCE,
        HirExpr::Unary(unary) => {
            let operand = value_facts_with(&unary.expr, resolve);
            match unary.op {
                HirUnaryOpKind::Not => operand
                    .truthiness()
                    .map_or(HirValueFacts::BOOLEAN, |v| HirValueFacts::boolean(!v)),
                HirUnaryOpKind::Neg if operand == HirValueFacts::NUMERIC => HirValueFacts::NUMERIC,
                HirUnaryOpKind::Length if operand == HirValueFacts::STRING => {
                    HirValueFacts::NUMERIC
                }
                _ => HirValueFacts::UNKNOWN,
            }
        }
        HirExpr::Binary(binary) => {
            if matches!(
                binary.op,
                HirBinaryOpKind::Eq | HirBinaryOpKind::Lt | HirBinaryOpKind::Le
            ) {
                return HirValueFacts::BOOLEAN;
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
            ) && value_facts_with(&binary.lhs, resolve) == HirValueFacts::NUMERIC
                && value_facts_with(&binary.rhs, resolve) == HirValueFacts::NUMERIC
            {
                HirValueFacts::NUMERIC
            } else {
                HirValueFacts::UNKNOWN
            }
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            let lhs = value_facts_with(&logical.lhs, resolve);
            let take_rhs_when = matches!(expr, HirExpr::LogicalAnd(_));
            let retained = lhs.restrict(!take_rhs_when);
            if lhs.restrict(take_rhs_when).0 == 0 {
                retained
            } else {
                retained.join(value_facts_with(&logical.rhs, resolve))
            }
        }
        HirExpr::Decision(decision) => decision_value_facts(decision, resolve),
        _ => HirValueFacts::UNKNOWN,
    }
}

fn decision_value_facts(
    decision: &HirDecisionExpr,
    resolve: &impl Fn(&HirExpr) -> Option<HirValueFacts>,
) -> HirValueFacts {
    super::decision::assert_valid_decision(decision);
    let mut facts = vec![None; decision.nodes.len()];
    let mut pending = vec![(decision.entry, false)];
    while let Some((id, expanded)) = pending.pop() {
        if facts[id.index()].is_some() {
            continue;
        }
        let node = &decision.nodes[id.index()];
        if !expanded {
            pending.push((id, true));
            for target in [&node.truthy, &node.falsy] {
                if let HirDecisionTarget::Node(child) = target {
                    pending.push((*child, false));
                }
            }
            continue;
        }
        let test = value_facts_with(&node.test, resolve);
        let mut result = HirValueFacts(0);
        for (truthy, target) in [(true, &node.truthy), (false, &node.falsy)] {
            let current = test.restrict(truthy);
            if current.0 == 0 {
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
        facts[id.index()] = Some(result);
    }
    facts[decision.entry.index()].expect("Decision entry has a result")
}
