//! 核对封闭常量选值函数的最终形状与无折扣内联成本。

use super::*;

/// 比较先预留 Boolean，再准备左值；select 的固定计数参数在 callee 上方依次分配。
pub(super) fn comparison_slots(
    call: &AstCallExpr,
    active: usize,
    occurrences: &BTreeMap<crate::hir::HirSourceSite, crate::hir::LocalId>,
    bodies: &BTreeMap<crate::hir::LocalId, HirLuauInliningBody>,
    slots: &BTreeMap<crate::hir::HirSourceSite, usize>,
    seen: &mut BTreeSet<crate::hir::HirSourceSite>,
) -> bool {
    let [argument] = call.args.as_slice() else {
        return true;
    };
    let mut pending = vec![argument];
    while let Some(value) = pending.pop() {
        if let AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) = value {
            pending.extend([&logical.rhs, &logical.lhs]);
            continue;
        }
        let AstExpr::Binary(binary) = value else {
            continue;
        };
        if binary.op != AstBinaryOpKind::Eq
            || !(literal_cost(&binary.rhs).is_some()
                || matches!(binary.rhs, AstExpr::Var(AstNameRef::Local(_))))
        {
            continue;
        }
        let AstExpr::Call(inner) = &binary.lhs else {
            continue;
        };
        let (value, expected) = if inner.required_luau_inlining.is_some() {
            (inner.as_ref(), active + 2)
        } else if matches!(&inner.callee, AstExpr::Var(AstNameRef::Global(name)) if name.text == "select")
            && inner.method_key.is_none()
            && let [AstExpr::String(marker), AstExpr::SingleValue(value)] = inner.args.as_slice()
            && marker.as_utf8() == Some("#")
            && let AstExpr::Call(value) = value.as_ref()
        {
            (value.as_ref(), active + 4)
        } else {
            continue;
        };
        let Some(site) = value.required_luau_inlining else {
            continue;
        };
        if !occurrences
            .get(&site)
            .and_then(|local| bodies.get(local))
            .is_some_and(|body| {
                matches!(
                    body,
                    HirLuauInliningBody::LiteralChoice { .. }
                        | HirLuauInliningBody::SeededPredicate { .. }
                        | HirLuauInliningBody::ValueExpression { .. }
                        | HirLuauInliningBody::CallingValue { .. }
                        | HirLuauInliningBody::CallingSharedValue { .. }
                        | HirLuauInliningBody::CallingObservedValue { .. }
                        | HirLuauInliningBody::CallingReadPair { .. }
                )
            })
        {
            continue;
        }
        if slots.get(&site) != Some(&expected) || !seen.insert(site) {
            return false;
        }
    }
    true
}

fn literal_cost(value: &AstExpr) -> Option<usize> {
    match value {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_) => Some(1),
        AstExpr::Vector(_) => Some(6),
        _ => None,
    }
}

pub(super) fn body(func: &AstFunctionExpr, template: usize, parameters: usize) -> bool {
    if func.function.index() != template
        || func.params.len() != parameters
        || parameters == 0
        || parameters > 4
        || func.is_vararg
        || !func.captured_bindings.is_empty()
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
        || func.named_vararg.is_some()
    {
        return false;
    }
    let [AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
        return false;
    };
    let [initial] = ret.values.as_slice() else {
        return false;
    };
    let mut value = initial;
    let mut cost = 0;
    if parameters == 1
        && let AstExpr::LogicalOr(first) = value
        && let AstExpr::LogicalAnd(selected) = &first.lhs
        && matches!(selected.lhs, AstExpr::Binary(_))
    {
        while let AstExpr::LogicalOr(other) = value {
            let AstExpr::LogicalAnd(selected) = &other.lhs else {
                return false;
            };
            let AstExpr::Binary(binary) = &selected.lhs else {
                return false;
            };
            if binary.op != crate::ast::AstBinaryOpKind::Eq
                || binary.lhs != AstExpr::Var(AstNameRef::Param(func.params[0]))
                || !matches!(binary.rhs, AstExpr::Nil | AstExpr::Boolean(_))
                || matches!(
                    selected.rhs,
                    AstExpr::Nil | AstExpr::Boolean(false) | AstExpr::Vector(_)
                )
                || literal_cost(&selected.rhs).is_none()
            {
                return false;
            }
            cost += 5;
            value = &other.rhs;
        }
        return !matches!(value, AstExpr::Vector(_))
            && literal_cost(value).is_some_and(|last| cost + last <= 25);
    }
    for parameter in &func.params {
        let AstExpr::LogicalOr(other) = value else {
            return false;
        };
        let AstExpr::LogicalAnd(selected) = &other.lhs else {
            return false;
        };
        if selected.lhs != AstExpr::Var(AstNameRef::Param(*parameter)) {
            return false;
        }
        let Some(value_cost) = literal_cost(&selected.rhs) else {
            return false;
        };
        if matches!(selected.rhs, AstExpr::Nil | AstExpr::Boolean(false)) {
            return false;
        }
        cost += 2 + value_cost;
        value = &other.rhs;
    }
    literal_cost(value).is_some_and(|last| cost + last <= 25)
}
