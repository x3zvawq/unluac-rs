//! 核对封闭常量选值函数的最终形状与无折扣内联成本。

use super::*;

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
