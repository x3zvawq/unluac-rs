//! 核对单次 repeat 查表的最终函数体和常量返回；原帧由 HIR 的展开事务证明。

use super::*;

fn integer(value: &AstExpr) -> Option<i64> {
    match value {
        AstExpr::Integer(value) => Some(*value),
        AstExpr::Number(value)
            if value.fract() == 0.0
                && (-32768.0..=32767.0).contains(value)
                && value.to_bits() != (-0.0f64).to_bits() =>
        {
            Some(*value as i64)
        }
        _ => None,
    }
}

pub(super) fn body(func: &AstFunctionExpr, template: usize, key: i64, result: i64) -> bool {
    if func.function.index() != template || func.params.len() != 2 {
        return false;
    }
    let [AstStmt::Repeat(loop_), AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
        return false;
    };
    let lookup = match loop_.body.stmts.as_slice() {
        [AstStmt::If(guard), AstStmt::If(test)] => {
            let AstExpr::Unary(not) = &guard.cond else {
                return false;
            };
            if not.op != AstUnaryOpKind::Not
                || not.original_operation
                || not.expr != AstExpr::Var(AstNameRef::Param(func.params[0]))
                || !matches!(guard.then_block.stmts.as_slice(), [AstStmt::Continue])
                || guard.else_block.is_some()
                || test.else_block.is_some()
                || !matches!(test.then_block.stmts.as_slice(), [AstStmt::Break])
            {
                return false;
            }
            let AstExpr::IndexAccess(lookup) = &test.cond else {
                return false;
            };
            lookup
        }
        [AstStmt::If(test)] => {
            let AstExpr::LogicalAnd(and) = &test.cond else {
                return false;
            };
            if and.lhs != AstExpr::Var(AstNameRef::Param(func.params[0]))
                || !matches!(test.then_block.stmts.as_slice(), [AstStmt::Break])
                || test.else_block.is_some()
            {
                return false;
            }
            let AstExpr::IndexAccess(lookup) = &and.rhs else {
                return false;
            };
            lookup
        }
        _ => return false,
    };
    // 常量真首实参折叠 guard/尾条件，留下原查表 TEST；两种结构的 pinned Luau 成本上界为 9。
    lookup.base == AstExpr::Var(AstNameRef::Param(func.params[1]))
        && integer(&lookup.index) == Some(key)
        && loop_.cond == AstExpr::Var(AstNameRef::Param(func.params[0]))
        && matches!(ret.values.as_slice(), [value] if integer(value) == Some(result))
}
