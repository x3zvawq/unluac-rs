//! 核对计数 repeat 的最终模板和 Boolean 常量实参，保证恢复调用在 O2 下消失。

use super::*;

pub(super) fn integer(expr: &AstExpr) -> Option<i64> {
    match expr {
        AstExpr::Integer(value) if i16::try_from(*value).is_ok() => Some(*value),
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

pub(super) fn body(
    func: &AstFunctionExpr,
    template: usize,
    initial: i64,
    increment: i64,
    limit: i64,
) -> bool {
    if func.function.index() != template
        || func.params.len() != 3
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.captured_bindings.is_empty()
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    let [
        AstStmt::LocalDecl(decl),
        AstStmt::Repeat(loop_),
        AstStmt::Return(ret),
    ] = func.body.stmts.as_slice()
    else {
        return false;
    };
    let ([binding], [value]) = (decl.bindings.as_slice(), decl.values.as_slice()) else {
        return false;
    };
    let [AstStmt::Assign(assign)] = loop_.body.stmts.as_slice() else {
        return false;
    };
    let [AstExpr::Binary(add)] = assign.values.as_slice() else {
        return false;
    };
    let AstExpr::LogicalOr(outer) = &loop_.cond else {
        return false;
    };
    let AstExpr::LogicalOr(inner) = &outer.rhs else {
        return false;
    };
    let AstExpr::Binary(compare) = &inner.rhs else {
        return false;
    };
    let parameter = |index| AstExpr::Var(AstNameRef::Param(func.params[index]));
    let conjunction = |expr: &AstExpr, right| {
        matches!(expr, AstExpr::LogicalAnd(and)
        if and.lhs == parameter(1) && and.rhs == parameter(right))
    };
    let state = AstExpr::Var(binding.id.to_name_ref());
    // pinned CostModel 对 repeat 乘 3；本模板五个二元条件和一次加法
    // 的成本上界为 18，低于 O2 基础阈值 25，不依赖常量折扣或循环求值结果。
    integer(value) == Some(initial)
        && add.op == AstBinaryOpKind::Add
        && add.lhs == state
        && integer(&add.rhs) == Some(increment)
        && assign.targets.as_slice() == [AstLValue::Name(binding.id.to_name_ref())]
        && ret.values.as_slice() == [state.clone()]
        && conjunction(&outer.lhs, 0)
        && conjunction(&inner.lhs, 2)
        && compare.op == AstBinaryOpKind::Gt
        && compare.lhs == state
        && integer(&compare.rhs) == Some(limit)
}

pub(super) fn arguments(args: &[AstExpr]) -> bool {
    matches!(args, [AstExpr::Boolean(false), AstExpr::Boolean(left), AstExpr::Boolean(right)] if left == right)
}
