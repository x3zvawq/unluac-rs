//! 验证 repeat 首段展开的最终源码、常量实参和两类调用的内联成本。

use super::*;

fn integer(expr: &AstExpr) -> Option<i64> {
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

pub(super) fn observation(stmt: &AstStmt, state: &AstNameRef) -> bool {
    matches!(stmt, AstStmt::CallStmt(stmt)
        if matches!(&stmt.call, AstCallKind::Call(call)
            if matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if name.text == "print")
                && call.method_key.is_none() && call.required_luau_inlining.is_none()
                && call.args.as_slice() == [AstExpr::Var(state.clone())]))
}

pub(super) fn body(func: &AstFunctionExpr, template: usize) -> bool {
    if func.function.index() != template || func.params.len() != 2 {
        return false;
    }
    let [
        AstStmt::LocalDecl(decl),
        AstStmt::Repeat(repeat),
        AstStmt::Return(ret),
    ] = func.body.stmts.as_slice()
    else {
        return false;
    };
    let ([binding], [initial]) = (decl.bindings.as_slice(), decl.values.as_slice()) else {
        return false;
    };
    let state = binding.id.to_name_ref();
    if integer(initial).is_none()
        || repeat.cond != AstExpr::Var(AstNameRef::Param(func.params[0]))
        || ret.values.as_slice() != [AstExpr::Var(state.clone())]
    {
        return false;
    }
    let Some((first, rest)) = repeat.body.stmts.split_first() else {
        return false;
    };
    let (steps, remainder) = rest.as_chunks::<3>();
    if !observation(first, &state) || !remainder.is_empty() {
        return false;
    }
    let mut increment = None;
    for (index, step) in steps.iter().enumerate() {
        let [AstStmt::Assign(assign), call, AstStmt::If(branch)] = step else {
            return false;
        };
        let [AstExpr::Binary(binary)] = assign.values.as_slice() else {
            return false;
        };
        let Some(value) = integer(&binary.rhs) else {
            return false;
        };
        if assign.targets.as_slice() != [AstLValue::Name(state.clone())]
            || binary.op != AstBinaryOpKind::Add
            || binary.lhs != AstExpr::Var(state.clone())
            || increment.is_some_and(|previous| previous != value)
            || !observation(call, &state)
            || branch.else_block.is_some()
            || !matches!(&branch.cond, AstExpr::LogicalAnd(cond)
                if cond.lhs == AstExpr::Var(AstNameRef::Param(func.params[0]))
                    && cond.rhs == AstExpr::Var(AstNameRef::Param(func.params[1])))
            || if index + 1 == steps.len() {
                !branch.then_block.stmts.is_empty()
            } else {
                !matches!(branch.then_block.stmts.as_slice(), [AstStmt::Continue])
            }
        {
            return false;
        }
        increment = Some(value);
    }
    crate::hir::luau_repeat_prefix_costs(steps.len())
}

/// 这些普通调用保留原完整路径，成本已由 body 证明高于内联阈值。
pub(super) fn retained_arguments(args: &[AstExpr]) -> bool {
    matches!(args, [first, AstExpr::Boolean(false) | AstExpr::Nil]
        if matches!(first, AstExpr::Boolean(true)) || integer(first).is_some())
}
